#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AWS Lambda handler for Sunrise Image Manager.

Triggered when a job manifest (manifest.json) is uploaded to the S3 uploads/ prefix.
Processes all images in the job: extracts EXIF metadata, compresses, renames with
rolling counter, generates HTML viewer pages, exports CSV, and sends email notification.

Architecture:
  uploads/{office}/{client}/{project}/{datetime}/manifest.json   <-- trigger
  uploads/{office}/{client}/{project}/{datetime}/raw/             <-- raw JPGs
  processed/{office}/{client}/{project}/{datetime}/               <-- compressed images + HTML + CSV
"""

import os
import io
import json
import csv
import re
import logging
import tempfile
import smtplib
from datetime import datetime
from decimal import Decimal, getcontext
from email.message import EmailMessage
from pathlib import Path

import threading
from concurrent.futures import ThreadPoolExecutor, as_completed

import boto3
import piexif
from PIL import Image, ExifTags
from jinja2 import Environment, BaseLoader
from markupsafe import Markup

# Optional geo/DXF dependencies — provided by the geo Lambda Layer.
# If the layer is not attached, DXF export is gracefully skipped.
try:
    import ezdxf
    from ezdxf.addons import Importer
    import shapefile  # pyshp — lightweight shapefile reader
    from shapely.geometry import Point, Polygon, shape
    from pyproj import Transformer
    HAS_GEO = True
except Exception as _geo_err:
    HAS_GEO = False
    # Log at module level so we can diagnose layer attachment issues
    import logging as _logging
    _logging.getLogger().warning("Geo layer import failed (%s): %s", type(_geo_err).__name__, _geo_err)

logger = logging.getLogger()
logger.setLevel(logging.INFO)
logger.info("Geo layer available: %s", HAS_GEO)

s3 = boto3.client("s3")

# Thread-local S3 clients for safe use in ThreadPoolExecutor workers.
# boto3 clients are not guaranteed thread-safe; each worker thread gets its own.
_thread_local = threading.local()


def _get_s3():
    """Return a thread-local S3 client (creates one per thread on first call)."""
    if not hasattr(_thread_local, "s3"):
        _thread_local.s3 = boto3.client("s3")
    return _thread_local.s3

# ---------------------------------------------------------------------------
# Environment / config  (set via Lambda env vars or SSM)
# ---------------------------------------------------------------------------
BUCKET = os.environ.get("S3_BUCKET", "sunrise-image-manager")
DOMAIN_BASE = os.environ.get("DOMAIN_BASE", "https://pano.seihds.com")
DOMAIN_PREFIX = os.environ.get("DOMAIN_PREFIX", "/processed")
MAX_WIDTH = int(os.environ.get("MAX_WIDTH", "8192"))
DEFAULT_JPEG_QUALITY = int(os.environ.get("JPEG_QUALITY", "30"))
PANO_ASPECT_RATIO = float(os.environ.get("PANO_ASPECT_RATIO", "1.9"))
COUNTER_KEY = os.environ.get("COUNTER_KEY", "state/photo_counter.json")
EMAIL_HOST = os.environ.get("EMAIL_HOST", "")
EMAIL_PORT = int(os.environ.get("EMAIL_PORT", "587"))
EMAIL_USER = os.environ.get("EMAIL_USER", "")
EMAIL_PASS = os.environ.get("EMAIL_PASS", "")
EMAIL_SENDER = os.environ.get("EMAIL_SENDER", "")
RECIPIENTS = [r.strip() for r in os.environ.get("EMAIL_RECIPIENTS", "").split(",") if r.strip()]
PANO_TEMPLATE_KEY = os.environ.get("PANO_TEMPLATE_KEY", "templates/Pano-Template.htm")
IMG_TEMPLATE_KEY = os.environ.get("IMG_TEMPLATE_KEY", "templates/img-Template.htm")
EMAIL_TEMPLATE_KEY = os.environ.get("EMAIL_TEMPLATE_KEY", "templates/Email-Report-Template.htm")
MASTER_DXF_KEY = os.environ.get("MASTER_DXF_KEY", "templates/master.dxf")
SHAPEFILE_PREFIX = os.environ.get("SHAPEFILE_PREFIX", "templates/NAD83SPCEPSG")
CLIENTS_KEY = os.environ.get("CLIENTS_KEY", "state/clients.json")
LANDING_PAGE_FILE = os.path.join(os.path.dirname(__file__), "project_landing.html")


# ---------------------------------------------------------------------------
# Rolling photo counter  (stored as JSON in S3)
# ---------------------------------------------------------------------------
def read_photo_counter():
    """Read the rolling photo counter from S3."""
    try:
        obj = s3.get_object(Bucket=BUCKET, Key=COUNTER_KEY)
        data = json.loads(obj["Body"].read().decode("utf-8"))
        return data.get("prefix", "A"), data.get("number", 0)
    except s3.exceptions.NoSuchKey:
        return "A", 0
    except Exception:
        return "A", 0


def write_photo_counter(prefix, number):
    """Persist the rolling photo counter to S3."""
    s3.put_object(
        Bucket=BUCKET,
        Key=COUNTER_KEY,
        Body=json.dumps({"prefix": prefix, "number": number}).encode("utf-8"),
        ContentType="application/json",
    )


def increment_prefix(prefix):
    i = len(prefix) - 1
    while i >= 0 and prefix[i] == "Z":
        i -= 1
    if i == -1:
        return "A" * (len(prefix) + 1)
    return prefix[:i] + chr(ord(prefix[i]) + 1) + "A" * (len(prefix) - i - 1)


# ---------------------------------------------------------------------------
# EXIF helpers
# ---------------------------------------------------------------------------
def convert_to_degrees_with_ref(value, ref):
    getcontext().prec = 28
    try:
        if isinstance(value, (list, tuple)) and len(value) == 3:
            if isinstance(value[0], tuple):
                d = value[0][0] / value[0][1]
                m = value[1][0] / value[1][1]
                s_ = value[2][0] / value[2][1]
            else:
                d, m, s_ = value
            result = d + (m / 60.0) + (s_ / 3600.0)
        else:
            result = float(value)
        if isinstance(ref, str) and ref.upper() in ("S", "W"):
            result = -result
        elif isinstance(ref, (int, float)) and ref == 1:
            result = -result
        return result
    except Exception as e:
        logger.warning("Error converting %s with ref %s: %s", value, ref, e)
        return None


def extract_image_metadata(image_bytes):
    """Extract GPS and datetime EXIF from in-memory image bytes."""
    lat = lon = alt = date_time = None
    try:
        with Image.open(io.BytesIO(image_bytes)) as img:
            exif_data = img._getexif()
            if exif_data:
                exif = {ExifTags.TAGS.get(tag, tag): v for tag, v in exif_data.items()}
                gps_info = exif.get("GPSInfo")
                if gps_info:
                    gps = {ExifTags.GPSTAGS.get(k, k): v for k, v in gps_info.items()}
                    if gps.get("GPSLatitude"):
                        lat = convert_to_degrees_with_ref(gps["GPSLatitude"], gps.get("GPSLatitudeRef"))
                    if gps.get("GPSLongitude"):
                        lon = convert_to_degrees_with_ref(gps["GPSLongitude"], gps.get("GPSLongitudeRef"))
                    if gps.get("GPSAltitude"):
                        alt = convert_to_degrees_with_ref(gps["GPSAltitude"], gps.get("GPSAltitudeRef"))
                date_time = (
                    exif.get("DateTimeOriginal")
                    or exif.get("DateTimeDigitized")
                    or exif.get("DateTime")
                )
    except Exception as e:
        logger.warning("Metadata extraction failed: %s", e)
    return lat, lon, alt, date_time


def classify_image_type(image_bytes):
    """Classify image as 'pano' or 'photo' based on aspect ratio.

    Equirectangular panoramas have a ~2:1 aspect ratio.  Images with
    width/height >= PANO_ASPECT_RATIO (default 1.9) are classified as pano.
    """
    try:
        with Image.open(io.BytesIO(image_bytes)) as img:
            ratio = img.width / img.height
            return "pano" if ratio >= PANO_ASPECT_RATIO else "photo"
    except Exception:
        return "photo"


# ---------------------------------------------------------------------------
# Image compression
# ---------------------------------------------------------------------------
def compress_image(image_bytes, quality=None):
    """Compress image in-memory. Returns (compressed_bytes, content_type)."""
    q = quality or DEFAULT_JPEG_QUALITY
    try:
        # Preserve EXIF
        exif_bytes = None
        try:
            exif_dict = piexif.load(image_bytes)
            if "0th" in exif_dict and 40961 in exif_dict["0th"]:
                del exif_dict["0th"][40961]
            icc_tags = {34675, 319, 318}
            for ifd in exif_dict:
                if ifd == "thumbnail":
                    continue
                for tag in list(exif_dict[ifd].keys()):
                    if tag in icc_tags:
                        del exif_dict[ifd][tag]
            try:
                exif_bytes = piexif.dump(exif_dict)
            except Exception:
                exif_bytes = None
        except Exception:
            exif_bytes = None

        with Image.open(io.BytesIO(image_bytes)) as img:
            img = img.convert("RGB")
            if "icc_profile" in img.info:
                del img.info["icc_profile"]
            if img.width > MAX_WIDTH:
                scale = MAX_WIDTH / img.width
                img = img.resize((MAX_WIDTH, int(img.height * scale)), Image.LANCZOS)
            buf = io.BytesIO()
            if exif_bytes:
                img.save(buf, "JPEG", quality=q, exif=exif_bytes)
            else:
                img.save(buf, "JPEG", quality=q)
            buf.seek(0)
            return buf.read(), "image/jpeg"
    except Exception as e:
        logger.error("Compression failed: %s", e)
        return image_bytes, "image/jpeg"


# ---------------------------------------------------------------------------
# Template rendering
# ---------------------------------------------------------------------------
def load_template_from_s3(template_key):
    """Load a Jinja2 template string from S3."""
    obj = s3.get_object(Bucket=BUCKET, Key=template_key)
    return obj["Body"].read().decode("utf-8")


def render_template_string(template_str, context):
    env = Environment(loader=BaseLoader(), autoescape=True)
    tmpl = env.from_string(template_str)
    return tmpl.render(**context)


# ---------------------------------------------------------------------------
# CSV export
# ---------------------------------------------------------------------------
def generate_csv(images_meta, output_prefix, type_str):
    """Generate CSV content as string with GPS and survey coordinate columns."""
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(["Filename", "Date Taken", "GPSLatitude", "GPSLongitude", "GPSAltitude",
                      "Northing", "Easting", "Elevation", "Hyperlink"])
    first_link = None
    for info in images_meta:
        base = info["base_name"].rsplit(".", 1)[0]
        hyperlink = f"{DOMAIN_BASE}/{output_prefix}{base}.htm"
        if first_link is None:
            first_link = hyperlink
        writer.writerow([base, info.get("date_time"), info.get("lat"), info.get("lon"), info.get("alt"),
                          info.get("northing", ""), info.get("easting", ""), info.get("csv_elevation", ""),
                          hyperlink])
    return buf.getvalue(), first_link


def generate_state_plane_csv(images_meta, output_prefix, type_str):
    """Generate CSV with State Plane coordinates (requires geo layer)."""
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(["Filename", "Date Taken", "ZoneName", "EPSG", "Easting", "Northing",
                      "Elevation_ft", "Hyperlink"])
    rows_written = 0
    for info in images_meta:
        base = info["base_name"].rsplit(".", 1)[0]
        hyperlink = f"{DOMAIN_BASE}/{output_prefix}{base}.htm"

        northing = info.get("northing")
        easting = info.get("easting")
        csv_elev = info.get("csv_elevation")
        if northing is not None and easting is not None:
            # CSV survey coordinates — already in State Plane
            writer.writerow([base, info.get("date_time"), "CSV", "", easting, northing,
                              csv_elev or 0, hyperlink])
            rows_written += 1
        else:
            lat, lon, alt = info.get("lat"), info.get("lon"), info.get("alt")
            if lat is None or lon is None:
                continue
            try:
                zone_name, epsg, x, y, z = latlon_to_state_plane(lat, lon, alt)
                writer.writerow([base, info.get("date_time"), zone_name, epsg, x, y, z, hyperlink])
                rows_written += 1
            except Exception as e:
                logger.warning("State Plane CSV: projection fail for %s: %s", base, e)
    if rows_written == 0:
        return None
    return buf.getvalue()


# ---------------------------------------------------------------------------
# Position CSV parsing  (name, northing, easting, elevation)
# ---------------------------------------------------------------------------
def parse_position_csv(csv_text):
    """Parse a position CSV into a dict keyed by lowercase name (no extension)."""
    positions = {}
    if not csv_text:
        return positions
    reader = csv.DictReader(io.StringIO(csv_text))
    for row in reader:
        name = row.get("name", "").strip()
        if not name:
            continue
        name_key = name.rsplit(".", 1)[0].replace(" ", "_").lower()
        try:
            positions[name_key] = {
                "northing": float(row.get("northing", 0)),
                "easting": float(row.get("easting", 0)),
                "elevation": float(row.get("elevation", 0)),
            }
        except (ValueError, TypeError):
            continue
    return positions


# ---------------------------------------------------------------------------
# Email notification
# ---------------------------------------------------------------------------
def send_email(project_name, client_name, office_name, dt_str, employee,
               office_name_raw, output_prefix, csv_keys=None, dxf_key=None,
               submitter_email=""):
    """Send HTML email notification via SMTP."""
    # Build recipient list: configured recipients + the submitter
    all_recipients = list(RECIPIENTS)
    if submitter_email and submitter_email not in all_recipients:
        all_recipients.append(submitter_email)

    if not EMAIL_HOST or not all_recipients:
        logger.info("Email not configured or no recipients; skipping notification.")
        return
    try:
        template_str = load_template_from_s3(EMAIL_TEMPLATE_KEY)

        # Landing page URL
        landing_url = f"{DOMAIN_BASE}/processed/{office_name_raw}/{client_name}/{project_name}/index.html"

        # Build download links HTML
        link_style = "color:#98805b;text-decoration:underline;"
        download_parts = []
        for csv_key in (csv_keys or []):
            label = csv_key.rsplit("/", 1)[-1]
            url = f"{DOMAIN_BASE}/{csv_key}"
            download_parts.append(f'<a href="{url}" style="{link_style}">{label}</a>')
        if dxf_key:
            label = dxf_key.rsplit("/", 1)[-1]
            url = f"{DOMAIN_BASE}/{dxf_key}"
            download_parts.append(f'<a href="{url}" style="{link_style}">{label}</a>')

        download_links = "<br>".join(download_parts) if download_parts else '<span style="color:#6b7280;">No downloads for this batch</span>'

        logo_url = f"{DOMAIN_BASE}/frontend/logo.jpg"

        html_content = render_template_string(template_str, {
            "OFFICE_NAME": office_name,
            "PROJECT_NAME": project_name,
            "CLIENT_NAME": client_name,
            "UPLOAD_TIME": dt_str,
            "EMPLOYEE": employee,
            "LANDING_URL": landing_url,
            "DOWNLOAD_LINKS": Markup(download_links),
            "LOGO_URL": logo_url,
        })
        msg = EmailMessage()
        msg["Subject"] = f"Sunrise Engineering - Project Update: {project_name}"
        msg["From"] = EMAIL_SENDER
        msg["To"] = ",".join(all_recipients)
        msg.set_content("Project update attached.")
        msg.add_alternative(html_content, subtype="html")
        with smtplib.SMTP(EMAIL_HOST, EMAIL_PORT) as smtp:
            smtp.starttls()
            smtp.login(EMAIL_USER, EMAIL_PASS)
            smtp.send_message(msg)
        logger.info("Status email sent to %s.", ", ".join(all_recipients))
    except Exception as e:
        logger.error("Failed to send email: %s", e)


# ---------------------------------------------------------------------------
# Coordinate projection helpers  (requires geo Lambda Layer)
# ---------------------------------------------------------------------------
_shapefile_cache = None


def _download_shapefile():
    """Download the NAD83 State Plane shapefile components from S3 to /tmp."""
    global _shapefile_cache
    if _shapefile_cache is not None:
        return _shapefile_cache
    tmp = Path(tempfile.gettempdir())
    for ext in (".shp", ".shx", ".dbf", ".prj", ".cpg"):
        key = SHAPEFILE_PREFIX + ext
        local = tmp / ("NAD83SPCEPSG" + ext)
        if not local.exists():
            logger.info("Downloading shapefile component: %s", key)
            s3.download_file(BUCKET, key, str(local))
    _shapefile_cache = str(tmp / "NAD83SPCEPSG.shp")
    return _shapefile_cache


def meters_to_feet(meters):
    return meters * (3937 / 1200)


def _shape_to_polygon(s):
    """Convert a pyshp shape to a Shapely Polygon, handling MULTIPATCH (type 31)."""
    if s.shapeType == 31:  # MULTIPATCH – build polygon from raw points/parts
        parts = list(s.parts) + [len(s.points)]
        rings = [s.points[parts[i]:parts[i + 1]] for i in range(len(parts) - 1)]
        return Polygon(rings[0], rings[1:])
    return shape(s.__geo_interface__)


def latlon_to_state_plane(lat, lon, alt=None):
    """Convert WGS84 lat/lon to State Plane coordinates using the NAD83 shapefile."""
    shp_path = _download_shapefile()
    pt = Point(lon, lat)
    reader = shapefile.Reader(shp_path)
    fields = [f[0] for f in reader.fields[1:]]  # skip DeletionFlag
    for sr in reader.iterShapeRecords():
        try:
            geom = _shape_to_polygon(sr.shape)
        except Exception:
            continue
        if geom.contains(pt):
            rec = dict(zip(fields, sr.record))
            epsg = int(rec["EPSG"])
            transformer = Transformer.from_crs("EPSG:4326", f"EPSG:{epsg}", always_xy=True)
            z = meters_to_feet(alt) if alt is not None else 0
            x, y = transformer.transform(lon, lat)
            return rec["ZONENAME"], epsg, x, y, z
    raise ValueError("No State Plane zone found for this location")


# ---------------------------------------------------------------------------
# DXF export  (requires geo Lambda Layer)
# ---------------------------------------------------------------------------
def export_dxf(bucket, pano_meta, photo_meta, office_name, client_name, project_name, file_dt, output_prefix):
    """
    Export pano and photo locations to a DXF file using block definitions from
    master.dxf.  The output is uploaded to S3 under the processed/ prefix.
    """
    if not HAS_GEO:
        logger.info("Geo layer not available; skipping DXF export.")
        return

    if not pano_meta and not photo_meta:
        return

    # Download master.dxf from S3 to /tmp
    tmp = Path(tempfile.gettempdir())
    master_path = tmp / "master.dxf"
    if not master_path.exists():
        logger.info("Downloading master.dxf from s3://%s/%s", BUCKET, MASTER_DXF_KEY)
        s3.download_file(BUCKET, MASTER_DXF_KEY, str(master_path))

    block_doc = ezdxf.readfile(str(master_path))
    doc = ezdxf.new(dxfversion="R2018")

    pano_block = "pano"
    photo_block = "photo"
    layer_pano = "V-PANO"
    layer_photo = "V-PHOTO"
    block_scale = 5.0

    doc.layers.add(name=layer_pano)
    doc.layers.add(name=layer_photo)
    msp = doc.modelspace()

    # Import block definitions from master.dxf
    for meta, block_name in [(pano_meta, pano_block), (photo_meta, photo_block)]:
        if meta and block_name not in doc.blocks:
            importer = Importer(block_doc, doc)
            importer.import_block(block_name)
            importer.finalize()

    # Determine projection slug from first image with GPS
    proj_slug = "NoGPS"
    for meta_list in (pano_meta, photo_meta):
        for info in meta_list:
            lat, lon, alt = info.get("lat"), info.get("lon"), info.get("alt")
            if lat is not None and lon is not None:
                try:
                    zone_name, _, _, _, _ = latlon_to_state_plane(lat, lon, alt)
                    proj_slug = zone_name.replace(" ", "_")
                    break
                except Exception:
                    continue
        if proj_slug != "NoGPS":
            break

    def insert_blocks(meta_list, block_name, layer_name):
        for info in meta_list:
            northing = info.get("northing")
            easting = info.get("easting")
            csv_elev = info.get("csv_elevation")

            if northing is not None and easting is not None:
                # CSV survey coordinates — use directly (easting=X, northing=Y)
                x, y, z = easting, northing, csv_elev or 0
            else:
                lat, lon, alt = info.get("lat"), info.get("lon"), info.get("alt")
                if lat is None or lon is None:
                    continue
                try:
                    _, epsg, x, y, z = latlon_to_state_plane(lat, lon, alt)
                except Exception as e:
                    logger.warning("Projection fail for %s: %s", info.get("base_name"), e)
                    continue

            base = info["base_name"].rsplit(".", 1)[0]
            hyperlink = f"{DOMAIN_BASE}/{output_prefix}{base}.htm"
            block_ref = msp.add_blockref(block_name, (x, y, z), dxfattribs={
                "layer": layer_name,
                "xscale": block_scale,
                "yscale": block_scale,
                "zscale": block_scale,
            })
            block_ref.add_auto_attribs({
                "###": base,
                "HYPERLINK": hyperlink,
            })

    insert_blocks(pano_meta, pano_block, layer_pano)
    insert_blocks(photo_meta, photo_block, layer_photo)

    # Save DXF to /tmp, then upload to S3
    dxf_filename = f"{client_name}_{project_name}_{file_dt}_{proj_slug}_PanoPhoto.dxf"
    local_dxf = tmp / dxf_filename
    doc.saveas(str(local_dxf))

    dxf_key = f"{output_prefix}{dxf_filename}"
    s3.upload_file(str(local_dxf), bucket, dxf_key)
    logger.info("DXF uploaded to s3://%s/%s", bucket, dxf_key)

    # Clean up local file
    local_dxf.unlink(missing_ok=True)

    return dxf_key


# ---------------------------------------------------------------------------
# Client/project registry  (state/clients.json in S3)
# ---------------------------------------------------------------------------
def register_client_project(office_name, client_name, project_name):
    """Add office/client/project to the registry if not already present."""
    try:
        try:
            obj = s3.get_object(Bucket=BUCKET, Key=CLIENTS_KEY)
            registry = json.loads(obj["Body"].read().decode("utf-8"))
        except Exception:
            registry = {}

        office_clients = registry.get(office_name, {})
        projects = office_clients.get(client_name, [])
        if project_name not in projects:
            projects.append(project_name)
            office_clients[client_name] = sorted(projects)
            registry[office_name] = office_clients
            s3.put_object(
                Bucket=BUCKET,
                Key=CLIENTS_KEY,
                Body=json.dumps(registry, indent=2).encode("utf-8"),
                ContentType="application/json",
            )
            logger.info("Registered office/client/project: %s / %s / %s", office_name, client_name, project_name)
    except Exception as e:
        logger.warning("Failed to update client registry: %s", e)


# ---------------------------------------------------------------------------
# Project landing page  (index.html + index.json per project)
# ---------------------------------------------------------------------------
def update_project_index(bucket, office_name, client_name, project_name, file_dt, employee_name,
                         pano_meta, photo_meta, output_prefix, csv_files=None, dxf_file=None,
                         plan_background=None):
    """Append the current batch to the project index and deploy the landing page."""
    project_prefix = f"processed/{office_name}/{client_name}/{project_name}/"
    index_key = f"{project_prefix}index.json"

    # Read existing index or start fresh
    try:
        obj = s3.get_object(Bucket=bucket, Key=index_key)
        index_data = json.loads(obj["Body"].read().decode("utf-8"))
    except Exception:
        index_data = {"office_name": office_name, "client_name": client_name, "project_name": project_name, "batches": []}

    # Store plan background reference if provided (project-level, not per-batch)
    if plan_background:
        index_data["plan_background"] = plan_background

    # Check if this project is password-protected
    auth_key = f"state/project-auth/{office_name}/{client_name}/{project_name}.json"
    try:
        s3.head_object(Bucket=bucket, Key=auth_key)
        index_data["protected"] = True
    except Exception:
        index_data.pop("protected", None)

    # Build image entries (paths relative to project_prefix)
    images = []
    for meta in pano_meta:
        name = meta["base_name"]
        base = name.rsplit(".", 1)[0]
        images.append({
            "filename": name, "type": "pano",
            "lat": meta.get("lat"), "lon": meta.get("lon"),
            "northing": meta.get("northing"), "easting": meta.get("easting"),
            "date_time": meta.get("date_time", ""),
            "viewer": f"{file_dt}/{base}.htm", "src": f"{file_dt}/{name}",
        })
    for meta in photo_meta:
        name = meta["base_name"]
        base = name.rsplit(".", 1)[0]
        images.append({
            "filename": name, "type": "photo",
            "lat": meta.get("lat"), "lon": meta.get("lon"),
            "northing": meta.get("northing"), "easting": meta.get("easting"),
            "date_time": meta.get("date_time", ""),
            "viewer": f"{file_dt}/{base}.htm", "src": f"{file_dt}/{name}",
        })

    # Relativize download paths
    def rel(key):
        return key.replace(project_prefix, "") if key else None

    batch_entry = {
        "file_dt": file_dt,
        "employee": employee_name,
        "submitted_at": datetime.utcnow().isoformat() + "Z",
        "pano_count": len(pano_meta),
        "photo_count": len(photo_meta),
        "csv_files": [rel(k) for k in (csv_files or [])],
        "dxf_file": rel(dxf_file),
        "images": images,
    }

    # Replace batch with same file_dt (re-processing), or append
    index_data["batches"] = [b for b in index_data["batches"] if b["file_dt"] != file_dt]
    index_data["batches"].append(batch_entry)

    # Write index.json (no-cache so CloudFront serves fresh data after appends)
    s3.put_object(
        Bucket=bucket, Key=index_key,
        Body=json.dumps(index_data, indent=2).encode("utf-8"),
        ContentType="application/json",
        CacheControl="no-cache, no-store, must-revalidate",
    )

    # Deploy landing page HTML (no-cache so users always see latest batches)
    try:
        with open(LANDING_PAGE_FILE, "r") as f:
            landing_html = f.read()
        s3.put_object(
            Bucket=bucket, Key=f"{project_prefix}index.html",
            Body=landing_html.encode("utf-8"),
            ContentType="text/html",
            CacheControl="no-cache, no-store, must-revalidate",
        )
    except Exception as e:
        logger.warning("Failed to deploy landing page: %s", e)

    logger.info("Updated project index: s3://%s/%s", bucket, index_key)


# ---------------------------------------------------------------------------
# Write a status.json so the desktop client can poll for completion
# ---------------------------------------------------------------------------
def write_status(prefix, status, message="", output_prefix="", first_link="", landing_page=""):
    body = json.dumps({
        "status": status,
        "message": message,
        "output_prefix": output_prefix,
        "first_link": first_link,
        "landing_page": landing_page,
        "updated_at": datetime.utcnow().isoformat() + "Z",
    })
    s3.put_object(
        Bucket=BUCKET,
        Key=f"{prefix}status.json",
        Body=body.encode("utf-8"),
        ContentType="application/json",
    )


# ---------------------------------------------------------------------------
# Main Lambda handler
# ---------------------------------------------------------------------------
def lambda_handler(event, context):
    """
    Triggered by S3 PUT on uploads/*/manifest.json.
    The manifest contains: client_name, project_name, employee_name, file_dt,
    and lists of pano_keys / photo_keys / image_keys (S3 keys of raw uploaded
    images).  Images in image_keys are auto-classified by aspect ratio.
    """
    for record in event.get("Records", []):
        bucket = record["s3"]["bucket"]["name"]
        manifest_key = record["s3"]["object"]["key"]
        logger.info("Processing manifest: s3://%s/%s", bucket, manifest_key)

        # Read manifest
        obj = s3.get_object(Bucket=bucket, Key=manifest_key)
        manifest = json.loads(obj["Body"].read().decode("utf-8"))

        office_name = manifest["office_name"]
        client_name = manifest["client_name"]
        project_name = manifest["project_name"]
        employee_name = manifest["employee_name"]
        file_dt = manifest["file_dt"]

        # Validate path components (defense-in-depth — API already validates)
        safe_name_re = re.compile(r'^[A-Za-z0-9][A-Za-z0-9_\-\.]{0,127}$')
        for name, label in [(office_name, "office_name"), (client_name, "client_name"),
                            (project_name, "project_name"), (file_dt, "file_dt")]:
            if not safe_name_re.match(name):
                raise ValueError(f"Invalid {label}: {name!r}")

        pano_keys = list(manifest.get("pano_keys", []))
        photo_keys = list(manifest.get("photo_keys", []))
        image_keys = manifest.get("image_keys", [])
        keep_filenames = manifest.get("keep_filenames", False)
        keep_originals = manifest.get("keep_originals", False)
        jpeg_quality = manifest.get("jpeg_quality")
        position_csv = manifest.get("position_csv", "")
        submitter_email = manifest.get("submitter_email", "")
        plan_key = manifest.get("plan_key", "")

        # Parse position CSV into lookup dict
        csv_positions = parse_position_csv(position_csv)

        # Auto-classify unclassified images by aspect ratio.
        # Only reads enough to check dimensions, then discards bytes.
        if image_keys:
            logger.info("Auto-classifying %d unclassified images", len(image_keys))
            for key in image_keys:
                try:
                    img_obj = s3.get_object(Bucket=bucket, Key=key)
                    img_bytes = img_obj["Body"].read()
                    img_type = classify_image_type(img_bytes)
                    del img_bytes  # free immediately — Phase 1 of process_image_set will re-download for EXIF
                    if img_type == "pano":
                        pano_keys.append(key)
                    else:
                        photo_keys.append(key)
                    logger.info("Classified %s as %s", key.rsplit("/", 1)[-1], img_type)
                except Exception as e:
                    logger.warning("Failed to classify %s, defaulting to photo: %s", key, e)
                    photo_keys.append(key)

        job_prefix = f"uploads/{office_name}/{client_name}/{project_name}/{file_dt}/"
        output_prefix = f"processed/{office_name}/{client_name}/{project_name}/{file_dt}/"

        write_status(job_prefix, "processing", "Image processing started")

        try:
            # Load templates once
            pano_template_str = load_template_from_s3(PANO_TEMPLATE_KEY)
            img_template_str = load_template_from_s3(IMG_TEMPLATE_KEY)

            # Process panos and photos
            total_images = len(pano_keys) + len(photo_keys)
            pano_meta = process_image_set(bucket, pano_keys, output_prefix, client_name, project_name, file_dt, "Pano", pano_template_str,
                                          keep_filenames=keep_filenames, keep_originals=keep_originals, jpeg_quality=jpeg_quality, csv_positions=csv_positions,
                                          job_prefix=job_prefix, total_images=total_images, images_done=0)
            photo_meta = process_image_set(bucket, photo_keys, output_prefix, client_name, project_name, file_dt, "Photo", img_template_str,
                                           keep_filenames=keep_filenames, keep_originals=keep_originals, jpeg_quality=jpeg_quality, csv_positions=csv_positions,
                                           job_prefix=job_prefix, total_images=total_images, images_done=len(pano_keys))

            # Generate CSVs
            first_link = None
            csv_keys = []
            if pano_meta:
                csv_content, first_link = generate_csv(pano_meta, output_prefix, "pano")
                csv_key = f"{output_prefix}{file_dt}_{client_name}_{project_name}_pano_WGS84.csv"
                s3.put_object(Bucket=bucket, Key=csv_key, Body=csv_content.encode("utf-8"), ContentType="text/csv")
                csv_keys.append(csv_key)
            if photo_meta:
                csv_content, link = generate_csv(photo_meta, output_prefix, "photo")
                csv_key = f"{output_prefix}{file_dt}_{client_name}_{project_name}_photo_WGS84.csv"
                s3.put_object(Bucket=bucket, Key=csv_key, Body=csv_content.encode("utf-8"), ContentType="text/csv")
                csv_keys.append(csv_key)
                if not first_link:
                    first_link = link

            # Generate DXF and State Plane CSVs (if geo layer is available)
            dxf_key = None
            try:
                dxf_key = export_dxf(bucket, pano_meta, photo_meta, office_name, client_name, project_name, file_dt, output_prefix)
            except Exception as e:
                logger.error("DXF export failed (non-fatal): %s", e, exc_info=True)

            if HAS_GEO:
                for meta_list, type_str in [(pano_meta, "pano"), (photo_meta, "photo")]:
                    if not meta_list:
                        continue
                    try:
                        sp_content = generate_state_plane_csv(meta_list, output_prefix, type_str)
                        if sp_content:
                            sp_key = f"{output_prefix}{file_dt}_{client_name}_{project_name}_{type_str}_StatePlane.csv"
                            s3.put_object(Bucket=bucket, Key=sp_key, Body=sp_content.encode("utf-8"), ContentType="text/csv")
                            csv_keys.append(sp_key)
                    except Exception as e:
                        logger.error("State Plane CSV failed for %s (non-fatal): %s", type_str, e, exc_info=True)

            # Copy plan background to project folder if provided
            plan_background = None
            if plan_key:
                try:
                    project_prefix = f"processed/{office_name}/{client_name}/{project_name}/"
                    plan_dest = f"{project_prefix}plan.jpg"
                    s3.copy_object(
                        Bucket=bucket,
                        CopySource={"Bucket": bucket, "Key": plan_key},
                        Key=plan_dest,
                        ContentType="image/jpeg",
                    )
                    plan_background = "plan.jpg"
                    logger.info("Plan background copied to s3://%s/%s", bucket, plan_dest)
                except Exception as e:
                    logger.error("Failed to copy plan background: %s", e)

            # Update project landing page (appendable across batches)
            update_project_index(bucket, office_name, client_name, project_name, file_dt, employee_name,
                                 pano_meta, photo_meta, output_prefix, csv_files=csv_keys, dxf_file=dxf_key,
                                 plan_background=plan_background)

            # Send email (include submitter)
            send_email(project_name, client_name, office_name, file_dt, employee_name,
                       office_name, output_prefix, csv_keys=csv_keys, dxf_key=dxf_key,
                       submitter_email=submitter_email)

            # Register office/client/project in the registry
            register_client_project(office_name, client_name, project_name)

            landing_url = f"{DOMAIN_BASE}/processed/{office_name}/{client_name}/{project_name}/index.html"
            write_status(job_prefix, "complete", "Processing finished", output_prefix, first_link or "", landing_url)
            logger.info("Job complete: %s", output_prefix)

        except Exception as e:
            logger.error("Job failed: %s", e, exc_info=True)
            write_status(job_prefix, "error", str(e))
            raise

    return {"statusCode": 200, "body": "OK"}


# Max parallel workers — balances throughput vs. Lambda memory/connections.
# Each worker holds one full image in memory (~5-30 MB), so 10 workers ≈ 300 MB peak.
_PARALLEL_WORKERS = 10


def process_image_set(bucket, s3_keys, output_prefix, client_name, project_name, file_dt, type_str, template_str,
                      keep_filenames=False, keep_originals=False, jpeg_quality=None, csv_positions=None,
                      job_prefix=None, total_images=0, images_done=0):
    """
    Process images in two phases to support large batches (1500+) without OOM.

    Phase 1 — Metadata scan (low memory):
        Download each image, extract EXIF (GPS/datetime), discard bytes.
        Only metadata + S3 key are kept. Memory: ~1 KB per image.

    Phase 2 — Parallel process + upload:
        After sorting and assigning filenames, re-download each image from S3,
        compress, render HTML, and upload — all in parallel via ThreadPoolExecutor.
        S3→S3 within the same region is fast (~100 ms/file), so the re-download
        cost is negligible compared to the parallelism gained.
        Peak memory: ~_PARALLEL_WORKERS images × 5-30 MB each ≈ 300 MB.
    """
    if not s3_keys:
        return []
    csv_positions = csv_positions or {}

    # ── Phase 1: Parallel metadata scan ────────────────────────────────
    # Each worker downloads one image, extracts EXIF, and discards the
    # bytes immediately.  Peak memory: _PARALLEL_WORKERS × one image.
    image_meta = [None] * len(s3_keys)

    def _scan_metadata(idx, key):
        """Download one image, extract EXIF metadata, discard bytes."""
        local_s3 = _get_s3()
        obj = local_s3.get_object(Bucket=bucket, Key=key)
        img_bytes = obj["Body"].read()
        lat, lon, alt, date_time = extract_image_metadata(img_bytes)
        del img_bytes

        if date_time:
            try:
                dt = datetime.strptime(date_time, "%Y:%m:%d %H:%M:%S")
            except Exception:
                dt = datetime.utcnow()
        else:
            dt = datetime.utcnow()

        orig_filename = key.rsplit("/", 1)[-1]
        orig_base = orig_filename.rsplit(".", 1)[0].lower()
        pos = csv_positions.get(orig_base)

        return {
            "s3_key": key,
            "orig_filename": orig_filename,
            "lat": lat, "lon": lon, "alt": alt,
            "northing": pos["northing"] if pos else None,
            "easting": pos["easting"] if pos else None,
            "csv_elevation": pos["elevation"] if pos else None,
            "date_time": date_time,
            "sort_dt": dt,
        }

    with ThreadPoolExecutor(max_workers=_PARALLEL_WORKERS) as executor:
        futures = {}
        for idx, key in enumerate(s3_keys):
            futures[executor.submit(_scan_metadata, idx, key)] = idx
        for future in as_completed(futures):
            idx = futures[future]
            try:
                image_meta[idx] = future.result()
            except Exception as e:
                logger.warning("Failed to read metadata for %s: %s", s3_keys[idx], e)

    image_meta = [m for m in image_meta if m is not None]

    # Sort by datetime
    image_meta.sort(key=lambda x: x["sort_dt"])

    # Assign sequential filenames (must be done before parallel phase)
    if not keep_filenames:
        prefix, number = read_photo_counter()

    for meta in image_meta:
        if keep_filenames:
            meta["final_name"] = meta["orig_filename"]
            meta["base_name"] = meta["final_name"].rsplit(".", 1)[0]
        else:
            number += 1
            if number > 999:
                number = 1
                prefix = increment_prefix(prefix)
            meta["final_name"] = f"{prefix}{number:03d}.jpg"
            meta["base_name"] = f"{prefix}{number:03d}"

    # ── Phase 2: Parallel download → compress → upload ──────────────────
    results = [None] * len(image_meta)
    processed_count = [0]  # mutable counter for progress reporting

    def _process_single(idx, meta):
        """Download, compress, render HTML, and upload a single image."""
        local_s3 = _get_s3()

        # Re-download from S3
        obj = local_s3.get_object(Bucket=bucket, Key=meta["s3_key"])
        img_bytes = obj["Body"].read()

        # Compress (or keep original)
        if keep_originals:
            output_bytes, content_type = img_bytes, "image/jpeg"
        else:
            output_bytes, content_type = compress_image(img_bytes, quality=jpeg_quality)
        del img_bytes  # free raw bytes

        # Upload compressed image to S3
        img_key = f"{output_prefix}{meta['final_name']}"
        local_s3.put_object(Bucket=bucket, Key=img_key, Body=output_bytes, ContentType=content_type)
        del output_bytes  # free compressed bytes

        # Render and upload HTML viewer page
        dt_str = meta.get("date_time")
        try:
            dt_obj = datetime.strptime(dt_str, "%Y:%m:%d %H:%M:%S") if dt_str else datetime.utcnow()
        except Exception:
            dt_obj = datetime.utcnow()
        converted_dt = dt_obj.strftime("%d-%b-%y %I:%M:%S%p")

        html_content = render_template_string(template_str, {
            "TITLE": client_name,
            "DESCRIPTION": file_dt,
            "IMG": meta["final_name"],
            "IMG_DATE": converted_dt,
        })
        html_key = f"{output_prefix}{meta['base_name']}.htm"
        local_s3.put_object(Bucket=bucket, Key=html_key,
                            Body=html_content.encode("utf-8"), ContentType="text/html")

        return {
            "base_name": meta["final_name"],
            "lat": meta["lat"], "lon": meta["lon"], "alt": meta["alt"],
            "northing": meta["northing"], "easting": meta["easting"],
            "csv_elevation": meta["csv_elevation"],
            "date_time": dt_str,
        }

    with ThreadPoolExecutor(max_workers=_PARALLEL_WORKERS) as executor:
        futures = {}
        for idx, meta in enumerate(image_meta):
            futures[executor.submit(_process_single, idx, meta)] = idx

        for future in as_completed(futures):
            idx = futures[future]
            results[idx] = future.result()  # raises on error

            processed_count[0] += 1
            # Report progress every 10 images
            if job_prefix and total_images and processed_count[0] % 10 == 0:
                done = images_done + processed_count[0]
                write_status(job_prefix, "processing",
                             f"Processing {done}/{total_images} images...")

    if not keep_filenames:
        write_photo_counter(prefix, number)
    logger.info("Processed %d %s images", len(results), type_str)
    return results
