#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AWS Lambda handler for Sunrise Image Manager.

Triggered when a job manifest (manifest.json) is uploaded to the S3 uploads/ prefix.
Processes all images in the job: extracts EXIF metadata, compresses, renames with
rolling counter, generates HTML viewer pages, exports CSV, and sends email notification.

Architecture:
  uploads/{client}/{project}/{datetime}/manifest.json   <-- trigger
  uploads/{client}/{project}/{datetime}/raw/             <-- raw JPGs
  processed/{client}/{project}/{datetime}/               <-- compressed images + HTML + CSV
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

import boto3
import piexif
from PIL import Image, ExifTags
from jinja2 import Environment, BaseLoader

# Optional geo/DXF dependencies — provided by the geo Lambda Layer.
# If the layer is not attached, DXF export is gracefully skipped.
try:
    import ezdxf
    from ezdxf.addons import Importer
    import geopandas as gpd
    from shapely.geometry import Point
    from pyproj import Transformer
    HAS_GEO = True
except ImportError:
    HAS_GEO = False

logger = logging.getLogger()
logger.setLevel(logging.INFO)

s3 = boto3.client("s3")

# ---------------------------------------------------------------------------
# Environment / config  (set via Lambda env vars or SSM)
# ---------------------------------------------------------------------------
BUCKET = os.environ.get("S3_BUCKET", "sunrise-image-manager")
DOMAIN_BASE = os.environ.get("DOMAIN_BASE", "https://www.seihds.com")
DOMAIN_PREFIX = os.environ.get("DOMAIN_PREFIX", "/auto")
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
    env = Environment(loader=BaseLoader())
    tmpl = env.from_string(template_str)
    return tmpl.render(**context)


# ---------------------------------------------------------------------------
# CSV export
# ---------------------------------------------------------------------------
def generate_csv(images_meta, client_name, project_name, file_dt, type_str):
    """Generate WGS84 CSV content as string."""
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(["Filename", "Date Taken", "GPSLatitude", "GPSLongitude", "GPSAltitude", "Hyperlink"])
    domain_path = f"{DOMAIN_PREFIX}/{client_name}/{project_name}/{file_dt}"
    first_link = None
    for info in images_meta:
        base = info["base_name"].rsplit(".", 1)[0]
        hyperlink = f"{DOMAIN_BASE}{domain_path}/{base}.htm"
        if first_link is None:
            first_link = hyperlink
        writer.writerow([base, info.get("date_time"), info.get("lat"), info.get("lon"), info.get("alt"), hyperlink])
    return buf.getvalue(), first_link


# ---------------------------------------------------------------------------
# Email notification
# ---------------------------------------------------------------------------
def send_email(project_name, client_name, dt_str, employee, first_link, s3_output_prefix):
    """Send HTML email notification via SMTP."""
    if not EMAIL_HOST or not RECIPIENTS:
        logger.info("Email not configured; skipping notification.")
        return
    try:
        template_str = load_template_from_s3(EMAIL_TEMPLATE_KEY)
        html_content = render_template_string(template_str, {
            "PROJECT_NAME": project_name,
            "CLIENT_NAME": client_name,
            "UPLOAD_TIME": dt_str,
            "EMPLOYEE": employee,
            "PANO_LINK": first_link or "",
            "DIRECTORY_PATH": f"s3://{BUCKET}/{s3_output_prefix}",
        })
        msg = EmailMessage()
        msg["Subject"] = f"Sunrise Engineering - Project Update: {project_name}"
        msg["From"] = EMAIL_SENDER
        msg["To"] = ",".join(RECIPIENTS)
        msg.set_content("Project update attached.")
        msg.add_alternative(html_content, subtype="html")
        with smtplib.SMTP(EMAIL_HOST, EMAIL_PORT) as smtp:
            smtp.starttls()
            smtp.login(EMAIL_USER, EMAIL_PASS)
            smtp.send_message(msg)
        logger.info("Status email sent.")
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


def latlon_to_state_plane(lat, lon, alt=None):
    """Convert WGS84 lat/lon to State Plane coordinates using the NAD83 shapefile."""
    shp_path = _download_shapefile()
    zones = gpd.read_file(shp_path)
    pt = Point(lon, lat)
    match = zones[zones.contains(pt)]
    if match.empty:
        raise ValueError("No State Plane zone found for this location")
    zone = match.iloc[0]
    epsg = int(zone["EPSG"])
    transformer = Transformer.from_crs("EPSG:4326", f"EPSG:{epsg}", always_xy=True)
    z = meters_to_feet(alt) if alt is not None else 0
    x, y = transformer.transform(lon, lat)
    return zone["ZONENAME"], epsg, x, y, z


# ---------------------------------------------------------------------------
# DXF export  (requires geo Lambda Layer)
# ---------------------------------------------------------------------------
def export_dxf(bucket, pano_meta, photo_meta, client_name, project_name, file_dt, output_prefix):
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

    domain_path = f"{DOMAIN_PREFIX}/{client_name}/{project_name}/{file_dt}"

    def insert_blocks(meta_list, block_name, layer_name):
        for info in meta_list:
            lat, lon, alt = info.get("lat"), info.get("lon"), info.get("alt")
            if lat is None or lon is None:
                continue
            try:
                _, epsg, x, y, z = latlon_to_state_plane(lat, lon, alt)
            except Exception as e:
                logger.warning("Projection fail for %s: %s", info.get("base_name"), e)
                continue
            base = info["base_name"].rsplit(".", 1)[0]
            hyperlink = f"{DOMAIN_BASE}{domain_path}/{base}.htm"
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
# Write a status.json so the desktop client can poll for completion
# ---------------------------------------------------------------------------
def write_status(prefix, status, message="", output_prefix="", first_link=""):
    body = json.dumps({
        "status": status,
        "message": message,
        "output_prefix": output_prefix,
        "first_link": first_link,
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

        client_name = manifest["client_name"]
        project_name = manifest["project_name"]
        employee_name = manifest["employee_name"]
        file_dt = manifest["file_dt"]
        pano_keys = list(manifest.get("pano_keys", []))
        photo_keys = list(manifest.get("photo_keys", []))
        image_keys = manifest.get("image_keys", [])

        # Auto-classify unclassified images by aspect ratio
        if image_keys:
            logger.info("Auto-classifying %d unclassified images", len(image_keys))
            for key in image_keys:
                try:
                    img_obj = s3.get_object(Bucket=bucket, Key=key)
                    img_bytes = img_obj["Body"].read()
                    img_type = classify_image_type(img_bytes)
                    if img_type == "pano":
                        pano_keys.append(key)
                    else:
                        photo_keys.append(key)
                    logger.info("Classified %s as %s", key.rsplit("/", 1)[-1], img_type)
                except Exception as e:
                    logger.warning("Failed to classify %s, defaulting to photo: %s", key, e)
                    photo_keys.append(key)

        job_prefix = f"uploads/{client_name}/{project_name}/{file_dt}/"
        output_prefix = f"processed/{client_name}/{project_name}/{file_dt}/"

        write_status(job_prefix, "processing", "Image processing started")

        try:
            # Load templates once
            pano_template_str = load_template_from_s3(PANO_TEMPLATE_KEY)
            img_template_str = load_template_from_s3(IMG_TEMPLATE_KEY)

            # Process panos and photos
            pano_meta = process_image_set(bucket, pano_keys, output_prefix, client_name, project_name, file_dt, "Pano", pano_template_str)
            photo_meta = process_image_set(bucket, photo_keys, output_prefix, client_name, project_name, file_dt, "Photo", img_template_str)

            # Generate CSVs
            first_link = None
            if pano_meta:
                csv_content, first_link = generate_csv(pano_meta, client_name, project_name, file_dt, "pano")
                csv_key = f"{output_prefix}{file_dt}_{client_name}_{project_name}_pano_WGS84.csv"
                s3.put_object(Bucket=bucket, Key=csv_key, Body=csv_content.encode("utf-8"), ContentType="text/csv")
            if photo_meta:
                csv_content, link = generate_csv(photo_meta, client_name, project_name, file_dt, "photo")
                csv_key = f"{output_prefix}{file_dt}_{client_name}_{project_name}_photo_WGS84.csv"
                s3.put_object(Bucket=bucket, Key=csv_key, Body=csv_content.encode("utf-8"), ContentType="text/csv")
                if not first_link:
                    first_link = link

            # Generate DXF (if geo layer is available)
            export_dxf(bucket, pano_meta, photo_meta, client_name, project_name, file_dt, output_prefix)

            # Send email
            send_email(project_name, client_name, file_dt, employee_name, first_link, output_prefix)

            write_status(job_prefix, "complete", "Processing finished", output_prefix, first_link or "")
            logger.info("Job complete: %s", output_prefix)

        except Exception as e:
            logger.error("Job failed: %s", e, exc_info=True)
            write_status(job_prefix, "error", str(e))
            raise

    return {"statusCode": 200, "body": "OK"}


def process_image_set(bucket, s3_keys, output_prefix, client_name, project_name, file_dt, type_str, template_str):
    """
    Download raw images from S3, extract metadata, rename, compress, generate HTML,
    upload processed outputs back to S3. Returns list of metadata dicts.
    """
    if not s3_keys:
        return []

    # Download and collect metadata
    raw_images = []
    for key in s3_keys:
        try:
            obj = s3.get_object(Bucket=bucket, Key=key)
            img_bytes = obj["Body"].read()
            lat, lon, alt, date_time = extract_image_metadata(img_bytes)
            if date_time:
                try:
                    dt = datetime.strptime(date_time, "%Y:%m:%d %H:%M:%S")
                except Exception:
                    dt = datetime.utcnow()
            else:
                dt = datetime.utcnow()
            raw_images.append({
                "s3_key": key,
                "bytes": img_bytes,
                "lat": lat,
                "lon": lon,
                "alt": alt,
                "date_time": date_time,
                "sort_dt": dt,
            })
        except Exception as e:
            logger.warning("Failed to download %s: %s", key, e)

    # Sort by datetime
    raw_images.sort(key=lambda x: x["sort_dt"])

    # Rename with rolling counter
    prefix, number = read_photo_counter()
    results = []

    for img_data in raw_images:
        number += 1
        if number > 999:
            number = 1
            prefix = increment_prefix(prefix)

        final_name = f"{prefix}{number:03d}.jpg"
        base_name = f"{prefix}{number:03d}"

        # Compress
        compressed_bytes, content_type = compress_image(img_data["bytes"])

        # Upload compressed image to S3
        img_key = f"{output_prefix}{final_name}"
        s3.put_object(
            Bucket=bucket,
            Key=img_key,
            Body=compressed_bytes,
            ContentType=content_type,
        )

        # Build metadata for CSV/HTML
        dt_str = img_data.get("date_time")
        try:
            dt_obj = datetime.strptime(dt_str, "%Y:%m:%d %H:%M:%S") if dt_str else datetime.utcnow()
        except Exception:
            dt_obj = datetime.utcnow()
        converted_dt = dt_obj.strftime("%d-%b-%y %I:%M:%S%p")

        # Render HTML viewer page
        html_content = render_template_string(template_str, {
            "TITLE": client_name,
            "DESCRIPTION": file_dt,
            "IMG": final_name,
            "IMG_DATE": converted_dt,
        })
        html_key = f"{output_prefix}{base_name}.htm"
        s3.put_object(
            Bucket=bucket,
            Key=html_key,
            Body=html_content.encode("utf-8"),
            ContentType="text/html",
        )

        results.append({
            "base_name": final_name,
            "lat": img_data["lat"],
            "lon": img_data["lon"],
            "alt": img_data["alt"],
            "date_time": dt_str,
        })

    write_photo_counter(prefix, number)
    logger.info("Processed %d %s images", len(results), type_str)
    return results
