#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SIM_configured.py
Refactor of SIM.py to externalize ALL hardcoded paths into a JSON config file.

How it works
------------
- Looks for a config file path in the environment variable SIM_CONFIG or a --config=<path> CLI arg.
- If not provided, it tries a local "config.json" next to this script and then "~/.sim_config.json".
- Reads paths, site options, image settings, employee list, etc. from that JSON.
- Secrets (FTP/Email) are managed through keyring for secure credential storage.

Author: ChatGPT (refactor for Kevin)
Date: 2025-09-09
"""

import os
import sys
import re
import json
import shutil
import threading
import time
import logging
from datetime import datetime
from pathlib import Path
from decimal import Decimal, getcontext
import ftplib
import csv
import smtplib
from email.message import EmailMessage
from concurrent.futures import ThreadPoolExecutor, as_completed

import piexif
from PIL import Image, ExifTags
import geopandas as gpd
from shapely.geometry import Point
from pyproj import Transformer
import keyring
from jinja2 import Environment, FileSystemLoader
import ezdxf
from ezdxf.addons import Importer

from PyQt5.QtWidgets import (
    QApplication, QMainWindow, QWidget, QLabel, QVBoxLayout, QHBoxLayout, QPushButton,
    QFileDialog, QMessageBox, QInputDialog, QComboBox, QLineEdit, QDialog, QDialogButtonBox, QTextEdit, QFrame,
    QFormLayout, QGroupBox, QScrollArea, QSpinBox, QCheckBox
)
from PyQt5.QtGui import QPixmap, QFont, QPalette, QColor, QDragEnterEvent, QDropEvent, QIcon
from PyQt5.QtCore import Qt, QMimeData, QSize, pyqtSignal
import warnings
from PIL import Image

warnings.simplefilter('ignore', Image.DecompressionBombWarning)

# --------------------
# Config loading
# --------------------
def _parse_cli_for_config(argv: list) -> Path | None:
    for a in argv[1:]:
        if a.startswith("--config="):
            return Path(a.split("=", 1)[1]).expanduser().resolve()
    return None

def _first_existing(paths: list[Path]) -> Path | None:
    for p in paths:
        try:
            if p and p.exists():
                return p
        except Exception:
            continue
    return None

def find_config_path() -> Path | None:
    # Priority: CLI arg -> ENV var -> local config.json -> ~/.sim_config.json
    cli = _parse_cli_for_config(sys.argv)
    if cli:
        return cli
    env = os.environ.get("SIM_CONFIG", "").strip()
    if env:
        return Path(env).expanduser().resolve()
    here = Path(__file__).resolve().parent / "config.json"
    home = Path.home() / ".sim_config.json"
    return _first_existing([here, home])

def load_config() -> dict:
    cfg_path = find_config_path()
    if not cfg_path:
        logging.warning("No config.json found. Using safe built-in defaults. "
                        "Set SIM_CONFIG or place a config.json next to the script.")
        return {}
    try:
        with open(cfg_path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        logging.error(f"Failed to read config file at {cfg_path}: {e}")
        return {}

def cfg_get(cfg: dict, dotted: str, default=None):
    cur = cfg
    for part in dotted.split("."):
        if not isinstance(cur, dict) or part not in cur:
            return default
        cur = cur[part]
    return cur

CONFIG: dict = load_config()

# --------------------
# Logging
# --------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s"
)

def safe_mkdir(path: Path):
    path.mkdir(parents=True, exist_ok=True)
    return path

def setup_project_logging(client_name, project_name, file_dt):
    """Setup logging to write to the project-specific directory"""
    output_directory = safe_mkdir(OUTPUT_ROOT / client_name / project_name / file_dt)
    log_file_path = output_directory / "sunrise_app.log"

    # Remove existing handlers
    for handler in logging.root.handlers[:]:
        logging.root.removeHandler(handler)

    # Setup new file handler
    file_handler = logging.FileHandler(str(log_file_path))
    file_handler.setLevel(logging.INFO)
    formatter = logging.Formatter("%(asctime)s [%(levelname)s] %(message)s")
    file_handler.setFormatter(formatter)

    # Add the handler to the root logger
    logging.root.addHandler(file_handler)

    logging.info(f"Logging initialized for project: {client_name}/{project_name}/{file_dt}")
    return log_file_path

# --------------------
# Keyring credential management
# --------------------
KEYRING_SERVICE = "SIM-FTP-Credentials"

def get_ftp_credentials():
    """Get FTP credentials from keyring"""
    try:
        server = keyring.get_password(KEYRING_SERVICE, "FTP_SERVER")
        username = keyring.get_password(KEYRING_SERVICE, "FTP_USERNAME")
        password = keyring.get_password(KEYRING_SERVICE, "FTP_PASSWORD")
        return server, username, password
    except Exception as e:
        logging.error(f"Failed to retrieve FTP credentials from keyring: {e}")
        return None, None, None

def set_ftp_credentials(server, username, password):
    """Set FTP credentials in keyring"""
    try:
        keyring.set_password(KEYRING_SERVICE, "FTP_SERVER", server)
        keyring.set_password(KEYRING_SERVICE, "FTP_USERNAME", username)
        keyring.set_password(KEYRING_SERVICE, "FTP_PASSWORD", password)
        logging.info("FTP credentials saved to keyring successfully")
        return True
    except Exception as e:
        logging.error(f"Failed to save FTP credentials to keyring: {e}")
        return False

def get_email_credentials():
    """Get email credentials from keyring"""
    try:
        host = keyring.get_password(KEYRING_SERVICE, "EMAIL_HOST")
        port = keyring.get_password(KEYRING_SERVICE, "EMAIL_PORT")
        user = keyring.get_password(KEYRING_SERVICE, "EMAIL_USER")
        password = keyring.get_password(KEYRING_SERVICE, "EMAIL_PASSWORD")
        sender = keyring.get_password(KEYRING_SERVICE, "EMAIL_SENDER")
        return host, port, user, password, sender
    except Exception as e:
        logging.error(f"Failed to retrieve email credentials from keyring: {e}")
        return None, None, None, None, None

def set_email_credentials(host, port, user, password, sender):
    """Set email credentials in keyring"""
    try:
        keyring.set_password(KEYRING_SERVICE, "EMAIL_HOST", host)
        keyring.set_password(KEYRING_SERVICE, "EMAIL_PORT", str(port))
        keyring.set_password(KEYRING_SERVICE, "EMAIL_USER", user)
        keyring.set_password(KEYRING_SERVICE, "EMAIL_PASSWORD", password)
        keyring.set_password(KEYRING_SERVICE, "EMAIL_SENDER", sender)
        logging.info("Email credentials saved to keyring successfully")
        return True
    except Exception as e:
        logging.error(f"Failed to save email credentials to keyring: {e}")
        return False

# Load credentials from keyring
FTP_SERVER, FTP_USERNAME, FTP_PASSWORD = get_ftp_credentials()
EMAIL_HOST, EMAIL_PORT_STR, EMAIL_USER, EMAIL_PASS, EMAIL_SENDER = get_email_credentials()
EMAIL_PORT = int(EMAIL_PORT_STR) if EMAIL_PORT_STR else 587

# --------------------
# Paths & settings from JSON
# --------------------
MASTER_DXF = Path(cfg_get(CONFIG, "paths.master_dxf", "")).expanduser()
OUTPUT_ROOT = Path(cfg_get(CONFIG, "paths.output_root", "./output")).expanduser()
TEMPLATES_DIR = Path(cfg_get(CONFIG, "paths.templates_dir", "./templates")).expanduser()
PHOTO_COUNTER_PATH = Path(cfg_get(CONFIG, "paths.photo_counter", "./_ROLLING_COUNT/photo_counter.txt")).expanduser()
STATEPLANE_SHAPEFILE = Path(cfg_get(CONFIG, "paths.stateplane_shapefile", "./NAD83SPCEPSG.shp")).expanduser()
RECIPIENTS_FILE = Path(cfg_get(CONFIG, "paths.recipients_file", "./email_recipients.txt")).expanduser()

TEMP_ROOT = Path(cfg_get(CONFIG, "paths.temp_root", "./panoTemp")).expanduser()

DOMAIN_BASE = cfg_get(CONFIG, "site.domain_base", "https://www.seihds.com")
DOMAIN_PREFIX = cfg_get(CONFIG, "site.domain_prefix", "/auto")

MAX_WIDTH = int(cfg_get(CONFIG, "images.max_width", 8192))
DEFAULT_JPEG_QUALITY = int(cfg_get(CONFIG, "images.compress_quality", 30))

EMPLOYEE_NAMES = list(cfg_get(CONFIG, "employees", ["Alan", "Burt", "Gabe", "Kevin", "Morgan", "Nick", "Tanner"]))

FTP_MAX_THREADS = int(cfg_get(CONFIG, "ftp.max_threads_probe", 6))

# ---- UI Constants ----
SUNRISE_NAVY = "#113e59"
SUNRISE_GRAY = "#a7a9ac"
SUNRISE_YELLOW = "#ffd457"
SUNRISE_RUBY = "#d2342e"
SUNRISE_FONT = cfg_get(CONFIG, "ui.font_family", "Segoe UI")
HEADER_FONT = QFont(SUNRISE_FONT, 16, QFont.Bold)
SUBHEADER_FONT = QFont(SUNRISE_FONT, 12, QFont.Bold)
BODY_FONT = QFont(SUNRISE_FONT, 10)

# --------------------
# Utility helpers
# --------------------
def validate_ftp_credentials():
    if not FTP_SERVER or not FTP_USERNAME or not FTP_PASSWORD:
        logging.error("🚨 FTP credentials are missing or incomplete. Please configure them in the settings.")
        return False
    logging.info(f"✅ FTP credentials loaded: server={FTP_SERVER}, username={FTP_USERNAME}")
    return True

def strip_extension(filename: str) -> str:
    name, _ = os.path.splitext(filename)
    return name

def increment_prefix(prefix: str) -> str:
    i = len(prefix) - 1
    while i >= 0 and prefix[i] == 'Z':
        i -= 1
    if i == -1:
        return 'A' * (len(prefix) + 1)
    return (
        prefix[:i] +
        chr(ord(prefix[i]) + 1) +
        'A' * (len(prefix) - i - 1)
    )

def read_photo_counter(counter_file_path):
    prefix = "A"
    number = 0
    if Path(counter_file_path).exists():
        with open(counter_file_path, "r") as f:
            for line in f:
                if line.startswith("CurrentPrefix="):
                    prefix = line.strip().split("=")[1]
                elif line.startswith("CurrentNumber="):
                    number = int(line.strip().split("=")[1])
    return prefix, number

def write_photo_counter(counter_file_path, prefix, number):
    safe_mkdir(Path(counter_file_path).parent)
    with open(counter_file_path, "w") as f:
        f.write(f"CurrentPrefix={prefix}\n")
        f.write(f"CurrentNumber={number}\n")

def convert_to_degrees_with_ref(value, ref):
    getcontext().prec = 28
    try:
        if isinstance(value, (list, tuple)) and len(value) == 3:
            if isinstance(value[0], tuple):
                d = value[0][0] / value[0][1]
                m = value[1][0] / value[1][1]
                s = value[2][0] / value[2][1]
            else:
                d, m, s = value
            result = d + (m / 60.0) + (s / 3600.0)
        else:
            result = float(value)
        if isinstance(ref, str) and ref.upper() in ["S", "W"]:
            result = -result
        elif isinstance(ref, (int, float)) and ref == 1:
            result = -result
        return result
    except Exception as e:
        logging.warning(f"Error converting {value} with ref {ref}: {e}")
        return None

def meters_to_feet(meters: float):
    factor = 3937 / 1200
    return meters * factor

def latlon_to_state_plane_auto(lat: float, lon: float, alt=None):
    zones = gpd.read_file(STATEPLANE_SHAPEFILE)
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

def extract_image_metadata(image_path):
    lat = lon = alt = date_time = None
    try:
        with Image.open(image_path) as img:
            exif_data = img._getexif()
            if exif_data:
                exif = {ExifTags.TAGS.get(tag, tag): value for tag, value in exif_data.items()}
                gps_info = exif.get("GPSInfo")
                if gps_info:
                    gps_data = {ExifTags.GPSTAGS.get(k, k): v for k, v in gps_info.items()}
                    lat = convert_to_degrees_with_ref(gps_data.get("GPSLatitude"), gps_data.get("GPSLatitudeRef")) if gps_data.get("GPSLatitude") else None
                    lon = convert_to_degrees_with_ref(gps_data.get("GPSLongitude"), gps_data.get("GPSLongitudeRef")) if gps_data.get("GPSLongitude") else None
                    alt = convert_to_degrees_with_ref(gps_data.get("GPSAltitude"), gps_data.get("GPSAltitudeRef")) if gps_data.get("GPSAltitude") else None
                date_time = exif.get("DateTimeOriginal") or exif.get("DateTimeDigitized") or exif.get("DateTime")
    except Exception as e:
        logging.warning(f"Metadata extraction fail: {image_path}: {e}")
    return lat, lon, alt, date_time

def compress_image(input_image_path: Path, remote_dir, quality=None):
    q = int(DEFAULT_JPEG_QUALITY if quality is None else quality)
    compressed_dir = safe_mkdir(OUTPUT_ROOT / remote_dir / "Compressed")
    try:
        exif_bytes = None
        try:
            exif_dict = piexif.load(str(input_image_path))
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

        with Image.open(str(input_image_path)) as img:
            img = img.convert("RGB")
            if "icc_profile" in img.info:
                del img.info["icc_profile"]
            if img.width > MAX_WIDTH:
                scale_factor = MAX_WIDTH / img.width
                new_width = MAX_WIDTH
                new_height = int(img.height * scale_factor)
                img = img.resize((new_width, new_height), Image.LANCZOS)
            new_path = compressed_dir / input_image_path.name
            if exif_bytes:
                img.save(str(new_path), "JPEG", quality=q, exif=exif_bytes)
            else:
                img.save(str(new_path), "JPEG", quality=q)
            return str(new_path)
    except Exception as e:
        logging.warning(f"Compression failed for {input_image_path}: {e}")
        return None

# --------------------
# FILE PROCESSING WORKFLOW
# --------------------
def process_image_set(files, client_name, project_name, file_dt, remote_dir, employee_name, type_str):
    """
    Copies images to temp, renames them, compresses, extracts metadata,
    and returns a dict of all relevant info per image.
    """
    temp_dir = safe_mkdir(TEMP_ROOT / type_str)
    for file in temp_dir.iterdir():
        if file.is_file():
            file.unlink()
    for file_path in files:
        if str(file_path).lower().endswith(".jpg"):
            shutil.copy2(file_path, temp_dir)
    image_files = list(temp_dir.glob("*.jpg"))
    if not image_files:
        logging.warning(f"No images found in {temp_dir}")
        return {}

    # Sort by EXIF datetime, fallback to file time
    img_meta_list = []
    for file in image_files:
        lat, lon, alt, date_time = extract_image_metadata(file)
        if date_time:
            try:
                dt = datetime.strptime(date_time, "%Y:%m:%d %H:%M:%S")
            except Exception:
                dt = datetime.fromtimestamp(file.stat().st_mtime)
        else:
            dt = datetime.fromtimestamp(file.stat().st_mtime)
        img_meta_list.append((file, lat, lon, alt, date_time, dt))

    img_meta_list.sort(key=lambda x: x[5])
    renamed_images = {}
    photo_prefix, photo_number = read_photo_counter(PHOTO_COUNTER_PATH)

    with ThreadPoolExecutor(max_workers=4) as executor:
        futures = {}
        for idx, (file, lat, lon, alt, date_time, dt) in enumerate(img_meta_list, start=1):
            photo_number += 1
            if photo_number > 999:
                photo_number = 1
                photo_prefix = increment_prefix(photo_prefix)
            ext = file.suffix.lower()
            final_name = f"{photo_prefix}{photo_number:03d}{ext}"
            final_path = file.parent / final_name
            if final_path.exists():
                final_path.unlink()
            file.rename(final_path)
            futures[executor.submit(compress_image, final_path, remote_dir, DEFAULT_JPEG_QUALITY)] = (
                final_name, str(final_path), lat, lon, alt, date_time
            )

    write_photo_counter(PHOTO_COUNTER_PATH, photo_prefix, photo_number)

    for future in as_completed(futures):
        final_name, final_path, lat, lon, alt, date_time = futures[future]
        compressed_path = future.result()
        renamed_images[final_name] = {
            "base_name": final_name,
            "full_path": final_path,
            "compressed_path": compressed_path,
            "lat": lat,
            "lon": lon,
            "alt": alt,
            "date_time": date_time,
        }
    return renamed_images

# --------------------
# CSV, DXF, and HTML EXPORTS
# --------------------
def make_domain_path(client_name, project_name, dt):
    # domain prefix is configurable, e.g., "/auto"
    return f"{DOMAIN_PREFIX}/{client_name}/{project_name}/{dt}"

def export_gps_and_date_to_csv(renamed_images, client_name, project_name, file_dt, type_str):
    """
    Exports two CSVs: one with image metadata, one with projected state plane coords.
    """
    client_name = client_name.strip()
    project_name = project_name.strip()
    if not renamed_images:
        logging.warning("No renamed images available for CSV export.")
        return None

    first_info = next(iter(renamed_images.values()))
    lat, lon, alt = first_info.get("lat"), first_info.get("lon"), first_info.get("alt")
    try:
        if lat is not None and lon is not None:
            zone_name, epsg, x, y, z = latlon_to_state_plane_auto(lat, lon, alt)
            proj_slug = zone_name.replace(" ", "_")
        else:
            proj_slug = "NoGPS"
    except Exception as e:
        proj_slug = "NoGPS"
        logging.warning(f"Failed state plane lookup for first image: {e}")

    type_suffix = f"_{type_str}" if type_str else ""
    output_csv = f"{file_dt}_{client_name}_{project_name}{type_suffix}_WGS84.csv"
    sp_output_csv = f"SP-{proj_slug}_{file_dt}_{client_name}_{project_name}{type_suffix}.csv"
    output_directory = safe_mkdir(OUTPUT_ROOT / client_name / project_name / file_dt)
    output_file_path = output_directory / output_csv
    sp_output_file_path = output_directory / sp_output_csv

    first_hyperlink = None
    with open(output_file_path, "w", newline="", encoding="utf-8") as csvfile, \
         open(sp_output_file_path, "w", newline="", encoding="utf-8") as sp_csvfile:
        writer = csv.writer(csvfile)
        sp_writer = csv.writer(sp_csvfile)
        writer.writerow(["Filename", "Date Taken", "GPSLatitude", "GPSLongitude", "GPSAltitude", "Hyperlink"])
        domain_path = make_domain_path(client_name, project_name, file_dt)
        for info in renamed_images.values():
            base_name = strip_extension(info["base_name"])
            hyperlink = f"{DOMAIN_BASE}{domain_path}/{base_name}.htm"
            if first_hyperlink is None:
                first_hyperlink = hyperlink
            writer.writerow([base_name, info["date_time"], info["lat"], info["lon"], info["alt"], hyperlink])
            # For SP: y, x, z, basename, hyperlink
            try:
                if info["lat"] is not None and info["lon"] is not None:
                    _, epsg, x, y, z = latlon_to_state_plane_auto(info["lat"], info["lon"], info["alt"])
                else:
                    x = y = z = None
                sp_writer.writerow([y, x, z, base_name, hyperlink])
            except Exception as e:
                sp_writer.writerow(["", "", "", base_name, hyperlink])
                logging.warning(f"Failed state plane transform for {base_name}: {e}")
    return first_hyperlink

def export_combined_photos_panos_to_dxf(
    pano_images, photo_images,
    client_name, project_name, file_dt,
    block_file=MASTER_DXF,
    output_file=None,
    pano_block="pano",
    photo_block="photo",
    layer_name_pano="V-PANO",
    layer_name_photo="V-PHOTO",
    block_scale_pano=5.0,
    block_scale_photo=5.0
):
    """
    Export both panos and photos to a single DXF, using only metadata (no need to access images).
    """
    if not Path(block_file).exists():
        logging.error(f"Block file not found: {block_file}")
        return
    block_doc = ezdxf.readfile(block_file)
    doc = ezdxf.new(dxfversion="R2018")
    doc.layers.add(name=layer_name_pano)
    doc.layers.add(name=layer_name_photo)
    msp = doc.modelspace()
    for block, block_name in [(pano_images, pano_block), (photo_images, photo_block)]:
        if block and block_name not in doc.blocks:
            importer = Importer(block_doc, doc)
            importer.import_block(block_name)
            importer.finalize()
    # Determine proj_slug from first pano or photo image with GPS
    proj_slug = "NoGPS"
    for images in (pano_images, photo_images):
        for info in images.values():
            lat, lon, alt = info.get("lat"), info.get("lon"), info.get("alt")
            if lat is not None and lon is not None:
                try:
                    zone_name, _, _, _, _ = latlon_to_state_plane_auto(lat, lon, alt)
                    proj_slug = zone_name.replace(" ", "_")
                    break
                except Exception:
                    continue
        if proj_slug != "NoGPS":
            break

    def insert_block(images, block_name, layer_name, block_scale):
        for info in images.values():
            lat, lon, alt = info.get("lat"), info.get("lon"), info.get("alt")
            if lat is None or lon is None:
                continue
            try:
                _, epsg, x, y, z = latlon_to_state_plane_auto(lat, lon, alt)
                insert_point = (x, y, z)
            except Exception as e:
                logging.warning(f"Projection fail for {info.get('base_name')}: {e}")
                continue
            base_name = strip_extension(info["base_name"])
            domain_path = make_domain_path(client_name, project_name, file_dt)
            hyperlink = f"{DOMAIN_BASE}{domain_path}/{base_name}.htm"
            block_ref = msp.add_blockref(block_name, insert_point, dxfattribs={
                "layer": layer_name,
                "xscale": block_scale,
                "yscale": block_scale,
                "zscale": block_scale,
            })
            block_ref.add_auto_attribs({
                "###": base_name,
                "HYPERLINK": hyperlink,
            })
    insert_block(pano_images, pano_block, layer_name_pano, block_scale_pano)
    insert_block(photo_images, photo_block, layer_name_photo, block_scale_photo)
    output_dir = safe_mkdir(OUTPUT_ROOT / client_name / project_name / file_dt)
    if output_file is None:
        output_file = f"{client_name}_{project_name}_{file_dt}_{proj_slug}_PanoPhoto.dxf"
    dxf_path = output_dir / output_file
    doc.saveas(str(dxf_path))
    logging.info(f"Combined DXF saved as {dxf_path}")
    return dxf_path

def make_proj_template(proj_compiled, images_dict, remote_dir, template_file):
    output_directory = safe_mkdir(OUTPUT_ROOT / remote_dir)
    env = Environment(loader=FileSystemLoader(TEMPLATES_DIR))
    try:
        template = env.get_template(template_file)
    except Exception as e:
        logging.error(f"Error loading template: {e}")
        return []
    html_files = []
    with ThreadPoolExecutor(max_workers=4) as executor:
        futures = {}
        for file_name, info in images_dict.items():
            future = executor.submit(render_template, file_name, info, proj_compiled, output_directory, template)
            futures[future] = file_name
        for future in as_completed(futures):
            try:
                result = future.result()
                html_files.append(result)
            except Exception as e:
                logging.warning(f"Error rendering template for {futures[future]}: {e}")
    return html_files

def render_template(file_name, info, proj_compiled, output_directory, template):
    try:
        dt_obj = datetime.strptime(info["date_time"], "%Y:%m:%d %H:%M:%S") if info.get("date_time") else datetime.now()
    except Exception:
        dt_obj = datetime.now()
    converted_dt = dt_obj.strftime("%d-%b-%y %I:%M:%S%p")
    rendered_html = template.render(
        TITLE=proj_compiled["name"],
        DESCRIPTION=proj_compiled["date_exif"],
        IMG=info["base_name"],
        IMG_DATE=converted_dt,
    )
    base_name, _ = os.path.splitext(file_name)
    output_filename = output_directory / f"{base_name}.htm"
    with open(output_filename, "w", encoding="utf-8") as f:
        f.write(rendered_html)
    return str(output_filename)

# --------------------
# FTP UPLOAD AND EMAIL
# --------------------
def create_remote_directory_recursive(ftp, remote_dir):
    try:
        ftp.cwd(remote_dir)
        return True
    except ftplib.error_perm:
        dirs = remote_dir.split('/')
        current_dir = ''
        for d in dirs:
            if d:
                current_dir += '/' + d
                try:
                    ftp.mkd(current_dir)
                except ftplib.error_perm:
                    pass
        try:
            ftp.cwd(remote_dir)
            return True
        except Exception:
            return False

def upload_file_via_ftp_with_retry(file_path, remote_dir, max_retries=3, delay_base=2):
    """
    Upload a file to the FTP server, with optional retry support and exponential backoff.
    """
    if not validate_ftp_credentials():
        return
    if not os.path.exists(file_path):
        logging.error(f"File not found at {file_path}")
        return

    for attempt in range(1, max_retries + 1):
        try:
            logging.info(f"Starting upload for: {file_path} (Attempt {attempt})")
            with ftplib.FTP(FTP_SERVER, timeout=30) as ftp:
                ftp.login(FTP_USERNAME, FTP_PASSWORD)
                create_remote_directory_recursive(ftp, remote_dir)
                with open(file_path, 'rb') as f:
                    ftp.storbinary(f"STOR {os.path.basename(file_path)}", f)
            logging.info(f"Successfully uploaded {os.path.basename(file_path)} on attempt {attempt}")
            return  # Success, exit the loop
        except Exception as e:
            logging.warning(f"Attempt {attempt} failed for {file_path}: {e}")
            if attempt == max_retries:
                logging.error(f"Giving up on {file_path} after {max_retries} attempts.")
            else:
                sleep_time = delay_base ** attempt
                logging.info(f"Retrying in {sleep_time} seconds...")
                time.sleep(sleep_time)

def probe_ftp_max_threads(max_test=None):
    """
    Probes or returns configured maximum FTP threads.
    """
    return int(FTP_MAX_THREADS if max_test is None else max_test)

def upload_html_templates_concurrently(html_files, remote_dir):
    # Print the remote directory being used.
    print("Remote directory to use:", remote_dir)

    # First, check (and/or create) the remote directory using a temporary FTP connection.
    try:
        with ftplib.FTP(FTP_SERVER, timeout=30) as ftp:
            ftp.login(FTP_USERNAME, FTP_PASSWORD)
            if not create_remote_directory_recursive(ftp, remote_dir):
                print(f"[{threading.current_thread().name}] Could not create remote directory for {remote_dir}.")
                return
    except Exception as e:
        print(f"Error establishing FTP connection: {e}")
        return

    max_threads = probe_ftp_max_threads()

    # Now, for each HTML file, submit an upload task that creates its own FTP connection.
    with ThreadPoolExecutor(max_workers=max_threads) as executor:
        for file in html_files:
            executor.submit(upload_file_via_ftp_with_retry, file, remote_dir)

def upload_images_concurrently(image_files, remote_dir):
    """
    Upload images concurrently using dynamic thread management.
    """
    max_threads = probe_ftp_max_threads()

    with ThreadPoolExecutor(max_workers=max_threads) as executor:
        for filename, file_info in image_files.items():
            try:
                executor.submit(upload_file_via_ftp_with_retry, file_info['compressed_path'], remote_dir)
            except Exception as e:
                logging.error(f"Error uploading {filename}: {e}")

def send_html_email(project_name, client_name, date, employee_name, first_link, remote_dir):
    template_path = TEMPLATES_DIR / "Email-Report-Template.htm"
    env = Environment(loader=FileSystemLoader(template_path.parent))
    template = env.get_template(template_path.name)
    html_content = template.render(
        PROJECT_NAME=str(project_name),
        CLIENT_NAME=str(client_name),
        UPLOAD_TIME=str(date),
        EMPLOYEE=str(employee_name),
        PANO_LINK=str(first_link),
        DIRECTORY_PATH=(OUTPUT_ROOT / remote_dir).as_posix()
    )
    # Load recipients from configurable file
    recipients_file = RECIPIENTS_FILE
    if not Path(recipients_file).exists():
        logging.error(f"Recipients file not found: {recipients_file}")
        return
    with open(recipients_file, "r") as f:
        recipients = [line.strip() for line in f if line.strip()]
    if not recipients:
        logging.warning("No recipients found in the recipients file.")
        return
    # Send email
    msg = EmailMessage()
    msg['Subject'] = f"Sunrise Engineering - Project Update: {project_name}"
    msg['From'] = EMAIL_SENDER
    msg['To'] = ",".join(recipients)
    msg.set_content("Project update attached.")
    msg.add_alternative(html_content, subtype="html")
    try:
        with smtplib.SMTP(EMAIL_HOST, EMAIL_PORT) as smtp:
            smtp.starttls()
            smtp.login(EMAIL_USER, EMAIL_PASS)
            smtp.send_message(msg)
        logging.info("Status email sent successfully.")
    except Exception as e:
        logging.error(f"Failed to send email: {e}")

# --------------------
# PyQt Custom Widgets
# --------------------
class ConfigDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("SIM Configuration")
        self.setMinimumSize(800, 600)
        self.setModal(True)
        
        # Create scroll area for the form
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        
        # Create main widget for scroll area
        main_widget = QWidget()
        main_layout = QVBoxLayout(main_widget)
        
        # Create form groups
        self.create_paths_group(main_layout)
        self.create_site_group(main_layout)
        self.create_images_group(main_layout)
        self.create_employees_group(main_layout)
        self.create_ftp_group(main_layout)
        self.create_credentials_group(main_layout)
        self.create_ui_group(main_layout)
        
        # Add scroll area to main layout
        layout = QVBoxLayout(self)
        layout.addWidget(scroll)
        scroll.setWidget(main_widget)
        
        # Add buttons
        buttons = QDialogButtonBox(QDialogButtonBox.Save | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.save_config)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)
        
        # Load default values
        self.load_defaults()
    
    def create_paths_group(self, layout):
        group = QGroupBox("Paths")
        form = QFormLayout(group)
        
        # Master DXF file
        self.master_dxf = QLineEdit()
        self.master_dxf.setPlaceholderText("Path to master DXF file")
        master_dxf_layout = QHBoxLayout()
        master_dxf_layout.addWidget(self.master_dxf)
        master_dxf_btn = QPushButton("📁")
        master_dxf_btn.setToolTip("Select DXF file")
        master_dxf_btn.setFixedSize(30, 30)
        master_dxf_btn.clicked.connect(lambda: self.select_file(self.master_dxf, "Select Master DXF File", "DXF Files (*.dxf);;All Files (*.*)"))
        master_dxf_layout.addWidget(master_dxf_btn)
        form.addRow("Master DXF:", master_dxf_layout)
        
        # Output root directory
        self.output_root = QLineEdit()
        self.output_root.setPlaceholderText("Output directory root")
        output_root_layout = QHBoxLayout()
        output_root_layout.addWidget(self.output_root)
        output_root_btn = QPushButton("📁")
        output_root_btn.setToolTip("Select output directory")
        output_root_btn.setFixedSize(30, 30)
        output_root_btn.clicked.connect(lambda: self.select_folder(self.output_root, "Select Output Directory"))
        output_root_layout.addWidget(output_root_btn)
        form.addRow("Output Root:", output_root_layout)
        
        # Templates directory
        self.templates_dir = QLineEdit()
        self.templates_dir.setPlaceholderText("Templates directory")
        templates_dir_layout = QHBoxLayout()
        templates_dir_layout.addWidget(self.templates_dir)
        templates_dir_btn = QPushButton("📁")
        templates_dir_btn.setToolTip("Select templates directory")
        templates_dir_btn.setFixedSize(30, 30)
        templates_dir_btn.clicked.connect(lambda: self.select_folder(self.templates_dir, "Select Templates Directory"))
        templates_dir_layout.addWidget(templates_dir_btn)
        form.addRow("Templates Dir:", templates_dir_layout)
        
        # Photo counter file
        self.photo_counter = QLineEdit()
        self.photo_counter.setPlaceholderText("Photo counter file path")
        photo_counter_layout = QHBoxLayout()
        photo_counter_layout.addWidget(self.photo_counter)
        photo_counter_btn = QPushButton("📁")
        photo_counter_btn.setToolTip("Select photo counter file")
        photo_counter_btn.setFixedSize(30, 30)
        photo_counter_btn.clicked.connect(lambda: self.select_file(self.photo_counter, "Select Photo Counter File", "Text Files (*.txt);;All Files (*.*)"))
        photo_counter_layout.addWidget(photo_counter_btn)
        form.addRow("Photo Counter:", photo_counter_layout)
        
        # State plane shapefile
        self.stateplane_shapefile = QLineEdit()
        self.stateplane_shapefile.setPlaceholderText("State plane shapefile path")
        stateplane_layout = QHBoxLayout()
        stateplane_layout.addWidget(self.stateplane_shapefile)
        stateplane_btn = QPushButton("📁")
        stateplane_btn.setToolTip("Select shapefile")
        stateplane_btn.setFixedSize(30, 30)
        stateplane_btn.clicked.connect(lambda: self.select_file(self.stateplane_shapefile, "Select State Plane Shapefile", "Shapefiles (*.shp);;All Files (*.*)"))
        stateplane_layout.addWidget(stateplane_btn)
        form.addRow("State Plane Shapefile:", stateplane_layout)
        
        # Recipients file
        self.recipients_file = QLineEdit()
        self.recipients_file.setPlaceholderText("Email recipients file path")
        recipients_layout = QHBoxLayout()
        recipients_layout.addWidget(self.recipients_file)
        recipients_btn = QPushButton("📁")
        recipients_btn.setToolTip("Select recipients file")
        recipients_btn.setFixedSize(30, 30)
        recipients_btn.clicked.connect(lambda: self.select_file(self.recipients_file, "Select Email Recipients File", "Text Files (*.txt);;All Files (*.*)"))
        recipients_layout.addWidget(recipients_btn)
        form.addRow("Recipients File:", recipients_layout)
        
        # Temp root directory
        self.temp_root = QLineEdit()
        self.temp_root.setPlaceholderText("Temporary files directory")
        temp_root_layout = QHBoxLayout()
        temp_root_layout.addWidget(self.temp_root)
        temp_root_btn = QPushButton("📁")
        temp_root_btn.setToolTip("Select temporary directory")
        temp_root_btn.setFixedSize(30, 30)
        temp_root_btn.clicked.connect(lambda: self.select_folder(self.temp_root, "Select Temporary Directory"))
        temp_root_layout.addWidget(temp_root_btn)
        form.addRow("Temp Root:", temp_root_layout)
        
        layout.addWidget(group)
    
    def create_site_group(self, layout):
        group = QGroupBox("Site Settings")
        form = QFormLayout(group)
        
        self.domain_base = QLineEdit()
        self.domain_base.setPlaceholderText("Base domain URL")
        form.addRow("Domain Base:", self.domain_base)
        
        self.domain_prefix = QLineEdit()
        self.domain_prefix.setPlaceholderText("Domain prefix path")
        form.addRow("Domain Prefix:", self.domain_prefix)
        
        layout.addWidget(group)
    
    def create_images_group(self, layout):
        group = QGroupBox("Image Settings")
        form = QFormLayout(group)
        
        self.max_width = QSpinBox()
        self.max_width.setRange(1000, 20000)
        self.max_width.setValue(8192)
        form.addRow("Max Width:", self.max_width)
        
        self.compress_quality = QSpinBox()
        self.compress_quality.setRange(1, 100)
        self.compress_quality.setValue(30)
        form.addRow("Compress Quality:", self.compress_quality)
        
        layout.addWidget(group)
    
    def create_employees_group(self, layout):
        group = QGroupBox("Employee Names")
        form = QFormLayout(group)
        
        self.employees = QTextEdit()
        self.employees.setMaximumHeight(100)
        self.employees.setPlaceholderText("Enter employee names, one per line")
        form.addRow("Employees:", self.employees)
        
        layout.addWidget(group)
    
    def create_ftp_group(self, layout):
        group = QGroupBox("FTP Settings")
        form = QFormLayout(group)
        
        self.ftp_max_threads = QSpinBox()
        self.ftp_max_threads.setRange(1, 20)
        self.ftp_max_threads.setValue(6)
        form.addRow("Max FTP Threads:", self.ftp_max_threads)
        
        layout.addWidget(group)
    
    def create_credentials_group(self, layout):
        group = QGroupBox("Credentials (Keyring)")
        form = QFormLayout(group)
        
        # FTP Credentials
        ftp_label = QLabel("FTP Credentials:")
        ftp_label.setFont(SUBHEADER_FONT)
        form.addRow(ftp_label, QLabel(""))
        
        self.ftp_server = QLineEdit()
        self.ftp_server.setPlaceholderText("FTP Server")
        self.ftp_server.setEchoMode(QLineEdit.Normal)
        form.addRow("FTP Server:", self.ftp_server)
        
        self.ftp_username = QLineEdit()
        self.ftp_username.setPlaceholderText("FTP Username")
        self.ftp_username.setEchoMode(QLineEdit.Normal)
        form.addRow("FTP Username:", self.ftp_username)
        
        self.ftp_password = QLineEdit()
        self.ftp_password.setPlaceholderText("FTP Password")
        self.ftp_password.setEchoMode(QLineEdit.Password)
        form.addRow("FTP Password:", self.ftp_password)
        
        # Email Credentials
        email_label = QLabel("Email Credentials:")
        email_label.setFont(SUBHEADER_FONT)
        form.addRow(email_label, QLabel(""))
        
        self.email_host = QLineEdit()
        self.email_host.setPlaceholderText("Email Host (SMTP)")
        form.addRow("Email Host:", self.email_host)
        
        self.email_port = QSpinBox()
        self.email_port.setRange(1, 65535)
        self.email_port.setValue(587)
        form.addRow("Email Port:", self.email_port)
        
        self.email_user = QLineEdit()
        self.email_user.setPlaceholderText("Email Username")
        form.addRow("Email User:", self.email_user)
        
        self.email_password = QLineEdit()
        self.email_password.setPlaceholderText("Email Password")
        self.email_password.setEchoMode(QLineEdit.Password)
        form.addRow("Email Password:", self.email_password)
        
        self.email_sender = QLineEdit()
        self.email_sender.setPlaceholderText("Email Sender Address")
        form.addRow("Email Sender:", self.email_sender)
        
        layout.addWidget(group)
    
    def create_ui_group(self, layout):
        group = QGroupBox("UI Settings")
        form = QFormLayout(group)
        
        self.font_family = QLineEdit()
        self.font_family.setPlaceholderText("Font family name")
        form.addRow("Font Family:", self.font_family)
        
        layout.addWidget(group)
    
    def load_defaults(self):
        """Load default configuration values and existing credentials"""
        self.master_dxf.setText("./master.dxf")
        self.output_root.setText("./output")
        self.templates_dir.setText("./templates")
        self.photo_counter.setText("./_ROLLING_COUNT/photo_counter.txt")
        self.stateplane_shapefile.setText("./NAD83SPCEPSG.shp")
        self.recipients_file.setText("./email_recipients.txt")
        self.temp_root.setText("./panoTemp")
        
        self.domain_base.setText("https://www.seihds.com")
        self.domain_prefix.setText("/auto")
        
        self.max_width.setValue(8192)
        self.compress_quality.setValue(30)
        
        self.employees.setPlainText("Alan\nBurt\nGabe\nKevin\nMorgan\nNick\nTanner")
        
        self.ftp_max_threads.setValue(6)
        
        self.font_family.setText("Segoe UI")
        
        # Load existing credentials from keyring
        self.load_existing_credentials()
    
    def select_file(self, line_edit, title="Select File", file_filter="All Files (*.*)"):
        """Open file dialog and update the line edit with selected file path"""
        current_path = line_edit.text().strip()
        if current_path and os.path.exists(current_path):
            start_dir = os.path.dirname(current_path)
        else:
            start_dir = str(Path.cwd())
        
        file_path, _ = QFileDialog.getOpenFileName(
            self, title, start_dir, file_filter
        )
        if file_path:
            line_edit.setText(file_path)
    
    def select_folder(self, line_edit, title="Select Folder"):
        """Open folder dialog and update the line edit with selected folder path"""
        current_path = line_edit.text().strip()
        if current_path and os.path.exists(current_path):
            start_dir = current_path
        else:
            start_dir = str(Path.cwd())
        
        folder_path = QFileDialog.getExistingDirectory(
            self, title, start_dir
        )
        if folder_path:
            line_edit.setText(folder_path)
    
    def load_existing_credentials(self):
        """Load existing credentials from keyring"""
        # Load FTP credentials
        ftp_server, ftp_username, ftp_password = get_ftp_credentials()
        if ftp_server:
            self.ftp_server.setText(ftp_server)
        if ftp_username:
            self.ftp_username.setText(ftp_username)
        if ftp_password:
            self.ftp_password.setText(ftp_password)
        
        # Load email credentials
        email_host, email_port, email_user, email_password, email_sender = get_email_credentials()
        if email_host:
            self.email_host.setText(email_host)
        if email_port:
            self.email_port.setValue(int(email_port))
        if email_user:
            self.email_user.setText(email_user)
        if email_password:
            self.email_password.setText(email_password)
        if email_sender:
            self.email_sender.setText(email_sender)
    
    def save_config(self):
        """Save configuration to JSON file and credentials to keyring"""
        # Save credentials to keyring first
        ftp_success = True
        email_success = True
        
        # Save FTP credentials if provided
        if self.ftp_server.text().strip() and self.ftp_username.text().strip() and self.ftp_password.text().strip():
            ftp_success = set_ftp_credentials(
                self.ftp_server.text().strip(),
                self.ftp_username.text().strip(),
                self.ftp_password.text().strip()
            )
        
        # Save email credentials if provided
        if (self.email_host.text().strip() and self.email_user.text().strip() and 
            self.email_password.text().strip() and self.email_sender.text().strip()):
            email_success = set_email_credentials(
                self.email_host.text().strip(),
                self.email_port.value(),
                self.email_user.text().strip(),
                self.email_password.text().strip(),
                self.email_sender.text().strip()
            )
        
        # Save configuration to JSON
        config = {
            "paths": {
                "master_dxf": self.master_dxf.text().strip(),
                "output_root": self.output_root.text().strip(),
                "templates_dir": self.templates_dir.text().strip(),
                "photo_counter": self.photo_counter.text().strip(),
                "stateplane_shapefile": self.stateplane_shapefile.text().strip(),
                "recipients_file": self.recipients_file.text().strip(),
                "temp_root": self.temp_root.text().strip()
            },
            "site": {
                "domain_base": self.domain_base.text().strip(),
                "domain_prefix": self.domain_prefix.text().strip()
            },
            "images": {
                "max_width": self.max_width.value(),
                "compress_quality": self.compress_quality.value()
            },
            "employees": [name.strip() for name in self.employees.toPlainText().split('\n') if name.strip()],
            "ftp": {
                "max_threads_probe": self.ftp_max_threads.value()
            },
            "ui": {
                "font_family": self.font_family.text().strip()
            }
        }
        
        # Save to config.json in the same directory as the script
        config_path = Path(__file__).parent / "config.json"
        try:
            with open(config_path, "w", encoding="utf-8") as f:
                json.dump(config, f, indent=2, ensure_ascii=False)
            
            # Show success message
            success_msg = f"Configuration saved to {config_path}"
            if ftp_success and email_success:
                success_msg += "\nCredentials saved to keyring successfully"
            elif not ftp_success or not email_success:
                success_msg += "\nWarning: Some credentials may not have been saved to keyring"
            
            QMessageBox.information(self, "Success", success_msg)
            self.accept()
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to save configuration: {e}")

class NameDialog(QDialog):
    def __init__(self, possible_names, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Select or Enter Name")
        layout = QVBoxLayout(self)
        label = QLabel("Select your name from the list or enter a new one:")
        label.setFont(BODY_FONT)
        layout.addWidget(label)
        self.combo = QComboBox()
        self.combo.addItems(possible_names)
        layout.addWidget(self.combo)
        label2 = QLabel("Or enter your name:")
        label2.setFont(BODY_FONT)
        layout.addWidget(label2)
        self.custom_entry = QLineEdit()
        layout.addWidget(self.custom_entry)
        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)
        self.setLayout(layout)
    def get_name(self):
        if self.exec_() == QDialog.Accepted:
            custom = self.custom_entry.text().strip()
            return custom if custom else self.combo.currentText()
        return None

class DualDropFrame(QFrame):
    def __init__(self, main_app):
        super().__init__()
        self.main_app = main_app
        self.setFrameStyle(QFrame.StyledPanel | QFrame.Plain)
        self.setStyleSheet(f"""
            QFrame {{
                border: 2px dashed {SUNRISE_NAVY};
                border-radius: 10px;
                background: #f8f9fa;
            }}
        """)
        self.setAcceptDrops(False)
        self.layout = QHBoxLayout(self)
        self.pano_area = SingleDropArea("Drop Panos Here", main_app, which="pano")
        self.layout.addWidget(self.pano_area)
        self.photo_area = SingleDropArea("Drop Photos Here", main_app, which="photo")
        self.layout.addWidget(self.photo_area)

class SingleDropArea(QFrame):
    def __init__(self, label_text, main_app, which):
        super().__init__()
        self.main_app = main_app
        self.which = which
        self.setFrameStyle(QFrame.StyledPanel | QFrame.Plain)
        self.setStyleSheet(f"""
            QFrame {{
                border: 2px dashed {SUNRISE_NAVY};
                border-radius: 10px;
                margin: 10px;
                background: #ffffff;
            }}
        """)
        self.setAcceptDrops(True)
        vlayout = QVBoxLayout(self)
        self.label = QLabel(label_text)
        self.label.setFont(BODY_FONT)
        self.label.setAlignment(Qt.AlignCenter)
        vlayout.addWidget(self.label)
        self.file_list = QTextEdit()
        self.file_list.setReadOnly(True)
        self.file_list.setMaximumHeight(300)
        vlayout.addWidget(self.file_list)
        self.files = []
    def dragEnterEvent(self, event: QDragEnterEvent):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()
        else:
            event.ignore()
    def dropEvent(self, event: QDropEvent):
        urls = event.mimeData().urls()
        file_paths = [url.toLocalFile() for url in urls if os.path.isfile(url.toLocalFile())]
        jpgs = [f for f in file_paths if f.lower().endswith(".jpg")]
        self.files = jpgs
        self.file_list.setPlainText("\n".join([os.path.basename(f) for f in jpgs]))
        if self.which == "pano":
            self.main_app.pano_files = jpgs
        elif self.which == "photo":
            self.main_app.photo_files = jpgs

# --------------------
# Main PyQt Application
# --------------------
class Pano2DWGApp(QMainWindow):
    show_upload_complete_signal = pyqtSignal(str)
    status_update_signal = pyqtSignal(str, bool)  # text, error
    progress_update_signal = pyqtSignal(int)      # percent
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Pano+Photo Image Process - Sunrise Engineering")
        self.setMinimumSize(1800, 1200)
        self.setAcceptDrops(False)
        self.pano_files = []
        self.photo_files = []
        
        # Create main widget and layout
        main_widget = QWidget()
        self.setCentralWidget(main_widget)
        main_layout = QVBoxLayout(main_widget)
        main_layout.setSpacing(10)
        
        # Create top bar with logo and settings button
        top_bar_layout = QHBoxLayout()
        top_bar_layout.setContentsMargins(0, 0, 0, 10)
        
        # Logo (left side)
        self.logo_label = QLabel()
        self.logo_label.setAlignment(Qt.AlignCenter)
        logo_path = str(TEMPLATES_DIR / "logo.jpg")
        if os.path.exists(logo_path):
            pixmap = QPixmap(logo_path)
            scaled_pixmap = pixmap.scaledToWidth(300, Qt.SmoothTransformation)
            self.logo_label.setPixmap(scaled_pixmap)
        else:
            self.logo_label.setText("[Logo not found]")
        
        # Settings button (right side)
        self.settings_button = QPushButton()
        self.settings_button.setFixedSize(40, 40)
        self.settings_button.setToolTip("Settings")
        self.settings_button.clicked.connect(self.open_settings)
        
        # Create cogwheel icon using Unicode symbol
        self.settings_button.setText("⚙")
        self.settings_button.setFont(QFont("Segoe UI Symbol", 16))
        self.settings_button.setStyleSheet(f"""
            QPushButton {{
                background: {SUNRISE_NAVY};
                color: white;
                border: none;
                border-radius: 20px;
                font-weight: bold;
            }}
            QPushButton:hover {{
                background: {SUNRISE_GRAY};
            }}
            QPushButton:pressed {{
                background: {SUNRISE_YELLOW};
                color: {SUNRISE_NAVY};
            }}
        """)
        
        # Add to top bar layout
        top_bar_layout.addWidget(self.logo_label)
        top_bar_layout.addStretch()  # Push settings button to the right
        top_bar_layout.addWidget(self.settings_button)
        
        # Add top bar to main layout
        main_layout.addLayout(top_bar_layout)
        # Drop zones
        self.drop_frame = DualDropFrame(self)
        main_layout.addWidget(self.drop_frame, 1)
        # Process button
        self.process_btn = QPushButton("Process All")
        self.process_btn.setFont(BODY_FONT)
        self.process_btn.setStyleSheet(f"background: {SUNRISE_YELLOW}; color: {SUNRISE_NAVY}; font-weight: bold; border-radius: 10px; padding: 8px;")
        self.process_btn.clicked.connect(self.process_all_files)
        main_layout.addWidget(self.process_btn)
        # Output/status
        self.status_label = QLabel("")
        self.status_label.setFont(BODY_FONT)
        self.status_label.setStyleSheet(f"color: {SUNRISE_NAVY}; margin-top: 8px;")
        main_layout.addWidget(self.status_label)
        # Progress bar
        from PyQt5.QtWidgets import QProgressBar
        self.progress_bar = QProgressBar()
        self.progress_bar.setMinimum(0)
        self.progress_bar.setMaximum(100)
        self.progress_bar.setValue(0)
        self.progress_bar.setTextVisible(True)
        self.progress_bar.setStyleSheet(f"margin-top: 8px; margin-bottom: 8px;")
        main_layout.addWidget(self.progress_bar)
        self.show_upload_complete_signal.connect(self.show_upload_complete)
        self.status_update_signal.connect(self.show_status)
        self.progress_update_signal.connect(self.update_progress_bar)
    def update_progress_bar(self, percent):
        self.progress_bar.setValue(percent)
    def show_status(self, text, error=False):
        color = SUNRISE_RUBY if error else SUNRISE_NAVY
        self.status_label.setStyleSheet(f"color: {color};")
        self.status_label.setText(text)
    def ask_user_name(self, possible_names):
        dlg = NameDialog(possible_names, parent=self)
        name = dlg.get_name()
        return name
    def ask_text(self, title, prompt):
        text, ok = QInputDialog.getText(self, title, prompt)
        return text.strip() if ok and text.strip() else None
    def show_warning(self, title, message):
        QMessageBox.warning(self, title, message)
    def show_info(self, title, message):
        QMessageBox.information(self, title, message)
    
    def open_settings(self):
        """Open the configuration dialog"""
        config_dialog = ConfigDialog(self)
        if config_dialog.exec_() == QDialog.Accepted:
            # Reload configuration after saving
            global CONFIG
            CONFIG = load_config()
            # Re-initialize global variables with new config
            reinitialize_globals()
            # Show success message
            self.show_info("Settings Updated", "Configuration has been updated successfully.")
    def show_upload_complete(self, local_dir):
        msg = QMessageBox(self)
        msg.setWindowTitle("Upload Complete")
        msg.setText("Upload complete!\\n\\nOpen directory?")
        msg.setStandardButtons(QMessageBox.Open | QMessageBox.Close)
        if msg.exec_() == QMessageBox.Open:
            os.startfile(local_dir)
    def process_all_files(self):
        client_name = self.ask_text("Input", "Enter client name")
        if not client_name:
            self.show_warning("Missing Input", "Client name is required.")
            return
        client_name = client_name.strip().replace(" ", "_")
        project_name = self.ask_text("Input", "Enter project name")
        if not project_name:
            self.show_warning("Missing Input", "Project name is required.")
            return
        project_name = project_name.strip().replace(" ", "_")
        employee_name = self.ask_user_name(EMPLOYEE_NAMES)
        if not employee_name:
            self.show_warning("Missing Input", "Employee name is required.")
            return
        dt = datetime.now().strftime("%d%b%y_%I-%M%p")
        remote_dir = f"{client_name}/{project_name}/{dt}"
        if not self.pano_files and not self.photo_files:
            self.show_warning("No Files", "No pano or photo files to process.")
            return
        # Main processing in a thread for UI responsiveness
        def run_processing():
            # Setup project-specific logging
            log_file_path = setup_project_logging(client_name, project_name, dt)

            pano_renamed_images = {}
            photo_renamed_images = {}
            # Count all steps: processing + HTML upload + image upload
            num_pano = len(self.pano_files)
            num_photo = len(self.photo_files)
            num_html = 0
            num_img = 0
            processed_steps = 0
            def update_progress():
                total_steps = num_pano + num_photo + num_html + num_img
                percent = int((processed_steps / max(total_steps, 1)) * 100)
                self.progress_update_signal.emit(percent)
            try:
                if self.pano_files:
                    self.status_update_signal.emit("Processing Panos...", False)
                    pano_renamed_images = process_image_set(self.pano_files, client_name, project_name, dt, remote_dir, employee_name, "Pano")
                    processed_steps += num_pano
                    update_progress()
                if self.photo_files:
                    self.status_update_signal.emit("Processing Photos...", False)
                    photo_renamed_images = process_image_set(self.photo_files, client_name, project_name, dt, remote_dir, employee_name, "Photo")
                    processed_steps += num_photo
                    update_progress()
                # Exports
                first_link = export_gps_and_date_to_csv(pano_renamed_images, client_name, project_name, dt, "pano")
                export_gps_and_date_to_csv(photo_renamed_images, client_name, project_name, dt, "photo")
                export_combined_photos_panos_to_dxf(pano_renamed_images, photo_renamed_images, client_name, project_name, dt)
                proj_compiled = {
                    "date_exif": datetime.now().strftime("%Y-%B-%d %H:%M"),
                    "name": client_name,
                    "folder": str(TEMP_ROOT),
                    "proj_name": project_name
                }
                pano_html_files = make_proj_template(proj_compiled, pano_renamed_images, remote_dir, "Pano-Template.htm")
                photo_html_files = make_proj_template(proj_compiled, photo_renamed_images, remote_dir, "img-Template.htm")
                all_html_files = pano_html_files + photo_html_files
                num_html = len(all_html_files)
                num_img = len(pano_renamed_images) + len(photo_renamed_images)
                # Upload HTML files with progress
                self.status_update_signal.emit("Uploading HTML files...", False)
                for html in all_html_files:
                    upload_file_via_ftp_with_retry(html, remote_dir)
                    processed_steps += 1
                    update_progress()
                # Upload images with progress
                self.status_update_signal.emit("Uploading images...", False)
                for info in pano_renamed_images.values():
                    if info.get('compressed_path'):
                        upload_file_via_ftp_with_retry(info['compressed_path'], remote_dir)
                        processed_steps += 1
                        update_progress()
                for info in photo_renamed_images.values():
                    if info.get('compressed_path'):
                        upload_file_via_ftp_with_retry(info['compressed_path'], remote_dir)
                        processed_steps += 1
                        update_progress()
                send_html_email(project_name, client_name, dt, employee_name, first_link, remote_dir)
                local_dir = OUTPUT_ROOT / remote_dir
                self.show_upload_complete_signal.emit(str(local_dir))
                self.status_update_signal.emit("Processing finished!", False)
                self.progress_update_signal.emit(100)
            except Exception as e:
                self.status_update_signal.emit(f"Error: {e}", True)
        threading.Thread(target=run_processing).start()

# --------------------
# Launch PyQt
# --------------------
def main():
    app = QApplication(sys.argv)
    palette = app.palette()
    palette.setColor(QPalette.Window, QColor("#ffffff"))
    app.setPalette(palette)
    
    # Check if config file exists
    config_path = find_config_path()
    if not config_path:
        # Show configuration dialog
        config_dialog = ConfigDialog()
        if config_dialog.exec_() == QDialog.Accepted:
            # Reload configuration after saving
            global CONFIG
            CONFIG = load_config()
            # Re-initialize global variables with new config
            reinitialize_globals()
        else:
            # User cancelled, exit application
            sys.exit(0)
    
    app.setFont(QFont(SUNRISE_FONT, 10))
    window = Pano2DWGApp()
    window.show()
    sys.exit(app.exec_())

def reinitialize_globals():
    """Re-initialize global variables after config reload"""
    global MASTER_DXF, OUTPUT_ROOT, TEMPLATES_DIR, PHOTO_COUNTER_PATH
    global STATEPLANE_SHAPEFILE, RECIPIENTS_FILE, TEMP_ROOT
    global DOMAIN_BASE, DOMAIN_PREFIX, MAX_WIDTH, DEFAULT_JPEG_QUALITY
    global EMPLOYEE_NAMES, FTP_MAX_THREADS, SUNRISE_FONT, HEADER_FONT, SUBHEADER_FONT, BODY_FONT
    global FTP_SERVER, FTP_USERNAME, FTP_PASSWORD, EMAIL_HOST, EMAIL_PORT, EMAIL_USER, EMAIL_PASS, EMAIL_SENDER
    
    # Re-initialize paths and settings from JSON
    MASTER_DXF = Path(cfg_get(CONFIG, "paths.master_dxf", "")).expanduser()
    OUTPUT_ROOT = Path(cfg_get(CONFIG, "paths.output_root", "./output")).expanduser()
    TEMPLATES_DIR = Path(cfg_get(CONFIG, "paths.templates_dir", "./templates")).expanduser()
    PHOTO_COUNTER_PATH = Path(cfg_get(CONFIG, "paths.photo_counter", "./_ROLLING_COUNT/photo_counter.txt")).expanduser()
    STATEPLANE_SHAPEFILE = Path(cfg_get(CONFIG, "paths.stateplane_shapefile", "./NAD83SPCEPSG.shp")).expanduser()
    RECIPIENTS_FILE = Path(cfg_get(CONFIG, "paths.recipients_file", "./email_recipients.txt")).expanduser()
    TEMP_ROOT = Path(cfg_get(CONFIG, "paths.temp_root", "./panoTemp")).expanduser()
    
    DOMAIN_BASE = cfg_get(CONFIG, "site.domain_base", "https://www.seihds.com")
    DOMAIN_PREFIX = cfg_get(CONFIG, "site.domain_prefix", "/auto")
    
    MAX_WIDTH = int(cfg_get(CONFIG, "images.max_width", 8192))
    DEFAULT_JPEG_QUALITY = int(cfg_get(CONFIG, "images.compress_quality", 30))
    
    EMPLOYEE_NAMES = list(cfg_get(CONFIG, "employees", ["Alan", "Burt", "Gabe", "Kevin", "Morgan", "Nick", "Tanner"]))
    
    FTP_MAX_THREADS = int(cfg_get(CONFIG, "ftp.max_threads_probe", 6))
    
    # Re-initialize UI constants
    SUNRISE_FONT = cfg_get(CONFIG, "ui.font_family", "Segoe UI")
    HEADER_FONT = QFont(SUNRISE_FONT, 16, QFont.Bold)
    SUBHEADER_FONT = QFont(SUNRISE_FONT, 12, QFont.Bold)
    BODY_FONT = QFont(SUNRISE_FONT, 10)
    
    # Re-load credentials from keyring
    FTP_SERVER, FTP_USERNAME, FTP_PASSWORD = get_ftp_credentials()
    EMAIL_HOST, EMAIL_PORT_STR, EMAIL_USER, EMAIL_PASS, EMAIL_SENDER = get_email_credentials()
    EMAIL_PORT = int(EMAIL_PORT_STR) if EMAIL_PORT_STR else 587

if __name__ == "__main__":
    main()
