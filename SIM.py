import os
import sys
import re
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
from dotenv import load_dotenv
from jinja2 import Environment, FileSystemLoader
import ezdxf
from ezdxf.addons import Importer

from PyQt5.QtWidgets import (
    QApplication, QMainWindow, QWidget, QLabel, QVBoxLayout, QHBoxLayout, QPushButton,
    QFileDialog, QMessageBox, QInputDialog, QComboBox, QLineEdit, QDialog, QDialogButtonBox, QTextEdit, QFrame
)
from PyQt5.QtGui import QPixmap, QFont, QPalette, QColor, QDragEnterEvent, QDropEvent
from PyQt5.QtCore import Qt, QMimeData, QSize, pyqtSignal
import warnings
from PIL import Image

warnings.simplefilter('ignore', Image.DecompressionBombWarning)


# ---- LOGGING ----
# Initial logging setup - will be reconfigured during processing
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s"
)

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


# ---- Load .env ----
def get_env_path():
    return Path(r"Z:/Survey/UT/_Scripts/SunrisePhoto/resources/.env")

load_dotenv(dotenv_path=get_env_path())
logging.info(f"Loaded .env from: {get_env_path()}")

FTP_SERVER = os.getenv("FTP_SERVER")
FTP_USERNAME = os.getenv("FTP_USERNAME")
FTP_PASSWORD = os.getenv("FTP_PASSWORD")
EMAIL_HOST = os.getenv("EMAIL_HOST")
EMAIL_PORT = int(os.getenv("EMAIL_PORT", 587))
EMAIL_USER = os.getenv("EMAIL_USER")
EMAIL_PASS = os.getenv("EMAIL_PASSWORD")
EMAIL_SENDER = os.getenv("EMAIL_SENDER")
MASTER_DXF = os.getenv("MASTER_DXF", r"Z:/Survey/UT/_Scripts/SunrisePhoto/resources/master.dxf")
OUTPUT_ROOT = Path(os.getenv("OUTPUT_ROOT", r"Z:/Survey/UT/ScriptFiles"))
TEMPLATES_DIR = Path(os.getenv("TEMPLATES_DIR", r"Z:/Survey/UT/_Scripts/SunrisePhoto/resources"))
PHOTO_COUNTER_PATH = Path(os.getenv("PHOTO_COUNTER_PATH", r"Z:/Survey/UT/ScriptFiles/_ROLLING_COUNT/photo_counter.txt"))
STATEPLANE_SHAPEFILE = Path(os.getenv("STATEPLANE_SHAPEFILE", r"Z:/Survey/UT/_Scripts/SunrisePhoto/resources/NAD83SPCEPSG.shp"))

TEMP_ROOT = Path("C:/panoTemp")
MAX_WIDTH = 8192

# ---- UI Constants ----
SUNRISE_NAVY = "#113e59"
SUNRISE_GRAY = "#a7a9ac"
SUNRISE_YELLOW = "#ffd457"
SUNRISE_RUBY = "#d2342e"
SUNRISE_FONT = "Segoe UI"
HEADER_FONT = QFont(SUNRISE_FONT, 16, QFont.Bold)
SUBHEADER_FONT = QFont(SUNRISE_FONT, 12, QFont.Bold)
BODY_FONT = QFont(SUNRISE_FONT, 10)

# ---- Utility Functions (same as before, refactored for single-metadata) ----
MAX_WIDTH = 8192
TEMP_ROOT = Path("C:/panoTemp")  # All temp subfolders go here

# ---- UTILITY FUNCTIONS ----
def validate_ftp_credentials():
    if not FTP_SERVER or not FTP_USERNAME or not FTP_PASSWORD:
        logging.error("🚨 FTP credentials are missing or incomplete. Check your .env file.")
        return False
    logging.info(f"✅ FTP credentials loaded: server={FTP_SERVER}, username={FTP_USERNAME}")
    return True


def safe_mkdir(path: Path):
    path.mkdir(parents=True, exist_ok=True)
    return path

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
    # Use cached geodataframe if available for performance
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

def compress_image(input_image_path: Path, remote_dir, quality=30):
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
                img.save(str(new_path), "JPEG", quality=quality, exif=exif_bytes)
            else:
                img.save(str(new_path), "JPEG", quality=quality)
            return str(new_path)
    except Exception as e:
        logging.warning(f"Compression failed for {input_image_path}: {e}")
        return None

# ---- FILE PROCESSING WORKFLOW ----

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
            futures[executor.submit(compress_image, final_path, remote_dir, 30)] = (
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

# ---- CSV, DXF, and HTML EXPORTS ----

def make_domain_path(client_name, project_name, dt):
    return f"/auto/{client_name}/{project_name}/{dt}"

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
            hyperlink = f"https://www.seihds.com{domain_path}/{base_name}.htm"
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
            hyperlink = f"https://www.seihds.com{domain_path}/{base_name}.htm"
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

# ---- FTP UPLOAD AND EMAIL ----

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
            # file is the full path to the HTML template.
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
    # Load recipients from external file
    recipients_file = Path(r"Z:/Survey/UT/_Scripts/SunrisePhoto/resources/email_recipients.txt")
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

# ---- PyQt Custom Widgets ----

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
        self.file_list.setMaximumHeight(300)  # Increased height for taller files table
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

# ---- Main PyQt Application ----

class Pano2DWGApp(QMainWindow):
    show_upload_complete_signal = pyqtSignal(str)
    status_update_signal = pyqtSignal(str, bool)  # text, error
    progress_update_signal = pyqtSignal(int)      # percent
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Pano+Photo Image Process - Sunrise Engineering")
        self.setMinimumSize(1800, 1200)  # Increased height for overall window
        self.setAcceptDrops(False)
        self.pano_files = []
        self.photo_files = []
        main_widget = QWidget()
        self.setCentralWidget(main_widget)
        main_layout = QVBoxLayout(main_widget)
        main_layout.setSpacing(10)
        # Logo
        self.logo_label = QLabel()
        self.logo_label.setAlignment(Qt.AlignCenter)
        logo_path = str(TEMPLATES_DIR / "logo.jpg")
        if os.path.exists(logo_path):
            pixmap = QPixmap(logo_path)
            # Scale logo to fit width, keep aspect ratio
            scaled_pixmap = pixmap.scaledToWidth(300, Qt.SmoothTransformation)
            self.logo_label.setPixmap(scaled_pixmap)
        else:
            self.logo_label.setText("[Logo not found]")
        main_layout.addWidget(self.logo_label)
        # Header
        #self.header = QLabel("ENSURE YOU HAVE GONE THROUGH ALL PHOTOS AND DELETED UNWANTED OR DUPLICATE FILES")
        #self.header.setFont(HEADER_FONT)
        #self.header.setStyleSheet(f"color: {SUNRISE_RUBY}; margin-top: 8px; margin-bottom: 8px;")
        #self.header.setAlignment(Qt.AlignCenter)
        #main_layout.addWidget(self.header)
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
    def show_upload_complete(self, local_dir):
        msg = QMessageBox(self)
        msg.setWindowTitle("Upload Complete")
        msg.setText("Upload complete!\n\nOpen directory?")
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
        employee_name = self.ask_user_name(["Alan", "Burt", "Gabe", "Kevin", "Morgan", "Nick", "Tanner"])
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

# ---- Launch PyQt ----

def main():
    app = QApplication(sys.argv)
    palette = app.palette()
    palette.setColor(QPalette.Window, QColor("#ffffff"))
    app.setPalette(palette)
    app.setFont(QFont(SUNRISE_FONT, 10))
    window = Pano2DWGApp()
    window.show()
    sys.exit(app.exec_())

if __name__ == "__main__":
    main()

def probe_ftp_max_threads(max_test=6):
    """
    Simulates probing the maximum number of FTP connections allowed.
    Returns a default value of max_test.
    """
    return max_test

