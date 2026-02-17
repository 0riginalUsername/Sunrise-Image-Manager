#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
API Lambda handler for Sunrise Image Manager.

Provides HTTP endpoints via API Gateway for the web frontend:
  POST /api/create-job    - Create a new job and get presigned upload URLs
  POST /api/submit-job    - Finalize uploads and trigger processing
  GET  /api/job-status    - Poll for job processing status
"""

import os
import re
import json
import uuid
import hashlib
import secrets
import logging
from datetime import datetime

import boto3

# Strict pattern for path components — prevents path traversal and XSS via S3 keys
SAFE_NAME_RE = re.compile(r'^[A-Za-z0-9][A-Za-z0-9_\-\.]{0,127}$')

logger = logging.getLogger()
logger.setLevel(logging.INFO)

s3 = boto3.client("s3")
BUCKET = os.environ.get("S3_BUCKET", "sunrise-image-manager")
PRESIGN_EXPIRY = int(os.environ.get("PRESIGN_EXPIRY", "3600"))  # 1 hour
ALLOWED_ORIGIN = os.environ.get("ALLOWED_ORIGIN", "*")
CLIENTS_KEY = os.environ.get("CLIENTS_KEY", "state/clients.json")


def cors_response(status_code, body):
    """Return a response with CORS headers."""
    return {
        "statusCode": status_code,
        "headers": {
            "Content-Type": "application/json",
            "Access-Control-Allow-Origin": ALLOWED_ORIGIN,
            "Access-Control-Allow-Headers": "Content-Type,Authorization",
            "Access-Control-Allow-Methods": "GET,POST,OPTIONS",
        },
        "body": json.dumps(body),
    }


def hash_password(password, salt=None):
    """Hash a password using PBKDF2-SHA256. Returns (hex_hash, hex_salt)."""
    if salt is None:
        salt = secrets.token_bytes(32)
    else:
        salt = bytes.fromhex(salt)
    pw_hash = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 100_000)
    return pw_hash.hex(), salt.hex()


def verify_password(password, stored_hash, stored_salt):
    """Verify a password against a stored PBKDF2 hash."""
    computed_hash, _ = hash_password(password, salt=stored_salt)
    return secrets.compare_digest(computed_hash, stored_hash)


def _apr1_md5_verify(password, apr1_hash):
    """Verify a password against an Apache $apr1$ (MD5) hash.

    Supports legacy .htpasswd entries migrated from Apache Basic Auth.
    The $apr1$ format is: $apr1$salt$hash
    """
    import struct

    if not apr1_hash.startswith("$apr1$"):
        return False
    parts = apr1_hash.split("$")
    # parts = ['', 'apr1', salt, hash]
    if len(parts) != 4:
        return False
    salt = parts[2]
    # APR1-MD5 custom itoa64 alphabet
    itoa64 = "./0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"

    pw = password.encode("utf-8")
    sl = salt.encode("utf-8")
    magic = b"$apr1$"

    ctx = hashlib.md5(pw + magic + sl)
    alt = hashlib.md5(pw + sl + pw).digest()

    plen = len(pw)
    i = plen
    while i > 0:
        ctx.update(alt[:min(16, i)])
        i -= 16

    i = plen
    while i:
        if i & 1:
            ctx.update(b"\x00")
        else:
            ctx.update(pw[:1])
        i >>= 1

    result = ctx.digest()

    for i in range(1000):
        ctx2 = hashlib.md5()
        if i & 1:
            ctx2.update(pw)
        else:
            ctx2.update(result)
        if i % 3:
            ctx2.update(sl)
        if i % 7:
            ctx2.update(pw)
        if i & 1:
            ctx2.update(result)
        else:
            ctx2.update(pw)
        result = ctx2.digest()

    def _to64(v, n):
        out = ""
        for _ in range(n):
            out += itoa64[v & 0x3F]
            v >>= 6
        return out

    computed = (
        _to64((result[0] << 16) | (result[6] << 8) | result[12], 4)
        + _to64((result[1] << 16) | (result[7] << 8) | result[13], 4)
        + _to64((result[2] << 16) | (result[8] << 8) | result[14], 4)
        + _to64((result[3] << 16) | (result[9] << 8) | result[15], 4)
        + _to64((result[4] << 16) | (result[10] << 8) | result[5], 4)
        + _to64(result[11], 2)
    )

    return secrets.compare_digest(computed, parts[3])


def lambda_handler(event, context):
    """Route API Gateway requests to the correct handler."""
    http_method = event.get("httpMethod", "")
    path = event.get("path", "")

    # Handle CORS preflight
    if http_method == "OPTIONS":
        return cors_response(200, {"message": "OK"})

    if path == "/api/create-job" and http_method == "POST":
        return handle_create_job(event)
    elif path == "/api/submit-job" and http_method == "POST":
        return handle_submit_job(event)
    elif path == "/api/job-status" and http_method == "GET":
        return handle_job_status(event)
    elif path == "/api/clients" and http_method == "GET":
        return handle_get_clients(event)
    elif path == "/api/project-password" and http_method == "POST":
        return handle_manage_project_password(event)
    elif path == "/api/project-index" and http_method == "GET":
        return handle_project_index(event)
    elif path == "/api/project-auth" and http_method == "GET":
        return handle_project_auth_check(event)
    elif path == "/api/project-auth" and http_method == "POST":
        return handle_project_auth_verify(event)
    elif path == "/api/save-plan-transform" and http_method == "POST":
        return handle_save_plan_transform(event)
    else:
        return cors_response(404, {"error": "Not found"})


def handle_create_job(event):
    """
    Create a new processing job.

    Expects JSON body with pre-classified lists:
    {
        "office_name": "...",
        "client_name": "...",
        "project_name": "...",
        "employee_name": "...",
        "pano_files": ["pano1.jpg", ...],
        "photo_files": ["photo1.jpg", ...]
    }

    Or a flat list (the processing Lambda will auto-classify by aspect ratio):
    {
        "office_name": "...",
        "client_name": "...",
        "project_name": "...",
        "employee_name": "...",
        "image_files": ["any1.jpg", "any2.jpg", ...]
    }

    Returns presigned URLs for each file so the browser can upload directly to S3.
    """
    try:
        body = json.loads(event.get("body", "{}"))
    except (json.JSONDecodeError, TypeError):
        return cors_response(400, {"error": "Invalid JSON body"})

    office_name = body.get("office_name", "").strip().replace(" ", "_")
    client_name = body.get("client_name", "").strip().replace(" ", "_")
    project_name = body.get("project_name", "").strip().replace(" ", "_")
    employee_name = body.get("employee_name", "").strip()
    pano_files = body.get("pano_files", [])
    photo_files = body.get("photo_files", [])
    image_files = body.get("image_files", [])
    plan_file = body.get("plan_file", "")

    if not office_name or not client_name or not project_name or not employee_name:
        return cors_response(400, {"error": "office_name, client_name, project_name, and employee_name are required"})

    for name, label in [(office_name, "office_name"), (client_name, "client_name"), (project_name, "project_name")]:
        if not SAFE_NAME_RE.match(name):
            return cors_response(400, {"error": f"Invalid {label}: only letters, numbers, hyphens, underscores, and dots are allowed"})

    if not pano_files and not photo_files and not image_files:
        return cors_response(400, {"error": "At least one image file is required"})

    file_dt = datetime.utcnow().strftime("%d%b%y_%I-%M%p")
    job_prefix = f"uploads/{office_name}/{client_name}/{project_name}/{file_dt}/"

    def sanitize_filename(name):
        """Replace spaces with underscores and strip all characters not in [A-Za-z0-9_.-]."""
        name = name.replace(" ", "_")
        name = re.sub(r'[^A-Za-z0-9_\-\.]', '', name)
        # Ensure it starts with an alphanumeric character
        name = name.lstrip('_-.')
        # Truncate to 128 characters
        if len(name) > 128:
            name = name[:128]
        return name

    rejected = []

    def make_uploads(filenames, subdir):
        uploads = []
        for fname in filenames:
            safe_name = sanitize_filename(fname)
            if not safe_name or not SAFE_NAME_RE.match(safe_name):
                rejected.append(fname)
                continue
            key = f"{job_prefix}raw/{subdir}/{safe_name}"
            url = s3.generate_presigned_url(
                "put_object",
                Params={"Bucket": BUCKET, "Key": key, "ContentType": "image/jpeg"},
                ExpiresIn=PRESIGN_EXPIRY,
            )
            uploads.append({"filename": fname, "key": key, "upload_url": url})
        return uploads

    # Generate presigned PUT URLs for each file
    pano_uploads = make_uploads(pano_files, "pano")
    photo_uploads = make_uploads(photo_files, "photo")

    # Flat image_files go to raw/ (unclassified) — handler will auto-classify
    image_uploads = make_uploads(image_files, "images")

    # Plan background file (optional)
    plan_upload = None
    if plan_file:
        safe_plan = sanitize_filename(plan_file)
        if safe_plan and SAFE_NAME_RE.match(safe_plan):
            plan_key = f"{job_prefix}raw/plan/{safe_plan}"
            plan_url = s3.generate_presigned_url(
                "put_object",
                Params={"Bucket": BUCKET, "Key": plan_key, "ContentType": "image/jpeg"},
                ExpiresIn=PRESIGN_EXPIRY,
            )
            plan_upload = {"filename": plan_file, "key": plan_key, "upload_url": plan_url}
        else:
            rejected.append(plan_file)

    if rejected:
        return cors_response(400, {
            "error": f"The following filenames contain unsupported characters and cannot be uploaded: {', '.join(rejected)}. "
                     "Please rename them using only letters, numbers, hyphens, underscores, and dots."
        })

    resp_body = {
        "job_prefix": job_prefix,
        "file_dt": file_dt,
        "office_name": office_name,
        "client_name": client_name,
        "project_name": project_name,
        "employee_name": employee_name,
        "pano_uploads": pano_uploads,
        "photo_uploads": photo_uploads,
        "image_uploads": image_uploads,
    }
    if plan_upload:
        resp_body["plan_upload"] = plan_upload
    return cors_response(200, resp_body)


def handle_submit_job(event):
    """
    Finalize a job after all files have been uploaded.
    Writes the manifest.json to S3 which triggers the processing Lambda.

    Expects JSON body:
    {
        "job_prefix": "uploads/Office/Client/Project/01Jan25_12-00PM/",
        "office_name": "...",
        "client_name": "...",
        "project_name": "...",
        "employee_name": "...",
        "file_dt": "...",
        "pano_keys": ["uploads/.../raw/pano/file1.jpg", ...],
        "photo_keys": ["uploads/.../raw/photo/file3.jpg", ...],
        "image_keys": ["uploads/.../raw/images/any.jpg", ...]  (optional, auto-classified)
    }
    """
    try:
        body = json.loads(event.get("body", "{}"))
    except (json.JSONDecodeError, TypeError):
        return cors_response(400, {"error": "Invalid JSON body"})

    job_prefix = body.get("job_prefix", "")
    if not job_prefix:
        return cors_response(400, {"error": "job_prefix is required"})

    # Validate that all submitted S3 keys belong to this job
    expected_prefix = job_prefix + "raw/"
    all_keys = body.get("pano_keys", []) + body.get("photo_keys", []) + body.get("image_keys", [])
    for key in all_keys:
        if not key.startswith(expected_prefix) or ".." in key:
            return cors_response(400, {"error": f"Invalid key: must start with {expected_prefix}"})

    # Store project password if provided (hash it, don't put plaintext in manifest)
    project_password = body.get("project_password", "").strip()
    if project_password:
        office_name_safe = body.get("office_name", "").strip().replace(" ", "_")
        client_name_safe = body.get("client_name", "").strip().replace(" ", "_")
        project_name_safe = body.get("project_name", "").strip().replace(" ", "_")
        for name in [office_name_safe, client_name_safe, project_name_safe]:
            if not SAFE_NAME_RE.match(name):
                return cors_response(400, {"error": "Invalid name in password storage path"})
        pw_hash, pw_salt = hash_password(project_password)
        auth_key = f"state/project-auth/{office_name_safe}/{client_name_safe}/{project_name_safe}.json"
        s3.put_object(
            Bucket=BUCKET,
            Key=auth_key,
            Body=json.dumps({"hash": pw_hash, "salt": pw_salt}).encode("utf-8"),
            ContentType="application/json",
        )
        logger.info("Stored project password for %s/%s/%s", office_name_safe, client_name_safe, project_name_safe)

    manifest = {
        "office_name": body.get("office_name", ""),
        "client_name": body.get("client_name", ""),
        "project_name": body.get("project_name", ""),
        "employee_name": body.get("employee_name", ""),
        "file_dt": body.get("file_dt", ""),
        "pano_keys": body.get("pano_keys", []),
        "photo_keys": body.get("photo_keys", []),
        "image_keys": body.get("image_keys", []),
        "keep_filenames": body.get("keep_filenames", False),
        "keep_originals": body.get("keep_originals", False),
        "jpeg_quality": body.get("jpeg_quality"),
        "position_csv": body.get("position_csv", ""),
        "submitter_email": body.get("submitter_email", ""),
        "submitted_at": datetime.utcnow().isoformat() + "Z",
    }
    plan_key = body.get("plan_key", "")
    if plan_key:
        if not plan_key.startswith(expected_prefix) or ".." in plan_key:
            return cors_response(400, {"error": f"Invalid plan_key: must start with {expected_prefix}"})
        manifest["plan_key"] = plan_key

    manifest_key = f"{job_prefix}manifest.json"
    s3.put_object(
        Bucket=BUCKET,
        Key=manifest_key,
        Body=json.dumps(manifest).encode("utf-8"),
        ContentType="application/json",
    )

    logger.info("Manifest written: s3://%s/%s", BUCKET, manifest_key)
    return cors_response(200, {
        "message": "Job submitted for processing",
        "manifest_key": manifest_key,
        "status_key": f"{job_prefix}status.json",
    })


def handle_job_status(event):
    """
    Check the status of a processing job.

    Query parameter: ?job_prefix=uploads/Client/Project/01Jan25_12-00PM/
    """
    params = event.get("queryStringParameters") or {}
    job_prefix = params.get("job_prefix", "")
    if not job_prefix:
        return cors_response(400, {"error": "job_prefix query parameter is required"})

    status_key = f"{job_prefix}status.json"
    try:
        obj = s3.get_object(Bucket=BUCKET, Key=status_key)
        status_data = json.loads(obj["Body"].read().decode("utf-8"))
        return cors_response(200, status_data)
    except s3.exceptions.NoSuchKey:
        return cors_response(200, {"status": "pending", "message": "Job not yet started"})
    except Exception as e:
        logger.error("Error reading status: %s", e)
        return cors_response(500, {"error": "Failed to read job status"})


def handle_get_clients(event):
    """
    Return the office/client/project registry.

    Response:
    {
        "clients": {
            "Salt_Lake": {
                "Ogden_City": ["Main_St_Survey", "Water_Line"],
                "UDOT": ["I15_Bridge"]
            },
            "St_George": { ... }
        }
    }
    """
    try:
        obj = s3.get_object(Bucket=BUCKET, Key=CLIENTS_KEY)
        clients = json.loads(obj["Body"].read().decode("utf-8"))
    except s3.exceptions.NoSuchKey:
        clients = {}
    except Exception as e:
        logger.error("Error reading clients registry: %s", e)
        clients = {}
    return cors_response(200, {"clients": clients})


def _sync_index_protected_flag(office, client, project, is_protected):
    """Update the 'protected' flag in a project's index.json immediately."""
    index_key = f"processed/{office}/{client}/{project}/index.json"
    try:
        obj = s3.get_object(Bucket=BUCKET, Key=index_key)
        index_data = json.loads(obj["Body"].read().decode("utf-8"))
    except Exception:
        # Project index doesn't exist yet — nothing to update
        return

    if is_protected:
        index_data["protected"] = True
    else:
        index_data.pop("protected", None)

    try:
        s3.put_object(
            Bucket=BUCKET, Key=index_key,
            Body=json.dumps(index_data, indent=2).encode("utf-8"),
            ContentType="application/json",
            CacheControl="no-cache, no-store, must-revalidate",
        )
        logger.info("Synced protected=%s in index.json for %s/%s/%s", is_protected, office, client, project)
    except Exception as e:
        logger.error("Failed to sync protected flag in index.json for %s/%s/%s: %s",
                     office, client, project, e)


def handle_manage_project_password(event):
    """
    Set, update, or remove a project password (requires Cognito auth).

    Expects JSON body:
    {
        "office": "OfficeName",
        "client": "ClientName",
        "project": "ProjectName",
        "password": "new-password"     // set/update
        // OR
        "password": ""                 // remove
        // OR
        "action": "remove"             // remove
    }

    Response: { "message": "...", "protected": true/false }
    """
    try:
        body = json.loads(event.get("body", "{}"))
    except (json.JSONDecodeError, TypeError):
        return cors_response(400, {"error": "Invalid JSON body"})

    office = body.get("office", "").strip().replace(" ", "_")
    client = body.get("client", "").strip().replace(" ", "_")
    project = body.get("project", "").strip().replace(" ", "_")
    action = body.get("action", "")
    password = body.get("password", "")

    if not office or not client or not project:
        return cors_response(400, {"error": "office, client, and project are required"})
    for name, label in [(office, "office"), (client, "client"), (project, "project")]:
        if not SAFE_NAME_RE.match(name):
            return cors_response(400, {"error": f"Invalid {label}"})

    auth_key = f"state/project-auth/{office}/{client}/{project}.json"

    # Remove password
    if action == "remove" or (not password and action != "check"):
        try:
            s3.delete_object(Bucket=BUCKET, Key=auth_key)
            _sync_index_protected_flag(office, client, project, False)
            logger.info("Removed project password for %s/%s/%s", office, client, project)
            return cors_response(200, {"message": "Password removed", "protected": False})
        except Exception as e:
            logger.error("Error removing project password: %s", e)
            return cors_response(500, {"error": "Failed to remove password"})

    # Check current status
    if action == "check":
        try:
            s3.head_object(Bucket=BUCKET, Key=auth_key)
            return cors_response(200, {"protected": True})
        except Exception:
            return cors_response(200, {"protected": False})

    # Set/update password
    pw_hash, pw_salt = hash_password(password)
    try:
        s3.put_object(
            Bucket=BUCKET,
            Key=auth_key,
            Body=json.dumps({"hash": pw_hash, "salt": pw_salt}).encode("utf-8"),
            ContentType="application/json",
        )
        _sync_index_protected_flag(office, client, project, True)
        logger.info("Set project password for %s/%s/%s", office, client, project)
        return cors_response(200, {"message": "Password set", "protected": True})
    except Exception as e:
        logger.error("Error setting project password: %s", e)
        return cors_response(500, {"error": "Failed to set password"})


def handle_project_auth_check(event):
    """
    Check if a project is password-protected.

    Query parameters: ?office=OfficeName&client=ClientName&project=ProjectName
    Response: { "protected": true/false }
    """
    params = event.get("queryStringParameters") or {}
    office = params.get("office", "").strip().replace(" ", "_")
    client = params.get("client", "").strip().replace(" ", "_")
    project = params.get("project", "").strip().replace(" ", "_")
    if not office or not client or not project:
        return cors_response(400, {"error": "office, client, and project query parameters are required"})
    for name in [office, client, project]:
        if not SAFE_NAME_RE.match(name):
            return cors_response(400, {"error": "Invalid parameter"})

    auth_key = f"state/project-auth/{office}/{client}/{project}.json"
    try:
        s3.get_object(Bucket=BUCKET, Key=auth_key)
        return cors_response(200, {"protected": True})
    except s3.exceptions.NoSuchKey:
        return cors_response(200, {"protected": False})
    except Exception as e:
        logger.error("Error checking project auth: %s", e)
        return cors_response(200, {"protected": False})


def handle_project_auth_verify(event):
    """
    Verify a project password.

    Expects JSON body: { "office": "...", "client": "...", "project": "...", "password": "..." }
    Response: { "authorized": true/false }
    """
    try:
        body = json.loads(event.get("body", "{}"))
    except (json.JSONDecodeError, TypeError):
        return cors_response(400, {"error": "Invalid JSON body"})

    office = body.get("office", "").strip().replace(" ", "_")
    client = body.get("client", "").strip().replace(" ", "_")
    project = body.get("project", "").strip().replace(" ", "_")
    password = body.get("password", "")

    if not office or not client or not project or not password:
        return cors_response(400, {"error": "office, client, project, and password are required"})
    for name in [office, client, project]:
        if not SAFE_NAME_RE.match(name):
            return cors_response(400, {"error": "Invalid parameter"})

    auth_key = f"state/project-auth/{office}/{client}/{project}.json"
    try:
        obj = s3.get_object(Bucket=BUCKET, Key=auth_key)
        auth_data = json.loads(obj["Body"].read().decode("utf-8"))
        # Support legacy $apr1$ hashes migrated from .htpasswd files
        if auth_data.get("format") == "apr1":
            authorized = _apr1_md5_verify(password, auth_data["apr1_hash"])
        else:
            authorized = verify_password(password, auth_data["hash"], auth_data["salt"])
        if authorized:
            return cors_response(200, {"authorized": True})
        else:
            return cors_response(200, {"authorized": False})
    except s3.exceptions.NoSuchKey:
        return cors_response(200, {"authorized": False})
    except Exception as e:
        logger.error("Error verifying project auth: %s", e)
        return cors_response(500, {"error": "Failed to verify password"})


DOMAIN_BASE = os.environ.get("DOMAIN_BASE", "https://pano.seihds.com")


def handle_save_plan_transform(event):
    """
    Save the plan background alignment transform for a project.

    Expects JSON body:
    {
        "office": "OfficeName",
        "client": "ClientName",
        "project": "ProjectName",
        "plan_transform": { "translate_x": 0, "translate_y": 0, "scale": 1, "rotation": 0 }
    }
    """
    try:
        body = json.loads(event.get("body", "{}"))
    except (json.JSONDecodeError, TypeError):
        return cors_response(400, {"error": "Invalid JSON body"})

    office = body.get("office", "").strip().replace(" ", "_")
    client = body.get("client", "").strip().replace(" ", "_")
    project = body.get("project", "").strip().replace(" ", "_")
    transform = body.get("plan_transform")

    if not office or not client or not project or not transform:
        return cors_response(400, {"error": "office, client, project, and plan_transform are required"})
    for name, label in [(office, "office"), (client, "client"), (project, "project")]:
        if not SAFE_NAME_RE.match(name):
            return cors_response(400, {"error": f"Invalid {label}"})

    # Validate transform fields
    allowed_keys = {"translate_x", "translate_y", "scale", "rotation"}
    if not isinstance(transform, dict) or not all(k in allowed_keys for k in transform):
        return cors_response(400, {"error": "plan_transform must contain translate_x, translate_y, scale, rotation"})

    index_key = f"processed/{office}/{client}/{project}/index.json"
    try:
        obj = s3.get_object(Bucket=BUCKET, Key=index_key)
        index_data = json.loads(obj["Body"].read().decode("utf-8"))
    except s3.exceptions.NoSuchKey:
        return cors_response(404, {"error": "Project not found"})
    except Exception as e:
        logger.error("Error reading project index: %s", e)
        return cors_response(500, {"error": "Failed to read project index"})

    index_data["plan_transform"] = {
        "translate_x": float(transform.get("translate_x", 0)),
        "translate_y": float(transform.get("translate_y", 0)),
        "scale": float(transform.get("scale", 1)),
        "rotation": float(transform.get("rotation", 0)),
    }

    s3.put_object(
        Bucket=BUCKET, Key=index_key,
        Body=json.dumps(index_data, indent=2).encode("utf-8"),
        ContentType="application/json",
        CacheControl="no-cache, no-store, must-revalidate",
    )

    logger.info("Saved plan transform for %s/%s/%s", office, client, project)
    return cors_response(200, {"message": "Plan alignment saved"})


def handle_project_index(event):
    """
    Return project summary for the Browse Projects view.

    Query parameters (all optional, for filtering):
      ?office=OfficeName&client=ClientName

    Returns the client registry enriched with summary data for each project.
    If office and client are specified, returns detailed batch info from index.json.
    """
    params = event.get("queryStringParameters") or {}
    office = params.get("office", "").strip()
    client = params.get("client", "").strip()
    project = params.get("project", "").strip()

    # If a specific project is requested, return its index.json
    if office and client and project:
        index_key = f"processed/{office}/{client}/{project}/index.json"
        try:
            obj = s3.get_object(Bucket=BUCKET, Key=index_key)
            index_data = json.loads(obj["Body"].read().decode("utf-8"))
            # Add landing page URL
            index_data["landing_url"] = f"{DOMAIN_BASE}/processed/{office}/{client}/{project}/index.html"
            return cors_response(200, index_data)
        except s3.exceptions.NoSuchKey:
            return cors_response(404, {"error": "Project not found"})
        except Exception as e:
            logger.error("Error reading project index: %s", e)
            return cors_response(500, {"error": "Failed to read project index"})

    # Otherwise, build summaries from the client registry + index.json files
    try:
        obj = s3.get_object(Bucket=BUCKET, Key=CLIENTS_KEY)
        registry = json.loads(obj["Body"].read().decode("utf-8"))
    except Exception:
        registry = {}

    # Filter by office if specified
    if office:
        registry = {office: registry.get(office, {})}

    # Filter by client if specified
    if client and office:
        clients = registry.get(office, {})
        registry = {office: {client: clients.get(client, [])}}

    # Build summary: for each project, try to read a lightweight summary from index.json
    result = {}
    for off_name, clients_map in registry.items():
        result[off_name] = {}
        for cli_name, projects in clients_map.items():
            result[off_name][cli_name] = []
            for proj_name in projects:
                summary = {
                    "name": proj_name,
                    "landing_url": f"{DOMAIN_BASE}/processed/{off_name}/{cli_name}/{proj_name}/index.html",
                }
                # Try to read index.json for batch/image counts
                index_key = f"processed/{off_name}/{cli_name}/{proj_name}/index.json"
                try:
                    obj = s3.get_object(Bucket=BUCKET, Key=index_key)
                    index_data = json.loads(obj["Body"].read().decode("utf-8"))
                    batches = index_data.get("batches", [])
                    total_pano = sum(b.get("pano_count", 0) for b in batches)
                    total_photo = sum(b.get("photo_count", 0) for b in batches)
                    last_batch = batches[-1] if batches else {}
                    summary["batch_count"] = len(batches)
                    summary["pano_count"] = total_pano
                    summary["photo_count"] = total_photo
                    summary["last_upload"] = last_batch.get("submitted_at", "")
                    summary["last_employee"] = last_batch.get("employee", "")
                    summary["protected"] = index_data.get("protected", False)
                except Exception:
                    summary["batch_count"] = 0
                    summary["pano_count"] = 0
                    summary["photo_count"] = 0
                    summary["last_upload"] = ""
                    summary["last_employee"] = ""
                    summary["protected"] = False
                result[off_name][cli_name].append(summary)
            # Sort projects by last_upload descending (most recent first)
            result[off_name][cli_name].sort(key=lambda p: p.get("last_upload", ""), reverse=True)

    return cors_response(200, {"projects": result})
