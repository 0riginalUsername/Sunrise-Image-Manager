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

    if not office_name or not client_name or not project_name or not employee_name:
        return cors_response(400, {"error": "office_name, client_name, project_name, and employee_name are required"})

    for name, label in [(office_name, "office_name"), (client_name, "client_name"), (project_name, "project_name")]:
        if not SAFE_NAME_RE.match(name):
            return cors_response(400, {"error": f"Invalid {label}: only letters, numbers, hyphens, underscores, and dots are allowed"})

    if not pano_files and not photo_files and not image_files:
        return cors_response(400, {"error": "At least one image file is required"})

    file_dt = datetime.utcnow().strftime("%d%b%y_%I-%M%p")
    job_prefix = f"uploads/{office_name}/{client_name}/{project_name}/{file_dt}/"

    def make_uploads(filenames, subdir):
        uploads = []
        for fname in filenames:
            safe_name = fname.replace(" ", "_")
            if not SAFE_NAME_RE.match(safe_name):
                continue  # skip files with dangerous characters
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

    return cors_response(200, {
        "job_prefix": job_prefix,
        "file_dt": file_dt,
        "office_name": office_name,
        "client_name": client_name,
        "project_name": project_name,
        "employee_name": employee_name,
        "pano_uploads": pano_uploads,
        "photo_uploads": photo_uploads,
        "image_uploads": image_uploads,
    })


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
        if verify_password(password, auth_data["hash"], auth_data["salt"]):
            return cors_response(200, {"authorized": True})
        else:
            return cors_response(200, {"authorized": False})
    except s3.exceptions.NoSuchKey:
        return cors_response(200, {"authorized": False})
    except Exception as e:
        logger.error("Error verifying project auth: %s", e)
        return cors_response(500, {"error": "Failed to verify password"})


DOMAIN_BASE = os.environ.get("DOMAIN_BASE", "https://pano.seihds.com")


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
