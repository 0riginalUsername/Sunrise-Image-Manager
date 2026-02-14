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
import json
import uuid
import logging
from datetime import datetime

import boto3

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
            "Access-Control-Allow-Headers": "Content-Type",
            "Access-Control-Allow-Methods": "GET,POST,OPTIONS",
        },
        "body": json.dumps(body),
    }


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
    else:
        return cors_response(404, {"error": "Not found"})


def handle_create_job(event):
    """
    Create a new processing job.

    Expects JSON body with pre-classified lists:
    {
        "client_name": "...",
        "project_name": "...",
        "employee_name": "...",
        "pano_files": ["pano1.jpg", ...],
        "photo_files": ["photo1.jpg", ...]
    }

    Or a flat list (the processing Lambda will auto-classify by aspect ratio):
    {
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

    client_name = body.get("client_name", "").strip().replace(" ", "_")
    project_name = body.get("project_name", "").strip().replace(" ", "_")
    employee_name = body.get("employee_name", "").strip()
    pano_files = body.get("pano_files", [])
    photo_files = body.get("photo_files", [])
    image_files = body.get("image_files", [])

    if not client_name or not project_name or not employee_name:
        return cors_response(400, {"error": "client_name, project_name, and employee_name are required"})

    if not pano_files and not photo_files and not image_files:
        return cors_response(400, {"error": "At least one image file is required"})

    file_dt = datetime.utcnow().strftime("%d%b%y_%I-%M%p")
    job_prefix = f"uploads/{client_name}/{project_name}/{file_dt}/"

    def make_uploads(filenames, subdir):
        uploads = []
        for fname in filenames:
            safe_name = fname.replace(" ", "_")
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
        "job_prefix": "uploads/Client/Project/01Jan25_12-00PM/",
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

    manifest = {
        "client_name": body.get("client_name", ""),
        "project_name": body.get("project_name", ""),
        "employee_name": body.get("employee_name", ""),
        "file_dt": body.get("file_dt", ""),
        "pano_keys": body.get("pano_keys", []),
        "photo_keys": body.get("photo_keys", []),
        "image_keys": body.get("image_keys", []),
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
    Return the client/project registry.

    Response:
    {
        "clients": {
            "Ogden_City": ["Main_St_Survey", "Water_Line"],
            "UDOT": ["I15_Bridge"]
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
