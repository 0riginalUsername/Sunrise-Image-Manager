#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Migrate Legacy Panorama Projects
=================================

Scans a local copy of the S3 bucket and:

1. Detects legacy PTGui projects (cube map tiles + PTGuiViewer.js) and
   legacy Pannellum projects (equirectangular + old skin).
2. Regenerates .htm files using the modern Sunrise templates with
   password gate support.
3. Imports .htpasswd passwords (Apache $apr1$ format) into project-auth
   JSON files compatible with the API's verification endpoint.
4. Creates/updates index.json for each project.
5. Outputs aws s3 sync commands to push only changed files back to S3.

Usage:
    python migrate_legacy_panos.py /path/to/local/s3-bucket-copy [--dry-run]

The local copy should mirror the S3 bucket structure:
    processed/<office>/<client>/<project>/<batch>/P001.htm
    processed/<office>/<client>/<project>/<batch>/P001_00.jpg ... P001_14.jpg
    processed/<office>/<client>/<project>/<batch>/PTGuiViewer.js
    processed/<office>/<client>/<project>/.htpasswd  (optional)
"""

import os
import re
import sys
import json
import argparse
import shutil
from pathlib import Path
from datetime import datetime


# ---------------------------------------------------------------------------
# Template paths (relative to this script)
# ---------------------------------------------------------------------------
SCRIPT_DIR = Path(__file__).resolve().parent
PTGUI_TEMPLATE_PATH = SCRIPT_DIR / "PTGui-Pano-Template.htm"
PANO_TEMPLATE_PATH = SCRIPT_DIR / "Pano-Template.htm"


# ---------------------------------------------------------------------------
# Regex patterns for parsing legacy PTGui .htm files
# ---------------------------------------------------------------------------
# Matches the viewer.setVars({...}) block (may span multiple lines)
SETVARS_RE = re.compile(
    r'viewer\.setVars\(\s*\{(.*?)\}\s*\)',
    re.DOTALL
)

# Matches individual key: value pairs inside setVars
# Handles both quoted and unquoted values
PARAM_RE = re.compile(
    r'(\w+)\s*:\s*("(?:[^"\\]|\\.)*"|\'(?:[^\'\\]|\\.)*\'|[^,}\s]+)'
)

# Detect PTGui viewer references
PTGUI_DETECT_RE = re.compile(r'PTGuiViewer\.js', re.IGNORECASE)

# Detect Pannellum references
PANNELLUM_DETECT_RE = re.compile(r'pannellum', re.IGNORECASE)

# Detect old-style Sunrise template (pre-2018 branding)
OLD_SKIN_RE = re.compile(
    r'sunrise-eng\.com/css/|'          # old CSS references
    r'seihds\.com/web/logo\.jpg|'      # old logo
    r'Small Giants',                   # old footer credit
    re.IGNORECASE
)


def parse_ptgui_setvars(htm_content):
    """Extract the viewer.setVars({...}) config from a PTGui .htm file.

    Returns the raw JSON-like string of parameters (for template injection),
    and a dict of parsed key-value pairs.
    """
    match = SETVARS_RE.search(htm_content)
    if not match:
        return None, {}

    raw_block = match.group(1).strip()
    params = {}
    for m in PARAM_RE.finditer(raw_block):
        key = m.group(1)
        val = m.group(2).strip()
        # Strip quotes from string values
        if (val.startswith('"') and val.endswith('"')) or \
           (val.startswith("'") and val.endswith("'")):
            val = val[1:-1]
        else:
            # Try numeric conversion
            try:
                val = int(val)
            except ValueError:
                try:
                    val = float(val)
                except ValueError:
                    pass
        params[key] = val

    return raw_block, params


def parse_htpasswd(htpasswd_path):
    """Parse an Apache .htpasswd file.

    Returns a list of (username, full_hash) tuples.
    Only $apr1$ hashes are supported for migration.
    """
    entries = []
    try:
        with open(htpasswd_path, 'r') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                if ':' in line:
                    username, hash_val = line.split(':', 1)
                    entries.append((username.strip(), hash_val.strip()))
    except (IOError, OSError) as e:
        print(f"  WARNING: Could not read {htpasswd_path}: {e}")
    return entries


def detect_project_type(htm_path):
    """Determine if an .htm file is a PTGui viewer or Pannellum viewer.

    Returns: 'ptgui', 'pannellum', or 'unknown'
    """
    try:
        with open(htm_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except (IOError, OSError):
        return 'unknown'

    if PTGUI_DETECT_RE.search(content):
        return 'ptgui'
    if PANNELLUM_DETECT_RE.search(content):
        return 'pannellum'
    return 'unknown'


def has_old_skin(htm_path):
    """Check if an .htm file uses the old (pre-2018) Sunrise website skin."""
    try:
        with open(htm_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except (IOError, OSError):
        return False
    return bool(OLD_SKIN_RE.search(content))


def has_password_gate(htm_path):
    """Check if an .htm file already has the modern password gate."""
    try:
        with open(htm_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except (IOError, OSError):
        return False
    return 'pw-locked' in content and 'verifyViewerPassword' in content


def extract_pannellum_config(htm_content):
    """Extract Pannellum viewer config from an .htm file.

    Returns a dict with 'panorama' image path and 'img_date' if found.
    """
    config = {}
    # Match the panorama image path
    pano_match = re.search(r'"panorama"\s*:\s*"([^"]+)"', htm_content)
    if pano_match:
        config['panorama'] = pano_match.group(1)

    # Match the image date
    date_match = re.search(r'Image date and time taken:\s*([^<]+)', htm_content)
    if date_match:
        config['img_date'] = date_match.group(1).strip()
        # Clean up template placeholders
        if '{{' in config['img_date']:
            config['img_date'] = ''

    return config


def generate_ptgui_htm(template_content, pano_vars_raw):
    """Generate a new PTGui .htm file from the template."""
    # Wrap the raw vars block back into a proper JS object
    vars_json = "{\n" + pano_vars_raw + "\n}"
    return template_content.replace("{{PANO_VARS}}", vars_json)


def generate_pannellum_htm(template_content, panorama_img, img_date=''):
    """Generate a new Pannellum .htm file from the template."""
    result = template_content.replace("{{IMG}}", panorama_img)
    result = result.replace("{{IMG_DATE}}", img_date)
    result = result.replace("{{TITLE}}", "Panorama Viewer")
    return result


def scan_bucket(root_path):
    """Scan the local S3 bucket copy for projects and their contents.

    Returns a list of project dicts:
    {
        'path': Path to project folder (office/client/project level),
        'office': office name,
        'client': client name,
        'project': project name,
        'batches': [{
            'batch_dir': batch folder name,
            'htm_files': [list of .htm paths],
            'type': 'ptgui' | 'pannellum' | 'unknown',
            'has_old_skin': bool,
            'has_password_gate': bool,
        }],
        'htpasswd': path to .htpasswd file or None,
        'has_index_json': bool,
    }
    """
    root = Path(root_path)
    processed_dir = root / "processed"
    if not processed_dir.exists():
        print(f"ERROR: No 'processed' directory found at {root}")
        print("Expected structure: <root>/processed/<office>/<client>/<project>/")
        sys.exit(1)

    projects = []

    # Walk: processed/<office>/<client>/<project>/
    for office_dir in sorted(processed_dir.iterdir()):
        if not office_dir.is_dir():
            continue
        for client_dir in sorted(office_dir.iterdir()):
            if not client_dir.is_dir():
                continue
            for project_dir in sorted(client_dir.iterdir()):
                if not project_dir.is_dir():
                    continue

                project = {
                    'path': project_dir,
                    'office': office_dir.name,
                    'client': client_dir.name,
                    'project': project_dir.name,
                    'batches': [],
                    'htpasswd': None,
                    'has_index_json': (project_dir / "index.json").exists(),
                }

                # Check for .htpasswd at project level
                htpasswd_path = project_dir / ".htpasswd"
                if htpasswd_path.exists():
                    project['htpasswd'] = htpasswd_path

                # Scan batch subdirectories
                for batch_dir in sorted(project_dir.iterdir()):
                    if not batch_dir.is_dir():
                        continue
                    # Skip non-batch directories
                    if batch_dir.name in ('__pycache__', '.git'):
                        continue

                    htm_files = sorted(batch_dir.glob("*.htm"))
                    if not htm_files:
                        continue

                    # Detect type from first .htm file
                    first_htm = htm_files[0]
                    proj_type = detect_project_type(first_htm)
                    old_skin = has_old_skin(first_htm)
                    pw_gate = has_password_gate(first_htm)

                    project['batches'].append({
                        'batch_dir': batch_dir,
                        'htm_files': htm_files,
                        'type': proj_type,
                        'has_old_skin': old_skin,
                        'has_password_gate': pw_gate,
                    })

                if project['batches']:
                    projects.append(project)

    return projects


def create_project_auth_json(htpasswd_path, output_dir):
    """Create a project-auth JSON file from an .htpasswd file.

    Stores the $apr1$ hash in the format expected by the API.
    Returns the auth data dict, or None if no valid entries found.
    """
    entries = parse_htpasswd(htpasswd_path)
    if not entries:
        return None

    # Use the first entry (typically one user per project .htpasswd)
    username, hash_val = entries[0]

    if not hash_val.startswith('$apr1$'):
        print(f"  WARNING: Unsupported hash format in {htpasswd_path}: {hash_val[:10]}...")
        return None

    auth_data = {
        "format": "apr1",
        "apr1_hash": hash_val,
        "migrated_from": ".htpasswd",
        "original_username": username,
        "migrated_at": datetime.utcnow().isoformat() + "Z",
    }

    return auth_data


def migrate_project(project, ptgui_template, pano_template, dry_run=False):
    """Migrate a single project's .htm files and passwords.

    Returns a dict of stats about what was changed.
    """
    stats = {
        'htm_updated': 0,
        'htm_skipped': 0,
        'password_imported': False,
        'index_json_created': False,
        'type': 'unknown',
    }

    for batch in project['batches']:
        batch_type = batch['type']
        stats['type'] = batch_type

        # Skip if already has modern skin + password gate
        if not batch['has_old_skin'] and batch['has_password_gate']:
            stats['htm_skipped'] += len(batch['htm_files'])
            continue

        for htm_path in batch['htm_files']:
            try:
                with open(htm_path, 'r', encoding='utf-8', errors='ignore') as f:
                    content = f.read()
            except (IOError, OSError) as e:
                print(f"  ERROR reading {htm_path}: {e}")
                continue

            new_content = None

            if batch_type == 'ptgui':
                raw_vars, params = parse_ptgui_setvars(content)
                if raw_vars:
                    new_content = generate_ptgui_htm(ptgui_template, raw_vars)
                else:
                    print(f"  WARNING: Could not parse setVars from {htm_path}")

            elif batch_type == 'pannellum':
                config = extract_pannellum_config(content)
                if config.get('panorama'):
                    new_content = generate_pannellum_htm(
                        pano_template,
                        config['panorama'],
                        config.get('img_date', '')
                    )
                else:
                    print(f"  WARNING: Could not extract panorama config from {htm_path}")

            if new_content:
                if not dry_run:
                    # Rename original to .old (preserve it, don't overwrite)
                    old_path = htm_path.with_suffix('.htm.old')
                    if not old_path.exists():
                        shutil.move(str(htm_path), str(old_path))
                    with open(htm_path, 'w', encoding='utf-8') as f:
                        f.write(new_content)
                stats['htm_updated'] += 1
            else:
                stats['htm_skipped'] += 1

    # Import .htpasswd password
    if project['htpasswd']:
        auth_data = create_project_auth_json(
            project['htpasswd'],
            project['path']
        )
        if auth_data:
            # Write project-auth JSON to state directory
            # This mirrors the S3 path: state/project-auth/<office>/<client>/<project>.json
            state_dir = project['path'].parents[3] / "state" / "project-auth" / \
                        project['office'] / project['client']
            auth_json_path = state_dir / f"{project['project']}.json"

            if not dry_run:
                state_dir.mkdir(parents=True, exist_ok=True)
                with open(auth_json_path, 'w') as f:
                    json.dump(auth_data, f, indent=2)
            stats['password_imported'] = True

    # Create/update index.json
    if not project['has_index_json'] or project['htpasswd']:
        index_data = {
            "office_name": project['office'],
            "client_name": project['client'],
            "project_name": project['project'],
        }
        if project['htpasswd']:
            index_data["protected"] = True

        # Collect batch info
        batches = []
        for batch in project['batches']:
            batch_images = []
            for htm_path in batch['htm_files']:
                base = htm_path.stem
                batch_images.append({
                    "filename": base + ".jpg",
                    "type": "pano",
                    "viewer": f"{batch['batch_dir'].name}/{base}.htm",
                })
            batches.append({
                "date": batch['batch_dir'].name,
                "images": batch_images,
            })
        index_data["batches"] = batches

        index_path = project['path'] / "index.json"
        if not dry_run:
            with open(index_path, 'w') as f:
                json.dump(index_data, f, indent=2)
        stats['index_json_created'] = True

    return stats


def main():
    parser = argparse.ArgumentParser(
        description="Migrate legacy panorama projects to modern templates with password support."
    )
    parser.add_argument(
        "bucket_path",
        help="Path to local copy of the S3 bucket root"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be changed without modifying any files"
    )
    parser.add_argument(
        "--skip-pannellum",
        action="store_true",
        help="Only migrate PTGui projects, skip Pannellum projects that already have modern skin"
    )
    args = parser.parse_args()

    bucket_root = Path(args.bucket_path).resolve()
    if not bucket_root.exists():
        print(f"ERROR: Path does not exist: {bucket_root}")
        sys.exit(1)

    # Load templates
    if not PTGUI_TEMPLATE_PATH.exists():
        print(f"ERROR: PTGui template not found: {PTGUI_TEMPLATE_PATH}")
        sys.exit(1)
    if not PANO_TEMPLATE_PATH.exists():
        print(f"ERROR: Pannellum template not found: {PANO_TEMPLATE_PATH}")
        sys.exit(1)

    ptgui_template = PTGUI_TEMPLATE_PATH.read_text(encoding='utf-8')
    pano_template = PANO_TEMPLATE_PATH.read_text(encoding='utf-8')

    mode = "DRY RUN" if args.dry_run else "LIVE"
    print(f"\n{'='*60}")
    print(f"  Legacy Panorama Migration Tool  [{mode}]")
    print(f"{'='*60}")
    print(f"  Bucket root:  {bucket_root}")
    print(f"  PTGui template: {PTGUI_TEMPLATE_PATH}")
    print(f"  Pano template:  {PANO_TEMPLATE_PATH}")
    print(f"{'='*60}\n")

    # Scan
    print("Scanning for projects...")
    projects = scan_bucket(bucket_root)
    print(f"Found {len(projects)} projects\n")

    if not projects:
        print("No projects found. Check that the path contains a 'processed/' directory.")
        sys.exit(0)

    # Summarize what was found
    ptgui_count = sum(1 for p in projects
                      if any(b['type'] == 'ptgui' for b in p['batches']))
    pannellum_count = sum(1 for p in projects
                         if any(b['type'] == 'pannellum' for b in p['batches']))
    htpasswd_count = sum(1 for p in projects if p['htpasswd'])
    old_skin_count = sum(1 for p in projects
                         if any(b['has_old_skin'] for b in p['batches']))

    print(f"  PTGui projects:     {ptgui_count}")
    print(f"  Pannellum projects: {pannellum_count}")
    print(f"  With .htpasswd:     {htpasswd_count}")
    print(f"  With old skin:      {old_skin_count}")
    print()

    # Migrate
    total_htm_updated = 0
    total_htm_skipped = 0
    total_pw_imported = 0
    total_index_created = 0
    changed_paths = set()

    for project in projects:
        label = f"{project['office']}/{project['client']}/{project['project']}"
        batch_types = set(b['type'] for b in project['batches'])

        if args.skip_pannellum and batch_types == {'pannellum'}:
            needs_update = any(b['has_old_skin'] for b in project['batches'])
            if not needs_update and not project['htpasswd']:
                continue

        print(f"  Migrating: {label}")

        stats = migrate_project(project, ptgui_template, pano_template, args.dry_run)

        if stats['htm_updated'] > 0:
            print(f"    HTM updated: {stats['htm_updated']} ({stats['type']})")
            total_htm_updated += stats['htm_updated']
            for batch in project['batches']:
                changed_paths.add(str(batch['batch_dir']))
        if stats['htm_skipped'] > 0:
            total_htm_skipped += stats['htm_skipped']
        if stats['password_imported']:
            print(f"    Password imported from .htpasswd")
            total_pw_imported += 1
            changed_paths.add(
                str(project['path'].parents[3] / "state" / "project-auth" /
                    project['office'] / project['client'])
            )
        if stats['index_json_created']:
            print(f"    index.json created")
            total_index_created += 1
            changed_paths.add(str(project['path']))

    # Summary
    print(f"\n{'='*60}")
    print(f"  Migration Summary  [{mode}]")
    print(f"{'='*60}")
    print(f"  HTM files updated:    {total_htm_updated}")
    print(f"  HTM files skipped:    {total_htm_skipped}")
    print(f"  Passwords imported:   {total_pw_imported}")
    print(f"  index.json created:   {total_index_created}")
    print(f"{'='*60}\n")

    # Generate S3 sync commands
    if changed_paths and not args.dry_run:
        print("To sync changes back to S3, run these commands:\n")
        bucket_name = "sunrise-image-manager"  # from config_s3.json
        for path in sorted(changed_paths):
            rel = Path(path).relative_to(bucket_root)
            print(f"  aws s3 sync \"{path}\" \"s3://{bucket_name}/{rel}/\" \\")
            print(f"    --exclude \"*\" --include \"*.htm\" --include \"*.json\" \\")
            print(f"    --exclude \"*.htm.old\"")
            print()

        # Also sync state directory for password auth files
        state_dir = bucket_root / "state"
        if state_dir.exists():
            print(f"  aws s3 sync \"{state_dir}\" \"s3://{bucket_name}/state/\" \\")
            print(f"    --include \"project-auth/*\"")
            print()

    elif args.dry_run and total_htm_updated > 0:
        print("Run again without --dry-run to apply changes.\n")


if __name__ == "__main__":
    main()
