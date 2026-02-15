#!/usr/bin/env bash
# ──────────────────────────────────────────────────────────────────────────
# Build the "geo" Lambda Layer containing pyproj, geopandas, shapely,
# fiona, and ezdxf — all the dependencies the Processing Lambda needs
# for DXF export and State Plane coordinate projection.
#
# The layer is built inside a Docker container that matches the Lambda
# runtime so that native extensions (GEOS, PROJ, GDAL) are compatible.
#
# Usage:
#   ./build_layer.sh                    # builds layers/geo/geo-layer.zip
#   ./build_layer.sh --publish          # also publishes to AWS Lambda
# ──────────────────────────────────────────────────────────────────────────
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LAYER_NAME="sunrise-geo-layer"
REGION="${AWS_DEFAULT_REGION:-us-east-1}"
ZIP_FILE="$SCRIPT_DIR/geo-layer.zip"
PUBLISH=false

# Git Bash / MSYS on Windows: convert /c/Users/... to C:/Users/... for Docker & AWS CLI
DOCKER_SCRIPT_DIR="$SCRIPT_DIR"
if [[ "$OSTYPE" == "msys" || "$OSTYPE" == "mingw"* || "$OSTYPE" == "cygwin" ]]; then
    DOCKER_SCRIPT_DIR="$(cygpath -w "$SCRIPT_DIR" 2>/dev/null || echo "$SCRIPT_DIR" | sed 's|^/\([a-zA-Z]\)/|\1:/|')"
fi

while [[ $# -gt 0 ]]; do
    case $1 in
        --publish) PUBLISH=true; shift ;;
        --region)  REGION="$2"; shift 2 ;;
        *) echo "Unknown arg: $1"; exit 1 ;;
    esac
done

echo "=== Building geo Lambda Layer ==="

# Clean previous build
rm -rf "$SCRIPT_DIR/build" "$ZIP_FILE"
mkdir -p "$SCRIPT_DIR/build/python"

# Build inside a Lambda-compatible container
export MSYS_NO_PATHCONV=1  # Prevent Git Bash from mangling paths in -v args
docker run --rm \
    -v "$DOCKER_SCRIPT_DIR/build/python:/out" \
    -v "$DOCKER_SCRIPT_DIR:/layer" \
    public.ecr.aws/sam/build-python3.11:latest \
    bash -c "
        pip install \
            pyproj \
            geopandas \
            shapely \
            fiona \
            ezdxf \
            -t /out \
            --no-cache-dir
        # Remove unnecessary files to shrink the layer
        find /out -type d -name '__pycache__' -exec rm -rf {} + 2>/dev/null || true
        find /out -type d -name 'tests' -exec rm -rf {} + 2>/dev/null || true
        find /out -type d -name 'test' -exec rm -rf {} + 2>/dev/null || true
        find /out -name '*.pyc' -delete 2>/dev/null || true
        find /out -name '*.pyi' -delete 2>/dev/null || true
    "

# Zip it up
echo ">> Creating ZIP..."
cd "$SCRIPT_DIR/build"
if command -v zip &>/dev/null; then
    zip -r9 "$ZIP_FILE" python/
else
    echo "   (zip not found — using Python zipfile)"
    python3 -c "
import zipfile, os, sys
with zipfile.ZipFile(sys.argv[1], 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
    for root, dirs, files in os.walk('python'):
        for f in files:
            fp = os.path.join(root, f)
            zf.write(fp)
" "$ZIP_FILE"
fi

if [ ! -f "$ZIP_FILE" ]; then
    echo "ERROR: $ZIP_FILE was not created. Docker build may have failed."
    exit 1
fi

LAYER_SIZE=$(du -sh "$ZIP_FILE" | cut -f1)
echo ">> Layer ZIP: $ZIP_FILE ($LAYER_SIZE)"

if [ "$PUBLISH" = true ]; then
    echo ">> Publishing layer to AWS..."
    # Use Windows-style path for fileb:// on Git Bash
    FILEB_PATH="$ZIP_FILE"
    if [[ "$OSTYPE" == "msys" || "$OSTYPE" == "mingw"* || "$OSTYPE" == "cygwin" ]]; then
        FILEB_PATH="$(cygpath -w "$ZIP_FILE" 2>/dev/null || echo "$ZIP_FILE" | sed 's|^/\([a-zA-Z]\)/|\1:/|')"
    fi
    LAYER_ARN=$(aws lambda publish-layer-version \
        --layer-name "$LAYER_NAME" \
        --description "pyproj, geopandas, shapely, fiona, ezdxf for Sunrise Image Manager" \
        --compatible-runtimes python3.11 \
        --zip-file "fileb://$FILEB_PATH" \
        --region "$REGION" \
        --query 'LayerVersionArn' \
        --output text)
    echo ""
    echo "=== Layer Published ==="
    echo "Layer ARN: $LAYER_ARN"
    echo ""
    echo "Add this to your template.yaml ProcessingFunction:"
    echo "  Layers:"
    echo "    - $LAYER_ARN"
else
    echo ""
    echo "Layer built but NOT published. Run with --publish to push to AWS."
    echo "  ./build_layer.sh --publish"
fi
