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
docker run --rm \
    -v "$SCRIPT_DIR/build/python:/out" \
    -v "$SCRIPT_DIR:/layer" \
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
zip -r9 "$ZIP_FILE" python/

LAYER_SIZE=$(du -sh "$ZIP_FILE" | cut -f1)
echo ">> Layer ZIP: $ZIP_FILE ($LAYER_SIZE)"

if [ "$PUBLISH" = true ]; then
    echo ">> Publishing layer to AWS..."
    LAYER_ARN=$(aws lambda publish-layer-version \
        --layer-name "$LAYER_NAME" \
        --description "pyproj, geopandas, shapely, fiona, ezdxf for Sunrise Image Manager" \
        --compatible-runtimes python3.11 \
        --zip-file "fileb://$ZIP_FILE" \
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
