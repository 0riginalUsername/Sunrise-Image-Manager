#!/usr/bin/env bash
# ──────────────────────────────────────────────────────────────────────────
# Build the "geo" Lambda Layer containing pyproj, shapely, pyshp, and
# ezdxf — the dependencies the Processing Lambda needs for DXF export
# and State Plane coordinate projection.
#
# The layer is built inside a Docker container that matches the Lambda
# runtime so that native extensions (GEOS, PROJ) are compatible.
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
        # Upgrade pip so it can find manylinux wheels with bundled native libs
        pip install --upgrade pip
        pip install \
            pyproj \
            shapely \
            pyshp \
            ezdxf \
            -t /out \
            --no-cache-dir \
            --only-binary :all:
        # Remove unnecessary files to shrink the layer
        echo '>> Cleaning up layer to reduce size...'
        find /out -type d -name '__pycache__' -exec rm -rf {} + 2>/dev/null || true
        find /out -type d -name 'tests' -exec rm -rf {} + 2>/dev/null || true
        find /out -type d -name 'test' -exec rm -rf {} + 2>/dev/null || true
        find /out -name '*.pyc' -delete 2>/dev/null || true
        find /out -name '*.pyi' -delete 2>/dev/null || true
        # Strip debug symbols from native .so files — but SKIP numpy and
        # numpy.libs because strip corrupts numpy 2.x compiled extensions,
        # causing 'should not import from source directory' errors at runtime.
        find /out -name '*.so' -not -path '*/numpy/*' -not -path '*/numpy.libs/*' \
            -exec strip --strip-debug {} + 2>/dev/null || true
        find /out -name '*.so.*' -not -path '*/numpy/*' -not -path '*/numpy.libs/*' \
            -exec strip --strip-debug {} + 2>/dev/null || true
        echo \">> Layer contents: \$(du -sh /out | cut -f1)\"
        # Smoke-test: verify key packages can actually be imported
        echo '>> Verifying layer imports...'
        PYTHONPATH=/out python3 -c '
import numpy; print(f\"   numpy {numpy.__version__} OK\")
import pyproj; print(f\"   pyproj {pyproj.__version__} OK\")
import shapely; print(f\"   shapely {shapely.__version__} OK\")
import ezdxf; print(f\"   ezdxf {ezdxf.__version__} OK\")
import shapefile; print(\"   pyshp OK\")
print(\">> All imports verified.\")
'
    "

# Zip it up
echo ">> Creating ZIP..."
cd "$SCRIPT_DIR/build"

# For the zip step, use Windows-style path on Git Bash so Python can find it
ZIP_FILE_NATIVE="$ZIP_FILE"
if [[ "$OSTYPE" == "msys" || "$OSTYPE" == "mingw"* || "$OSTYPE" == "cygwin" ]]; then
    ZIP_FILE_NATIVE="$(cygpath -w "$ZIP_FILE" 2>/dev/null || echo "$ZIP_FILE" | sed 's|^/\([a-zA-Z]\)/|\1:/|')"
fi

if command -v zip &>/dev/null; then
    zip -r1 "$ZIP_FILE_NATIVE" python/
else
    echo "   (zip not found — using Python zipfile, this may take a minute...)"
    python3 -c "
import zipfile, os, sys
count = 0
with zipfile.ZipFile(sys.argv[1], 'w', zipfile.ZIP_DEFLATED, compresslevel=1) as zf:
    for root, dirs, files in os.walk('python'):
        for f in files:
            fp = os.path.join(root, f)
            zf.write(fp)
            count += 1
            if count % 500 == 0:
                print(f'   {count} files zipped...', flush=True)
print(f'   Done: {count} files zipped.', flush=True)
" "$ZIP_FILE_NATIVE"
fi

if [ ! -f "$ZIP_FILE_NATIVE" ] && [ ! -f "$ZIP_FILE" ]; then
    echo "ERROR: Layer zip was not created. Docker build may have failed."
    exit 1
fi

LAYER_SIZE=$(du -sh "$ZIP_FILE_NATIVE" 2>/dev/null || du -sh "$ZIP_FILE" | cut -f1)
LAYER_SIZE=$(echo "$LAYER_SIZE" | cut -f1)
echo ">> Layer ZIP: $ZIP_FILE_NATIVE ($LAYER_SIZE)"

if [ "$PUBLISH" = true ]; then
    echo ">> Publishing layer to AWS..."
    # Use Windows-style path for fileb:// on Git Bash
    FILEB_PATH="$ZIP_FILE"
    if [[ "$OSTYPE" == "msys" || "$OSTYPE" == "mingw"* || "$OSTYPE" == "cygwin" ]]; then
        FILEB_PATH="$(cygpath -w "$ZIP_FILE" 2>/dev/null || echo "$ZIP_FILE" | sed 's|^/\([a-zA-Z]\)/|\1:/|')"
    fi

    # Direct upload works for zips <50 MB; larger zips go via S3
    ZIP_BYTES=$(wc -c < "$FILEB_PATH" 2>/dev/null || wc -c < "$ZIP_FILE")
    if [ "$ZIP_BYTES" -gt 50000000 ]; then
        echo "   ZIP is ${LAYER_SIZE} (>50 MB) — uploading via S3..."
        S3_KEY="layers/${LAYER_NAME}.zip"
        aws s3 cp "$FILEB_PATH" "s3://${BUCKET:-$LAYER_NAME}/$S3_KEY" --region "$REGION"
        LAYER_ARN=$(aws lambda publish-layer-version \
            --layer-name "$LAYER_NAME" \
            --description "pyproj, shapely, pyshp, ezdxf for Sunrise Image Manager" \
            --compatible-runtimes python3.11 \
            --content "S3Bucket=${BUCKET:-$LAYER_NAME},S3Key=$S3_KEY" \
            --region "$REGION" \
            --query 'LayerVersionArn' \
            --output text)
    else
        LAYER_ARN=$(aws lambda publish-layer-version \
            --layer-name "$LAYER_NAME" \
            --description "pyproj, shapely, pyshp, ezdxf for Sunrise Image Manager" \
            --compatible-runtimes python3.11 \
            --zip-file "fileb://$FILEB_PATH" \
            --region "$REGION" \
            --query 'LayerVersionArn' \
            --output text)
    fi
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
