#!/usr/bin/env bash
# ──────────────────────────────────────────────────────────────────────────
# Sunrise Image Manager - Deployment Script
#
# Deploys the full stack:
#   1. SAM build + deploy (Lambda functions + API Gateway + S3 bucket)
#   2. Upload HTML templates, master.dxf, and shapefile to S3 (templates/ prefix)
#   3. Upload frontend static files to S3 (frontend/ prefix)
#
# Prerequisites:
#   - AWS CLI configured with appropriate credentials
#   - AWS SAM CLI installed (pip install aws-sam-cli)
#   - S3 bucket name set in template.yaml or passed as parameter
#   - (Optional) Geo Lambda Layer built and published for DXF export
#     see: layers/geo/build_layer.sh --publish
#
# Usage:
#   ./deploy.sh                              # Deploy (auto-detects geo layer)
#   ./deploy.sh --bucket my-bucket-name      # Deploy with custom bucket
#   ./deploy.sh --geo-layer-arn arn:aws:...   # Deploy with explicit geo layer ARN
#   ./deploy.sh --no-geo                     # Deploy without DXF export
#   ./deploy.sh --cf-alias pano.seihds.com --acm-cert arn:aws:acm:...  # Custom domain
# ──────────────────────────────────────────────────────────────────────────
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
STACK_NAME="sunrise-image-manager"
S3_BUCKET="sunrise-image-manager"
REGION="${AWS_DEFAULT_REGION:-us-east-1}"
GEO_LAYER_ARN=""
CF_ALIAS=""
ACM_CERT=""
NO_GEO=false

# Parse args
while [[ $# -gt 0 ]]; do
    case $1 in
        --bucket)        S3_BUCKET="$2"; shift 2 ;;
        --stack)         STACK_NAME="$2"; shift 2 ;;
        --region)        REGION="$2"; shift 2 ;;
        --geo-layer-arn) GEO_LAYER_ARN="$2"; shift 2 ;;
        --no-geo)        NO_GEO=true; shift ;;
        --cf-alias)      CF_ALIAS="$2"; shift 2 ;;
        --acm-cert)      ACM_CERT="$2"; shift 2 ;;
        *) echo "Unknown arg: $1"; exit 1 ;;
    esac
done

# Auto-detect the latest published geo layer if not specified
if [ -z "$GEO_LAYER_ARN" ] && [ "$NO_GEO" = false ]; then
    echo ">> No --geo-layer-arn provided, checking for published layer..."
    DETECTED_ARN=$(aws lambda list-layer-versions \
        --layer-name "sunrise-geo-layer" \
        --region "$REGION" \
        --query 'LayerVersions[0].LayerVersionArn' \
        --output text 2>/dev/null || true)
    if [ -n "$DETECTED_ARN" ] && [ "$DETECTED_ARN" != "None" ]; then
        GEO_LAYER_ARN="$DETECTED_ARN"
        echo "   Found: $GEO_LAYER_ARN"
    else
        echo "   No published geo layer found. DXF export will be disabled."
        echo "   To enable, run: layers/geo/build_layer.sh --publish"
    fi
fi

echo ""
echo "=== Sunrise Image Manager Deployment ==="
echo "Stack:      $STACK_NAME"
echo "Bucket:     $S3_BUCKET"
echo "Region:     $REGION"
echo "Geo Layer:  ${GEO_LAYER_ARN:-<none — DXF export disabled>}"
echo "CF Alias:   ${CF_ALIAS:-<none — using *.cloudfront.net>}"
echo ""

# Step 1: SAM build
echo ">> Building Lambda functions..."
cd "$SCRIPT_DIR/lambda_function"
sam build --template template.yaml

# Step 2: SAM deploy
echo ">> Deploying CloudFormation stack..."
PARAM_OVERRIDES="S3BucketName=$S3_BUCKET DomainPrefix=/processed"
if [ -n "$GEO_LAYER_ARN" ]; then
    PARAM_OVERRIDES="$PARAM_OVERRIDES GeoLayerArn=$GEO_LAYER_ARN"
fi
if [ -n "$CF_ALIAS" ]; then
    PARAM_OVERRIDES="$PARAM_OVERRIDES CloudFrontAlias=$CF_ALIAS AcmCertificateArn=$ACM_CERT"
fi

set +e
SAM_OUTPUT=$(sam deploy \
    --stack-name "$STACK_NAME" \
    --region "$REGION" \
    --resolve-s3 \
    --capabilities CAPABILITY_IAM \
    --parameter-overrides $PARAM_OVERRIDES \
    --no-confirm-changeset 2>&1)
SAM_EXIT=$?
set -e

echo "$SAM_OUTPUT"

if [ $SAM_EXIT -ne 0 ]; then
    if echo "$SAM_OUTPUT" | grep -q "No changes to deploy"; then
        echo ">> No infrastructure changes — continuing with frontend upload..."
    else
        echo ">> SAM deploy failed!"
        exit 1
    fi
fi

# Get outputs
API_URL=$(aws cloudformation describe-stacks \
    --stack-name "$STACK_NAME" \
    --region "$REGION" \
    --query "Stacks[0].Outputs[?OutputKey=='ApiURL'].OutputValue" \
    --output text)

WEBSITE_URL=$(aws cloudformation describe-stacks \
    --stack-name "$STACK_NAME" \
    --region "$REGION" \
    --query "Stacks[0].Outputs[?OutputKey=='WebsiteURL'].OutputValue" \
    --output text)

COGNITO_USER_POOL_ID=$(aws cloudformation describe-stacks \
    --stack-name "$STACK_NAME" \
    --region "$REGION" \
    --query "Stacks[0].Outputs[?OutputKey=='CognitoUserPoolId'].OutputValue" \
    --output text)

COGNITO_CLIENT_ID=$(aws cloudformation describe-stacks \
    --stack-name "$STACK_NAME" \
    --region "$REGION" \
    --query "Stacks[0].Outputs[?OutputKey=='CognitoClientId'].OutputValue" \
    --output text)

CF_DISTRIBUTION_ID=$(aws cloudformation describe-stacks \
    --stack-name "$STACK_NAME" \
    --region "$REGION" \
    --query "Stacks[0].Outputs[?OutputKey=='CloudFrontDistributionId'].OutputValue" \
    --output text)

echo ""
echo ">> API URL:             $API_URL"
echo ">> Website URL:         $WEBSITE_URL"
echo ">> CloudFront Dist:     $CF_DISTRIBUTION_ID"
echo ">> Cognito User Pool:   $COGNITO_USER_POOL_ID"
echo ">> Cognito Client ID:   $COGNITO_CLIENT_ID"

# Step 3: Upload HTML templates to S3
echo ""
echo ">> Uploading HTML templates to S3..."
cd "$SCRIPT_DIR"
aws s3 cp Pano-Template.htm "s3://$S3_BUCKET/templates/Pano-Template.htm" --content-type "text/html"
aws s3 cp img-Template.htm "s3://$S3_BUCKET/templates/img-Template.htm" --content-type "text/html"
aws s3 cp Email-Report-Template.htm "s3://$S3_BUCKET/templates/Email-Report-Template.htm" --content-type "text/html"

# Step 3b: Upload DXF block file and shapefile for geo/DXF export
echo ">> Uploading master.dxf and shapefile to S3..."
aws s3 cp master.dxf "s3://$S3_BUCKET/templates/master.dxf"
for ext in shp shx dbf prj cpg; do
    if [ -f "NAD83SPCEPSG.$ext" ]; then
        aws s3 cp "NAD83SPCEPSG.$ext" "s3://$S3_BUCKET/templates/NAD83SPCEPSG.$ext"
    fi
done

# Step 4: Upload frontend with API URL injected
echo ""
echo ">> Uploading frontend to S3..."
# Create a config.js that points to the deployed API and Cognito
cat > "$SCRIPT_DIR/frontend/config.js" << EOF
// Auto-generated by deploy.sh — points frontend to the deployed API and Cognito
window.SIM_CONFIG = {
    apiBase: '${API_URL}/api',
    cognitoUserPoolId: '${COGNITO_USER_POOL_ID}',
    cognitoClientId: '${COGNITO_CLIENT_ID}'
};
EOF

aws s3 sync "$SCRIPT_DIR/frontend/" "s3://$S3_BUCKET/frontend/" \
    --content-type "text/html" \
    --exclude "*" --include "*.html"

aws s3 sync "$SCRIPT_DIR/frontend/" "s3://$S3_BUCKET/frontend/" \
    --content-type "application/javascript" \
    --exclude "*" --include "*.js"

aws s3 sync "$SCRIPT_DIR/frontend/" "s3://$S3_BUCKET/frontend/" \
    --content-type "image/x-icon" \
    --exclude "*" --include "*.ico"

# Upload the logo
if [ -f "$SCRIPT_DIR/logo.jpg" ]; then
    aws s3 cp "$SCRIPT_DIR/logo.jpg" "s3://$S3_BUCKET/frontend/logo.jpg" --content-type "image/jpeg"
fi

# Step 5: Invalidate CloudFront cache so new frontend files are served immediately
echo ""
echo ">> Invalidating CloudFront cache..."
aws cloudfront create-invalidation \
    --distribution-id "$CF_DISTRIBUTION_ID" \
    --paths "/frontend/*" \
    --query "Invalidation.Id" \
    --output text

echo ""
echo "=== Deployment Complete ==="
echo ""
echo "Frontend URL: ${WEBSITE_URL}/frontend/index.html"
echo "API URL:      $API_URL"
echo ""
echo "Users can now navigate to the frontend URL to upload and process images."
