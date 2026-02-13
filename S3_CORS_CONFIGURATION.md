# S3 CORS Configuration for Pano Plugin

Your bucket policy is correct for public access. However, you also need to configure CORS (Cross-Origin Resource Sharing) for the JavaScript pano plugin to load images.

## Steps to Configure CORS:

1. Go to AWS S3 Console
2. Select your bucket: `www.seihds.com`
3. Click on the **Permissions** tab
4. Scroll down to **Cross-origin resource sharing (CORS)**
5. Click **Edit**
6. Paste the following configuration:

```json
[
    {
        "AllowedHeaders": [
            "*"
        ],
        "AllowedMethods": [
            "GET",
            "HEAD"
        ],
        "AllowedOrigins": [
            "*"
        ],
        "ExposeHeaders": []
    }
]
```

## Alternative (More Secure):

If you want to restrict CORS to only your domain:

```json
[
    {
        "AllowedHeaders": [
            "*"
        ],
        "AllowedMethods": [
            "GET",
            "HEAD"
        ],
        "AllowedOrigins": [
            "https://www.seihds.com",
            "http://www.seihds.com"
        ],
        "ExposeHeaders": []
    }
]
```

## Why CORS is Needed:

- Your bucket policy allows public read access [OK]
- But browsers block JavaScript from loading resources from different origins without CORS headers
- The pano plugin (pannellum) uses JavaScript to load images, which requires CORS
- CORS configuration tells the browser it's safe to allow these cross-origin requests

After configuring CORS, the pano plugin should be able to load images successfully.
