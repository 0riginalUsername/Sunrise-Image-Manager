/**
 * Sunrise Image Manager - Web Frontend
 *
 * Handles:
 *  1. Drag-and-drop / file picker for pano + photo JPGs
 *  2. Requests presigned S3 upload URLs from the API
 *  3. Uploads files directly to S3 from the browser
 *  4. Submits a job manifest to trigger Lambda processing
 *  5. Polls for job completion status
 */

// ── Configuration ──────────────────────────────────────────────────────────
// Set this to your deployed API Gateway base URL
const API_BASE = window.SIM_CONFIG?.apiBase || '/api';

// ── State ──────────────────────────────────────────────────────────────────
let panoFiles = [];
let photoFiles = [];

// ── DOM refs ───────────────────────────────────────────────────────────────
const panoDropZone   = document.getElementById('panoDropZone');
const photoDropZone  = document.getElementById('photoDropZone');
const panoInput      = document.getElementById('panoInput');
const photoInput     = document.getElementById('photoInput');
const panoFileList   = document.getElementById('panoFileList');
const photoFileList  = document.getElementById('photoFileList');
const processBtn     = document.getElementById('processBtn');
const progressSection = document.getElementById('progressSection');
const progressBar    = document.getElementById('progressBar');
const statusText     = document.getElementById('statusText');
const resultSection  = document.getElementById('resultSection');
const resultMessage  = document.getElementById('resultMessage');
const resultLink     = document.getElementById('resultLink');

// ── Drop zone wiring ──────────────────────────────────────────────────────
function setupDropZone(zone, input, fileListEl, getFiles, setFiles) {
    // Prevent default drag behavior on the whole zone
    ['dragenter', 'dragover', 'dragleave', 'drop'].forEach(evt => {
        zone.addEventListener(evt, e => { e.preventDefault(); e.stopPropagation(); });
    });
    zone.addEventListener('dragenter', () => zone.classList.add('dragover'));
    zone.addEventListener('dragover',  () => zone.classList.add('dragover'));
    zone.addEventListener('dragleave', () => zone.classList.remove('dragover'));
    zone.addEventListener('drop', e => {
        zone.classList.remove('dragover');
        const dropped = Array.from(e.dataTransfer.files).filter(f =>
            f.name.toLowerCase().endsWith('.jpg') || f.name.toLowerCase().endsWith('.jpeg')
        );
        if (dropped.length) {
            setFiles(dropped);
            renderFileList(fileListEl, getFiles(), setFiles);
            zone.classList.add('has-files');
        }
    });

    // File input change
    input.addEventListener('change', () => {
        const picked = Array.from(input.files).filter(f =>
            f.name.toLowerCase().endsWith('.jpg') || f.name.toLowerCase().endsWith('.jpeg')
        );
        if (picked.length) {
            setFiles(picked);
            renderFileList(fileListEl, getFiles(), setFiles);
            zone.classList.add('has-files');
        }
    });
}

function renderFileList(container, files, setFiles) {
    container.innerHTML = '';
    files.forEach((file, idx) => {
        const div = document.createElement('div');
        div.className = 'file-item';
        const sizeMB = (file.size / (1024 * 1024)).toFixed(1);
        div.innerHTML = `
            <span>${file.name} (${sizeMB} MB)</span>
            <button class="remove-btn" title="Remove">&times;</button>
        `;
        div.querySelector('.remove-btn').addEventListener('click', e => {
            e.stopPropagation();
            const newFiles = [...files];
            newFiles.splice(idx, 1);
            setFiles(newFiles);
            renderFileList(container, newFiles, setFiles);
            if (newFiles.length === 0) {
                container.closest('.drop-zone').classList.remove('has-files');
            }
        });
        container.appendChild(div);
    });
}

setupDropZone(
    panoDropZone, panoInput, panoFileList,
    () => panoFiles,
    files => { panoFiles = files; }
);
setupDropZone(
    photoDropZone, photoInput, photoFileList,
    () => photoFiles,
    files => { photoFiles = files; }
);

// ── Progress helpers ──────────────────────────────────────────────────────
function showProgress() {
    progressSection.classList.add('visible');
    resultSection.classList.remove('visible');
}

function setProgress(percent, text, isError) {
    progressBar.style.width = percent + '%';
    progressBar.textContent = Math.round(percent) + '%';
    statusText.textContent = text;
    statusText.className = 'status-text' + (isError ? ' error' : '');
}

function showResult(message, link) {
    resultSection.classList.add('visible');
    resultMessage.textContent = message;
    if (link) {
        resultLink.href = link;
        resultLink.style.display = 'inline-block';
    } else {
        resultLink.style.display = 'none';
    }
}

// ── Main processing flow ──────────────────────────────────────────────────
async function startProcessing() {
    const clientName   = document.getElementById('clientName').value.trim();
    const projectName  = document.getElementById('projectName').value.trim();
    const employeeName = document.getElementById('employeeName').value;

    // Validate
    if (!clientName) { alert('Please enter a client name.'); return; }
    if (!projectName) { alert('Please enter a project name.'); return; }
    if (!employeeName) { alert('Please select an employee.'); return; }
    if (panoFiles.length === 0 && photoFiles.length === 0) {
        alert('Please add at least one panoramic or standard photo.');
        return;
    }

    processBtn.disabled = true;
    showProgress();
    setProgress(0, 'Requesting upload URLs...', false);

    try {
        // Step 1: Create job and get presigned URLs
        const createResp = await fetch(`${API_BASE}/create-job`, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({
                client_name: clientName,
                project_name: projectName,
                employee_name: employeeName,
                pano_files: panoFiles.map(f => f.name),
                photo_files: photoFiles.map(f => f.name),
            }),
        });

        if (!createResp.ok) {
            const err = await createResp.json();
            throw new Error(err.error || 'Failed to create job');
        }

        const jobData = await createResp.json();
        setProgress(5, 'Uploading images to server...', false);

        // Step 2: Upload all files directly to S3 via presigned URLs
        const allUploads = [
            ...jobData.pano_uploads.map((u, i) => ({ ...u, file: panoFiles[i] })),
            ...jobData.photo_uploads.map((u, i) => ({ ...u, file: photoFiles[i] })),
        ];

        const totalFiles = allUploads.length;
        let uploaded = 0;

        // Upload with concurrency limit
        const CONCURRENCY = 4;
        const queue = [...allUploads];
        const workers = [];

        for (let i = 0; i < Math.min(CONCURRENCY, queue.length); i++) {
            workers.push(uploadWorker());
        }

        async function uploadWorker() {
            while (queue.length > 0) {
                const item = queue.shift();
                await uploadFileToS3(item.upload_url, item.file);
                uploaded++;
                const pct = 5 + (uploaded / totalFiles) * 70;  // 5% to 75%
                setProgress(pct, `Uploaded ${uploaded} of ${totalFiles} files...`, false);
            }
        }

        await Promise.all(workers);

        setProgress(78, 'Submitting job for processing...', false);

        // Step 3: Submit job manifest
        const submitResp = await fetch(`${API_BASE}/submit-job`, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({
                job_prefix: jobData.job_prefix,
                client_name: jobData.client_name,
                project_name: jobData.project_name,
                employee_name: jobData.employee_name,
                file_dt: jobData.file_dt,
                pano_keys: jobData.pano_uploads.map(u => u.key),
                photo_keys: jobData.photo_uploads.map(u => u.key),
            }),
        });

        if (!submitResp.ok) {
            const err = await submitResp.json();
            throw new Error(err.error || 'Failed to submit job');
        }

        const submitData = await submitResp.json();
        setProgress(80, 'Server is processing images...', false);

        // Step 4: Poll for completion
        const result = await pollJobStatus(jobData.job_prefix);

        setProgress(100, 'Processing complete!', false);
        statusText.className = 'status-text success';

        showResult(
            `All images processed and published. ${panoFiles.length} panoramas and ${photoFiles.length} photos.`,
            result.first_link || null
        );

    } catch (err) {
        setProgress(0, `Error: ${err.message}`, true);
        console.error('Processing error:', err);
    } finally {
        processBtn.disabled = false;
    }
}


/**
 * Upload a single file to S3 using a presigned PUT URL.
 */
async function uploadFileToS3(presignedUrl, file) {
    const maxRetries = 3;
    for (let attempt = 1; attempt <= maxRetries; attempt++) {
        try {
            const resp = await fetch(presignedUrl, {
                method: 'PUT',
                headers: { 'Content-Type': 'image/jpeg' },
                body: file,
            });
            if (!resp.ok) {
                throw new Error(`S3 upload failed: HTTP ${resp.status}`);
            }
            return;
        } catch (err) {
            if (attempt === maxRetries) throw err;
            // Exponential backoff
            await new Promise(r => setTimeout(r, Math.pow(2, attempt) * 1000));
        }
    }
}


/**
 * Poll the job status endpoint until processing is complete or fails.
 */
async function pollJobStatus(jobPrefix) {
    const POLL_INTERVAL = 3000;  // 3 seconds
    const MAX_POLLS = 200;       // ~10 minutes max wait

    for (let i = 0; i < MAX_POLLS; i++) {
        await new Promise(r => setTimeout(r, POLL_INTERVAL));

        try {
            const resp = await fetch(
                `${API_BASE}/job-status?job_prefix=${encodeURIComponent(jobPrefix)}`
            );
            if (!resp.ok) continue;

            const data = await resp.json();

            if (data.status === 'complete') {
                return data;
            } else if (data.status === 'error') {
                throw new Error(data.message || 'Server processing failed');
            } else if (data.status === 'processing') {
                setProgress(80 + (i / MAX_POLLS) * 18, `Server processing: ${data.message || 'working...'}`, false);
            }
        } catch (err) {
            if (err.message.includes('Server processing failed')) throw err;
            // Network hiccup, keep polling
        }
    }

    throw new Error('Processing timed out. Please check the server.');
}
