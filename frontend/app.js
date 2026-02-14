/**
 * Sunrise Image Manager - Web Frontend
 *
 * Handles:
 *  1. Cognito authentication (sign-up, sign-in, session management)
 *  2. Drag-and-drop / file picker for JPG images (any mix of pano + photo)
 *  3. Auto-classifies images as panoramic (aspect ratio >= 1.9) or standard
 *  4. Requests presigned S3 upload URLs from the API
 *  5. Uploads files directly to S3 from the browser
 *  6. Submits a job manifest to trigger Lambda processing
 *  7. Polls for job completion status
 */

// ── Configuration ──────────────────────────────────────────────────────────
const API_BASE = window.SIM_CONFIG?.apiBase || '/api';
const PANO_ASPECT_RATIO = 1.9;  // width/height >= this => panoramic

// ── Cognito setup ──────────────────────────────────────────────────────────
const userPool = (window.AmazonCognitoIdentity && window.SIM_CONFIG?.cognitoUserPoolId)
    ? new AmazonCognitoIdentity.CognitoUserPool({
        UserPoolId: window.SIM_CONFIG.cognitoUserPoolId,
        ClientId: window.SIM_CONFIG.cognitoClientId,
    })
    : null;

let currentSession = null;
let pendingConfirmEmail = null;  // email awaiting verification code

// ── Auth functions ─────────────────────────────────────────────────────────
function checkAuth() {
    if (!userPool) {
        // Cognito not configured — show app without auth (dev/local mode)
        showApp('(no auth)');
        return;
    }
    const user = userPool.getCurrentUser();
    if (user) {
        user.getSession(function(err, session) {
            if (!err && session && session.isValid()) {
                currentSession = session;
                showApp(user.getUsername());
            } else {
                showAuth();
            }
        });
    } else {
        showAuth();
    }
}

function getAuthToken() {
    if (!currentSession) return null;
    return currentSession.getIdToken().getJwtToken();
}

function authHeaders() {
    const headers = { 'Content-Type': 'application/json' };
    const token = getAuthToken();
    if (token) headers['Authorization'] = token;
    return headers;
}

function showApp(email) {
    document.getElementById('authScreen').style.display = 'none';
    document.getElementById('appContent').style.display = 'block';
    document.getElementById('userInfo').style.display = 'flex';
    document.getElementById('userEmail').textContent = email;
    loadClientRegistry();
}

function showAuth() {
    document.getElementById('authScreen').style.display = 'flex';
    document.getElementById('appContent').style.display = 'none';
    document.getElementById('userInfo').style.display = 'none';
}

function showAuthTab(tab) {
    document.getElementById('signinForm').style.display = tab === 'signin' ? 'block' : 'none';
    document.getElementById('signupForm').style.display = tab === 'signup' ? 'block' : 'none';
    document.getElementById('confirmForm').style.display = tab === 'confirm' ? 'block' : 'none';
    document.getElementById('tabSignin').classList.toggle('active', tab === 'signin');
    document.getElementById('tabSignup').classList.toggle('active', tab === 'signup' || tab === 'confirm');
    // Clear errors
    document.getElementById('signinError').textContent = '';
    document.getElementById('signupError').textContent = '';
    document.getElementById('confirmError').textContent = '';
}

function signIn() {
    const email = document.getElementById('signinEmail').value.trim();
    const password = document.getElementById('signinPassword').value;
    const errorEl = document.getElementById('signinError');
    errorEl.textContent = '';

    if (!email || !password) {
        errorEl.textContent = 'Please enter email and password.';
        return;
    }

    document.getElementById('signinBtn').disabled = true;

    const authDetails = new AmazonCognitoIdentity.AuthenticationDetails({
        Username: email,
        Password: password,
    });
    const cognitoUser = new AmazonCognitoIdentity.CognitoUser({
        Username: email,
        Pool: userPool,
    });

    cognitoUser.authenticateUser(authDetails, {
        onSuccess: function(session) {
            currentSession = session;
            document.getElementById('signinBtn').disabled = false;
            showApp(email);
        },
        onFailure: function(err) {
            document.getElementById('signinBtn').disabled = false;
            if (err.code === 'UserNotConfirmedException') {
                pendingConfirmEmail = email;
                showAuthTab('confirm');
                return;
            }
            errorEl.textContent = err.message || 'Sign in failed.';
        },
    });
}

function signUp() {
    const email = document.getElementById('signupEmail').value.trim();
    const password = document.getElementById('signupPassword').value;
    const confirm = document.getElementById('signupConfirm').value;
    const errorEl = document.getElementById('signupError');
    errorEl.textContent = '';

    if (!email || !password) {
        errorEl.textContent = 'Please enter email and password.';
        return;
    }
    if (password !== confirm) {
        errorEl.textContent = 'Passwords do not match.';
        return;
    }
    if (password.length < 8) {
        errorEl.textContent = 'Password must be at least 8 characters.';
        return;
    }

    document.getElementById('signupBtn').disabled = true;

    const attrs = [
        new AmazonCognitoIdentity.CognitoUserAttribute({ Name: 'email', Value: email }),
    ];

    userPool.signUp(email, password, attrs, null, function(err, result) {
        document.getElementById('signupBtn').disabled = false;
        if (err) {
            errorEl.textContent = err.message || 'Sign up failed.';
            return;
        }
        pendingConfirmEmail = email;
        showAuthTab('confirm');
    });
}

function confirmSignUp() {
    const code = document.getElementById('confirmCode').value.trim();
    const errorEl = document.getElementById('confirmError');
    const infoEl = document.getElementById('confirmInfo');
    errorEl.textContent = '';
    infoEl.textContent = '';

    if (!code) {
        errorEl.textContent = 'Please enter the verification code.';
        return;
    }

    document.getElementById('confirmBtn').disabled = true;

    const cognitoUser = new AmazonCognitoIdentity.CognitoUser({
        Username: pendingConfirmEmail,
        Pool: userPool,
    });

    cognitoUser.confirmRegistration(code, true, function(err, result) {
        document.getElementById('confirmBtn').disabled = false;
        if (err) {
            errorEl.textContent = err.message || 'Verification failed.';
            return;
        }
        infoEl.textContent = 'Email verified! You can now sign in.';
        setTimeout(function() { showAuthTab('signin'); }, 1500);
    });
}

function signOut() {
    if (userPool) {
        const user = userPool.getCurrentUser();
        if (user) user.signOut();
    }
    currentSession = null;
    showAuth();
}

// Start auth check on page load
checkAuth();

// ── State ──────────────────────────────────────────────────────────────────
// Each entry: { file: File, type: 'pano'|'photo'|'classifying' }
let imageFiles = [];
// Client/project registry: { "ClientName": ["Project1", "Project2"], ... }
let clientRegistry = {};

// ── DOM refs ───────────────────────────────────────────────────────────────
const dropZone           = document.getElementById('dropZone');
const fileInput          = document.getElementById('fileInput');
const fileListEl         = document.getElementById('fileList');
const classificationEl   = document.getElementById('classificationSummary');
const processBtn         = document.getElementById('processBtn');
const progressSection    = document.getElementById('progressSection');
const progressBar        = document.getElementById('progressBar');
const statusText         = document.getElementById('statusText');
const resultSection      = document.getElementById('resultSection');
const resultMessage      = document.getElementById('resultMessage');
const resultLink         = document.getElementById('resultLink');
const clientInput        = document.getElementById('clientName');
const projectInput       = document.getElementById('projectName');
const clientDatalist     = document.getElementById('clientList');
const projectDatalist    = document.getElementById('projectList');

// ── Client/project registry ─────────────────────────────────────────────
async function loadClientRegistry() {
    try {
        const resp = await fetch(`${API_BASE}/clients`, { headers: authHeaders() });
        if (resp.ok) {
            const data = await resp.json();
            clientRegistry = data.clients || {};
            populateClientList();
        }
    } catch (err) {
        console.warn('Could not load client registry:', err);
    }
}

function populateClientList() {
    clientDatalist.innerHTML = '';
    for (const client of Object.keys(clientRegistry).sort()) {
        const opt = document.createElement('option');
        opt.value = client;
        clientDatalist.appendChild(opt);
    }
}

function populateProjectList(clientName) {
    projectDatalist.innerHTML = '';
    const projects = clientRegistry[clientName] || [];
    for (const proj of projects) {
        const opt = document.createElement('option');
        opt.value = proj;
        projectDatalist.appendChild(opt);
    }
}

// When the client input changes, update the project suggestions
clientInput.addEventListener('input', () => {
    populateProjectList(clientInput.value.trim());
});

// ── Batch options ────────────────────────────────────────────────────────
const qualitySlider = document.getElementById('jpegQuality');
const qualityValue  = document.getElementById('qualityValue');
qualitySlider.addEventListener('input', () => {
    qualityValue.textContent = qualitySlider.value;
});

// ── Auto-classification ──────────────────────────────────────────────────
/**
 * Read image dimensions and return 'pano' or 'photo'.
 * Equirectangular panoramas have a 2:1 aspect ratio; we use >= 1.9 as
 * the threshold to allow for minor cropping while excluding 16:9 (1.78).
 */
function classifyImage(file) {
    return new Promise(resolve => {
        const url = URL.createObjectURL(file);
        const img = new Image();
        img.onload = () => {
            const ratio = img.width / img.height;
            URL.revokeObjectURL(url);
            resolve(ratio >= PANO_ASPECT_RATIO ? 'pano' : 'photo');
        };
        img.onerror = () => {
            URL.revokeObjectURL(url);
            resolve('photo');  // default to photo on error
        };
        img.src = url;
    });
}

async function classifyFiles(files) {
    const entries = files.map(f => ({ file: f, type: 'classifying' }));
    // Classify all in parallel
    const types = await Promise.all(files.map(f => classifyImage(f)));
    types.forEach((type, i) => { entries[i].type = type; });
    return entries;
}

// ── Drop zone wiring ────────────────────────────────────────────────────
['dragenter', 'dragover', 'dragleave', 'drop'].forEach(evt => {
    dropZone.addEventListener(evt, e => { e.preventDefault(); e.stopPropagation(); });
});
dropZone.addEventListener('dragenter', () => dropZone.classList.add('dragover'));
dropZone.addEventListener('dragover',  () => dropZone.classList.add('dragover'));
dropZone.addEventListener('dragleave', () => dropZone.classList.remove('dragover'));

dropZone.addEventListener('drop', async e => {
    dropZone.classList.remove('dragover');
    const dropped = Array.from(e.dataTransfer.files).filter(f =>
        f.name.toLowerCase().endsWith('.jpg') || f.name.toLowerCase().endsWith('.jpeg')
    );
    if (dropped.length) {
        const newEntries = await classifyFiles(dropped);
        imageFiles = imageFiles.concat(newEntries);
        renderFileList();
    }
});

fileInput.addEventListener('change', async () => {
    const picked = Array.from(fileInput.files).filter(f =>
        f.name.toLowerCase().endsWith('.jpg') || f.name.toLowerCase().endsWith('.jpeg')
    );
    if (picked.length) {
        const newEntries = await classifyFiles(picked);
        imageFiles = imageFiles.concat(newEntries);
        renderFileList();
    }
});

// ── File list rendering ─────────────────────────────────────────────────
function renderFileList() {
    fileListEl.innerHTML = '';

    if (imageFiles.length > 0) {
        dropZone.classList.add('has-files');
    } else {
        dropZone.classList.remove('has-files');
    }

    const panoCnt = imageFiles.filter(e => e.type === 'pano').length;
    const photoCnt = imageFiles.filter(e => e.type === 'photo').length;
    if (imageFiles.length > 0) {
        classificationEl.textContent = `${panoCnt} panoramic, ${photoCnt} standard photo${photoCnt !== 1 ? 's' : ''} (${imageFiles.length} total)`;
    } else {
        classificationEl.textContent = '';
    }

    imageFiles.forEach((entry, idx) => {
        const div = document.createElement('div');
        div.className = 'file-item';
        const sizeMB = (entry.file.size / (1024 * 1024)).toFixed(1);
        const badgeClass = entry.type === 'pano' ? 'badge-pano' : 'badge-photo';
        const badgeLabel = entry.type === 'pano' ? 'PANO' : 'PHOTO';
        div.innerHTML = `
            <span>${entry.file.name} (${sizeMB} MB)<span class="file-type-badge ${badgeClass}">${badgeLabel}</span></span>
            <button class="remove-btn" title="Remove">&times;</button>
        `;
        div.querySelector('.remove-btn').addEventListener('click', e => {
            e.stopPropagation();
            imageFiles.splice(idx, 1);
            renderFileList();
        });
        fileListEl.appendChild(div);
    });
}

// ── Progress helpers ────────────────────────────────────────────────────
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

function showResult(message, link, landingPage) {
    resultSection.classList.add('visible');
    resultMessage.textContent = message;
    if (link) {
        resultLink.href = link;
        resultLink.style.display = 'inline-block';
    } else {
        resultLink.style.display = 'none';
    }
    const landingEl = document.getElementById('landingLink');
    if (landingPage) {
        landingEl.href = landingPage;
        landingEl.style.display = 'inline-block';
    } else {
        landingEl.style.display = 'none';
    }
}

// ── Main processing flow ────────────────────────────────────────────────
async function startProcessing() {
    const clientName   = document.getElementById('clientName').value.trim();
    const projectName  = document.getElementById('projectName').value.trim();
    const employeeName = document.getElementById('employeeName').value;

    // Validate
    if (!clientName) { alert('Please enter a client name.'); return; }
    if (!projectName) { alert('Please enter a project name.'); return; }
    if (!employeeName) { alert('Please select an employee.'); return; }
    if (imageFiles.length === 0) {
        alert('Please add at least one image.');
        return;
    }

    // Read batch options
    const keepFilenames = document.getElementById('keepFilenames').checked;
    const jpegQuality = parseInt(document.getElementById('jpegQuality').value, 10);
    const projectPassword = document.getElementById('projectPassword').value;
    let positionCsv = '';
    const csvFile = document.getElementById('csvUpload').files[0];
    if (csvFile) {
        positionCsv = await csvFile.text();
    }

    const panoEntries = imageFiles.filter(e => e.type === 'pano');
    const photoEntries = imageFiles.filter(e => e.type === 'photo');

    processBtn.disabled = true;
    showProgress();
    setProgress(0, 'Requesting upload URLs...', false);

    try {
        // Step 1: Create job and get presigned URLs
        const createResp = await fetch(`${API_BASE}/create-job`, {
            method: 'POST',
            headers: authHeaders(),
            body: JSON.stringify({
                client_name: clientName,
                project_name: projectName,
                employee_name: employeeName,
                pano_files: panoEntries.map(e => e.file.name),
                photo_files: photoEntries.map(e => e.file.name),
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
            ...jobData.pano_uploads.map((u, i) => ({ ...u, file: panoEntries[i].file })),
            ...jobData.photo_uploads.map((u, i) => ({ ...u, file: photoEntries[i].file })),
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

        // Step 3: Submit job manifest (include project password if set)
        const submitBody = {
            job_prefix: jobData.job_prefix,
            client_name: jobData.client_name,
            project_name: jobData.project_name,
            employee_name: jobData.employee_name,
            file_dt: jobData.file_dt,
            pano_keys: jobData.pano_uploads.map(u => u.key),
            photo_keys: jobData.photo_uploads.map(u => u.key),
            keep_filenames: keepFilenames,
            jpeg_quality: jpegQuality,
            position_csv: positionCsv,
        };
        if (projectPassword) {
            submitBody.project_password = projectPassword;
        }

        const submitResp = await fetch(`${API_BASE}/submit-job`, {
            method: 'POST',
            headers: authHeaders(),
            body: JSON.stringify(submitBody),
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
            `All images processed and published. ${panoEntries.length} panoramas and ${photoEntries.length} photos.`,
            result.first_link || null,
            result.landing_page || null
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
                `${API_BASE}/job-status?job_prefix=${encodeURIComponent(jobPrefix)}`,
                { headers: authHeaders() }
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
