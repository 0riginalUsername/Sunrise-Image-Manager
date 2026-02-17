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

// ── Utilities ─────────────────────────────────────────────────────────────
function escapeHtml(str) {
    const d = document.createElement('div');
    d.textContent = str;
    return d.innerHTML;
}

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
// Client/project registry: { "OfficeName": { "ClientName": ["Project1", "Project2"] }, ... }
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
const officeInput        = document.getElementById('officeName');
const clientInput        = document.getElementById('clientName');
const projectInput       = document.getElementById('projectName');
const officeDatalist     = document.getElementById('officeList');
const clientDatalist     = document.getElementById('clientList');
const projectDatalist    = document.getElementById('projectList');

// ── Client/project registry ─────────────────────────────────────────────
async function loadClientRegistry() {
    try {
        const resp = await fetch(`${API_BASE}/clients`, { headers: authHeaders() });
        if (resp.ok) {
            const data = await resp.json();
            clientRegistry = data.clients || {};
            populateOfficeList();
        }
    } catch (err) {
        console.warn('Could not load client registry:', err);
    }
}

function populateOfficeList() {
    officeDatalist.innerHTML = '';
    for (const office of Object.keys(clientRegistry).sort()) {
        const opt = document.createElement('option');
        opt.value = office;
        officeDatalist.appendChild(opt);
    }
}

function populateClientList(officeName) {
    clientDatalist.innerHTML = '';
    const clients = clientRegistry[officeName] || {};
    for (const client of Object.keys(clients).sort()) {
        const opt = document.createElement('option');
        opt.value = client;
        clientDatalist.appendChild(opt);
    }
}

function populateProjectList(officeName, clientName) {
    projectDatalist.innerHTML = '';
    const clients = clientRegistry[officeName] || {};
    const projects = clients[clientName] || [];
    for (const proj of projects) {
        const opt = document.createElement('option');
        opt.value = proj;
        projectDatalist.appendChild(opt);
    }
}

// When the office input changes, update client suggestions
officeInput.addEventListener('input', () => {
    populateClientList(officeInput.value.trim());
    projectDatalist.innerHTML = '';
    checkProjectPasswordStatus();
});

// When the client input changes, update the project suggestions and check password
clientInput.addEventListener('input', () => {
    populateProjectList(officeInput.value.trim(), clientInput.value.trim());
    checkProjectPasswordStatus();
});

// When the project input changes, check password status
projectInput.addEventListener('input', () => {
    checkProjectPasswordStatus();
});

// ── Project password management ─────────────────────────────────────────
let pwCheckTimeout = null;

function checkProjectPasswordStatus() {
    const office = officeInput.value.trim();
    const client = clientInput.value.trim();
    const project = projectInput.value.trim();
    const panel = document.getElementById('pwManagePanel');

    // Only show for existing office+client+project combos
    const officeClients = clientRegistry[office] || {};
    if (!office || !client || !project || !officeClients[client] || !officeClients[client].includes(project)) {
        panel.classList.remove('visible');
        return;
    }

    panel.classList.add('visible');
    document.getElementById('pwBadge').textContent = 'checking...';
    document.getElementById('pwBadge').className = 'pw-badge';
    document.getElementById('pwMsg').textContent = '';

    // Debounce the API call
    clearTimeout(pwCheckTimeout);
    pwCheckTimeout = setTimeout(async () => {
        try {
            const resp = await fetch(`${API_BASE}/project-password`, {
                method: 'POST',
                headers: authHeaders(),
                body: JSON.stringify({ office, client, project, action: 'check' }),
            });
            if (!resp.ok) return;
            const data = await resp.json();
            updatePwBadge(data.protected);
        } catch (err) {
            console.warn('Could not check project password status:', err);
        }
    }, 300);
}

function updatePwBadge(isProtected) {
    const badge = document.getElementById('pwBadge');
    const removeBtn = document.getElementById('pwRemoveBtn');
    const setBtn = document.getElementById('pwSetBtn');
    if (isProtected) {
        badge.textContent = 'ENABLED';
        badge.className = 'pw-badge pw-badge-on';
        removeBtn.style.display = 'inline-block';
        setBtn.textContent = 'Change Password';
    } else {
        badge.textContent = 'NONE';
        badge.className = 'pw-badge pw-badge-off';
        removeBtn.style.display = 'none';
        setBtn.textContent = 'Set Password';
    }
}

async function setProjectPassword() {
    const office = officeInput.value.trim();
    const client = clientInput.value.trim();
    const project = projectInput.value.trim();
    const password = document.getElementById('pwManageInput').value;
    const msgEl = document.getElementById('pwMsg');
    msgEl.textContent = '';

    if (!password) {
        msgEl.textContent = 'Enter a password first.';
        msgEl.className = 'pw-msg pw-msg-err';
        return;
    }

    document.getElementById('pwSetBtn').disabled = true;
    try {
        const resp = await fetch(`${API_BASE}/project-password`, {
            method: 'POST',
            headers: authHeaders(),
            body: JSON.stringify({ office, client, project, password }),
        });
        const data = await resp.json();
        if (resp.ok) {
            msgEl.textContent = data.message || 'Password set.';
            msgEl.className = 'pw-msg pw-msg-ok';
            document.getElementById('pwManageInput').value = '';
            updatePwBadge(true);
        } else {
            msgEl.textContent = data.error || 'Failed to set password.';
            msgEl.className = 'pw-msg pw-msg-err';
        }
    } catch (err) {
        msgEl.textContent = 'Request failed.';
        msgEl.className = 'pw-msg pw-msg-err';
    } finally {
        document.getElementById('pwSetBtn').disabled = false;
    }
}

async function removeProjectPassword() {
    const office = officeInput.value.trim();
    const client = clientInput.value.trim();
    const project = projectInput.value.trim();
    const msgEl = document.getElementById('pwMsg');
    msgEl.textContent = '';

    if (!confirm('Remove password protection from this project?')) return;

    document.getElementById('pwRemoveBtn').disabled = true;
    try {
        const resp = await fetch(`${API_BASE}/project-password`, {
            method: 'POST',
            headers: authHeaders(),
            body: JSON.stringify({ office, client, project, action: 'remove' }),
        });
        const data = await resp.json();
        if (resp.ok) {
            msgEl.textContent = data.message || 'Password removed.';
            msgEl.className = 'pw-msg pw-msg-ok';
            updatePwBadge(false);
        } else {
            msgEl.textContent = data.error || 'Failed to remove password.';
            msgEl.className = 'pw-msg pw-msg-err';
        }
    } catch (err) {
        msgEl.textContent = 'Request failed.';
        msgEl.className = 'pw-msg pw-msg-err';
    } finally {
        document.getElementById('pwRemoveBtn').disabled = false;
    }
}

// ── Batch options ────────────────────────────────────────────────────────
const qualitySlider = document.getElementById('jpegQuality');
const qualityValue  = document.getElementById('qualityValue');
const keepOriginalsCheckbox = document.getElementById('keepOriginals');
const qualityGroup  = document.getElementById('qualityGroup');

qualitySlider.addEventListener('input', () => {
    qualityValue.textContent = qualitySlider.value;
});

keepOriginalsCheckbox.addEventListener('change', () => {
    const disabled = keepOriginalsCheckbox.checked;
    qualitySlider.disabled = disabled;
    qualityGroup.style.opacity = disabled ? '0.4' : '1';
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

/**
 * Classify files in batches so the main thread can repaint between chunks.
 * @param {File[]} files
 * @param {(done:number, total:number)=>void} [onProgress]
 * @returns {Promise<{file:File, type:string}[]>}
 */
async function classifyFiles(files, onProgress) {
    const BATCH = 50;
    const entries = [];
    for (let i = 0; i < files.length; i += BATCH) {
        const batch = files.slice(i, i + BATCH);
        const types = await Promise.all(batch.map(f => classifyImage(f)));
        for (let j = 0; j < batch.length; j++) {
            entries.push({ file: batch[j], type: types[j] });
        }
        if (onProgress) onProgress(entries.length, files.length);
        // Yield to the browser so it can repaint the overlay text
        await new Promise(r => requestAnimationFrame(r));
    }
    return entries;
}

// ── Scanning overlay helpers ─────────────────────────────────────────────
function showScanOverlay(done, total) {
    let overlay = dropZone.querySelector('.drop-zone-overlay');
    if (!overlay) {
        overlay = document.createElement('div');
        overlay.className = 'drop-zone-overlay';
        overlay.innerHTML = '<div class="scan-spinner"></div><div class="scan-text"></div>';
        dropZone.appendChild(overlay);
    }
    overlay.querySelector('.scan-text').textContent =
        `Registering images\u2026 ${done} / ${total}`;
}

function hideScanOverlay() {
    const overlay = dropZone.querySelector('.drop-zone-overlay');
    if (overlay) overlay.remove();
}

/**
 * Shared handler: filter JPEGs, show scanning overlay, classify in batches,
 * then update the file list.
 */
async function handleIncomingFiles(fileList) {
    const jpgs = Array.from(fileList).filter(f =>
        f.name.toLowerCase().endsWith('.jpg') || f.name.toLowerCase().endsWith('.jpeg')
    );
    if (!jpgs.length) return;

    showScanOverlay(0, jpgs.length);
    try {
        const newEntries = await classifyFiles(jpgs, (done, total) => {
            showScanOverlay(done, total);
        });
        imageFiles = imageFiles.concat(newEntries);
        renderFileList();
    } finally {
        hideScanOverlay();
    }
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
    await handleIncomingFiles(e.dataTransfer.files);
});

fileInput.addEventListener('change', async () => {
    await handleIncomingFiles(fileInput.files);
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
    const officeName   = document.getElementById('officeName').value.trim();
    const clientName   = document.getElementById('clientName').value.trim();
    const projectName  = document.getElementById('projectName').value.trim();
    // Use authenticated user's email as employee name
    let employeeName = '';
    try {
        if (currentSession) {
            employeeName = currentSession.getIdToken().payload.email || '';
        }
    } catch (e) { /* ignore */ }
    if (!employeeName) {
        const el = document.getElementById('userEmail');
        employeeName = el ? el.textContent : '';
    }

    // Validate
    if (!officeName) { alert('Please enter an office name.'); return; }
    if (!clientName) { alert('Please enter a client name.'); return; }
    if (!projectName) { alert('Please enter a project name.'); return; }
    if (imageFiles.length === 0) {
        alert('Please add at least one image.');
        return;
    }

    // Read batch options
    const keepFilenames = document.getElementById('keepFilenames').checked;
    const keepOriginals = document.getElementById('keepOriginals').checked;
    const jpegQuality = parseInt(document.getElementById('jpegQuality').value, 10);
    const projectPassword = document.getElementById('projectPassword').value;
    let positionCsv = '';
    const csvFile = document.getElementById('csvUpload').files[0];
    if (csvFile) {
        positionCsv = await csvFile.text();
    }

    const panoEntries = imageFiles.filter(e => e.type === 'pano');
    const photoEntries = imageFiles.filter(e => e.type === 'photo');
    const planFile = document.getElementById('planUpload').files[0] || null;

    processBtn.disabled = true;
    showProgress();
    setProgress(0, 'Requesting upload URLs...', false);

    try {
        // Step 1: Create job and get presigned URLs
        const createBody = {
            office_name: officeName,
            client_name: clientName,
            project_name: projectName,
            employee_name: employeeName,
            pano_files: panoEntries.map(e => e.file.name),
            photo_files: photoEntries.map(e => e.file.name),
        };
        if (planFile) {
            createBody.plan_file = planFile.name;
        }
        const createResp = await fetch(`${API_BASE}/create-job`, {
            method: 'POST',
            headers: authHeaders(),
            body: JSON.stringify(createBody),
        });

        if (!createResp.ok) {
            const err = await createResp.json();
            throw new Error(err.error || 'Failed to create job');
        }

        const jobData = await createResp.json();
        setProgress(5, 'Uploading images to server...', false);

        // Step 2: Upload all files directly to S3 via presigned URLs
        // Match uploads back to local files by filename (not index) in case
        // the API sanitised or reordered them.
        const panoByName = Object.fromEntries(panoEntries.map(e => [e.file.name, e.file]));
        const photoByName = Object.fromEntries(photoEntries.map(e => [e.file.name, e.file]));
        const allUploads = [
            ...jobData.pano_uploads.map(u => ({ ...u, file: panoByName[u.filename] })),
            ...jobData.photo_uploads.map(u => ({ ...u, file: photoByName[u.filename] })),
        ];
        // Include plan background file if present
        if (jobData.plan_upload && planFile) {
            allUploads.push({ ...jobData.plan_upload, file: planFile });
        }

        const totalFiles = allUploads.length;
        let uploaded = 0;

        // Upload with concurrency limit
        const CONCURRENCY = 8;
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
        // Get submitter email from Cognito session
        let submitterEmail = '';
        try {
            if (currentSession) {
                submitterEmail = currentSession.getIdToken().payload.email || '';
            }
        } catch (e) { /* ignore */ }

        const submitBody = {
            job_prefix: jobData.job_prefix,
            office_name: jobData.office_name,
            client_name: jobData.client_name,
            project_name: jobData.project_name,
            employee_name: jobData.employee_name,
            file_dt: jobData.file_dt,
            pano_keys: jobData.pano_uploads.map(u => u.key),
            photo_keys: jobData.photo_uploads.map(u => u.key),
            keep_filenames: keepFilenames,
            keep_originals: keepOriginals,
            jpeg_quality: jpegQuality,
            position_csv: positionCsv,
            submitter_email: submitterEmail,
        };
        if (jobData.plan_upload) {
            submitBody.plan_key = jobData.plan_upload.key;
        }
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

        // Invalidate browse cache so new project shows up
        browseLoaded = false;

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
    const MAX_POLLS = 360;       // ~18 minutes max wait (Lambda timeout is 15 min)

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


// ── App tabs (Upload / Browse) ────────────────────────────────────────
function showAppTab(tab) {
    document.getElementById('tabUpload').classList.toggle('active', tab === 'upload');
    document.getElementById('tabBrowse').classList.toggle('active', tab === 'browse');
    document.getElementById('uploadSection').style.display = tab === 'upload' ? 'block' : 'none';
    const browseEl = document.getElementById('browseSection');
    if (tab === 'browse') {
        browseEl.classList.add('visible');
        loadBrowseProjects();
    } else {
        browseEl.classList.remove('visible');
    }
}

// ── Browse projects ──────────────────────────────────────────────────
let browseData = null;  // cached project index data
let browseLoaded = false;

const browseOffice  = document.getElementById('browseOffice');
const browseClient  = document.getElementById('browseClient');
const browseProject = document.getElementById('browseProject');
const projectGrid   = document.getElementById('projectGrid');

browseOffice.addEventListener('change', () => {
    populateBrowseClients();
    populateBrowseProjects();
    renderProjectCards();
});
browseClient.addEventListener('change', () => {
    populateBrowseProjects();
    renderProjectCards();
});
browseProject.addEventListener('change', () => {
    renderProjectCards();
});

async function loadBrowseProjects() {
    if (browseLoaded) return;
    const loadingEl = document.getElementById('browseLoading');
    const emptyEl = document.getElementById('browseEmpty');
    loadingEl.style.display = 'block';
    emptyEl.style.display = 'none';
    projectGrid.innerHTML = '';

    try {
        const resp = await fetch(`${API_BASE}/project-index`, { headers: authHeaders() });
        if (resp.ok) {
            const data = await resp.json();
            browseData = data.projects || {};
            browseLoaded = true;
            populateBrowseOffices();
            renderProjectCards();
        }
    } catch (err) {
        console.warn('Could not load project index:', err);
    } finally {
        loadingEl.style.display = 'none';
    }
}

function populateBrowseOffices() {
    const current = browseOffice.value;
    browseOffice.innerHTML = '<option value="">All Offices</option>';
    for (const office of Object.keys(browseData).sort()) {
        const opt = document.createElement('option');
        opt.value = office;
        opt.textContent = office.replace(/_/g, ' ');
        browseOffice.appendChild(opt);
    }
    browseOffice.value = current;
    populateBrowseClients();
}

function populateBrowseClients() {
    const selectedOffice = browseOffice.value;
    const current = browseClient.value;
    browseClient.innerHTML = '<option value="">All Clients</option>';
    const offices = selectedOffice ? { [selectedOffice]: browseData[selectedOffice] || {} } : browseData;
    const clientSet = new Set();
    for (const clients of Object.values(offices)) {
        for (const cli of Object.keys(clients || {})) {
            clientSet.add(cli);
        }
    }
    for (const cli of [...clientSet].sort()) {
        const opt = document.createElement('option');
        opt.value = cli;
        opt.textContent = cli.replace(/_/g, ' ');
        browseClient.appendChild(opt);
    }
    browseClient.value = clientSet.has(current) ? current : '';
    populateBrowseProjects();
}

function populateBrowseProjects() {
    const selectedOffice = browseOffice.value;
    const selectedClient = browseClient.value;
    const current = browseProject.value;
    browseProject.innerHTML = '<option value="">All Projects</option>';
    const projectSet = new Set();
    const offices = selectedOffice ? { [selectedOffice]: browseData[selectedOffice] || {} } : browseData;
    for (const clients of Object.values(offices)) {
        const clientMap = selectedClient ? { [selectedClient]: clients[selectedClient] || [] } : clients;
        for (const projects of Object.values(clientMap || {})) {
            for (const proj of (projects || [])) {
                projectSet.add(proj.name);
            }
        }
    }
    for (const proj of [...projectSet].sort()) {
        const opt = document.createElement('option');
        opt.value = proj;
        opt.textContent = proj.replace(/_/g, ' ');
        browseProject.appendChild(opt);
    }
    browseProject.value = projectSet.has(current) ? current : '';
}

function renderProjectCards() {
    if (!browseData) return;
    const selectedOffice = browseOffice.value;
    const selectedClient = browseClient.value;
    const selectedProject = browseProject.value;
    const emptyEl = document.getElementById('browseEmpty');

    projectGrid.innerHTML = '';
    let count = 0;

    const offices = selectedOffice ? { [selectedOffice]: browseData[selectedOffice] || {} } : browseData;
    for (const [officeName, clients] of Object.entries(offices).sort()) {
        const clientMap = selectedClient ? { [selectedClient]: clients[selectedClient] || [] } : clients;
        for (const [clientName, projects] of Object.entries(clientMap || {}).sort()) {
            const sorted = [...(projects || [])].sort((a, b) => (b.last_upload || '').localeCompare(a.last_upload || ''));
            for (const proj of sorted) {
                if (selectedProject && proj.name !== selectedProject) continue;

                const card = document.createElement('a');
                card.className = 'project-card';
                card.href = proj.landing_url;
                card.target = '_blank';

                const lastUpload = proj.last_upload
                    ? new Date(proj.last_upload).toLocaleDateString('en-US', { month: 'short', day: 'numeric', year: 'numeric' })
                    : '';

                card.innerHTML = `
                    <h3>${escapeHtml(proj.name.replace(/_/g, ' '))}${proj.protected ? '<span class="pw-icon" title="Password protected">&#x1F512;</span>' : ''}</h3>
                    <div class="project-client">${escapeHtml(officeName.replace(/_/g, ' '))} / ${escapeHtml(clientName.replace(/_/g, ' '))}</div>
                    <div class="project-stats">
                        <span class="stat"><span class="stat-label">Batches:</span> ${parseInt(proj.batch_count) || 0}</span>
                        <span class="stat"><span class="stat-label">Pano:</span> ${parseInt(proj.pano_count) || 0}</span>
                        <span class="stat"><span class="stat-label">Photo:</span> ${parseInt(proj.photo_count) || 0}</span>
                    </div>
                    ${lastUpload ? `<div class="project-meta">Last upload: ${escapeHtml(lastUpload)}${proj.last_employee ? ' by ' + escapeHtml(proj.last_employee) : ''}</div>` : ''}
                `;
                projectGrid.appendChild(card);
                count++;
            }
        }
    }

    emptyEl.style.display = count === 0 ? 'block' : 'none';
}

// Expose tab function globally (called from onclick)
window.showAppTab = showAppTab;
