'use strict';
const http = require('http'), fs = require('fs'), path = require('path'), crypto = require('crypto');
const { execFile } = require('child_process'), zlib = require('zlib'), os = require('os');

const FFMPEG = 'ffmpeg', FFPROBE = 'ffprobe';
const PORT = 3000, UPLOAD_DIR = path.join(__dirname, 'uploads'), VIDEO_DIR = path.join(__dirname, 'video'), THUMB_DIR = path.join(__dirname, 'thumbs');
const DB_FILE = path.join(__dirname, 'db.json'), CPU_CORES = Math.max(1, Math.min(os.cpus().length, 4));
const MAX_PARALLEL = CPU_CORES, ADMIN_PASS = 'admin1234';
[UPLOAD_DIR, VIDEO_DIR, THUMB_DIR].forEach(d => { if (!fs.existsSync(d)) fs.mkdirSync(d, { recursive: true }); });

// ── Sessions ──
const sessions = new Map();
const makeToken = () => crypto.randomBytes(24).toString('hex');
function getSession(req) { const m = (req.headers.cookie || '').match(/mvs=([a-f0-9]+)/); if (!m) return null; const s = sessions.get(m[1]); if (!s || s.expires < Date.now()) { if (s) sessions.delete(m[1]); return null; } return s; }
function setCookie(res, token, maxAge = 86400 * 7) { res.setHeader('Set-Cookie', `mvs=${token}; Path=/; HttpOnly; Max-Age=${maxAge}; SameSite=Strict`); }

// ── DB ──
let _db = null, _dirty = false, _dbTimer = null;
function readDB() { if (_db) return _db; try { _db = JSON.parse(fs.readFileSync(DB_FILE, 'utf8')); } catch { _db = { posts: [] }; } return _db; }
function writeDB(db) {
    const safe = { posts: (db.posts || []).map(p => ({ id: p.id, files: Array.isArray(p.files) ? p.files.filter(f => typeof f === 'string') : [], type: typeof p.type === 'string' ? p.type : 'image', createdAt: typeof p.createdAt === 'string' ? p.createdAt : new Date().toISOString(), convFile: typeof p.convFile === 'string' ? p.convFile : undefined, thumb: typeof p.thumb === 'string' ? p.thumb : undefined, broken: p.broken || undefined, brokenReason: p.brokenReason || undefined, meta: p.meta && typeof p.meta === 'object' && !Buffer.isBuffer(p.meta) ? p.meta : undefined })) };
    _db = safe; _dirty = true; clearTimeout(_dbTimer);
    _dbTimer = setTimeout(() => { if (!_dirty) return; const tmp = DB_FILE + '.tmp'; try { fs.writeFileSync(tmp, JSON.stringify(safe), 'utf8'); fs.renameSync(tmp, DB_FILE); _dirty = false; } catch (e) { console.error('[writeDB]', e.message); } }, 200);
}
function flushDB() { if (!_dirty || !_db) return; clearTimeout(_dbTimer); const tmp = DB_FILE + '.tmp'; try { fs.writeFileSync(tmp, JSON.stringify(_db), 'utf8'); fs.renameSync(tmp, DB_FILE); _dirty = false; } catch (e) { console.error('[flushDB]', e.message); } }
function deletePostFiles(post) { (post.files || []).forEach(f => { try { fs.unlinkSync(path.join(UPLOAD_DIR, f)); } catch { } }); if (post.convFile) try { fs.unlinkSync(path.join(VIDEO_DIR, post.convFile)); } catch { } if (post.thumb) try { fs.unlinkSync(path.join(THUMB_DIR, post.thumb)); } catch { } }

// ── Body / Multipart ──
const collectBody = req => new Promise((res, rej) => { const c = []; req.on('data', d => c.push(d)); req.on('end', () => res(Buffer.concat(c))); req.on('error', rej); });

function streamMultipart(req, boundary, uploadDir) {
    return new Promise((resolve, reject) => {
        const startSep = Buffer.from('--' + boundary + '\r\n'), midSep = Buffer.from('\r\n--' + boundary), hdrEnd = Buffer.from('\r\n\r\n'), TAIL = midSep.length + 4;
        let chunks = [], chunksLen = 0, state = 'start', currentStream = null, currentMeta = null;
        const saved = [], resolved = { v: false };
        function peekN(n) { if (n <= 0) return Buffer.alloc(0); if (chunks.length === 1 && chunks[0].length >= n) return chunks[0].slice(0, n); const out = Buffer.allocUnsafe(n); let off = 0, rem = n; for (const c of chunks) { if (rem <= 0) break; const take = Math.min(c.length, rem); c.copy(out, off, 0, take); off += take; rem -= take; } return out; }
        function dropN(n) { if (n <= 0) return; chunksLen -= n; if (chunksLen < 0) chunksLen = 0; while (n > 0 && chunks.length) { if (chunks[0].length <= n) { n -= chunks[0].length; chunks.shift(); } else { chunks[0] = chunks[0].slice(n); n = 0; } } }
        function consumeToStream(n) { if (n <= 0) return; let rem = n; while (rem > 0 && chunks.length) { const c = chunks[0]; if (c.length <= rem) { if (currentStream) currentStream.write(c); rem -= c.length; chunksLen -= c.length; chunks.shift(); } else { if (currentStream) currentStream.write(c.slice(0, rem)); chunks[0] = c.slice(rem); chunksLen -= rem; rem = 0; } } }
        function finish(err) { if (resolved.v) return; resolved.v = true; if (currentStream) { try { currentStream.destroy(); } catch { } currentStream = null; } chunks = []; chunksLen = 0; if (err) return reject(err); const pending = saved.filter(s => s.finishPromise).map(s => s.finishPromise); const result = saved.map(({ finishPromise: _, ...rest }) => rest).filter(Boolean); if (!pending.length) return resolve(result); Promise.all(pending).then(() => resolve(result)).catch(() => resolve(result)); }
        function process() {
            while (true) {
                if (state === 'start') { if (chunksLen < startSep.length + 2) return; const flat = peekN(Math.min(chunksLen, 4096)); const idx = flat.indexOf(startSep); if (idx === -1) { if (chunksLen > startSep.length + 2) dropN(chunksLen - startSep.length - 2); return; } dropN(idx + startSep.length); state = 'header'; }
                if (state === 'header') { if (chunksLen < hdrEnd.length) return; const flat = peekN(Math.min(chunksLen, 4096)); const hIdx = flat.indexOf(hdrEnd); if (hIdx === -1) return; const hdr = flat.slice(0, hIdx).toString('utf8'); dropN(hIdx + hdrEnd.length); const nm = hdr.match(/name="([^"]+)"/), fn = hdr.match(/filename="([^"]+)"/), ct = hdr.match(/Content-Type:\s*([^\r\n]+)/i); if (nm && nm[1] === 'files' && fn && fn[1]) { const ext = path.extname(fn[1]) || '.bin', fname = Date.now() + '_' + Math.random().toString(36).slice(2, 8) + ext; currentStream = fs.createWriteStream(path.join(uploadDir, fname), { highWaterMark: 256 * 1024 }); currentMeta = { fname, contentType: (ct && ct[1] && ct[1].trim()) || 'application/octet-stream' }; currentStream.on('error', finish); } else { currentStream = null; currentMeta = null; } state = 'body'; }
                if (state === 'body') { if (chunksLen < TAIL) return; const searchLen = Math.min(chunksLen, 65536 + midSep.length); const flat = peekN(searchLen); const sepIdx = flat.indexOf(midSep); if (sepIdx === -1) { const safe = chunksLen - TAIL; if (safe > 0) consumeToStream(safe); return; } consumeToStream(sepIdx); dropN(midSep.length); if (currentStream) { const fp = new Promise(r => currentStream.once('finish', r)); currentStream.end(); saved.push({ ...currentMeta, finishPromise: fp }); currentStream = null; currentMeta = null; } if (chunksLen < 2) return; const tag = peekN(2).toString(); if (tag === '--') { finish(); return; } if (tag === '\r\n') dropN(2); state = 'header'; }
            }
        }
        req.on('data', chunk => { chunks.push(chunk); chunksLen += chunk.length; process(); });
        req.on('end', () => { if (!resolved.v) { if (currentStream && chunksLen > 0) { const flat = peekN(chunksLen); const si = flat.indexOf(midSep); const wl = si >= 0 ? si : chunksLen; if (wl > 0) consumeToStream(wl); const fp = new Promise(r => currentStream.once('finish', r)); currentStream.end(); saved.push({ ...currentMeta, finishPromise: fp }); currentStream = null; } finish(); } });
        req.on('error', finish);
    });
}

const MIME = { '.mp4': 'video/mp4', '.webm': 'video/webm', '.mov': 'video/quicktime', '.mkv': 'video/x-matroska', '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg', '.png': 'image/png', '.gif': 'image/gif', '.webp': 'image/webp', '.html': 'text/html', '.json': 'application/json' };

// ── ffmpeg ──
const LOG_FILE = path.join(__dirname, 'ffmpeg.log');
const logFFmpeg = (type, id, message, stderr = '') => {
    const timestamp = new Date().toISOString().slice(11, 19);
    const logEntry = `[${timestamp}] [${type}] ${id}${message ? ': ' + message : ''}${stderr ? ' | ' + stderr : ''}\n`;
    console.log(logEntry.trim());
    fs.appendFileSync(LOG_FILE, logEntry);
};

// ... rest of the code remains the same ...
const ffprobe = fp => new Promise(resolve => { 
    logFFmpeg(`[FFPROBE] Starting analysis for: ${fp}`); 
    execFile(FFPROBE, ['-v', 'quiet', '-print_format', 'json', '-show_streams', '-show_format', fp], { maxBuffer: 2 * 1024 * 1024 }, (err, stdout, stderr) => { 
        if (err) { 
            logFFmpeg(`[FFPROBE err] ${fp}`, `${err.message}\n${stderr?.slice(0, 500) || ''}`); 
            return resolve(null); 
        } 
        try { 
            logFFmpeg(`[FFPROBE] Success for: ${fp}`); 
            resolve(JSON.parse(stdout)); 
        } catch (e) { 
            logFFmpeg(`[FFPROBE parse err] ${fp}`, e.message); 
            resolve(null); 
        } 
    }); 
});
const validateContainer = fp => new Promise(resolve => { 
    logFFmpeg(`[VALIDATE] Checking container for: ${fp}`); 
    execFile(FFPROBE, ['-v', 'error', '-show_entries', 'format=duration', '-of', 'default=noprint_wrappers=1', fp], { maxBuffer: 256 * 1024, timeout: 12000 }, (err, _, stderr) => { 
        if (err && stderr) logFFmpeg(`[VALIDATE err] ${fp}`, stderr.slice(0, 500)); 
        if (!err) { 
            logFFmpeg(`[VALIDATE] Success for: ${fp}`); 
            return resolve(true); 
        } 
        const s = (stderr || '').toLowerCase(); 
        const isBroken = s.includes('moov atom not found') || s.includes('invalid data') || s.includes('error opening input'); 
        logFFmpeg(`[VALIDATE] Result for: ${fp} BROKEN: ${isBroken}`); 
        resolve(!isBroken); 
    }); 
});
const BROKEN_ERR = 'BROKEN_CONTAINER';
function makeMP4(videoPath, id) {
    const outFile = path.join(VIDEO_DIR, id + '.mp4');
    if (fs.existsSync(outFile)) { 
        logFFmpeg(`[MP4] Output file already exists: ${outFile}`); 
        return Promise.resolve(outFile); 
    }
    logFFmpeg(`[MP4] Starting conversion for: ${videoPath} -> ${outFile}`);
    return ffprobe(videoPath).then(async info => {
        if (!info) { 
            logFFmpeg(`[MP4] FFprobe failed, cannot convert: ${videoPath}`); 
            return null; 
        }
        if (!await validateContainer(videoPath)) { 
            const e = new Error(BROKEN_ERR); 
            e.broken = true; 
            logFFmpeg(`[MP4] Container is broken: ${videoPath}`); 
            throw e; 
        }
        const vStream = info?.streams?.find(s => s.codec_type === 'video'), aStream = info?.streams?.find(s => s.codec_type === 'audio');
        const vCodec = vStream?.codec_name || '', aCodec = aStream?.codec_name || '';
        const cv = vCodec === 'h264', ca = aCodec === 'aac';
        logFFmpeg(`[MP4] Codecs - Video: ${vCodec}, Audio: ${aCodec}, Copy video: ${cv}, Copy audio: ${ca}`);
        const args = ['-i', videoPath, '-threads', String(Math.max(1, Math.floor(CPU_CORES / MAX_PARALLEL)))];
        if (cv) args.push('-c:v', 'copy'); else args.push('-c:v', 'libx264', '-preset', 'ultrafast', '-tune', 'film', '-crf', '22', '-profile:v', 'high', '-level', '4.1', '-pix_fmt', 'yuv420p', '-vf', 'scale=trunc(iw/2)*2:trunc(ih/2)*2:flags=fast_bilinear', '-x264-params', 'ref=2:bframes=3:me=dia:subme=2:trellis=0');
        if (aStream) { if (ca) args.push('-c:a', 'copy'); else args.push('-c:a', 'aac', '-b:a', '128k', '-ar', '44100', '-ac', '2'); } else args.push('-an');
        args.push('-movflags', '+faststart', '-y', outFile);
        logFFmpeg(`[MP4] FFmpeg command: ${FFMPEG} ${args.join(' ')}`);
        return new Promise(resolve => { 
            execFile(FFMPEG, args, { maxBuffer: 10 * 1024 * 1024 }, (err, _, stderr) => { 
                if (err) { 
                    logFFmpeg(`[MP4 ENCODE err] ${id}`, `${err.message}\n${stderr?.slice(-500) || ''}`); 
                    try { fs.unlinkSync(outFile); } catch { } 
                    resolve(null); 
                } else { 
                    logFFmpeg(`[MP4 ENCODE success] ${id} -> ${outFile}`); 
                    resolve(outFile); 
                } 
            }); 
        });
    }).catch(err => { 
        logFFmpeg(`[MP4] Conversion failed: ${videoPath}`, err.message); 
        return null; 
    });
}
function generateThumb(videoPath, id) {
    const outFile = path.join(THUMB_DIR, id + '.jpg');
    if (fs.existsSync(outFile)) { 
        logFFmpeg(`[THUMB] Output already exists: ${outFile}`); 
        return Promise.resolve(outFile); 
    }
    logFFmpeg(`[THUMB] Generating thumbnail for: ${videoPath}`);
    return ffprobe(videoPath).then(info => {
        const dur = parseFloat(info?.format?.duration || info?.streams?.find(s => s.codec_type === 'video')?.duration || 0);
        const seekTo = Math.min(10, Math.max(0.5, dur * 0.15 || 1));
        logFFmpeg(`[THUMB] Duration: ${dur}, Seek to: ${seekTo}`);
        const args = ['-ss', String(seekTo), '-i', videoPath, '-vframes', '1', '-vf', 'scale=320:-2', '-q:v', '6', '-y', outFile];
        logFFmpeg(`[THUMB] FFmpeg command: ${FFMPEG} ${args.join(' ')}`);
        return new Promise(resolve => {
            execFile(FFMPEG, args, { timeout: 15000, maxBuffer: 2 * 1024 * 1024 }, (err, stdout, stderr) => {
                if (err) { 
                    logFFmpeg(`[THUMB err] ${id}`, `${err.message}\n${stderr?.slice(0, 500) || ''}`); 
                    try { fs.unlinkSync(outFile); } catch { } 
                    return resolve(null); 
                }
                logFFmpeg(`[THUMB success] ${id} -> ${outFile}`);
                resolve(outFile);
            });
        });
    }).catch(err => { 
        logFFmpeg(`[THUMB] Failed for: ${videoPath}`, err.message); 
        return null; 
    });
}

const gzipSend = (res, html, ct = 'text/html; charset=utf-8') => zlib.gzip(Buffer.from(html), (err, buf) => { if (err) { res.writeHead(200, { 'Content-Type': ct }); return res.end(html); } res.writeHead(200, { 'Content-Type': ct, 'Content-Encoding': 'gzip', 'Vary': 'Accept-Encoding', 'Cache-Control': 'no-cache' }); res.end(buf); });

// ── SVG Icons ──
const SVG = {
    back: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2"><polyline points="15 18 9 12 15 6"/></svg>`,
    play: `<svg viewBox="0 0 24 24" fill="currentColor"><polygon points="5 3 19 12 5 21"/></svg>`,
    upload: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="17 8 12 3 7 8"/><line x1="12" y1="3" x2="12" y2="15"/></svg>`,
    trash: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><polyline points="3 6 5 6 21 6"/><path d="M19 6l-1 14H6L5 6"/><path d="M10 11v6M14 11v6M9 6V4h6v2"/></svg>`,
    shuffle: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><polyline points="16 3 21 3 21 8"/><line x1="4" y1="20" x2="21" y2="3"/><polyline points="21 16 21 21 16 21"/><line x1="15" y1="15" x2="21" y2="21"/></svg>`,
    logout: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><polyline points="16 17 21 12 16 7"/><line x1="21" y1="12" x2="9" y2="12"/></svg>`,
    chart: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><line x1="18" y1="20" x2="18" y2="10"/><line x1="12" y1="20" x2="12" y2="4"/><line x1="6" y1="20" x2="6" y2="14"/></svg>`,
    status: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><rect x="2" y="3" width="20" height="14" rx="2"/><line x1="8" y1="21" x2="16" y2="21"/><line x1="12" y1="17" x2="12" y2="21"/></svg>`,
    video: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><polygon points="23 7 16 12 23 17 23 7"/><rect x="1" y="5" width="15" height="14" rx="2"/></svg>`,
    image: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><rect x="3" y="3" width="18" height="18" rx="2"/><circle cx="8.5" cy="8.5" r="1.5"/><polyline points="21 15 16 10 5 21"/></svg>`,
    clock: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><circle cx="12" cy="12" r="10"/><polyline points="12 6 12 12 16 14"/></svg>`,
    fwd: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><polyline points="23 4 23 10 17 10"/><path d="M20.49 15a9 9 0 1 1-.49-4.95"/></svg>`,
    star: `<svg viewBox="0 0 24 24" fill="currentColor" stroke="none"><polygon points="12 2 15.09 8.26 22 9.27 17 14.14 18.18 21.02 12 17.77 5.82 21.02 7 14.14 2 9.27 8.91 8.26 12 2"/></svg>`,
    eye: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z"/><circle cx="12" cy="12" r="3"/></svg>`,
    trend: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><polyline points="23 6 13.5 15.5 8.5 10.5 1 18"/><polyline points="17 6 23 6 23 12"/></svg>`,
    info: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><circle cx="12" cy="12" r="10"/><line x1="12" y1="8" x2="12" y2="12"/><line x1="12" y1="16" x2="12.01" y2="16"/></svg>`,
    skip: `<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><polyline points="5 4 15 12 5 20"/><line x1="19" y1="4" x2="19" y2="20"/></svg>`,
};

// ════════════════════════════════════════════════════════
// ANALYTICS PAGE
// ════════════════════════════════════════════════════════
function buildAnalyticsHTML() {
    return `<!DOCTYPE html>
<html lang="th"><head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>MyVault · Analytics</title>
<link href="https://fonts.googleapis.com/css2?family=Space+Grotesk:wght@400;500;600;700&family=JetBrains+Mono:wght@400;600&display=swap" rel="stylesheet">
<style>
*{margin:0;padding:0;box-sizing:border-box}
:root{--bg:#060408;--s1:#0e0c12;--s2:#161320;--s3:#1e1a2a;--acc:#a855f7;--acc2:#c084fc;--acc3:#7c3aed;--grn:#22d3ee;--red:#f43f5e;--yel:#fbbf24;--txt:#f1eeff;--muted:#6b6480;--border:#2a2440}
body{background:var(--bg);color:var(--txt);font-family:'Space Grotesk',sans-serif;min-height:100vh}
.page{padding:28px 20px 80px;max-width:1100px;margin:0 auto}
.topbar{display:flex;align-items:center;justify-content:space-between;margin-bottom:32px;flex-wrap:wrap;gap:12px}
.brand{display:flex;align-items:center;gap:10px}
.brand-dot{width:10px;height:10px;border-radius:50%;background:var(--acc);box-shadow:0 0 12px var(--acc)}
.brand-name{font-size:18px;font-weight:700}.brand-sub{font-size:11px;color:var(--muted);font-family:'JetBrains Mono',monospace}
.top-actions{display:flex;gap:8px}
.btn{display:inline-flex;align-items:center;gap:6px;padding:8px 14px;border-radius:8px;font-size:12px;font-weight:600;cursor:pointer;text-decoration:none;border:none;font-family:'Space Grotesk',sans-serif;transition:all .15s}
.btn-ghost{background:rgba(168,85,247,.1);border:1px solid rgba(168,85,247,.2);color:var(--acc2)}.btn-ghost:hover{background:rgba(168,85,247,.2)}
.btn-danger{background:rgba(244,63,94,.1);border:1px solid rgba(244,63,94,.2);color:#fb7185}.btn-danger:hover{background:rgba(244,63,94,.2)}
.btn svg{width:13px;height:13px;stroke:currentColor;fill:none;stroke-width:2}
h2{font-size:13px;font-weight:600;color:var(--muted);text-transform:uppercase;letter-spacing:1px;margin-bottom:14px}
.summary-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:10px;margin-bottom:28px}
.scard{background:var(--s1);border:1px solid var(--border);border-radius:12px;padding:16px 18px;position:relative;overflow:hidden}
.scard::before{content:'';position:absolute;top:0;left:0;right:0;height:2px;background:var(--acc);opacity:.6}
.scard.grn::before{background:var(--grn)}.scard.red::before{background:var(--red)}.scard.yel::before{background:var(--yel)}
.scard-n{font-size:30px;font-weight:700;font-family:'JetBrains Mono',monospace;line-height:1.1}
.scard-l{font-size:11px;color:var(--muted);margin-top:4px;display:flex;align-items:center;gap:5px}
.scard-l svg{width:12px;height:12px;stroke:currentColor;fill:none;stroke-width:2;flex-shrink:0}
.section{background:var(--s1);border:1px solid var(--border);border-radius:14px;padding:20px;margin-bottom:16px}
.section-head{display:flex;align-items:center;justify-content:space-between;margin-bottom:16px;flex-wrap:wrap;gap:8px}
.section-title{font-size:14px;font-weight:700;display:flex;align-items:center;gap:7px}
.section-title svg{width:15px;height:15px;stroke:var(--acc);fill:none;stroke-width:2}
.algo-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:10px;margin-bottom:20px}
.algo-card{background:var(--s2);border:1px solid var(--border);border-radius:10px;padding:14px 16px}
.algo-card-title{font-size:12px;font-weight:700;color:var(--acc2);margin-bottom:6px;display:flex;align-items:center;gap:6px}
.algo-card-title svg{width:13px;height:13px;stroke:currentColor;fill:none;stroke-width:2}
.algo-card p{font-size:11px;color:var(--muted);line-height:1.5}
.score-bar-wrap{margin-top:10px}.score-label{display:flex;justify-content:space-between;font-size:10px;color:var(--muted);margin-bottom:4px}
.score-bar{height:6px;background:var(--s3);border-radius:3px;overflow:hidden}
.score-fill{height:100%;border-radius:3px;background:linear-gradient(90deg,var(--acc3),var(--acc2));transition:width .6s cubic-bezier(.4,0,.2,1)}
.post-table{width:100%;border-collapse:collapse;font-size:12px}
.post-table th{text-align:left;padding:8px 10px;color:var(--muted);font-weight:600;border-bottom:1px solid var(--border);font-size:11px;text-transform:uppercase;letter-spacing:.5px;white-space:nowrap}
.post-table td{padding:9px 10px;border-bottom:1px solid rgba(42,36,64,.5);vertical-align:middle}
.post-table tr:last-child td{border-bottom:none}.post-table tr:hover td{background:rgba(168,85,247,.04)}
.thumb-cell{width:36px}.score-cell{font-family:'JetBrains Mono',monospace;font-weight:600;font-size:13px}
.score-cell.hi{color:var(--grn)}.score-cell.mid{color:var(--yel)}.score-cell.lo{color:var(--red)}
.badge-sm{display:inline-flex;align-items:center;gap:3px;padding:2px 7px;border-radius:4px;font-size:10px;font-weight:700}
.badge-sm.v{background:rgba(34,211,238,.1);color:var(--grn)}.badge-sm.i{background:rgba(168,85,247,.1);color:var(--acc2)}
.mini-bar{height:4px;background:var(--s3);border-radius:2px;width:80px;overflow:hidden;display:inline-block;vertical-align:middle;margin-left:6px}
.mini-fill{height:100%;border-radius:2px;background:var(--acc);transition:width .5s}
.dist-chart{display:flex;align-items:flex-end;gap:2px;height:80px;padding:0 2px}
.dist-bar-wrap{flex:1;display:flex;flex-direction:column;align-items:center;gap:3px;height:100%}
.dist-bar{width:100%;border-radius:3px 3px 0 0;background:var(--acc);opacity:.7;min-height:2px}
.dist-bar:hover{opacity:1}.dist-label{font-size:9px;color:var(--muted);white-space:nowrap;font-family:'JetBrains Mono',monospace}
.ring-wrap{display:flex;align-items:center;gap:20px;flex-wrap:wrap}
.ring{position:relative;width:80px;height:80px;flex-shrink:0}
.ring svg{transform:rotate(-90deg)}.ring-bg{fill:none;stroke:var(--s3);stroke-width:8}
.ring-fill{fill:none;stroke:var(--acc);stroke-width:8;stroke-linecap:round;transition:stroke-dashoffset .8s cubic-bezier(.4,0,.2,1)}
.ring-val{position:absolute;inset:0;display:flex;align-items:center;justify-content:center;font-family:'JetBrains Mono',monospace;font-size:15px;font-weight:700}
.ring-stats{flex:1}.ring-stat{display:flex;align-items:center;gap:8px;padding:5px 0;border-bottom:1px solid var(--border);font-size:12px}
.ring-stat:last-child{border:none}.ring-stat-l{color:var(--muted);min-width:120px}
.ring-stat-v{font-family:'JetBrains Mono',monospace;font-weight:600}
.weight-row{display:grid;grid-template-columns:100px 1fr 50px;align-items:center;gap:10px;padding:6px 0;border-bottom:1px solid rgba(42,36,64,.4);font-size:12px}
.weight-row:last-child{border:none}.weight-name{color:var(--muted);font-size:11px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.weight-track{height:6px;background:var(--s3);border-radius:3px;overflow:hidden}
.weight-fill{height:100%;border-radius:3px;background:linear-gradient(90deg,var(--acc3),var(--grn))}
.weight-score{font-family:'JetBrains Mono',monospace;font-size:11px;font-weight:600;color:var(--acc2);text-align:right}
.tabs{display:flex;gap:4px;margin-bottom:16px}
.tab{padding:6px 14px;border-radius:6px;font-size:12px;font-weight:600;cursor:pointer;background:transparent;border:1px solid var(--border);color:var(--muted);font-family:'Space Grotesk',sans-serif;transition:all .15s}
.tab.on{background:rgba(168,85,247,.15);border-color:rgba(168,85,247,.4);color:var(--acc2)}
.empty-msg{padding:30px;text-align:center;color:var(--muted);font-size:13px}
.spin{display:inline-block;width:14px;height:14px;border:2px solid rgba(168,85,247,.2);border-top-color:var(--acc);border-radius:50%;animation:spin .7s linear infinite}
@keyframes spin{to{transform:rotate(360deg)}}
</style></head><body>
<div class="page">
  <div class="topbar">
    <div class="brand"><div class="brand-dot"></div><span class="brand-name">MyVault</span><span class="brand-sub">/ analytics</span></div>
    <div class="top-actions">
      <a href="/admin" class="btn btn-ghost">${SVG.back} Admin</a>
      <a href="/status" class="btn btn-ghost">${SVG.status} Status</a>
      <a href="#" class="btn btn-danger" onclick="fetch('/api/logout',{method:'POST'});window.location='/login';return false">${SVG.logout} ออก</a>
    </div>
  </div>
  <h2>ภาพรวม</h2>
  <div class="summary-grid">
    <div class="scard"><div class="scard-n" id="sTotal">—</div><div class="scard-l">${SVG.video} วิดีโอทั้งหมด</div></div>
    <div class="scard grn"><div class="scard-n" id="sTracked">—</div><div class="scard-l">${SVG.eye} มีข้อมูล engagement</div></div>
    <div class="scard yel"><div class="scard-n" id="sWatchTime">—</div><div class="scard-l">${SVG.clock} รวมเวลาดู (นาที)</div></div>
    <div class="scard red"><div class="scard-n" id="sAvgRatio">—</div><div class="scard-l">${SVG.trend} avg watch ratio</div></div>
  </div>
  <div class="section">
    <div class="section-head"><div class="section-title">${SVG.info} อัลกอริทึม Weighted Shuffle</div><button class="btn btn-ghost" onclick="loadData()"><span id="refreshSpinner" style="display:none" class="spin"></span> รีเฟรช</button></div>
    <div class="algo-grid">
      <div class="algo-card"><div class="algo-card-title">${SVG.eye} Watch Ratio (60%)</div><p>สัดส่วนเวลาที่ดูจริงต่อความยาวทั้งหมด ยิ่งดูนาน score สูง</p><div class="score-bar-wrap"><div class="score-label"><span>0%</span><span>100%</span></div><div class="score-bar"><div class="score-fill" style="width:60%"></div></div></div></div>
      <div class="algo-card"><div class="algo-card-title">${SVG.trend} Watch Bonus (+20/+8)</div><p>ดูจบ &gt;80% = +20, ดูจบ &gt;50% = +8 คะแนน</p><div class="score-bar-wrap"><div class="score-label"><span>50%+</span><span>80%+</span></div><div class="score-bar"><div class="score-fill" style="width:40%;background:linear-gradient(90deg,#22d3ee,#a855f7)"></div></div></div></div>
      <div class="algo-card"><div class="algo-card-title">${SVG.skip} Skip Penalty (-10)</div><p>สไลด์ผ่านใน &lt;1.5 วินาที นับเป็น skip หักคะแนน</p><div class="score-bar-wrap"><div class="score-label"><span>skip&gt;1</span><span>จะหัก</span></div><div class="score-bar"><div class="score-fill" style="width:80%;background:linear-gradient(90deg,#f43f5e,#fbbf24)"></div></div></div></div>
      <div class="algo-card"><div class="algo-card-title">${SVG.star} New Content (random 20–80)</div><p>วิดีโอใหม่ได้ score สุ่ม 20–80 ทุกครั้ง ไม่ถูกกลบโดย video เก่า</p><div class="score-bar-wrap"><div class="score-label"><span>สุ่ม</span><span>20–80</span></div><div class="score-bar"><div class="score-fill" style="width:60%;background:linear-gradient(90deg,#fbbf24,#a855f7)"></div></div></div></div>
    </div>
  </div>
  <div class="section">
    <div class="section-head"><div class="section-title">${SVG.star} Top Scored Content</div><div class="tabs"><button class="tab on" onclick="setTab('top',this)">สูงสุด</button><button class="tab" onclick="setTab('low',this)">ต่ำสุด</button><button class="tab" onclick="setTab('skipped',this)">Skip มาก</button><button class="tab" onclick="setTab('rewatched',this)">ดูซ้ำ</button></div></div>
    <table class="post-table"><thead><tr><th>#</th><th></th><th>ไฟล์</th><th>ประเภท</th><th>Score</th><th>Watch%</th><th>Views</th><th>Skips</th></tr></thead><tbody id="topTbody"><tr><td colspan="8" class="empty-msg">กำลังโหลด...</td></tr></tbody></table>
  </div>
  <div class="section"><div class="section-head"><div class="section-title">${SVG.chart} การกระจาย Score</div></div><div class="dist-chart" id="distChart"></div></div>
  <div class="section">
    <div class="section-head"><div class="section-title">${SVG.eye} สถิติการรับชม</div></div>
    <div class="ring-wrap">
      <div class="ring"><svg viewBox="0 0 80 80" width="80" height="80"><circle class="ring-bg" cx="40" cy="40" r="36"/><circle class="ring-fill" id="ringFill" cx="40" cy="40" r="36" stroke-dasharray="226" stroke-dashoffset="226"/></svg><div class="ring-val" id="ringVal">0%</div></div>
      <div class="ring-stats">
        <div class="ring-stat"><span class="ring-stat-l">Avg Watch Ratio</span><span class="ring-stat-v" id="rsRatio">—</span></div>
        <div class="ring-stat"><span class="ring-stat-l">รวมเวลาดู</span><span class="ring-stat-v" id="rsTotal">—</span></div>
        <div class="ring-stat"><span class="ring-stat-l">Total Views</span><span class="ring-stat-v" id="rsViews">—</span></div>
        <div class="ring-stat"><span class="ring-stat-l">Unique Content</span><span class="ring-stat-v" id="rsUniq">—</span></div>
      </div>
    </div>
  </div>
  <div class="section"><div class="section-head"><div class="section-title">${SVG.trend} Algorithm Weight ต่อไฟล์ (Top 20)</div></div><div id="weightList"></div></div>
</div>
<script>
function getEngStats(){try{var s=localStorage.getItem('mvStats');return s?JSON.parse(s):{};}catch{return{};}}
function calcScore(st,dur){if(!st||st.views===0)return null;var d=Math.max(dur||st.totalDur||5,1),r=Math.min(1,(st.totalWatch/st.views)/d);var b=r>0.8?20:r>0.5?8:r>0.3?3:0,pen=Math.max(0,(st.skips||0)-1)*10,vpen=st.views>5?Math.min(15,Math.floor(st.views/5)*3):0;return Math.max(1,Math.round(r*60+b-pen-vpen));}
var allPostsMeta=[],curTab='top';
function loadData(){document.getElementById('refreshSpinner').style.display='inline-block';fetch('/api/posts').then(r=>r.json()).then(posts=>{document.getElementById('refreshSpinner').style.display='none';allPostsMeta=posts;renderAll();}).catch(()=>document.getElementById('refreshSpinner').style.display='none');}
function buildRows(){var stats=getEngStats();return allPostsMeta.map(p=>{var st=stats[p.id],dur=(p.meta&&p.meta.dur)||0,score=calcScore(st,dur),ratio=0;if(st&&st.views>0&&dur>0)ratio=Math.min(1,(st.totalWatch/st.views)/dur);return{post:p,st:st||null,dur,score,ratio,views:st?st.views:0,skips:st?st.skips||0:0,rewatches:st?st.rewatches||0:0};});}
function renderAll(){
  var rows=buildRows(),tracked=Object.keys(getEngStats()).length;
  var videos=allPostsMeta.filter(p=>p.type==='video');
  document.getElementById('sTotal').textContent=videos.length;document.getElementById('sTracked').textContent=tracked;
  var t2=rows.filter(r=>r.st),tW=t2.reduce((a,r)=>a+(r.st.totalWatch||0),0),tV=t2.reduce((a,r)=>a+r.views,0),aR=t2.length?t2.reduce((a,r)=>a+r.ratio,0)/t2.length:0;
  document.getElementById('sWatchTime').textContent=Math.round(tW/60);document.getElementById('sAvgRatio').textContent=Math.round(aR*100)+'%';
  document.getElementById('ringFill').style.strokeDashoffset=226*(1-aR);document.getElementById('ringVal').textContent=Math.round(aR*100)+'%';
  document.getElementById('rsRatio').textContent=Math.round(aR*100)+'%';document.getElementById('rsTotal').textContent=Math.round(tW/60)+' นาที';document.getElementById('rsViews').textContent=tV;document.getElementById('rsUniq').textContent=t2.length;
  renderTable(rows,curTab);renderDist(rows);renderWeights(rows);
}
function setTab(tab,el){curTab=tab;document.querySelectorAll('.tab').forEach(t=>t.classList.remove('on'));el.classList.add('on');renderTable(buildRows(),tab);}
function renderTable(rows,tab){
  var sorted;
  if(tab==='top')sorted=rows.slice().sort((a,b)=>a.score===null&&b.score===null?0:a.score===null?1:b.score===null?-1:b.score-a.score);
  else if(tab==='low')sorted=rows.filter(r=>r.st&&r.score!==null).slice().sort((a,b)=>a.score-b.score);
  else if(tab==='skipped')sorted=rows.filter(r=>r.st&&r.skips>0).slice().sort((a,b)=>b.skips-a.skips);
  else sorted=rows.filter(r=>r.st&&r.rewatches>0).slice().sort((a,b)=>b.rewatches-a.rewatches);
  sorted=sorted.slice(0,30);
  var tb=document.getElementById('topTbody');
  if(!sorted.length){tb.innerHTML='<tr><td colspan="8" class="empty-msg">ไม่มีข้อมูล</td></tr>';return;}
  tb.innerHTML=sorted.map((r,i)=>{
    var p=r.post,fname=((p.files||[])[0]||'');
    var thumb=p.type==='video'&&p.thumb&&p.thumb[0]!=='_'?'<img src="/thumbs/'+p.thumb+'" style="width:32px;height:44px;object-fit:cover;border-radius:5px;display:block;">':p.type==='video'?'<div style="width:32px;height:44px;background:var(--s3);border-radius:5px"></div>':'<div style="width:32px;height:44px;background:var(--s3);border-radius:5px"></div>';
    var sd=r.score===null?'<span style="font-size:10px;font-weight:700;color:var(--yel);background:rgba(251,191,36,.12);padding:2px 7px;border-radius:4px">NEW</span>':'<span class="score-cell '+(r.score>=60?'hi':r.score>=30?'mid':'lo')+'">'+r.score+'</span>';
    var rp=Math.round(r.ratio*100);
    return '<tr><td style="color:var(--muted);font-family:JetBrains Mono,monospace;font-size:11px">'+(i+1)+'</td><td>'+thumb+'</td><td style="font-size:11px;font-family:JetBrains Mono,monospace;color:#6b6480">'+(fname.length>22?fname.slice(0,20)+'…':fname)+'</td><td>'+(p.type==='video'?'<span class="badge-sm v">VIDEO</span>':'<span class="badge-sm i">IMAGE</span>')+'</td><td>'+sd+'</td><td><span style="font-size:11px;font-family:JetBrains Mono,monospace">'+rp+'%</span><span class="mini-bar"><span class="mini-fill" style="width:'+rp+'%"></span></span></td><td style="font-family:JetBrains Mono,monospace;font-size:11px">'+r.views+'</td><td style="font-family:JetBrains Mono,monospace;font-size:11px;color:'+(r.skips>2?'#f43f5e':r.skips>0?'#fbbf24':'#6b6480')+'">'+r.skips+'</td></tr>';
  }).join('');
}
function renderDist(rows){var b=new Array(10).fill(0);rows.forEach(r=>{if(r.score===null)return;b[Math.min(9,Math.floor(r.score/10))]++;});var mx=Math.max(1,...b);document.getElementById('distChart').innerHTML=b.map((v,i)=>'<div class="dist-bar-wrap"><div style="flex:1;display:flex;align-items:flex-end"><div class="dist-bar" style="height:'+Math.round(v/mx*100)+'%;width:100%" title="'+i*10+'-'+(i*10+9)+': '+v+'"></div></div><div class="dist-label">'+i*10+'</div></div>').join('');}
function renderWeights(rows){var s=rows.filter(r=>r.st&&r.score!==null).slice().sort((a,b)=>b.score-a.score).slice(0,20),mx=Math.max(1,...s.map(r=>r.score)),wl=document.getElementById('weightList');if(!s.length){wl.innerHTML='<div class="empty-msg">ยังไม่มีข้อมูล engagement</div>';return;}wl.innerHTML=s.map(r=>'<div class="weight-row"><div class="weight-name">'+((r.post.files||[])[0]||'').slice(-28)+'</div><div class="weight-track"><div class="weight-fill" style="width:'+Math.round(r.score/mx*100)+'%"></div></div><div class="weight-score">'+r.score+'</div></div>').join('');}
loadData();
</script></body></html>`;
}

// ════════════════════════════════════════════════════════
// STATUS PAGE
// ════════════════════════════════════════════════════════
function buildStatusHTML() {
    return `<!DOCTYPE html>
<html lang="th"><head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>MyVault · Status</title>
<link href="https://fonts.googleapis.com/css2?family=Space+Grotesk:wght@400;500;600;700&family=JetBrains+Mono:wght@400;600&display=swap" rel="stylesheet">
<style>
*{margin:0;padding:0;box-sizing:border-box}
:root{--bg:#0d0900;--s1:#150e00;--s2:#1e1500;--s3:#2a1e00;--acc:#ff7300;--acc2:#ffaa33;--txt:#fff5e6;--muted:#887755;--border:#2e2010;--ok:#22c55e;--err:#ef4444;--warn:#f59e0b}
body{background:var(--bg);color:var(--txt);font-family:'Space Grotesk',sans-serif;min-height:100vh;padding:24px 16px}
h1{font-size:20px;font-weight:800;margin-bottom:4px;color:var(--acc2)}.sub{font-size:12px;color:var(--muted);margin-bottom:20px}
.topbar{display:flex;align-items:center;justify-content:space-between;margin-bottom:20px;flex-wrap:wrap;gap:10px}
.actions{display:flex;gap:8px;flex-wrap:wrap}
.btn{background:rgba(255,115,0,.12);border:1px solid rgba(255,115,0,.25);border-radius:8px;color:var(--acc2);font-size:12px;font-weight:600;padding:7px 12px;cursor:pointer;text-decoration:none;display:inline-flex;align-items:center;gap:5px;font-family:'Space Grotesk',sans-serif;transition:background .15s}
.btn:hover{background:rgba(255,115,0,.25)}.btn svg{width:13px;height:13px;stroke:currentColor;fill:none;stroke-width:2;flex-shrink:0}
.btn.danger{background:rgba(239,68,68,.08);border-color:rgba(239,68,68,.25);color:#fca5a5}
.summary{display:grid;grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:10px;margin-bottom:20px}
.card{background:var(--s2);border:1px solid var(--border);border-radius:12px;padding:14px 16px}
.card-n{font-size:28px;font-weight:800;line-height:1;font-family:'JetBrains Mono',monospace}.card-l{font-size:11px;color:var(--muted);margin-top:3px}
.progress-wrap{background:var(--s3);border-radius:6px;height:6px;margin-bottom:20px;overflow:hidden}
.progress-fill{height:100%;background:linear-gradient(90deg,var(--acc),var(--acc2));border-radius:6px;transition:width .5s}
.filter-row{display:flex;gap:6px;margin-bottom:14px;flex-wrap:wrap}
.ftab{background:transparent;border:1px solid var(--border);border-radius:6px;color:var(--muted);font-size:11px;font-weight:600;padding:5px 12px;cursor:pointer;font-family:'Space Grotesk',sans-serif;transition:all .15s}
.ftab.on{background:rgba(255,115,0,.12);border-color:rgba(255,115,0,.35);color:var(--acc2)}
.diag-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(280px,1fr));gap:12px;margin-bottom:24px}
.diag-card{background:var(--s2);border:1px solid var(--border);border-radius:8px;padding:12px 16px;display:flex;gap:12px;align-items:flex-start}
.diag-card.ok{border-left:3px solid var(--ok)}.diag-card.warn{border-left:3px solid var(--warn)}.diag-card.error{border-left:3px solid var(--err)}
.diag-ico{margin-top:2px;flex-shrink:0}.diag-ico.ok svg{stroke:var(--ok)}.diag-ico.warn svg{stroke:var(--warn)}.diag-ico.error svg{stroke:var(--err)}.diag-ico.info svg{stroke:var(--acc2)}
.diag-body{flex-grow:1}.diag-title{font-weight:700;font-size:13px;margin-bottom:4px;color:#fff}.diag-msg{font-size:11px;color:var(--muted);line-height:1.4}.diag-act{margin-top:8px}
.diag-act button{background:transparent;border:1px solid var(--border);color:var(--acc2);font-size:10px;padding:4px 10px;border-radius:4px;cursor:pointer}
.diag-act button:hover{background:rgba(255,115,0,.1)}.diag-btn-danger{color:var(--err)!important;border-color:rgba(239,68,68,.3)!important}.diag-btn-danger:hover{background:rgba(239,68,68,.1)!important}
.table-wrap{overflow-x:auto}
table{width:100%;border-collapse:collapse;font-size:12px}
th{text-align:left;padding:8px 10px;color:var(--muted);font-weight:600;border-bottom:1px solid var(--border);white-space:nowrap}
td{padding:8px 10px;border-bottom:1px solid rgba(46,32,16,.5);vertical-align:middle}
tr:hover td{background:rgba(255,255,255,.02)}
.badge{display:inline-flex;align-items:center;gap:4px;border-radius:5px;padding:2px 8px;font-size:10px;font-weight:700;white-space:nowrap}
.badge.ok{background:rgba(34,197,94,.12);color:var(--ok)}.badge.no{background:rgba(239,68,68,.1);color:var(--err)}
.badge.proc{background:rgba(245,158,11,.12);color:var(--warn)}.badge.queue{background:rgba(100,100,100,.12);color:var(--muted)}
.badge.broken{background:rgba(239,68,68,.15);color:#fca5a5;border:1px solid rgba(239,68,68,.3)}
.badge svg{width:10px;height:10px;stroke:currentColor;fill:none;stroke-width:2.5}
.fname{font-family:'JetBrains Mono',monospace;color:var(--muted);font-size:10px;max-width:200px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.running-bar{background:rgba(255,115,0,.06);border:1px solid rgba(255,115,0,.18);border-radius:8px;padding:10px 14px;margin-bottom:16px;font-size:12px;color:var(--acc2);display:none}
.running-bar.on{display:flex;align-items:center;gap:8px}
.running-bar svg{width:14px;height:14px;stroke:var(--acc2);fill:none;stroke-width:2;flex-shrink:0;animation:spin .8s linear infinite}
@keyframes spin{to{transform:rotate(360deg)}}
</style></head><body>
<div class="topbar">
  <div><h1>Status</h1><div class="sub">สถานะการแปลงวิดีโอ · <a href="/admin" style="color:var(--acc2)">← กลับ Admin</a></div></div>
  <div class="actions">
    <button id="startBtn" class="btn" onclick="startProcess()">${SVG.play} เริ่มแปลง</button>
    <button id="forceBtn" class="btn danger" onclick="forceProcess()">${SVG.fwd} บังคับแปลงใหม่</button>
    <button id="clearBrokenBtn" class="btn danger" onclick="clearBroken()" style="display:none">${SVG.trash} ล้าง Broken</button>
    <button id="metaBtn" class="btn" onclick="refetchMeta(false)">${SVG.info} รีเฟรช Meta</button>
    <button id="metaAllBtn" class="btn" onclick="refetchMeta(true)">${SVG.fwd} รีทั้งหมด</button>
    <button id="thumbBtn" class="btn" onclick="genThumbs()">${SVG.image} สร้างปก</button>
    <button id="forceThumbBtn" class="btn danger" onclick="forceGenThumbs()">${SVG.fwd} บังคับสร้างปกใหม่</button>
    <a href="/analytics" class="btn">${SVG.chart} Analytics</a>
    <a href="/media-stats" class="btn">${SVG.image} สถิติไฟล์</a>
    <a href="#" class="btn danger" onclick="fetch('/api/logout',{method:'POST'});window.location='/login';return false">${SVG.logout} ออก</a>
  </div>
</div>
<div class="running-bar" id="runBar">${SVG.fwd}<span id="runMsg">กำลังแปลง...</span></div>
<div id="errMsg" style="display:none;background:rgba(239,68,68,.08);border:1px solid rgba(239,68,68,.25);border-radius:8px;padding:10px 14px;margin-bottom:16px;font-size:12px;color:#fca5a5"></div>
<div class="summary">
  <div class="card"><div class="card-n" id="sTotal">—</div><div class="card-l">วิดีโอทั้งหมด</div></div>
  <div class="card"><div class="card-n" style="color:var(--ok)" id="sDone">—</div><div class="card-l">แปลงแล้ว</div></div>
  <div class="card"><div class="card-n" style="color:var(--err)" id="sPend">—</div><div class="card-l">ยังไม่แปลง</div></div>
  <div class="card"><div class="card-n" style="color:#fca5a5" id="sBroken">—</div><div class="card-l">Broken</div></div>
  <div class="card"><div class="card-n" style="color:var(--acc2)" id="sPct">—</div><div class="card-l">% เสร็จ</div></div>
</div>
<div class="progress-wrap"><div class="progress-fill" id="progFill" style="width:0%"></div></div>

<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:12px">
  <h2 style="font-size:16px;margin:0">Diagnostics & Errors</h2>
  <button class="btn" onclick="loadDiag()" id="diagRefreshBtn" style="padding:4px 10px;font-size:11px">${SVG.fwd} เช็คใหม่</button>
</div>
<div class="diag-grid" id="diagGrid"></div>

<div class="filter-row">
  <button class="ftab on" onclick="setFilter('all',this)">ทั้งหมด</button>
  <button class="ftab" onclick="setFilter('done',this)">เสร็จแล้ว</button>
  <button class="ftab" onclick="setFilter('pending',this)">ยังไม่แปลง</button>
  <button class="ftab" id="brokenTab" onclick="setFilter('broken',this)" style="display:none">Broken</button>
</div>
<div class="table-wrap"><table>
  <thead><tr><th>#</th><th>ไฟล์</th><th>ขนาด</th><th>ความยาว</th><th>Codec</th><th>แปลงแล้ว</th><th>วันที่</th></tr></thead>
  <tbody id="tbody"></tbody>
</table></div>
<script>
var allItems=[],curFilter='all',pollTimer=null;
function setFilter(f,el){curFilter=f;document.querySelectorAll('.ftab').forEach(b=>b.classList.remove('on'));el.classList.add('on');renderTable();}
function fmtSize(b){if(!b)return'—';if(b>=1073741824)return(b/1073741824).toFixed(1)+' GB';if(b>=1048576)return(b/1048576).toFixed(1)+' MB';return(b/1024).toFixed(0)+' KB';}
function fmtDur(s){if(!s)return'—';var h=Math.floor(s/3600),m=Math.floor((s%3600)/60),sec=s%60;return h>0?h+':'+String(m).padStart(2,'0')+':'+String(sec).padStart(2,'0'):m+':'+String(sec).padStart(2,'0');}
function renderTable(){
  var rows=allItems.filter(x=>curFilter==='done'?x.convReady:curFilter==='pending'?(!x.convReady&&!x.broken):curFilter==='broken'?x.broken:true);
  var ok='<svg viewBox="0 0 24 24" width="10" height="10" fill="none" stroke="currentColor" stroke-width="2.5"><polyline points="20 6 9 17 4 12"/></svg>';
  var no='<svg viewBox="0 0 24 24" width="10" height="10" fill="none" stroke="currentColor" stroke-width="2.5"><line x1="18" y1="6" x2="6" y2="18"/><line x1="6" y1="6" x2="18" y2="18"/></svg>';
  var sp='<svg viewBox="0 0 24 24" width="10" height="10" fill="none" stroke="currentColor" stroke-width="2" style="animation:spin .8s linear infinite"><path d="M21 12a9 9 0 1 1-9-9"/></svg>';
  document.getElementById('tbody').innerHTML=rows.map((x,i)=>{
    var conv=x.broken?'<span class="badge broken">'+no+' broken</span>':x.isCurrent?'<span class="badge proc">'+sp+' กำลังแปลง</span>':x.inQueue?'<span class="badge queue">รอคิว</span>':x.convReady?'<span class="badge ok">'+ok+' พร้อม</span>':'<span class="badge no">'+no+' ยังไม่แปลง</span>';
    var dt=x.createdAt?new Date(x.createdAt).toLocaleDateString('th-TH',{day:'2-digit',month:'2-digit',year:'2-digit',hour:'2-digit',minute:'2-digit'}):'—';
    return '<tr><td style="color:var(--muted);font-family:JetBrains Mono,monospace">'+(i+1)+'</td><td><div class="fname">'+x.file+'</div></td><td style="white-space:nowrap;color:var(--muted)">'+fmtSize(x.size)+'</td><td style="white-space:nowrap;color:var(--muted)">'+fmtDur(x.dur)+'</td><td>'+(x.convInfo?'<span style="font-family:JetBrains Mono,monospace;font-size:10px;color:var(--acc2)">'+x.convInfo+'</span>':'<span style="color:var(--muted)">—</span>')+'</td><td>'+conv+'</td><td style="color:var(--muted);white-space:nowrap;font-size:10px">'+dt+'</td></tr>';
  }).join('')||'<tr><td colspan="7" style="text-align:center;color:var(--muted);padding:30px">ไม่มีรายการ</td></tr>';
}
function updateSummary(d){
  document.getElementById('sTotal').textContent=d.total;document.getElementById('sDone').textContent=d.done;
  document.getElementById('sPend').textContent=d.total-d.done-(d.brokenCount||0);document.getElementById('sBroken').textContent=d.brokenCount||0;
  document.getElementById('sPct').textContent=d.pct+'%';document.getElementById('progFill').style.width=d.pct+'%';
  var hb=(d.brokenCount||0)>0;document.getElementById('clearBrokenBtn').style.display=hb?'':'none';document.getElementById('brokenTab').style.display=hb?'':'none';
  var bar=document.getElementById('runBar');
  if(d.running){bar.classList.add('on');var ns=(d.currentFiles||[]).map(f=>f.length>28?f.slice(0,26)+'…':f).join(', ');document.getElementById('runMsg').textContent='กำลังแปลง '+(d.currentFiles||[]).length+' ไฟล์ ('+d.done+'/'+d.total+') — '+ns;}
  else bar.classList.remove('on');
  var btn=document.getElementById('startBtn');if(btn)btn.disabled=!!d.running;
}
function toast(msg,type){var t=document.getElementById('toastEl');if(!t){t=document.createElement('div');t.id='toastEl';t.style.cssText='position:fixed;bottom:24px;left:50%;transform:translateX(-50%);padding:10px 20px;border-radius:10px;font-size:13px;font-weight:600;z-index:999;transition:opacity .3s;pointer-events:none;font-family:Space Grotesk,sans-serif;white-space:nowrap';document.body.appendChild(t);}t.style.background=type==='err'?'rgba(239,68,68,.9)':type==='ok'?'rgba(34,197,94,.9)':'rgba(255,115,0,.9)';t.style.color='#fff';t.style.opacity='1';t.textContent=msg;clearTimeout(t._timer);t._timer=setTimeout(()=>t.style.opacity='0',3000);}
function load(){fetch('/api/status-data').then(r=>{if(r.status===401){location.href='/login';return null;}return r.json();}).then(d=>{if(!d)return;allItems=d.items;updateSummary(d);renderTable();if(d.running){if(!pollTimer)pollTimer=setInterval(load,2000);}else{clearInterval(pollTimer);pollTimer=null;}}).catch(()=>document.getElementById('errMsg').style.display='block');}
function apiPost(url,body){return fetch(url,{method:'POST',headers:body?{'Content-Type':'application/json'}:{},body:body?JSON.stringify(body):undefined}).then(r=>{if(r.status===401){location.href='/login';return null;}if(!r.ok)throw new Error('HTTP '+r.status);return r.json();});}
function showErr(msg){var e=document.getElementById('errMsg');e.textContent=msg;e.style.display='block';}

const diagIcos = { ok: '<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke-width="2.5"><path d="M20 6L9 17l-5-5"/></svg>', warn: '<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke-width="2.5"><circle cx="12" cy="12" r="10"/><line x1="12" y1="8" x2="12" y2="12"/><line x1="12" y1="16" x2="12.01" y2="16"/></svg>', error: '<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke-width="2.5"><circle cx="12" cy="12" r="10"/><line x1="15" y1="9" x2="9" y2="15"/><line x1="9" y1="9" x2="15" y2="15"/></svg>', info: '<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke-width="2.5"><circle cx="12" cy="12" r="10"/><line x1="12" y1="16" x2="12" y2="12"/><line x1="12" y1="8" x2="12.01" y2="8"/></svg>' };
function loadDiag() { const btn=document.getElementById('diagRefreshBtn'); if(btn) btn.disabled=true; fetch('/api/diagnostics').then(r=>r.json()).then(d=>{ if(btn) btn.disabled=false; const g=document.getElementById('diagGrid'); if(!g||!d||!d.items)return; g.innerHTML=d.items.map(i=>'<div class="diag-card '+i.type+'"><div class="diag-ico '+i.type+'">'+diagIcos[i.type]+'</div><div class="diag-body"><div class="diag-title">'+i.title+'</div><div class="diag-msg">'+i.msg+'</div>'+(i.action?'<div class="diag-msg" style="margin-top:4px;color:var(--acc2)">วิธีแก้: '+i.action+'</div>':'')+(i.actBtn?'<div class="diag-act"><button '+(i.actBtn==='fixMissing'||i.actBtn==='fixOrphan'?'class="diag-btn-danger" ':'')+'onclick="'+i.actBtn+'()">'+(i.actBtn==='fixMissing'?'ลบโพสต์ไฟล์หาย':i.actBtn==='fixOrphan'?'ลบไฟล์ขยะ':'แก้ไข')+'</button></div>':'')+'</div></div>').join(''); }).catch(()=>{if(btn) btn.disabled=false;}); }
function fixMissing() { if(!confirm('ลบโพสต์ที่ไฟล์หายไปจาก DB ทั้งหมด?'))return; apiPost('/api/fix-missing').then(d=>{if(!d)return;toast('ลบไป '+d.cleared+' โพสต์','ok');loadDiag();load();}).catch(e=>showErr(e.message)); }
function fixOrphan() { if(!confirm('ลบไฟล์ตกค้างทั้งหมดทิ้ง? (ไม่สามารถกู้ได้)'))return; apiPost('/api/fix-orphan').then(d=>{if(!d)return;toast('ลบไป '+d.cleared+' ไฟล์','ok');loadDiag();}).catch(e=>showErr(e.message)); }

function startProcess(){document.getElementById('startBtn').disabled=true;apiPost('/api/process').then(d=>{document.getElementById('startBtn').disabled=false;if(!d)return;if(d.queued===-1)toast('กำลังแปลงอยู่แล้ว');else if(d.queued===0)toast('ไม่มีวิดีโอที่ต้องแปลง','ok');else{toast('เริ่มแปลง '+d.queued+' ไฟล์','ok');pollTimer=pollTimer||setInterval(load,2000);load();}}).catch(e=>{document.getElementById('startBtn').disabled=false;showErr(e.message);});}
function forceProcess(){if(!confirm('บังคับแปลงใหม่ทั้งหมด?'))return;document.getElementById('forceBtn').disabled=true;apiPost('/api/process-force').then(d=>{document.getElementById('forceBtn').disabled=false;if(!d)return;if(d.queued===-1)toast('รอเสร็จก่อน','err');else if(d.queued===0)toast('ไม่มีวิดีโอ','err');else{toast('บังคับแปลง '+d.queued+' ไฟล์','ok');pollTimer=pollTimer||setInterval(load,2000);load();}}).catch(e=>{document.getElementById('forceBtn').disabled=false;showErr(e.message);});}
function refetchMeta(force){var bi=force?'metaAllBtn':'metaBtn',btn=document.getElementById(bi);btn.disabled=true;btn.textContent='กำลังรี...';apiPost('/api/refetch-meta',{force:!!force}).then(d=>{if(!d){btn.disabled=false;btn.textContent=force?'รีทั้งหมด':'รีเฟรช Meta';return;}if(d.queued===-1){btn.disabled=false;btn.textContent=force?'รีทั้งหมด':'รีเฟรช Meta';toast('กำลังรีอยู่แล้ว');return;}if(d.queued===0){btn.disabled=false;btn.textContent=force?'รีทั้งหมด':'รีเฟรช Meta';toast('ทุกไฟล์มี Meta แล้ว','ok');return;}toast('รีเฟรช Meta '+d.queued+' ไฟล์...');var t=setInterval(()=>fetch('/api/meta-status').then(r=>r.json()).then(s=>{if(s.running){btn.textContent=(force?'รีทั้งหมด':'รีเฟรช Meta')+' ('+s.done+'/'+s.total+')';}else{clearInterval(t);btn.disabled=false;btn.textContent=force?'รีทั้งหมด':'รีเฟรช Meta';toast('รีเฟรช Meta เสร็จ','ok');load();loadDiag();}}),1500);}).catch(e=>{btn.disabled=false;btn.textContent=force?'รีทั้งหมด':'รีเฟรช Meta';showErr(e.message);});}
function clearBroken(){var n=allItems.filter(x=>x.broken).length;if(!confirm('ล้าง broken flag '+n+' ไฟล์?'))return;var btn=document.getElementById('clearBrokenBtn');btn.disabled=true;apiPost('/api/clear-broken').then(d=>{btn.disabled=false;if(!d)return;toast('ล้าง broken '+d.cleared+' ไฟล์แล้ว','ok');load();loadDiag();}).catch(e=>{btn.disabled=false;showErr(e.message);});}
function genThumbs(){var btn=document.getElementById('thumbBtn');btn.disabled=true;btn.textContent='กำลังสร้าง...';apiPost('/api/generate-thumbs').then(d=>{if(!d){btn.disabled=false;btn.innerHTML='${SVG.image} สร้างปก';return;}if(d.queued===-1){btn.disabled=false;btn.innerHTML='${SVG.image} สร้างปก';toast('กำลังสร้างอยู่แล้ว');return;}if(d.queued===0){btn.disabled=false;btn.innerHTML='${SVG.image} สร้างปก';toast('ทุกไฟล์มีปกแล้ว','ok');return;}toast('กำลังสร้างปก '+d.queued+' ไฟล์...','ok');var t=setInterval(()=>fetch('/api/thumb-status').then(r=>r.json()).then(s=>{if(s.running){btn.textContent='สร้างปก ('+s.done+'/'+s.total+')';}else{clearInterval(t);btn.disabled=false;btn.innerHTML='${SVG.image} สร้างปก';toast('สร้างปกเสร็จแล้ว','ok');loadDiag();}}),1500);}).catch(e=>{btn.disabled=false;btn.innerHTML='${SVG.image} สร้างปก';showErr(e.message);});}
function forceGenThumbs(){if(!confirm('ลบปกทั้งหมดแล้วสร้างใหม่? จะลบโฟลเดอร์ thumbs/ ทั้งหมด!'))return;var btn=document.getElementById('forceThumbBtn');btn.disabled=true;btn.textContent='กำลังลบ...';apiPost('/api/force-generate-thumbs').then(d=>{if(!d){btn.disabled=false;btn.innerHTML='${SVG.fwd} บังคับสร้างปกใหม่';return;}if(d.queued===-1){btn.disabled=false;btn.innerHTML='${SVG.fwd} บังคับสร้างปกใหม่';toast('รอเสร็จก่อน','err');return;}if(d.queued===0){btn.disabled=false;btn.innerHTML='${SVG.fwd} บังคับสร้างปกใหม่';toast('ไม่มีวิดีโอ','err');return;}toast('ลบปกเก่าและสร้างใหม่ '+d.queued+' ไฟล์...','ok');var t=setInterval(()=>fetch('/api/thumb-status').then(r=>r.json()).then(s=>{if(s.running){btn.textContent='สร้างปกใหม่ ('+s.done+'/'+s.total+')';}else{clearInterval(t);btn.disabled=false;btn.innerHTML='${SVG.fwd} บังคับสร้างปกใหม่';toast('สร้างปกใหม่เสร็จแล้ว','ok');load();loadDiag();}}),1500);}).catch(e=>{btn.disabled=false;btn.innerHTML='${SVG.fwd} บังคับสร้างปกใหม่';showErr(e.message);});}
load();loadDiag();
</script></body></html>`;
}

// ════════════════════════════════════════════════════════
// MEDIA STATS PAGE
// ════════════════════════════════════════════════════════
function buildMediaStatsHTML() {
    const db = readDB(), posts = db.posts || [];
    let totalFiles = 0, videoFiles = 0, imageFiles = 0, videoConvDone = 0, videoConvPend = 0, totalSizeBytes = 0;
    const rows = [];
    posts.forEach(post => { const isVideo = post.type === 'video'; (post.files || []).forEach(fname => { const fp = path.join(UPLOAD_DIR, fname); let size = 0; try { size = fs.statSync(fp).size; } catch { } totalFiles++; totalSizeBytes += size; if (isVideo) { videoFiles++; const cr = post.convFile && fs.existsSync(path.join(VIDEO_DIR, post.convFile)); if (cr) videoConvDone++; else videoConvPend++; rows.push({ name: fname, type: 'video', size, convReady: !!cr, thumb: post.thumb || '', createdAt: post.createdAt }); } else { imageFiles++; rows.push({ name: fname, type: 'image', size, convReady: true, imgSrc: fname, createdAt: post.createdAt }); } }); });
    rows.sort((a, b) => new Date(b.createdAt) - new Date(a.createdAt));
    function fmtSize(b) { if (b >= 1073741824) return (b / 1073741824).toFixed(2) + ' GB'; if (b >= 1048576) return (b / 1048576).toFixed(1) + ' MB'; if (b >= 1024) return Math.round(b / 1024) + ' KB'; return b + ' B'; }
    const dayMap = {}; rows.forEach(r => { const d = new Date(r.createdAt), k = d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0'); if (!dayMap[k]) dayMap[k] = { video: 0, image: 0, label: d.toLocaleDateString('th-TH', { day: '2-digit', month: 'short', year: '2-digit' }) }; if (r.type === 'video') dayMap[k].video++; else dayMap[k].image++; });
    const dayKeys = Object.keys(dayMap).sort().reverse();
    const tableRows = rows.map((r, i) => {
        const sn = r.name.length > 30 ? r.name.slice(0, 28) + '…' : r.name, dt = new Date(r.createdAt).toLocaleDateString('th-TH', { day: '2-digit', month: '2-digit', year: '2-digit' });
        const tb = r.type === 'video' ? '<span style="background:rgba(255,115,0,.12);color:#ff7300;border-radius:4px;padding:2px 7px;font-size:10px;font-weight:700">VDO</span>' : '<span style="background:rgba(99,102,241,.12);color:#818cf8;border-radius:4px;padding:2px 7px;font-size:10px;font-weight:700">IMG</span>';
        const sb = r.type === 'video' ? (r.convReady ? '<span style="color:#22c55e;font-size:10px;font-weight:700">✓ พร้อม</span>' : '<span style="color:#ef4444;font-size:10px;font-weight:700">✗ ยังไม่แปลง</span>') : '<span style="color:#6b7280;font-size:10px">—</span>';
        const th = r.imgSrc ? '<img src="/uploads/' + r.imgSrc + '" style="width:32px;height:44px;object-fit:cover;border-radius:4px">' : r.type === 'video' && r.thumb && r.thumb[0] !== '_' ? '<img src="/thumbs/' + r.thumb + '" style="width:32px;height:44px;object-fit:cover;border-radius:4px">' : '<div style="width:32px;height:44px;background:var(--s3);border-radius:4px"></div>';
        return '<tr><td style="color:var(--muted);font-family:JetBrains Mono,monospace;font-size:10px;text-align:center">' + (i + 1) + '</td><td>' + th + '</td><td class="fname">' + sn + '</td><td style="text-align:center">' + tb + '</td><td style="font-family:JetBrains Mono,monospace;font-size:11px;text-align:right">' + fmtSize(r.size) + '</td><td style="text-align:center">' + sb + '</td><td style="font-size:10px;color:var(--muted);text-align:center">' + dt + '</td></tr>';
    }).join('');
    return `<!DOCTYPE html>
<html lang="th"><head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>MyVault · สถิติไฟล์</title>
<link href="https://fonts.googleapis.com/css2?family=Space+Grotesk:wght@400;500;600;700&family=JetBrains+Mono:wght@400;600&display=swap" rel="stylesheet">
<style>
*{margin:0;padding:0;box-sizing:border-box}
:root{--bg:#0d0900;--s1:#150e00;--s2:#1e1500;--s3:#2a1e00;--acc:#ff7300;--acc2:#ffaa33;--txt:#fff5e6;--muted:#887755;--border:#2e2010}
body{background:var(--bg);color:var(--txt);font-family:'Space Grotesk',sans-serif;min-height:100vh;padding:24px 16px}
h1{font-size:20px;font-weight:800;margin-bottom:4px;color:var(--acc2)}.sub{font-size:12px;color:var(--muted);margin-bottom:20px}
.topbar{display:flex;align-items:center;justify-content:space-between;margin-bottom:24px;flex-wrap:wrap;gap:10px}
.btn{background:rgba(255,115,0,.12);border:1px solid rgba(255,115,0,.25);border-radius:8px;color:var(--acc2);font-size:12px;font-weight:600;padding:7px 12px;cursor:pointer;text-decoration:none;display:inline-flex;align-items:center;gap:5px;font-family:'Space Grotesk',sans-serif;transition:background .15s}
.btn:hover{background:rgba(255,115,0,.25)}.btn.danger{background:rgba(239,68,68,.08);border-color:rgba(239,68,68,.25);color:#fca5a5}
.summary{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:10px;margin-bottom:24px}
.card{background:var(--s2);border:1px solid var(--border);border-radius:14px;padding:18px 16px}
.card-n{font-size:32px;font-weight:800;line-height:1;font-family:'JetBrains Mono',monospace}.card-l{font-size:11px;color:var(--muted);margin-top:4px}.card-sub{font-size:10px;color:var(--muted);margin-top:2px;font-family:'JetBrains Mono',monospace}
.bar-wrap{background:var(--s3);border-radius:99px;height:8px;margin-bottom:24px;overflow:hidden;display:flex}
.bar-seg{height:100%}
.filter-row{display:flex;gap:6px;margin-bottom:14px;flex-wrap:wrap}
.ftab{background:transparent;border:1px solid var(--border);border-radius:6px;color:var(--muted);font-size:11px;font-weight:600;padding:5px 12px;cursor:pointer;font-family:'Space Grotesk',sans-serif;transition:all .15s}
.ftab.on{background:rgba(255,115,0,.12);border-color:rgba(255,115,0,.35);color:var(--acc2)}
.table-wrap{overflow-x:auto;border:1px solid var(--border);border-radius:12px;overflow:hidden}
table{width:100%;border-collapse:collapse;font-size:12px}
th{text-align:left;padding:10px 12px;color:var(--muted);font-weight:600;border-bottom:1px solid var(--border);background:var(--s2);white-space:nowrap}
td{padding:8px 12px;border-bottom:1px solid rgba(46,32,16,.4);vertical-align:middle}
tr:last-child td{border-bottom:none}.fname{font-family:'JetBrains Mono',monospace;color:var(--muted);font-size:10px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.search-wrap input{background:var(--s2);border:1px solid var(--border);border-radius:8px;color:var(--txt);font-size:12px;padding:8px 12px;width:100%;max-width:320px;font-family:'Space Grotesk',sans-serif;outline:none;margin-bottom:14px}
.search-wrap input:focus{border-color:rgba(255,115,0,.4)}
</style></head><body>
<div class="topbar">
  <div><h1>สถิติไฟล์</h1><div class="sub">นับไฟล์จริงทุกใบ · <a href="/admin" style="color:var(--acc2)">← กลับ Admin</a></div></div>
  <div style="display:flex;gap:8px;flex-wrap:wrap">
    <a href="/status" class="btn">Status</a><a href="/analytics" class="btn">Analytics</a>
    <a href="#" class="btn danger" onclick="fetch('/api/logout',{method:'POST'});window.location='/login';return false">ออก</a>
  </div>
</div>
<div class="summary">
  <div class="card"><div class="card-n">${totalFiles}</div><div class="card-l">ไฟล์ทั้งหมด</div><div class="card-sub">${fmtSize(totalSizeBytes)}</div></div>
  <div class="card"><div class="card-n" style="color:#818cf8">${imageFiles}</div><div class="card-l">รูปภาพ</div><div class="card-sub">${totalFiles > 0 ? Math.round(imageFiles / totalFiles * 100) : 0}%</div></div>
  <div class="card"><div class="card-n" style="color:var(--acc)">${videoFiles}</div><div class="card-l">วิดีโอ</div><div class="card-sub">${totalFiles > 0 ? Math.round(videoFiles / totalFiles * 100) : 0}%</div></div>
  <div class="card"><div class="card-n" style="color:#22c55e">${videoConvDone}</div><div class="card-l">วิดีโอแปลงแล้ว</div><div class="card-sub">${videoFiles > 0 ? Math.round(videoConvDone / videoFiles * 100) : 0}%</div></div>
  <div class="card"><div class="card-n" style="color:#ef4444">${videoConvPend}</div><div class="card-l">ยังไม่แปลง</div><div class="card-sub">${posts.length} โพสต์</div></div>
</div>
<div class="bar-wrap">
  <div class="bar-seg" style="width:${totalFiles > 0 ? Math.round(imageFiles / totalFiles * 100) : 0}%;background:linear-gradient(90deg,#6366f1,#818cf8)"></div>
  <div class="bar-seg" style="width:${totalFiles > 0 ? Math.round(videoFiles / totalFiles * 100) : 0}%;background:linear-gradient(90deg,#ff7300,#ffaa33)"></div>
</div>
${dayKeys.length > 0 ? `<div style="background:var(--s2);border:1px solid var(--border);border-radius:14px;padding:18px 16px;margin-bottom:20px">
<div style="font-size:13px;font-weight:700;margin-bottom:12px">ไฟล์ที่อัพโหลดแต่ละวัน</div>
<div style="overflow-x:auto"><table style="width:100%;border-collapse:collapse;font-size:12px">
<thead><tr><th style="text-align:left;padding:6px 10px;color:var(--muted);font-weight:600;border-bottom:1px solid var(--border)">วันที่</th><th style="text-align:right;padding:6px 10px;color:#ff7300;border-bottom:1px solid var(--border)">วิดีโอ</th><th style="text-align:right;padding:6px 10px;color:#818cf8;border-bottom:1px solid var(--border)">รูปภาพ</th><th style="text-align:right;padding:6px 10px;border-bottom:1px solid var(--border)">รวม</th><th style="padding:6px 10px;border-bottom:1px solid var(--border)"></th></tr></thead>
<tbody>${dayKeys.map((k, i) => `<tr style="${i % 2 ? 'background:rgba(255,255,255,.015)' : ''}"><td style="font-family:JetBrains Mono,monospace;font-size:11px;color:var(--muted)">${dayMap[k].label}</td><td style="font-family:JetBrains Mono,monospace;font-size:13px;font-weight:700;color:#ff7300;text-align:right">${dayMap[k].video}</td><td style="font-family:JetBrains Mono,monospace;font-size:13px;font-weight:700;color:#818cf8;text-align:right">${dayMap[k].image}</td><td style="font-family:JetBrains Mono,monospace;font-size:13px;font-weight:700;text-align:right">${dayMap[k].video + dayMap[k].image}</td><td style="text-align:right"><button class="del-day-btn" data-date="${k}" data-count="${dayMap[k].video + dayMap[k].image}" style="background:rgba(239,68,68,.1);border:1px solid rgba(239,68,68,.25);color:#fca5a5;border-radius:6px;padding:3px 10px;font-size:11px;font-weight:600;cursor:pointer">ลบทั้งวัน</button></td></tr>`).join('')}</tbody>
</table></div></div>`: ''}
<div class="search-wrap"><input type="text" id="srch" placeholder="ค้นหาชื่อไฟล์…" oninput="filterTable()"></div>
<div class="filter-row">
  <button class="ftab on" onclick="setF('all',this)">ทั้งหมด (${totalFiles})</button>
  <button class="ftab" onclick="setF('image',this)">รูปภาพ (${imageFiles})</button>
  <button class="ftab" onclick="setF('video',this)">วิดีโอ (${videoFiles})</button>
  ${videoConvPend > 0 ? `<button class="ftab" onclick="setF('pending',this)">ยังไม่แปลง (${videoConvPend})</button>` : ''}
</div>
<div class="table-wrap"><table id="mainTable">
  <thead><tr><th style="width:36px;text-align:center">#</th><th style="width:40px">ภาพ</th><th>ชื่อไฟล์</th><th style="text-align:center">ประเภท</th><th style="text-align:right">ขนาด</th><th style="text-align:center">สถานะ</th><th style="text-align:center">วันที่</th></tr></thead>
  <tbody id="tbody">${tableRows}</tbody>
</table></div>
<div style="margin-top:24px">
  <div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:12px;flex-wrap:wrap;gap:8px">
    <div><div style="font-size:13px;font-weight:700">ตรวจสอบความสมบูรณ์</div><div style="font-size:11px;color:var(--muted);margin-top:2px">เปรียบเทียบ DB กับดิสก์จริง</div></div>
    <button class="btn" onclick="loadAudit()">รีเฟรช</button>
  </div>
  <div id="auditResult"><span style="color:var(--muted);font-size:12px">กำลังโหลด...</span></div>
</div>
<script>
var curF='all',rows=document.querySelectorAll('#tbody tr');
function setF(f,el){curF=f;document.querySelectorAll('.ftab').forEach(b=>b.classList.remove('on'));el.classList.add('on');filterTable();}
function filterTable(){var q=document.getElementById('srch').value.toLowerCase();rows.forEach(r=>{var fn=r.querySelector('.fname'),nm=!fn||fn.textContent.toLowerCase().includes(q),tc=r.cells[3]?r.cells[3].textContent.trim():'';var tm=curF==='all'||(curF==='image'&&tc.includes('IMG'))||(curF==='video'&&tc.includes('VDO'))||(curF==='pending'&&r.cells[5]&&r.cells[5].textContent.includes('ยังไม่แปลง'));r.style.display=(nm&&tm)?'':'none';});var i=1;rows.forEach(r=>{if(r.style.display!=='none')r.cells[0].textContent=i++;});}
function fmtSz(b){if(!b)return'0 B';if(b>=1073741824)return(b/1073741824).toFixed(2)+' GB';if(b>=1048576)return(b/1048576).toFixed(1)+' MB';if(b>=1024)return Math.round(b/1024)+' KB';return b+' B';}
function loadAudit(){document.getElementById('auditResult').innerHTML='<span style="color:var(--muted);font-size:12px">กำลังตรวจสอบ...</span>';fetch('/api/file-audit').then(r=>r.json()).then(d=>{var s=d.summary,html='<div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:10px;margin-bottom:16px"><div class="card"><div class="card-n">'+s.dbPosts+'</div><div class="card-l">โพสต์ใน DB</div></div><div class="card"><div class="card-n">'+s.dbFiles+'</div><div class="card-l">ไฟล์ใน DB</div></div><div class="card"><div class="card-n">'+s.diskUploads+'</div><div class="card-l">ไฟล์บนดิสก์</div></div><div class="card"><div class="card-n" style="color:'+(s.orphanCount>0?'#f59e0b':'#22c55e')+'">'+s.orphanCount+'</div><div class="card-l">Orphan files</div><div class="card-sub">'+fmtSz(s.orphanSize)+'</div></div><div class="card"><div class="card-n" style="color:'+(s.missingCount>0?'#ef4444':'#22c55e')+'">'+s.missingCount+'</div><div class="card-l">ไฟล์หายจากดิสก์</div></div></div>';if(s.missingCount>0)html+='<div style="background:rgba(239,68,68,.08);border:1px solid rgba(239,68,68,.2);border-radius:10px;padding:14px;margin-bottom:12px"><div style="font-size:12px;font-weight:700;color:#fca5a5;margin-bottom:8px">⚠ ไฟล์ upload หายจากดิสก์ ('+s.missingCount+')</div>'+fileList(d.missing.uploads,'uploads')+'</div>';if(s.orphanCount>0)html+='<div style="background:rgba(245,158,11,.06);border:1px solid rgba(245,158,11,.18);border-radius:10px;padding:14px;margin-bottom:12px"><div style="font-size:12px;font-weight:700;color:#fbbf24;margin-bottom:8px">📂 ไฟล์บนดิสก์ไม่มีใน DB ('+s.orphanCount+' ไฟล์ · '+fmtSz(s.orphanSize)+')</div>'+fileList(d.orphan.uploads,'uploads')+'</div>';if(s.missingCount===0&&s.orphanCount===0)html+='<div style="background:rgba(34,197,94,.08);border:1px solid rgba(34,197,94,.2);border-radius:10px;padding:14px;font-size:12px;color:#86efac">✓ ทุกไฟล์ตรงกันหมด</div>';document.getElementById('auditResult').innerHTML=html;}).catch(()=>document.getElementById('auditResult').innerHTML='<span style="color:#fca5a5;font-size:12px">ตรวจสอบไม่สำเร็จ</span>');}
function fileList(arr,label){if(!arr||!arr.length)return'';return'<div style="margin-bottom:6px"><span style="font-size:10px;color:var(--muted);margin-right:6px">'+label+':</span>'+arr.slice(0,30).map(f=>'<span style="display:inline-block;background:var(--s3);border-radius:4px;padding:1px 6px;margin:2px;font-size:10px;font-family:JetBrains Mono,monospace;color:var(--muted)">'+f+'</span>').join('')+(arr.length>30?'<span style="font-size:10px;color:var(--muted)"> +อีก '+(arr.length-30)+'</span>':'')+'</div>';}
loadAudit();
document.addEventListener('click',e=>{var btn=e.target.closest('.del-day-btn');if(!btn)return;var dk=btn.dataset.date,cnt=btn.dataset.count;if(!confirm('ลบไฟล์ทั้งหมดของวัน '+dk+' ('+cnt+' รายการ)?'))return;btn.disabled=true;btn.textContent='กำลังลบ...';fetch('/api/delete-by-date',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({date:dk})}).then(r=>r.json()).then(d=>{if(d&&d.ok)location.reload();else{btn.disabled=false;btn.textContent='ลบทั้งวัน';}}).catch(()=>{btn.disabled=false;btn.textContent='ลบทั้งวัน';});});
</script></body></html>`;
}

// ════════════════════════════════════════════════════════
// LOGIN HTML
// ════════════════════════════════════════════════════════
function buildLoginHTML() {
    return `<!DOCTYPE html>
<html lang="th"><head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no">
<title>MyVault · เข้าสู่ระบบ</title>
<link href="https://fonts.googleapis.com/css2?family=Syne:wght@700;800&family=Inter:wght@400;500;600&display=swap" rel="stylesheet">
<style>
*{margin:0;padding:0;box-sizing:border-box}
:root{--bg:#0d0900;--s1:#150e00;--s3:#2a1e00;--acc:#ff7300;--acc2:#ffaa33;--border:#2e2010;--txt:#fff5e6;--muted:#887755}
html,body{height:100%;background:var(--bg);color:var(--txt);font-family:'Inter',sans-serif;display:flex;align-items:center;justify-content:center}
.wrap{width:100%;max-width:360px;padding:24px 20px}
.brand{font-family:'Syne',sans-serif;font-size:32px;font-weight:800;letter-spacing:-1px;display:flex;align-items:center;gap:10px;margin-bottom:6px}
.dot{width:12px;height:12px;border-radius:50%;background:linear-gradient(135deg,var(--acc),var(--acc2));flex-shrink:0}
.sub{font-size:13px;color:var(--muted);margin-bottom:36px}
.card{background:var(--s1);border:1px solid var(--border);border-radius:18px;padding:24px 20px}
.card h2{font-family:'Syne',sans-serif;font-size:18px;font-weight:700;margin-bottom:18px}
.field{margin-bottom:14px}.field label{display:block;font-size:11px;font-weight:600;color:var(--muted);margin-bottom:6px;text-transform:uppercase;letter-spacing:.5px}
.field input{width:100%;background:var(--s3);border:1px solid var(--border);border-radius:10px;padding:12px 14px;color:var(--txt);font-size:14px;outline:none;transition:border-color .2s}
.field input:focus{border-color:var(--acc)}
.err{font-size:12px;color:#ff6644;margin-bottom:12px;min-height:18px}
.btn{width:100%;background:linear-gradient(135deg,var(--acc),var(--acc2));border:none;border-radius:11px;padding:14px;color:#000;font-size:14px;font-weight:700;cursor:pointer;transition:opacity .2s}
.btn:hover{opacity:.9}
.guest{margin-top:14px;text-align:center}.guest a{font-size:13px;color:var(--muted);text-decoration:none;border-bottom:1px solid var(--border);padding-bottom:1px}
</style></head><body>
<div class="wrap">
  <div class="brand"><div class="dot"></div>MyVault</div>
  <div class="sub">ระบบจัดเก็บมีเดียส่วนตัว</div>
  <div class="card">
    <h2>เข้าสู่ระบบ Admin</h2>
    <div class="field"><label>รหัสผ่าน</label><input type="password" id="pw" placeholder="••••••••" autocomplete="current-password"></div>
    <div class="err" id="err"></div>
    <button class="btn" onclick="doLogin()">เข้าสู่ระบบ</button>
    <div class="guest"><a href="/guest">ดูในฐานะผู้เยี่ยมชม →</a></div>
  </div>
</div>
<script>
document.getElementById('pw').addEventListener('keydown',e=>{if(e.key==='Enter')doLogin();});
function doLogin(){var pw=document.getElementById('pw').value,err=document.getElementById('err');if(!pw){err.textContent='กรุณากรอกรหัสผ่าน';return;}err.textContent='';fetch('/api/login',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({password:pw})}).then(r=>r.json()).then(d=>{if(d.ok)location.href='/admin';else err.textContent='รหัสผ่านไม่ถูกต้อง';}).catch(()=>err.textContent='เกิดข้อผิดพลาด');}
</script></body></html>`;
}

// ════════════════════════════════════════════════════════
// MAIN APP HTML
// ════════════════════════════════════════════════════════
function buildHTML(isAdmin) {
    const fabBtn = isAdmin ? `<button class="fab" onclick="goUpload()" title="อัพโหลด">${SVG.upload}</button>` : '';
    const topAct = isAdmin
        ? `<div style="display:flex;gap:6px;align-items:center"><a class="top-act" href="/analytics">${SVG.chart}</a><a class="top-act" href="/status">${SVG.status}</a><button class="top-act" onclick="doLogout()">${SVG.logout}</button></div>`
        : `<a class="top-act" href="/login">Admin</a>`;
    const delBtn = isAdmin ? `<button class="del-btn" onclick="askDelete()">${SVG.trash}</button><button class="conv-btn" id="convBtn" onclick="requestConvertCur()" style="display:none"></button>` : '';
    const uploadScreen = isAdmin ? `
<div class="screen" id="su">
  <div class="uh"><button class="ub" onclick="goVault()">${SVG.back} กลับ</button><div class="ut">อัพโหลด</div><div class="us">วิดีโอ / รูปภาพ · ขนาดไม่จำกัด</div></div>
  <div class="dz" id="dz"><input type="file" id="fi" multiple accept="image/*,video/*"><span class="dz-ic">${SVG.upload}</span><div class="dz-t">แตะหรือลากวางไฟล์</div><div class="dz-s">หลายไฟล์พร้อมกันได้</div><div class="dz-ps"><span class="dz-p">MP4</span><span class="dz-p">MOV</span><span class="dz-p">WEBM</span><span class="dz-p">MKV</span><span class="dz-p">JPG</span><span class="dz-p">PNG</span><span class="dz-p">GIF</span><span class="dz-p">WEBP</span></div></div>
  <div class="su-body"><div id="gl"></div>
    <div class="ubot" id="ubot" style="display:none">
      <div class="pb-wrap" id="pbw"><div class="pb-fill" id="pbf"></div></div>
      <div class="ub-row" style="flex-direction:column;gap:6px">
        <div style="display:flex;justify-content:space-between;align-items:center;width:100%"><span class="ub-cnt" id="ucnt"></span><span id="uploadSpeed" style="font-size:11px;font-family:JetBrains Mono,monospace;color:var(--acc2)"></span></div>
        <button class="up-btn" id="ubtn" onclick="doUpload()"><span class="bt">${SVG.upload} บันทึกทั้งหมด</span><div class="sp"></div></button>
      </div>
    </div>
  </div>
</div>`: '';

    return `<!DOCTYPE html>
<html lang="th"><head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no">
<title>MyVault</title>
<link href="https://fonts.googleapis.com/css2?family=Syne:wght@700;800&family=Inter:wght@400;500;600&display=swap" rel="stylesheet">
<style>
*{margin:0;padding:0;box-sizing:border-box;-webkit-tap-highlight-color:transparent}
:root{--bg:#0d0900;--s1:#150e00;--s2:#1e1500;--s3:#2a1e00;--acc:#ff7300;--acc2:#ffaa33;--txt:#fff5e6;--muted:#887755;--border:#2e2010}
html,body{height:100%;overflow:hidden;background:var(--bg);color:var(--txt);font-family:'Inter',sans-serif}
.screen{position:absolute;inset:0;display:none;flex-direction:column;overflow:hidden}.screen.on{display:flex}
#sv{overflow:hidden}
.v-top{flex-shrink:0;padding:52px 16px 12px;background:linear-gradient(180deg,var(--bg) 60%,transparent);z-index:10}
.v-brand{font-family:'Syne',sans-serif;font-size:26px;font-weight:800;letter-spacing:-1px;display:flex;align-items:center;gap:8px}
.v-brand-row{display:flex;align-items:center;justify-content:space-between}
.top-act{background:rgba(255,115,0,.1);border:1px solid rgba(255,115,0,.22);border-radius:20px;padding:6px 11px;font-size:11px;font-weight:600;color:var(--acc2);cursor:pointer;font-family:'Inter',sans-serif;text-decoration:none;display:inline-flex;align-items:center;gap:5px;transition:background .15s;white-space:nowrap}
.top-act:hover{background:rgba(255,115,0,.2)}.top-act svg{width:13px;height:13px;stroke:currentColor;fill:none;stroke-width:2;flex-shrink:0}
.top-right{display:flex;align-items:center;gap:8px}
.vfs-btn{width:30px;height:30px;border-radius:50%;border:none;cursor:pointer;background:rgba(255,255,255,.07);display:flex;align-items:center;justify-content:center;flex-shrink:0;transition:background .15s}
.vfs-btn:hover{background:rgba(255,115,0,.2)}.vfs-btn svg{width:14px;height:14px;stroke:var(--muted);fill:none;stroke-width:2.2}
.v-brand .dot{width:10px;height:10px;border-radius:50%;background:linear-gradient(135deg,var(--acc),var(--acc2))}
.v-meta{font-size:12px;color:var(--muted);margin-top:2px}
.v-tabs{display:flex;gap:6px;margin-top:12px;overflow-x:auto;scrollbar-width:none;padding-bottom:2px}
.v-tabs::-webkit-scrollbar{display:none}
.vtab{background:var(--s2);border:1px solid var(--border);border-radius:20px;padding:5px 13px;font-size:12px;font-weight:600;color:var(--muted);cursor:pointer;transition:all .15s;font-family:'Inter',sans-serif;flex-shrink:0;display:inline-flex;align-items:center;gap:5px}
.vtab svg{width:11px;height:11px;stroke:currentColor;fill:none;stroke-width:2.5}.vtab.on{background:var(--acc);border-color:var(--acc);color:#000}.vtab.on svg{stroke:#000}
.v-scroll{flex:1;overflow-y:auto;padding:0 3px 100px;scrollbar-width:none;-webkit-overflow-scrolling:touch}
.v-scroll::-webkit-scrollbar{display:none}
.v-grid{display:grid;grid-template-columns:repeat(3,1fr);gap:3px;padding:3px}
.v-item{aspect-ratio:9/16;position:relative;overflow:hidden;background:var(--s2);cursor:pointer;border-radius:6px;transform:translateZ(0);transition:transform .15s}
.v-item:active{transform:scale(.97) translateZ(0)}
.v-item img{position:absolute;inset:0;width:100%;height:100%;object-fit:cover}
.vi-type{position:absolute;top:5px;left:5px;width:18px;height:18px;background:rgba(0,0,0,.55);border-radius:4px;display:flex;align-items:center;justify-content:center;backdrop-filter:blur(4px)}
.vi-type svg{width:9px;height:9px;stroke:#fff;fill:none;stroke-width:2.2}.vi-type.isv svg{fill:#fff;stroke:none}
.vi-set{position:absolute;top:5px;right:5px;background:rgba(0,0,0,.6);border-radius:4px;padding:2px 5px;font-size:9px;font-weight:700;color:#fff}
.vi-cap{position:absolute;bottom:0;left:0;right:0;background:linear-gradient(to top,rgba(0,0,0,.72),transparent);padding:16px 6px 5px;font-size:9px;color:rgba(255,245,230,.8);overflow:hidden;white-space:nowrap;text-overflow:ellipsis}
.vi-ov{position:absolute;inset:0;background:rgba(0,0,0,.3);display:flex;align-items:center;justify-content:center;opacity:0;transition:opacity .12s}
.v-item:hover .vi-ov{opacity:1}.vi-ov svg{width:26px;height:26px;fill:rgba(255,255,255,.9)}
.v-empty{grid-column:1/-1;padding:60px 20px;text-align:center}
.v-empty .et{font-family:'Syne',sans-serif;font-size:20px;color:var(--muted);margin-top:12px}.v-empty .es{font-size:12px;color:var(--muted);opacity:.6;margin-top:5px}
.hist-bar{flex-shrink:0;padding:8px 16px;display:flex;align-items:center;justify-content:space-between;background:rgba(255,115,0,.05);border-bottom:1px solid rgba(255,115,0,.12);display:none}
.hist-bar.on{display:flex}.hist-info{font-size:12px;color:var(--muted)}
.hist-clear{background:rgba(255,115,0,.1);border:1px solid rgba(255,115,0,.22);border-radius:8px;color:var(--acc2);font-size:11px;font-weight:700;padding:5px 12px;cursor:pointer;font-family:'Inter',sans-serif;display:inline-flex;align-items:center;gap:5px}
.sort-bar{flex-shrink:0;padding:6px 12px;display:flex;align-items:center;gap:6px;overflow-x:auto;scrollbar-width:none}
.sort-bar::-webkit-scrollbar{display:none}
.sort-btn{background:var(--s2);border:1px solid var(--border);border-radius:20px;padding:4px 11px;font-size:11px;font-weight:600;color:var(--muted);cursor:pointer;font-family:'Inter',sans-serif;white-space:nowrap;display:flex;align-items:center;gap:4px;transition:all .15s;flex-shrink:0}
.sort-btn.on{background:rgba(255,115,0,.12);border-color:rgba(255,115,0,.35);color:var(--acc2)}
.fab{position:fixed;bottom:26px;right:18px;z-index:200;width:52px;height:52px;border-radius:16px;border:none;cursor:pointer;background:linear-gradient(135deg,var(--acc),var(--acc2));display:flex;align-items:center;justify-content:center;box-shadow:0 6px 24px rgba(255,115,0,.4);transition:transform .2s;transform:translateZ(0)}
.fab:hover{transform:scale(1.08) translateZ(0)}.fab:active{transform:scale(.96) translateZ(0)}.fab svg{width:22px;height:22px;stroke:#000;stroke-width:2.8;fill:none}
#svw{background:#000;overflow:hidden}
.rw{height:100%;position:relative;overflow:hidden}
.rt{height:100%;will-change:transform;transition:transform .3s cubic-bezier(.4,0,.2,1);transform:translateZ(0);display:flex;flex-direction:column}
.reel{height:100%;width:100%;position:relative;display:flex;align-items:center;justify-content:center;background:#000;overflow:hidden}
.reel-bg{position:absolute;inset:-20px;background-size:cover;background-position:center;filter:blur(28px) brightness(.35) saturate(1.5);transform:scale(1.1) translateZ(0);z-index:0}
.reel video{width:100%;height:100%;object-fit:contain;display:block;position:relative;z-index:1}
.rg{position:absolute;inset:0;pointer-events:none;z-index:2;background:linear-gradient(to top,rgba(0,0,0,.55) 0%,transparent 35%),linear-gradient(to bottom,rgba(0,0,0,.4) 0%,transparent 20%)}
.vt{position:absolute;top:0;left:0;right:0;z-index:30;display:flex;align-items:center;padding:52px 14px 14px;gap:10px}
.back-btn{width:34px;height:34px;border-radius:50%;border:none;cursor:pointer;background:rgba(0,0,0,.5);backdrop-filter:blur(10px);display:flex;align-items:center;justify-content:center;flex-shrink:0}
.back-btn svg{width:17px;height:17px;stroke:#fff;fill:none;stroke-width:2.2}
.v-title{font-size:13px;color:rgba(255,255,255,.7);font-weight:500;overflow:hidden;white-space:nowrap;text-overflow:ellipsis;flex:1}
.shuf-btn{width:34px;height:34px;border-radius:50%;border:none;cursor:pointer;backdrop-filter:blur(10px);display:flex;align-items:center;justify-content:center;flex-shrink:0}
.shuf-btn svg{width:16px;height:16px;stroke:#fff;fill:none;stroke-width:2}
.shuf-btn.off{background:rgba(0,0,0,.5)}.shuf-btn.on{background:rgba(255,115,0,.5);box-shadow:0 0 10px rgba(255,115,0,.4)}.shuf-btn.on svg{stroke:var(--acc2)}
.nc{position:absolute;top:108px;left:50%;transform:translateX(-50%);background:rgba(0,0,0,.5);backdrop-filter:blur(8px);border-radius:20px;padding:3px 11px;font-size:11px;font-weight:600;color:rgba(255,255,255,.65);z-index:30;opacity:0;transition:opacity .3s;white-space:nowrap;pointer-events:none}
.nc.on{opacity:1}
.del-btn{position:absolute;bottom:max(160px,calc(env(safe-area-inset-bottom)+160px));right:50px;z-index:30;width:38px;height:38px;border-radius:50%;border:none;cursor:pointer;background:rgba(0,0,0,.5);backdrop-filter:blur(8px);display:flex;align-items:center;justify-content:center}
.del-btn svg{width:16px;height:16px;stroke:#ff6644;fill:none;stroke-width:2}
.conv-btn{position:absolute;bottom:max(160px,calc(env(safe-area-inset-bottom)+160px));right:96px;z-index:30;height:38px;border-radius:19px;border:1px solid rgba(255,115,0,.5);cursor:pointer;background:rgba(0,0,0,.5);backdrop-filter:blur(8px);color:#fff;font-size:11px;font-weight:600;font-family:inherit;padding:0 13px;display:flex;align-items:center;gap:5px;white-space:nowrap}
.conv-btn svg{width:13px;height:13px;stroke:currentColor;fill:none;stroke-width:2.5;flex-shrink:0}
.conv-btn.done{border-color:rgba(74,222,128,.4);color:rgba(74,222,128,.9)}
.vc{position:absolute;bottom:0;left:0;right:0;z-index:30;padding:0 14px max(14px,env(safe-area-inset-bottom)) 14px;background:linear-gradient(to top,rgba(0,0,0,.7),transparent);transition:opacity .25s}
.sw{display:flex;align-items:center;gap:8px;margin-bottom:8px}
.tlbl{font-size:11px;font-weight:600;color:rgba(255,255,255,.65);min-width:34px;text-align:center;font-variant-numeric:tabular-nums}
.sb{flex:1;position:relative;cursor:pointer;padding:10px 0;margin:-10px 0}
.sb-bg{position:absolute;top:10px;left:0;right:0;height:3px;background:rgba(255,255,255,.16);border-radius:2px}
.sb-buf{position:absolute;top:10px;left:0;height:3px;background:rgba(255,255,255,.26);border-radius:2px;width:0}
.sb-fill{position:absolute;top:10px;left:0;height:3px;background:var(--acc);border-radius:2px;width:0}
.sb-thumb{position:absolute;top:5px;width:13px;height:13px;border-radius:50%;background:#fff;transform:translateX(-50%);box-shadow:0 1px 4px rgba(0,0,0,.6);left:0}
.cr{display:flex;align-items:center;justify-content:space-between;margin-bottom:5px}
.cl,.cright{display:flex;align-items:center;gap:4px}
.cb{width:36px;height:36px;border-radius:50%;border:none;cursor:pointer;background:rgba(255,255,255,.1);backdrop-filter:blur(8px);display:flex;align-items:center;justify-content:center;transition:background .12s}
.cb:hover{background:rgba(255,115,0,.25)}.cb:active{transform:scale(.92)}.cb svg{width:17px;height:17px;stroke:#fff;fill:none;stroke-width:2;pointer-events:none}
.spd{background:rgba(255,255,255,.1);border:none;border-radius:7px;padding:5px 8px;color:#fff;font-size:12px;font-weight:700;cursor:pointer;backdrop-filter:blur(8px)}
.vw{display:flex;align-items:center;gap:5px}
.vsl{-webkit-appearance:none;width:65px;height:3px;border-radius:2px;background:rgba(255,255,255,.2);outline:none;cursor:pointer}
.vsl::-webkit-slider-thumb{-webkit-appearance:none;width:11px;height:11px;border-radius:50%;background:#fff;cursor:pointer}
.pp{position:absolute;inset:0;display:flex;align-items:center;justify-content:center;pointer-events:none;opacity:0;z-index:25}
.pp.show{animation:ppfade .45s ease forwards}
.pp-c{width:68px;height:68px;border-radius:50%;background:rgba(0,0,0,.45);backdrop-filter:blur(12px);display:flex;align-items:center;justify-content:center;border:1.5px solid rgba(255,115,0,.25)}
.pp-c svg{width:28px;height:28px;fill:#fff}
.car{position:relative;width:100%;height:100%}
.cat{display:flex;height:100%;transition:transform .2s ease}
.cas{min-width:100%;height:100%;flex-shrink:0;position:relative;overflow:hidden;background:#000}
.cas-bg{position:absolute;inset:-20px;background-size:cover;background-position:center;filter:blur(28px) brightness(.35) saturate(1.5);transform:scale(1.1) translateZ(0)}
.cas-fg{position:absolute;inset:0;display:flex;align-items:center;justify-content:center;z-index:1}
.cas-fg img{max-width:100%;max-height:100%;object-fit:contain;display:block}
.cdots{position:absolute;bottom:128px;left:50%;transform:translateX(-50%);display:flex;gap:4px;z-index:20;pointer-events:none}
.cd{width:5px;height:5px;border-radius:50%;background:rgba(255,255,255,.3);transition:all .18s}.cd.on{width:16px;border-radius:3px;background:var(--acc)}
.cnum{position:absolute;top:108px;right:14px;z-index:20;background:rgba(0,0,0,.5);backdrop-filter:blur(8px);border-radius:6px;padding:3px 7px;font-size:11px;font-weight:700;color:rgba(255,255,255,.8)}
#su{flex-direction:column}
.uh{flex-shrink:0;padding:52px 16px 14px;border-bottom:1px solid var(--border);background:var(--s1)}
.ub{background:none;border:none;color:var(--muted);cursor:pointer;font-size:13px;margin-bottom:7px;padding:0;display:inline-flex;align-items:center;gap:5px;font-family:'Inter',sans-serif}
.ub svg{width:13px;height:13px;stroke:currentColor;fill:none;stroke-width:2.2}
.ut{font-family:'Syne',sans-serif;font-size:26px;font-weight:800;letter-spacing:-1px}.us{font-size:12px;color:var(--muted);margin-top:2px}
.dz{flex-shrink:0;margin:10px 12px 4px;border:2px dashed var(--border);border-radius:13px;padding:16px 20px;text-align:center;cursor:pointer;background:var(--s1);transition:all .15s;position:relative;overflow:hidden}
.dz:hover,.dz.drag{border-color:var(--acc);background:rgba(255,115,0,.05)}.dz input{position:absolute;inset:0;opacity:0;cursor:pointer;width:100%;height:100%;z-index:2}
.dz-ic{display:block;margin-bottom:5px;color:var(--muted)}.dz-ic svg{width:38px;height:38px;stroke:currentColor;fill:none;stroke-width:1.5}
.dz-t{font-size:13px;font-weight:700;margin-bottom:2px}.dz-s{font-size:11px;color:var(--muted)}
.dz-ps{display:flex;gap:4px;justify-content:center;flex-wrap:wrap;margin-top:7px}.dz-p{background:var(--s2);border:1px solid var(--border);border-radius:20px;padding:2px 7px;font-size:9px;color:var(--muted);font-weight:600}
.su-body{flex:1;min-height:0;display:flex;flex-direction:column;overflow:hidden}
#gl{flex:1;min-height:0;overflow-y:auto;scrollbar-width:none;-webkit-overflow-scrolling:touch}
#gl::-webkit-scrollbar{display:none}
.fc{background:var(--s2);border:1px solid var(--border);border-radius:12px;margin:6px 12px;overflow:hidden}
.fc-head{display:flex;align-items:center;justify-content:space-between;padding:10px 12px}
.fc-info{display:flex;align-items:center;gap:10px;flex:1;min-width:0}
.fc-ico{width:36px;height:36px;border-radius:8px;display:flex;align-items:center;justify-content:center;flex-shrink:0}
.fc-ico.vid{background:rgba(255,115,0,.15)}.fc-ico.img{background:rgba(99,102,241,.15)}
.fc-ico svg{width:18px;height:18px;stroke:currentColor;fill:none;stroke-width:1.8}
.fc-ico.vid svg{stroke:#ff7300}.fc-ico.img svg{stroke:#818cf8}
.fc-text{flex:1;min-width:0}.fc-name{font-size:12px;font-weight:600;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}.fc-meta{font-size:10px;color:var(--muted);margin-top:1px}
.fc-rm{background:none;border:none;color:var(--muted);cursor:pointer;padding:4px;border-radius:4px;display:flex;align-items:center;flex-shrink:0}
.fc-rm:hover{background:rgba(255,68,0,.15);color:#ff6644}.fc-rm svg{width:14px;height:14px;stroke:currentColor;fill:none;stroke-width:2.2}
.fc-prog{padding:0 12px 10px}.fc-pbar{height:3px;background:var(--s3);border-radius:2px;overflow:hidden}
.fc-pfill{height:100%;width:0;background:linear-gradient(90deg,var(--acc),var(--acc2));border-radius:2px;transition:width .15s}
.fc-ppct{font-size:9px;color:var(--acc2);font-weight:700;margin-top:3px;text-align:right;display:none}
.fc-files{padding:0 12px 8px;display:flex;flex-direction:column;gap:3px}
.fc-frow{display:flex;align-items:center;justify-content:space-between;gap:6px;padding:3px 6px;background:var(--s3);border-radius:6px}
.fc-frow-name{font-size:10px;color:var(--muted);overflow:hidden;text-overflow:ellipsis;white-space:nowrap;flex:1}
.fc-frow-size{font-size:10px;color:var(--muted);flex-shrink:0;font-weight:600}
.fc-frow-rm{background:none;border:none;color:var(--muted);cursor:pointer;padding:2px;border-radius:3px;display:flex;align-items:center;flex-shrink:0}
.fc-frow-rm:hover{color:#ff6644}
.uploading .fc-rm,.uploading .fc-frow-rm{display:none}
.ubot{flex-shrink:0;background:var(--bg);border-top:1px solid var(--border);padding:10px 12px max(13px,env(safe-area-inset-bottom))}
.ub-row{display:flex;align-items:center;gap:10px}.ub-cnt{font-size:12px;color:var(--muted);white-space:nowrap}
.pb-wrap{height:3px;background:var(--border);border-radius:2px;margin-bottom:9px;display:none;overflow:hidden}.pb-wrap.on{display:block}
.pb-fill{height:100%;width:0;background:linear-gradient(90deg,var(--acc),var(--acc2));border-radius:2px}
.up-btn{flex:1;background:linear-gradient(135deg,var(--acc),var(--acc2));border:none;border-radius:11px;padding:13px;color:#000;font-size:14px;font-weight:700;cursor:pointer;transition:opacity .15s;display:flex;align-items:center;justify-content:center;gap:7px}
.up-btn:disabled{opacity:.4;cursor:default}.up-btn svg{width:15px;height:15px;stroke:#000;fill:none;stroke-width:2.5}
.up-btn .sp{display:none;width:15px;height:15px;border:2px solid rgba(0,0,0,.3);border-top-color:#000;border-radius:50%;animation:spin .6s linear infinite}
.up-btn.ld .bt{display:none}.up-btn.ld .sp{display:block}
.toast{position:fixed;top:18px;left:50%;transform:translateX(-50%) translateY(-65px);background:var(--s3);border:1px solid var(--border);border-radius:10px;padding:8px 15px;font-size:13px;font-weight:600;z-index:999;transition:transform .28s cubic-bezier(.4,0,.2,1);white-space:nowrap;box-shadow:0 8px 24px rgba(0,0,0,.5);pointer-events:none}
.toast.on{transform:translateX(-50%) translateY(0)}.toast.ok{border-color:rgba(255,115,0,.35);color:var(--acc2)}.toast.err{border-color:rgba(255,68,0,.35);color:#ff6644}
.mb{position:fixed;inset:0;background:rgba(0,0,0,.72);z-index:500;display:none;align-items:flex-end;justify-content:center;backdrop-filter:blur(4px)}.mb.on{display:flex}
.modal{background:var(--s2);border-radius:18px 18px 0 0;border:1px solid var(--border);padding:22px 18px max(38px,env(safe-area-inset-bottom));width:100%;max-width:500px;text-align:center}
.modal h3{font-family:'Syne',sans-serif;font-size:17px;margin-bottom:7px}.modal p{font-size:13px;color:var(--muted);margin-bottom:18px}
.mbs{display:flex;gap:8px}.mc,.mx{flex:1;border:none;border-radius:11px;padding:12px;font-size:13px;font-weight:700;cursor:pointer;font-family:'Inter',sans-serif}
.mc{background:var(--s3);color:var(--muted)}.mx{background:rgba(255,68,0,.15);color:#ff6644;border:1px solid rgba(255,68,0,.25)}
.mb2{position:fixed;inset:0;background:rgba(0,0,0,.72);z-index:500;display:none;align-items:flex-end;justify-content:center;backdrop-filter:blur(4px)}.mb2.on{display:flex}
.lb-wrap{position:fixed;inset:0;background:rgba(0,0,0,.92);z-index:600;display:none;align-items:center;justify-content:center;backdrop-filter:blur(8px)}.lb-wrap.on{display:flex}
.lb-img{max-width:calc(100vw - 80px);max-height:calc(100vh - 80px);object-fit:contain;border-radius:6px;transition:opacity .18s;user-select:none}
.lb-nav{position:fixed;top:50%;transform:translateY(-50%);background:rgba(255,255,255,.08);border:1px solid rgba(255,255,255,.12);border-radius:50%;width:44px;height:44px;display:flex;align-items:center;justify-content:center;color:#fff;cursor:pointer}
.lb-nav:hover{background:rgba(255,255,255,.18)}.lb-nav-l{left:12px}.lb-nav-r{right:12px}
.lb-counter{position:fixed;bottom:24px;left:50%;transform:translateX(-50%);font-size:12px;color:rgba(255,255,255,.5);pointer-events:none}
.lb-close{position:fixed;top:16px;right:16px;background:rgba(255,255,255,.08);border:1px solid rgba(255,255,255,.12);border-radius:50%;width:40px;height:40px;display:flex;align-items:center;justify-content:center;color:#fff;cursor:pointer}
.shuf-badge{position:fixed;bottom:80px;left:50%;transform:translateX(-50%);background:rgba(255,115,0,.16);border:1px solid rgba(255,115,0,.35);border-radius:20px;padding:5px 14px;font-size:12px;font-weight:700;color:var(--acc2);z-index:400;opacity:0;transition:opacity .25s;pointer-events:none;white-space:nowrap}
.shuf-badge.on{opacity:1}
.shuf-pick{position:fixed;bottom:80px;left:50%;transform:translateX(-50%);background:var(--s2);border:1px solid var(--border);border-radius:16px;padding:8px 6px;display:flex;gap:4px;z-index:500;opacity:0;pointer-events:none;transition:opacity .18s;white-space:nowrap}
.shuf-pick.on{opacity:1;pointer-events:auto}
.shuf-pick button{background:transparent;border:1px solid transparent;border-radius:10px;color:var(--muted);font-size:11px;font-weight:600;padding:5px 12px;cursor:pointer;transition:all .12s;font-family:'Inter',sans-serif}
.shuf-pick button:hover{background:rgba(255,115,0,.12);color:var(--acc2)}.shuf-pick button.act{background:rgba(255,115,0,.18);border-color:rgba(255,115,0,.35);color:var(--acc2)}
@keyframes spin{to{transform:rotate(360deg)}}
@keyframes ppfade{0%{opacity:1}100%{opacity:0;transform:scale(1.1)}}
</style></head><body>

<div class="screen on" id="sv">
  <div class="v-top">
    <div class="v-brand-row">
      <div class="v-brand"><div class="dot"></div>MyVault</div>
      <div class="top-right">
        <button class="vfs-btn" id="vfsBtn" onclick="toggleFullscreen()">
          <svg id="vfsIco" viewBox="0 0 24 24"><path d="M8 3H5a2 2 0 0 0-2 2v3"/><path d="M21 8V5a2 2 0 0 0-2-2h-3"/><path d="M3 16v3a2 2 0 0 0 2 2h3"/><path d="M16 21h3a2 2 0 0 0 2-2v-3"/></svg>
        </button>
        ${topAct}
      </div>
    </div>
    <div class="v-meta" id="vmeta"></div>
    <div class="v-tabs">
      <button class="vtab on" onclick="fvault('all',this)">ทั้งหมด</button>
      <button class="vtab" onclick="fvault('video',this)">${SVG.video} วิดีโอ</button>
      <button class="vtab" onclick="fvault('image',this)">${SVG.image} รูป</button>
      <button class="vtab" onclick="fvault('history',this)">${SVG.clock} ประวัติ</button>
    </div>
  </div>
  <div class="hist-bar" id="histBar"><span class="hist-info" id="histInfo"></span><button class="hist-clear" onclick="askClearHistory()">✕ ล้างประวัติ</button></div>
  <div class="sort-bar" id="sortBar">
    <button class="sort-btn" id="sbDate" onclick="setSort('date')">ล่าสุด <span id="saDate">↓</span></button>
    <button class="sort-btn" id="sbSize" onclick="setSort('size')">ขนาดไฟล์ <span id="saSize">↓</span></button>
    <button class="sort-btn" id="sbDur" onclick="setSort('dur')">ความยาว <span id="saDur">↓</span></button>
  </div>
  <div class="v-scroll" id="vscroll"><div class="v-grid" id="vgrid"></div></div>
  ${fabBtn}
</div>

<div class="screen" id="svw">
  <div class="rw"><div class="rt" id="rt"></div></div>
  <div class="vt">
    <button class="back-btn" onclick="backVault()">${SVG.back}</button>
    <span class="v-title" id="vtitle"></span>
    <button class="shuf-btn off" id="shufBtn" onclick="toggleShuffle()">${SVG.shuffle}</button>
    ${delBtn}
  </div>
  <div class="nc" id="nc"></div>
</div>

${uploadScreen}

<div class="mb" id="mb"><div class="modal"><h3>ลบรายการนี้?</h3><p>ไฟล์จะถูกลบถาวร</p><div class="mbs"><button class="mc" onclick="closeModal()">ยกเลิก</button><button class="mx" onclick="doDelete()">ลบเลย</button></div></div></div>
<div class="mb2" id="mb2"><div class="modal"><h3>ล้างประวัติทั้งหมด?</h3><p>ไฟล์มีเดียไม่ได้รับผลกระทบ</p><div class="mbs"><button class="mc" onclick="closeModal2()">ยกเลิก</button><button class="mx" onclick="doClearHistory()">ล้างเลย</button></div></div></div>
<div id="lb" class="lb-wrap" onclick="closeLightbox()">
  <button id="lbPrev" class="lb-nav lb-nav-l" onclick="event.stopPropagation();lbPrev()"><svg viewBox="0 0 24 24" width="22" height="22" fill="none" stroke="currentColor" stroke-width="2.5"><polyline points="15 18 9 12 15 6"/></svg></button>
  <img id="lbImg" class="lb-img" onclick="event.stopPropagation()" draggable="false">
  <button id="lbNext" class="lb-nav lb-nav-r" onclick="event.stopPropagation();lbNext()"><svg viewBox="0 0 24 24" width="22" height="22" fill="none" stroke="currentColor" stroke-width="2.5"><polyline points="9 18 15 12 9 6"/></svg></button>
  <div id="lbCounter" class="lb-counter"></div>
  <button class="lb-close" onclick="closeLightbox()"><svg viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="2.5"><line x1="18" y1="6" x2="6" y2="18"/><line x1="6" y1="6" x2="18" y2="18"/></svg></button>
</div>
<div class="toast" id="tst"></div>
<div class="shuf-badge" id="shufBadge"></div>
<div class="shuf-pick" id="shufPick">
  <button id="spAll" onclick="setShuf('all')">ทั้งหมด</button>
  <button id="spVid" onclick="setShuf('video')">วิดีโอ</button>
  <button id="spImg" onclick="setShuf('image')">รูปภาพ</button>
  <button id="spOff" onclick="setShuf('off')">ปิด</button>
</div>

<script>
var IS_ADMIN=${isAdmin ? 'true' : 'false'};
function doLogout(){fetch('/api/logout',{method:'POST'}).then(()=>location.href='/login');}

// ── Snap pool (object-fit:cover, seek ~10s) ──
var _snapQ=[],_snapAct=0,_snapMax=3,_snapCache={};
function snapFrame(src,canvas){if(_snapCache[src]){_drawSnap(canvas,_snapCache[src]);return;}_snapQ.push({src,canvas});_runSnap();}
function _runSnap(){
  while(_snapAct<_snapMax&&_snapQ.length){
    _snapAct++;
    var job=_snapQ.shift();
    var vid=document.createElement('video');
    vid.muted=true;vid.playsInline=true;vid.preload='metadata';
    vid.style.cssText='position:absolute;width:1px;height:1px;opacity:0;pointer-events:none;';
    document.body.appendChild(vid);
    var done=false;
    function finish(){
      if(done)return;done=true;
      try{
        var w=job.canvas.width||160,h=job.canvas.height||284;
        var ctx=job.canvas.getContext('2d');
        var vw=vid.videoWidth||w,vh=vid.videoHeight||h;
        // object-fit:cover — crop source rect centred
        var sc=Math.max(w/vw,h/vh);
        var sw=w/sc,sh=h/sc;
        var sx=(vw-sw)/2,sy=(vh-sh)/2;
        ctx.drawImage(vid,sx,sy,sw,sh,0,0,w,h);
        var url=job.canvas.toDataURL('image/jpeg',.80);
        _snapCache[job.src]=url;
      }catch(e){}
      vid.src='';vid.remove();_snapAct--;_runSnap();
      _snapQ.filter(q=>q.src===job.src).forEach(q=>{_drawSnap(q.canvas,_snapCache[job.src]);});
      _snapQ=_snapQ.filter(q=>q.src!==job.src);
    }
    vid.addEventListener('seeked',finish,{once:true});
    vid.addEventListener('error',()=>{vid.src='';vid.remove();_snapAct--;_runSnap();},{once:true});
    vid.addEventListener('loadedmetadata',()=>{
      // seek to ~10s or 15% of duration, whichever is smaller, min 0.5s
      var t=Math.min(10,Math.max(0.5,vid.duration*0.15||1));
      vid.currentTime=t;
    },{once:true});
    vid.src=job.src;vid.load();
  }
}
function _drawSnap(canvas,dataUrl){if(!dataUrl)return;var img=new Image();img.onload=()=>{var ctx=canvas.getContext('2d');ctx.drawImage(img,0,0,canvas.width,canvas.height);};img.src=dataUrl;}

const SLOT_COUNT=3;var slotData=[-1,-1,-1];
var allPosts=[],filteredPosts=[],flatPosts=[];
var curFilter='all',curReel=0,animating=false,carSt={},delId=null;
var sdrag=false,sdragIdx=-1,isSeeking=false;
var speeds=[0.25,0.5,0.75,1,1.25,1.5,2],spIdx={},hcTimer=null;
var uploadGroups=[],swY=0,swX=0;
var shuffleMode=false,playOrder=[],playPos=0,shuffleFilter='off',shufflePostPool=[];
var engStats={},curReelStartTime=0;
var sortKey='date',sortDir={date:-1,size:-1,dur:-1};

function loadStats(){try{var s=localStorage.getItem('mvStats');if(s)engStats=JSON.parse(s);}catch{}}
function saveStats(){try{localStorage.setItem('mvStats',JSON.stringify(engStats));}catch{}}
function getStats(id){if(!engStats[id])engStats[id]={views:0,totalWatch:0,totalDur:0,rewatches:0,skips:0};return engStats[id];}
loadStats();

var HIST_KEY='mvWatchHistory',HIST_MAX=200;
function loadWatchHistory(){try{var s=localStorage.getItem(HIST_KEY);return s?JSON.parse(s):[];}catch{return[];}}
function saveWatchHistory(arr){try{localStorage.setItem(HIST_KEY,JSON.stringify(arr));}catch{}}
function pushWatchHistory(post){if(!post)return;var arr=loadWatchHistory().filter(x=>x.id!==post.id);arr.unshift({id:post.id,type:post.type,files:post.files,convFile:post.convFile||'',viewedAt:new Date().toISOString()});if(arr.length>HIST_MAX)arr=arr.slice(0,HIST_MAX);saveWatchHistory(arr);}
function clearWatchHistory(){try{localStorage.removeItem(HIST_KEY);}catch{}}

var vaultDirty=true;
function goVault(){show('sv');if(vaultDirty)loadVault();}
function goUpload(){show('su');}
function backVault(){trackLeavePost(getCurPost());pauseAll();if(document.fullscreenElement)document.exitFullscreen();show('sv');if(vaultDirty)loadVault();}
function toggleFullscreen(){if(!document.fullscreenElement)document.documentElement.requestFullscreen().catch(()=>{});else document.exitFullscreen();}
function _updateFsIcons(){var isFs=!!document.fullscreenElement;var e1='<path d="M8 3H5a2 2 0 0 0-2 2v3"/><path d="M21 8V5a2 2 0 0 0-2-2h-3"/><path d="M3 16v3a2 2 0 0 0 2 2h3"/><path d="M16 21h3a2 2 0 0 0 2-2v-3"/>';var e2='<path d="M8 3v3a2 2 0 0 1-2 2H3"/><path d="M21 8h-3a2 2 0 0 1-2-2V3"/><path d="M3 16h3a2 2 0 0 1 2 2v3"/><path d="M16 21v-3a2 2 0 0 1 2-2h3"/>';var el=document.getElementById('vfsIco');if(el)el.innerHTML=isFs?e2:e1;}
document.addEventListener('fullscreenchange',_updateFsIcons);
function show(id){document.querySelectorAll('.screen').forEach(s=>s.classList.remove('on'));document.getElementById(id).classList.add('on');}
function toast(msg,type){var t=document.getElementById('tst');t.textContent=msg;t.className='toast '+(type||'ok');requestAnimationFrame(()=>t.classList.add('on'));setTimeout(()=>t.classList.remove('on'),2500);}

function setSort(key){if(sortKey===key)sortDir[key]*=-1;else sortKey=key;updateSortUI();applyFilter(curFilter);}
function updateSortUI(){['date','size','dur'].forEach(k=>{var bn=document.getElementById('sb'+k.charAt(0).toUpperCase()+k.slice(1)),ar=document.getElementById('sa'+k.charAt(0).toUpperCase()+k.slice(1));if(bn)bn.classList.toggle('on',k===sortKey);if(ar)ar.textContent=sortDir[k]===-1?'↓':'↑';});}
function sortPosts(arr){var d=sortDir[sortKey];return arr.slice().sort((a,b)=>{if(sortKey==='size')return d*(((b.meta&&b.meta.size)||0)-((a.meta&&a.meta.size)||0));if(sortKey==='dur')return d*(((b.meta&&b.meta.dur)||0)-((a.meta&&a.meta.dur)||0));return d*(b.id-a.id);});}

function loadVault(){
  var g=document.getElementById('vgrid');
  if(g&&!allPosts.length)g.innerHTML='<div class="v-empty" style="opacity:.5"><div class="et">กำลังโหลด…</div></div>';
  fetch('/api/posts').then(r=>{if(!r.ok)throw new Error(r.status);return r.json();}).then(d=>{allPosts=d;vaultDirty=false;applyFilter(curFilter);}).catch(()=>{if(g)g.innerHTML='<div class="v-empty"><div class="et" style="color:#ff6644">โหลดไม่สำเร็จ</div></div>';});
}
function fvault(f,el){curFilter=f;document.querySelectorAll('.vtab').forEach(t=>t.classList.remove('on'));el.classList.add('on');if(f==='history')applyFilter('history');else{if(vaultDirty)loadVault();else applyFilter(f);}}

function applyFilter(f){
  var histBar=document.getElementById('histBar'),sortBarEl=document.getElementById('sortBar');
  if(f==='history'){
    filteredPosts=loadWatchHistory();histBar.classList.add('on');
    if(sortBarEl)sortBarEl.style.display='none';
    document.getElementById('histInfo').textContent=filteredPosts.length?filteredPosts.length+' รายการที่ดูล่าสุด':'';
  } else {
    histBar.classList.remove('on');
    var isVideo=(f==='video'),isImg=(f==='image');
    if(sortBarEl)sortBarEl.style.display=isVideo?'':'none';
    var sbSize=document.getElementById('sbSize'),sbDur=document.getElementById('sbDur');
    if(sbSize)sbSize.style.display=isImg?'none':'';
    if(sbDur)sbDur.style.display=isImg?'none':'';
    if(isImg&&(sortKey==='size'||sortKey==='dur')){sortKey='date';updateSortUI();}
    var base=f==='all'?allPosts:f==='video'?allPosts.filter(p=>p.type==='video'):allPosts.filter(p=>p.type!=='video');
    filteredPosts=sortPosts(base);
  }
  renderGrid();
}

// ── renderFlatGrid ──
function renderFlatGrid(g){
  if(!flatPosts.length){g.innerHTML='<div class="v-empty"><div class="et">ยังไม่มีไฟล์</div></div>';return;}
  var playIco='<svg viewBox="0 0 24 24" width="9" height="9" fill="#fff"><polygon points="5 3 19 12 5 21"/></svg>';
  var tmp=document.createElement('div');
  tmp.innerHTML=flatPosts.map((item,i)=>{
    var isV=item._flatType==='video';
    var mh=isV
      ?(item._thumb&&item._thumb[0]!=='_'?'<img data-src="/thumbs/'+item._thumb+'" decoding="async" loading="lazy" style="position:absolute;inset:0;width:100%;height:100%;object-fit:cover;display:block;opacity:0">':'<canvas data-vsrc="/uploads/'+item._file+'" width="160" height="284" style="position:absolute;inset:0;width:100%;height:100%;object-fit:cover;display:block;"></canvas>')
      :'<img data-src="/uploads/'+item._file+'" decoding="async" loading="lazy" style="position:absolute;inset:0;width:100%;height:100%;object-fit:cover;display:block;opacity:0">';
    return '<div class="v-item" onclick="openFlatViewer('+i+')">'
      +mh+(isV?'<div class="vi-type isv">'+playIco+'</div>':'')
      +'<div class="vi-ov"><svg viewBox="0 0 24 24" fill="#fff"><polygon points="5 3 19 12 5 21"/></svg></div></div>';
  }).join('');
  var frag=document.createDocumentFragment();while(tmp.firstChild)frag.appendChild(tmp.firstChild);
  g.innerHTML='';g.appendChild(frag);
  var obs=new IntersectionObserver(entries=>{entries.forEach(e=>{if(!e.isIntersecting)return;var el=e.target;obs.unobserve(el);if(el.tagName==='CANVAS'&&el.dataset.vsrc){snapFrame(el.dataset.vsrc,el);delete el.dataset.vsrc;}else if(el.dataset.src){el.onload=()=>el.style.opacity='1';el.src=el.dataset.src;delete el.dataset.src;}});},{rootMargin:'200px',threshold:0});
  g.querySelectorAll('img[data-src],canvas[data-vsrc]').forEach(el=>obs.observe(el));
}

function renderGrid(){
  var isHistory=(curFilter==='history');
  var vc=allPosts.filter(p=>p.type==='video').length,ic=allPosts.length-vc;
  if(isHistory)document.getElementById('vmeta').textContent='ประวัติการดู';
  else{var parts=[];if(vc)parts.push(vc+' วิดีโอ');if(ic)parts.push(ic+' อัลบั้ม');document.getElementById('vmeta').textContent=allPosts.length+' ทั้งหมด'+(parts.length?' · '+parts.join(' · '):'');}
  var g=document.getElementById('vgrid');
  if(!filteredPosts.length){g.innerHTML='<div class="v-empty"><div class="et">'+(isHistory?'ยังไม่มีประวัติการดู':'ยังไม่มีไฟล์')+'</div><div class="es">'+(isHistory?'รายการที่ดูจะแสดงที่นี่':'กดปุ่มเพื่อเพิ่มไฟล์แรก')+'</div></div>';return;}
  var playIco='<svg viewBox="0 0 24 24" width="9" height="9" fill="#fff"><polygon points="5 3 19 12 5 21"/></svg>';
  var imgIco='<svg viewBox="0 0 24 24" width="9" height="9" fill="none" stroke="#fff" stroke-width="2.5"><rect x="3" y="3" width="18" height="18" rx="2"/><circle cx="8.5" cy="8.5" r="1.5" fill="#fff" stroke="none"/><polyline points="21 15 16 10 5 21"/></svg>';
  var tmp=document.createElement('div');
  tmp.innerHTML=filteredPosts.map((p,i)=>{
    var f=(p.files||[])[0],isV=p.type==='video',isI=p.type==='images';
    var mh=isV
      ?(p.thumb&&p.thumb[0]!=='_'?'<img data-src="/thumbs/'+p.thumb+'" decoding="async" loading="lazy" style="position:absolute;inset:0;width:100%;height:100%;object-fit:cover;display:block;opacity:0">':'<canvas class="vi-snap" data-vsrc="/uploads/'+f+'" width="160" height="284" style="position:absolute;inset:0;width:100%;height:100%;object-fit:cover;display:block;"></canvas>')
      :'<img data-src="/uploads/'+f+'" decoding="async" loading="lazy" style="position:absolute;inset:0;width:100%;height:100%;object-fit:cover;display:block;opacity:0">';
    var viewedLabel='';
    if(isHistory&&p.viewedAt){var dd=new Date(p.viewedAt),now=new Date(),diff=Math.floor((now-dd)/1000);viewedLabel=diff<60?'เมื่อกี้':diff<3600?Math.floor(diff/60)+' นาที':diff<86400?Math.floor(diff/3600)+' ชม.':dd.toLocaleDateString('th-TH',{day:'2-digit',month:'2-digit',year:'2-digit'});}
    return '<div class="v-item" onclick="openViewer('+i+')">'
      +mh+'<div class="vi-type'+(isV?' isv':'')+'">'+( isV?playIco:imgIco)+'</div>'
      +(isI&&!isHistory?'<div class="vi-set">'+p.files.length+'</div>':'')
      +(viewedLabel?'<div class="vi-cap">'+viewedLabel+'</div>':'')
      +'<div class="vi-ov"><svg viewBox="0 0 24 24" fill="#fff"><polygon points="5 3 19 12 5 21"/></svg></div></div>';
  }).join('');
  var frag=document.createDocumentFragment();while(tmp.firstChild)frag.appendChild(tmp.firstChild);
  g.innerHTML='';g.appendChild(frag);
  var obs=new IntersectionObserver(entries=>{entries.forEach(e=>{if(!e.isIntersecting)return;var el=e.target;obs.unobserve(el);if(el.tagName==='CANVAS'&&el.dataset.vsrc){snapFrame(el.dataset.vsrc,el);delete el.dataset.vsrc;}else if(el.dataset.src){el.onload=()=>el.style.opacity='1';el.src=el.dataset.src;delete el.dataset.src;}});},{rootMargin:'200px',threshold:0});
  g.querySelectorAll('img[data-src],canvas[data-vsrc]').forEach(el=>obs.observe(el));
}

var _flatIdx=0;
function openFlatViewer(idx){_flatIdx=idx;var item=flatPosts[idx];if(!item)return;if(item._flatType==='video'){filteredPosts=allPosts;openViewer(item._postIdx);return;}showLightbox(idx);}
function showLightbox(idx){_flatIdx=idx;var item=flatPosts[idx];if(!item||item._flatType==='video')return;var lbImg=document.getElementById('lbImg'),lbCnt=document.getElementById('lbCounter');lbImg.src='/uploads/'+item._file;lbImg.style.opacity='0';lbImg.onload=()=>lbImg.style.opacity='1';var imgs=flatPosts.filter(x=>x._flatType==='image'),ii=imgs.indexOf(item);lbCnt.textContent=(ii+1)+' / '+imgs.length;document.getElementById('lb').classList.add('on');updateLbNav();}
function lbPrev(){for(var i=_flatIdx-1;i>=0;i--){if(flatPosts[i]._flatType==='image'){showLightbox(i);return;}}}
function lbNext(){for(var i=_flatIdx+1;i<flatPosts.length;i++){if(flatPosts[i]._flatType==='image'){showLightbox(i);return;}}}
function updateLbNav(){var hp=false,hn=false;for(var i=_flatIdx-1;i>=0;i--){if(flatPosts[i]._flatType==='image'){hp=true;break;}}for(var i=_flatIdx+1;i<flatPosts.length;i++){if(flatPosts[i]._flatType==='image'){hn=true;break;}}var pl=document.getElementById('lbPrev'),nl=document.getElementById('lbNext');if(pl){pl.style.opacity=hp?'1':'0.2';pl.style.pointerEvents=hp?'auto':'none';}if(nl){nl.style.opacity=hn?'1':'0.2';nl.style.pointerEvents=hn?'auto':'none';}}
function closeLightbox(){document.getElementById('lb').classList.remove('on');}
document.addEventListener('keydown',e=>{var lb=document.getElementById('lb');if(!lb||!lb.classList.contains('on'))return;if(e.key==='ArrowLeft')lbPrev();else if(e.key==='ArrowRight')lbNext();else if(e.key==='Escape')closeLightbox();});

function askClearHistory(){document.getElementById('mb2').classList.add('on');}
function closeModal2(){document.getElementById('mb2').classList.remove('on');}
function doClearHistory(){closeModal2();clearWatchHistory();applyFilter('history');toast('ล้างประวัติแล้ว');}

function makeShufPool(){return allPosts.filter(p=>shuffleFilter==='video'?p.type==='video':shuffleFilter==='image'?p.type!=='video':true);}
function weightedShufPosts(posts){
  var pool=posts.slice(),wpool=pool.map(p=>{var st=engStats[p.id];if(!st||st.views===0)return 20+Math.floor(Math.random()*61);var dur=Math.max(st.totalDur,1),wr=Math.min(1,(st.totalWatch/st.views)/dur);var b=wr>0.8?20:wr>0.5?8:wr>0.3?3:0,pen=Math.max(0,(st.skips||0)-1)*10,vpen=st.views>5?Math.min(15,Math.floor(st.views/5)*3):0;return Math.max(1,Math.round(wr*60+b-pen-vpen));});
  var result=[];
  while(pool.length){var total=wpool.reduce((a,b)=>a+b,0),r=Math.random()*total,cum=0,chosen=pool.length-1;for(var i=0;i<pool.length;i++){cum+=wpool[i];if(r<=cum){chosen=i;break;}}result.push(pool[chosen]);pool.splice(chosen,1);wpool.splice(chosen,1);}
  return result;
}
function buildOrder(startIdx){var n=filteredPosts.length;if(!n)return;if(shuffleMode){shufflePostPool=makeShufPool();if(!shufflePostPool.length)shufflePostPool=allPosts.slice();var shuffled=weightedShufPosts(shufflePostPool);var cp=filteredPosts[startIdx];if(cp){shuffled=shuffled.filter(p=>p.id!==cp.id);shuffled.unshift(cp);}playOrder=shuffled.map(p=>p.id);}else{playOrder=[];for(var i=0;i<n;i++)playOrder.push(i);playOrder=playOrder.slice(startIdx).concat(playOrder.slice(0,startIdx));}playPos=0;}
function _shufPickClose(){document.getElementById('shufPick').classList.remove('on');document.removeEventListener('click',_shufOutside);}
function _shufOutside(e){var pick=document.getElementById('shufPick'),btn=document.getElementById('shufBtn');if(!pick.contains(e.target)&&e.target!==btn&&!btn.contains(e.target))_shufPickClose();}
function toggleShuffle(){var pick=document.getElementById('shufPick');if(pick.classList.contains('on')){_shufPickClose();return;}var map={off:'spOff',all:'spAll',video:'spVid',image:'spImg'};['spAll','spVid','spImg','spOff'].forEach(id=>{var el=document.getElementById(id);if(el)el.classList.toggle('act',id===map[shuffleFilter]);});pick.classList.add('on');setTimeout(()=>document.addEventListener('click',_shufOutside),10);}
function setShuf(mode){shuffleFilter=mode;shuffleMode=(mode!=='off');_shufPickClose();document.getElementById('shufBtn').className='shuf-btn '+(shuffleMode?'on':'off');buildOrder(curReel);playPos=0;var labels={off:'ปิดสุ่ม',all:'สุ่มทั้งหมด',video:'สุ่มวิดีโอ',image:'สุ่มรูปภาพ'};var badge=document.getElementById('shufBadge');badge.textContent=labels[mode];badge.classList.add('on');clearTimeout(badge._t);badge._t=setTimeout(()=>badge.classList.remove('on'),1800);}

function openViewer(idx){curReel=idx;carSt={};spIdx={};buildOrder(idx);show('svw');buildSlots();loadSlots();setSlotPos(1,false);setupSwipe();setTimeout(()=>{autoPlay();trackEnterPost(getCurPost());},50);updateVUI();}
function buildSlots(){var track=document.getElementById('rt');track.innerHTML='';track.style.cssText='display:flex;flex-direction:column;width:100%;height:100%;will-change:transform;transform:translateZ(0)';for(var s=0;s<SLOT_COUNT;s++){var div=document.createElement('div');div.id='slot'+s;div.style.cssText='height:100%;min-height:0;width:100%;flex:0 0 100%;position:relative;overflow:hidden;background:#000;display:flex;align-items:center;justify-content:center;contain:layout style paint;';track.appendChild(div);}}
function loadSlots(){fillSlot(0,getPrevPost());fillSlot(1,curReel);fillSlot(2,getNextPost());}
function getPrevPost(){if(playPos<=0)return -1;return shuffleMode?resolveShufIdx(playOrder[playPos-1]):playOrder[playPos-1];}
function getNextPost(){var np=playPos+1;if(np>=playOrder.length)extendPlayOrder();var v=playOrder[np];if(v===undefined)return -1;return shuffleMode?resolveShufIdx(v):v;}
function resolveShufIdx(id){for(var i=0;i<allPosts.length;i++){if(allPosts[i].id===id)return i;}return -1;}
function extendPlayOrder(){if(shuffleMode){shufflePostPool=makeShufPool();if(!shufflePostPool.length)shufflePostPool=allPosts.slice();playOrder=playOrder.concat(weightedShufPosts(shufflePostPool).map(p=>p.id));}else{var seq=[];for(var i=0;i<filteredPosts.length;i++)seq.push(i);playOrder=playOrder.concat(seq);}}
function fillSlot(slot,postIdx){slotData[slot]=postIdx;var el=document.getElementById('slot'+slot);if(!el)return;var srcArr=shuffleMode?allPosts:filteredPosts;if(postIdx<0||postIdx>=srcArr.length){el.innerHTML='';return;}var p=srcArr[postIdx];el.innerHTML=buildReelContent(p,postIdx,slot);if(p.type==='images')initCarSlot(slot,postIdx,(p.files||[]).length);if(p.type==='video')wireVidSlot(slot,postIdx);}
function buildReelContent(p,postIdx,slot){
  var isV=p.type==='video',isI=p.type==='images',files=p.files||[],sid='s'+slot+'_',media='';
  if(isV){
    var vsrc=p.convFile?'/video/'+p.convFile:'/uploads/'+files[0];
    media='<video id="'+sid+'v" playsinline loop preload="'+(slot===1?'auto':'metadata')+'" data-src="'+vsrc+'" style="width:100%;height:100%;object-fit:contain;display:block;position:relative;z-index:1;" onclick="togglePlaySlot('+slot+')"></video><div class="pp" id="'+sid+'pp"><div class="pp-c"><svg viewBox="0 0 24 24" id="'+sid+'pi"><polygon points="5 3 19 12 5 21" fill="white"/></svg></div></div>';
  } else if(isI){
    media='<div class="car" id="'+sid+'car"><div class="cat" id="'+sid+'cat">'+files.map(f=>'<div class="cas"><div class="cas-bg" style="background-image:url(/uploads/'+f+')"></div><div class="cas-fg"><img src="/uploads/'+f+'" loading="lazy" decoding="async"></div></div>').join('')+'</div><div class="cdots">'+files.map((_,di)=>'<div class="cd'+(di===0?' on':'')+'" id="'+sid+'d'+di+'"></div>').join('')+'</div><div class="cnum" id="'+sid+'cn">1 / '+files.length+'</div></div>';
  } else {
    media='<div class="reel-bg" style="background-image:url(/uploads/'+files[0]+')"></div><div style="position:relative;z-index:1;width:100%;height:100%;display:flex;align-items:center;justify-content:center;"><img src="/uploads/'+files[0]+'" loading="lazy" decoding="async" style="max-width:100%;max-height:100%;object-fit:contain;display:block;"></div>';
  }
  return media+'<div class="rg"></div>'+(isV?buildCtrlSlot(slot):'');
}
function buildCtrlSlot(slot){var s='s'+slot+'_';return '<div class="vc" id="'+s+'vc" style="opacity:0"><div class="sw"><span class="tlbl" id="'+s+'ct">0:00</span><div class="sb" id="'+s+'sb"><div class="sb-bg"></div><div class="sb-buf" id="'+s+'sbuf"></div><div class="sb-fill" id="'+s+'sf"></div><div class="sb-thumb" id="'+s+'st"></div></div><span class="tlbl" id="'+s+'dt">0:00</span></div><div class="cr"><div class="cl"><button class="cb" onclick="seekRelSlot('+slot+',-10)"><svg viewBox="0 0 24 24"><polyline points="1 4 1 10 7 10"/><path d="M3.51 15a9 9 0 1 0 .49-4.95"/></svg></button><button class="cb" onclick="seekRelSlot('+slot+',10)"><svg viewBox="0 0 24 24"><polyline points="23 4 23 10 17 10"/><path d="M20.49 15a9 9 0 1 1-.49-4.95"/></svg></button></div><div class="cright"><button class="spd" id="'+s+'sp" onclick="cycleSpd(&quot;'+s+'&quot;)">1×</button><div class="vw"><button class="cb" onclick="toggleMuteSlot('+slot+')"><svg viewBox="0 0 24 24" id="'+s+'vi"><polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"/><path d="M15.54 8.46a5 5 0 0 1 0 7.07"/></svg></button><input type="range" class="vsl" min="0" max="1" step="0.05" value="1" oninput="setVolSlot('+slot+',this.value)" id="'+s+'vs"></div></div></div></div>';}
function wireVidSlot(slot,postIdx){var s='s'+slot+'_',vid=document.getElementById(s+'v');if(!vid||vid._w)return;vid._w=true;if(vid.dataset.src)vid.src=vid.dataset.src;var rafId=null;vid.addEventListener('timeupdate',()=>{if(rafId)return;rafId=requestAnimationFrame(()=>{rafId=null;updSeekSlot(slot,s);});});vid.addEventListener('progress',()=>updBufSlot(slot,s));vid.addEventListener('loadedmetadata',()=>{var el=document.getElementById(s+'dt');if(el)el.textContent=fmtT(vid.duration);showCtrlSlot(s);});vid.addEventListener('play',()=>updPlayIcoSlot(s,false));vid.addEventListener('pause',()=>updPlayIcoSlot(s,true));var sb=document.getElementById(s+'sb');if(sb){sb.addEventListener('mousedown',e=>{sdrag=true;sdragIdx=s;applySeekSlot(e.clientX,s);e.stopPropagation();document.addEventListener('mousemove',onSM2);document.addEventListener('mouseup',onSU2);});sb.addEventListener('touchstart',e=>{isSeeking=true;sdragIdx=s;applySeekSlot(e.touches[0].clientX,s);e.stopPropagation();},{passive:false});sb.addEventListener('touchmove',e=>{if(isSeeking){applySeekSlot(e.touches[0].clientX,s);e.stopPropagation();e.preventDefault();}},{passive:false});sb.addEventListener('touchend',e=>{isSeeking=false;e.stopPropagation();},{passive:false});}}
function onSM2(e){if(sdrag)applySeekSlot(e.clientX,sdragIdx);}function onSU2(){sdrag=false;document.removeEventListener('mousemove',onSM2);document.removeEventListener('mouseup',onSU2);}
function applySeekSlot(cx,s){var sb=document.getElementById(s+'sb'),vid=document.getElementById(s+'v');if(!sb||!vid||!vid.duration)return;var r=sb.getBoundingClientRect(),p=Math.max(0,Math.min(1,(cx-r.left)/r.width));vid.currentTime=p*vid.duration;updSeekUISlot(s,p);showCtrlSlot(s);}
function updSeekSlot(slot,s){var vid=document.getElementById(s+'v');if(!vid||!vid.duration)return;var p=vid.currentTime/vid.duration;updSeekUISlot(s,p);var ct=document.getElementById(s+'ct');if(ct)ct.textContent=fmtT(vid.currentTime);}
function updSeekUISlot(s,p){var fill=document.getElementById(s+'sf'),thumb=document.getElementById(s+'st');if(fill)fill.style.width=(p*100)+'%';if(thumb)thumb.style.left=(p*100)+'%';}
function updBufSlot(slot,s){var vid=document.getElementById(s+'v');if(!vid||!vid.duration||!vid.buffered.length)return;var buf=document.getElementById(s+'sbuf');if(buf)buf.style.width=(vid.buffered.end(vid.buffered.length-1)/vid.duration*100)+'%';}
function showCtrlSlot(s){var vc=document.getElementById(s+'vc');if(!vc)return;vc.style.opacity='1';clearTimeout(hcTimer);hcTimer=setTimeout(()=>{if(vc)vc.style.opacity='0';},3200);}
function togglePlaySlot(slot){var s='s'+slot+'_',vid=document.getElementById(s+'v');if(!vid)return;var pp=document.getElementById(s+'pp');if(vid.paused)vid.play();else vid.pause();if(pp){pp.classList.remove('show');void pp.offsetWidth;pp.classList.add('show');}showCtrlSlot(s);}
function updPlayIcoSlot(s,paused){var ico=document.getElementById(s+'pi');if(!ico)return;ico.innerHTML=paused?'<polygon points="5 3 19 12 5 21" fill="white" stroke="none"/>':'<line x1="6" y1="4" x2="6" y2="20" stroke="white" stroke-width="3"/><line x1="18" y1="4" x2="18" y2="20" stroke="white" stroke-width="3"/>';}
function seekRelSlot(slot,d){var s='s'+slot+'_',vid=document.getElementById(s+'v');if(!vid)return;vid.currentTime=Math.max(0,Math.min(vid.duration||0,vid.currentTime+d));showCtrlSlot(s);}
function toggleMuteSlot(slot){var s='s'+slot+'_',vid=document.getElementById(s+'v');if(!vid)return;vid.muted=!vid.muted;var sl=document.getElementById(s+'vs');if(sl)sl.value=vid.muted?0:vid.volume;updVolIcoSlot(s,vid.muted);showCtrlSlot(s);}
function setVolSlot(slot,v){var s='s'+slot+'_',vid=document.getElementById(s+'v');if(!vid)return;vid.volume=parseFloat(v);vid.muted=parseFloat(v)===0;updVolIcoSlot(s,vid.muted);}
function updVolIcoSlot(s,muted){var ico=document.getElementById(s+'vi');if(!ico)return;ico.innerHTML=muted?'<polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"/><line x1="23" y1="9" x2="17" y2="15"/><line x1="17" y1="9" x2="23" y2="15"/>':'<polygon points="11 5 6 9 2 9 2 15 6 15 11 19 11 5"/><path d="M15.54 8.46a5 5 0 0 1 0 7.07"/>';}
function initCarSlot(slot,postIdx,total){if(!carSt[postIdx])carSt[postIdx]=0;var s='s'+slot+'_',car=document.getElementById(s+'car');if(!car)return;var mx2=0,mdn2=false;car.addEventListener('mousedown',e=>{mdn2=true;mx2=e.clientX;});window.addEventListener('mouseup',e=>{if(!mdn2)return;mdn2=false;var dx=e.clientX-mx2,c=carSt[postIdx]||0;if(Math.abs(dx)>22){if(dx<0&&c<total-1)setSlideSlot(slot,postIdx,c+1,total);else if(dx>0&&c>0)setSlideSlot(slot,postIdx,c-1,total);}});}
function setSlideSlot(slot,postIdx,si,total){carSt[postIdx]=si;var s='s'+slot+'_',t=document.getElementById(s+'cat'),cn=document.getElementById(s+'cn');if(t)t.style.transform='translateX('+(-si*100)+'%)';if(cn)cn.textContent=(si+1)+' / '+total;for(var d=0;d<total;d++){var dot=document.getElementById(s+'d'+d);if(dot)dot.className='cd'+(d===si?' on':'');}}
function setSlotPos(slotIdx,anim){var t=document.getElementById('rt'),h=t.parentElement.offsetHeight||window.innerHeight;t.style.transition=anim?'transform .3s cubic-bezier(.4,0,.2,1)':'none';t.style.transform='translateY('+(-slotIdx*h)+'px) translateZ(0)';if(!anim)t.offsetHeight;}

function setupSwipe(){
  var wrap=document.querySelector('#svw .rw'),nw=wrap.cloneNode(false);while(wrap.firstChild)nw.appendChild(wrap.firstChild);wrap.parentNode.replaceChild(nw,wrap);wrap=nw;
  wrap.addEventListener('touchstart',e=>{swY=e.touches[0].clientY;swX=e.touches[0].clientX;},{passive:true});
  wrap.addEventListener('touchend',e=>{if(animating||isSeeking)return;var dy=e.changedTouches[0].clientY-swY,dx=e.changedTouches[0].clientX-swX,ax=Math.abs(dx),ay=Math.abs(dy),p=getCurPost();if(p&&p.type==='images'){if(ax>ay&&ax>22){var c=carSt[curReel]||0,total=(p.files||[]).length;if(dx<0&&c<total-1)setSlideSlot(1,curReel,c+1,total);else if(dx>0&&c>0)setSlideSlot(1,curReel,c-1,total);return;}if(ay>ax&&ay>40){if(dy<0)advanceReel(1);else advanceReel(-1);}return;}if(ay>ax&&ay>40){if(dy<0)advanceReel(1);else advanceReel(-1);}},{passive:true});
  var wc=false;wrap.addEventListener('wheel',e=>{e.preventDefault();if(animating||wc)return;var delta=e.deltaY;if(e.deltaMode===1)delta*=30;if(e.deltaMode===2)delta*=300;if(Math.abs(delta)<40)return;wc=true;setTimeout(()=>wc=false,450);if(delta>0)advanceReel(1);else advanceReel(-1);},{passive:false});
}
function getCurPost(){return shuffleMode?allPosts[curReel]||null:filteredPosts[curReel]||null;}
function trackEnterPost(p){curReelStartTime=Date.now();if(!p)return;var st=getStats(p.id),vid=document.getElementById('s1_v');if(vid&&vid.duration>0&&vid.duration>st.totalDur)st.totalDur=vid.duration;st.views++;if(st.views>1)st.rewatches++;saveStats();pushWatchHistory(p);}
function trackLeavePost(p){if(!p)return;var elapsed=(Date.now()-curReelStartTime)/1000,vid=document.getElementById('s1_v'),watched,dur;if(vid&&vid.duration>0){watched=vid.currentTime;dur=vid.duration;}else{watched=Math.min(elapsed,8);dur=Math.max(getStats(p.id).totalDur||5,5);}var st=getStats(p.id);st.totalWatch+=watched;if(dur>st.totalDur)st.totalDur=dur;var ratio=dur>0?watched/dur:0;if(watched<1.5&&ratio<0.08)st.skips++;else if(ratio>0.5&&st.skips>0)st.skips=Math.max(0,st.skips-1);saveStats();}
function advanceReel(dir){
  if(animating)return;
  var srcLen=shuffleMode?allPosts.length:filteredPosts.length;
  if(dir===1){var np=playPos+1;if(np>=playOrder.length)extendPlayOrder();if(slotData[2]<0||slotData[2]>=srcLen)return;trackLeavePost(getCurPost());animating=true;setSlotPos(2,true);setTimeout(()=>{playPos=np;curReel=shuffleMode?resolveShufIdx(playOrder[playPos]):playOrder[playPos];var pv=getPrevPost(),nx=getNextPost();slotData[0]=pv;slotData[1]=curReel;slotData[2]=nx;fillSlot(0,pv);fillSlot(1,curReel);fillSlot(2,nx);setSlotPos(1,false);animating=false;autoPlay();trackEnterPost(getCurPost());updateVUI();},320);}
  else{if(playPos<=0||slotData[0]<0)return;trackLeavePost(getCurPost());animating=true;setSlotPos(0,true);setTimeout(()=>{playPos--;curReel=shuffleMode?resolveShufIdx(playOrder[playPos]):playOrder[playPos];var pv=getPrevPost(),nx=getNextPost();slotData[0]=pv;slotData[1]=curReel;slotData[2]=nx;fillSlot(0,pv);fillSlot(1,curReel);fillSlot(2,nx);setSlotPos(1,false);animating=false;autoPlay();trackEnterPost(getCurPost());updateVUI();},320);}
}
function updateVUI(){
  document.getElementById('vtitle').textContent='';
  var nc=document.getElementById('nc');nc.textContent=shuffleMode?'~':(curReel+1)+'/'+filteredPosts.length;nc.classList.add('on');clearTimeout(nc._t);nc._t=setTimeout(()=>nc.classList.remove('on'),1600);
  if(!IS_ADMIN)return;
  var p=getCurPost(),btn=document.getElementById('convBtn');if(!btn)return;
  if(!p||p.type!=='video'){btn.style.display='none';return;}
  var svgIco='<svg viewBox="0 0 24 24" width="13" height="13"><polyline points="23 4 23 10 17 10"/><path d="M20.49 15a9 9 0 1 1-.49-4.95"/></svg>';
  btn.style.display='flex';btn.disabled=false;btn.style.opacity='1';btn._postId=p.id;
  if(p.convFile){btn.className='conv-btn done';btn.innerHTML=svgIco+'แปลงใหม่';}
  else{btn.className='conv-btn';btn.innerHTML=svgIco+'แปลงวิดีโอ';}
}
function requestConvertCur(){var btn=document.getElementById('convBtn');if(!btn||!btn._postId)return;var pid=btn._postId;btn.disabled=true;btn.style.opacity='.5';fetch('/api/convert/'+pid,{method:'POST'}).then(r=>r.json()).then(d=>{if(d.ok){var si='<svg viewBox="0 0 24 24" width="13" height="13"><polyline points="23 4 23 10 17 10"/><path d="M20.49 15a9 9 0 1 1-.49-4.95"/></svg>';btn.className='conv-btn';btn.innerHTML=si+'อยู่ในคิว';pollConvertDone(pid);}else{toast('เกิดข้อผิดพลาด','err');btn.disabled=false;btn.style.opacity='1';}}).catch(()=>{toast('เกิดข้อผิดพลาด','err');btn.disabled=false;btn.style.opacity='1';});}
function pauseAll(){for(var s=0;s<SLOT_COUNT;s++){var vid=document.getElementById('s'+s+'_v');if(vid)try{vid.pause();}catch{}}}
function autoPlay(){pauseAll();var vid=document.getElementById('s1_v');if(!vid)return;if(vid.dataset.src){vid.src=vid.dataset.src;delete vid.dataset.src;}vid.play().catch(()=>{});showCtrlSlot('s1_');}
function fmtT(s){if(!isFinite(s)||s<0)return'0:00';return Math.floor(s/60)+':'+String(Math.floor(s%60)).padStart(2,'0');}
function cycleSpd(prefix){if(spIdx[prefix]===undefined)spIdx[prefix]=3;spIdx[prefix]=(spIdx[prefix]+1)%speeds.length;var sp=speeds[spIdx[prefix]],vid=document.getElementById(prefix+'v'),btn=document.getElementById(prefix+'sp');if(vid)vid.playbackRate=sp;if(btn)btn.textContent=sp+'×';showCtrlSlot(prefix);}
function pollConvertDone(postId){var t=setInterval(()=>{fetch('/api/convert-status/'+postId).then(r=>r.json()).then(d=>{if(d.done){clearInterval(t);var ap=allPosts.find(x=>x.id===postId);if(ap&&d.convFile)ap.convFile=d.convFile;buildSlots();loadSlots();setTimeout(()=>{autoPlay();updateVUI();},80);toast('แปลงเสร็จแล้ว ✅');}else if(d.failed){clearInterval(t);toast('แปลงไม่สำเร็จ','err');}}).catch(()=>{});},2000);}
function askDelete(){var p=getCurPost();delId=p?p.id:null;document.getElementById('mb').classList.add('on');}
function closeModal(){document.getElementById('mb').classList.remove('on');}
function doDelete(){closeModal();if(!delId)return;fetch('/api/delete/'+delId,{method:'DELETE'}).then(r=>r.json()).then(()=>{toast('ลบแล้ว');vaultDirty=true;allPosts=allPosts.filter(p=>p.id!==delId);applyFilter(curFilter);if(!filteredPosts.length){backVault();return;}curReel=Math.min(curReel,Math.max(0,filteredPosts.length-1));carSt={};spIdx={};buildOrder(curReel);buildSlots();loadSlots();setSlotPos(1,false);setTimeout(()=>{autoPlay();trackEnterPost(getCurPost());},60);updateVUI();}).catch(()=>toast('เกิดข้อผิดพลาด','err'));}

// ── Upload ──
function initUpload(){
  var fi=document.getElementById('fi'),dz=document.getElementById('dz');
  fi.addEventListener('change',e=>{addGroups(Array.from(e.target.files));fi.value='';});
  dz.addEventListener('dragover',e=>{e.preventDefault();dz.classList.add('drag');});
  dz.addEventListener('dragleave',()=>dz.classList.remove('drag'));
  dz.addEventListener('drop',e=>{e.preventDefault();dz.classList.remove('drag');addGroups(Array.from(e.dataTransfer.files));});
}
function addGroups(files){if(!files.length)return;var videos=files.filter(f=>f.type.startsWith('video/')),images=files.filter(f=>f.type.startsWith('image/'));videos.forEach(v=>uploadGroups.push({files:[v],id:Date.now()+Math.random()}));if(images.length)uploadGroups.push({files:images,id:Date.now()+Math.random()});renderGroups();}
function fmtSize(b){if(b<1024)return b+'B';if(b<1048576)return(b/1024).toFixed(1)+'KB';return(b/1048576).toFixed(1)+'MB';}
function rmGroup(gi){uploadGroups.splice(gi,1);renderGroups();}
function rmFile(gi,fi){uploadGroups[gi].files.splice(fi,1);if(!uploadGroups[gi].files.length)uploadGroups.splice(gi,1);renderGroups();}
function renderGroups(){
  var list=document.getElementById('gl'),bot=document.getElementById('ubot'),cnt=document.getElementById('ucnt');
  if(!uploadGroups.length){list.innerHTML='';bot.style.display='none';return;}
  bot.style.display='block';
  var ts=uploadGroups.reduce((a,g)=>a+g.files.reduce((b,f)=>b+f.size,0),0);
  cnt.textContent=uploadGroups.length+' รายการ | '+fmtSize(ts);
  var xS='<svg viewBox="0 0 24 24" width="10" height="10" fill="none" stroke="currentColor" stroke-width="3"><line x1="18" y1="6" x2="6" y2="18"/><line x1="6" y1="6" x2="18" y2="18"/></svg>';
  var rmS='<svg viewBox="0 0 24 24" width="14" height="14" fill="none" stroke="currentColor" stroke-width="2"><polyline points="3 6 5 6 21 6"/><path d="M19 6l-1 14H6L5 6"/><path d="M10 11v6M14 11v6M9 6V4h6v2"/></svg>';
  var vS='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8"><polygon points="23 7 16 12 23 17 23 7"/><rect x="1" y="5" width="15" height="14" rx="2"/></svg>';
  var iS='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8"><rect x="3" y="3" width="18" height="18" rx="2"/><circle cx="8.5" cy="8.5" r="1.5"/><polyline points="21 15 16 10 5 21"/></svg>';
  list.innerHTML=uploadGroups.map((g,gi)=>{
    var isV=g.files[0]&&g.files[0].type.startsWith('video/');
    var mn=g.files[0].name,ms=g.files.reduce((a,f)=>a+f.size,0),sn=mn.length>32?mn.slice(0,30)+'…':mn;
    var lbl=isV?'วิดีโอ':(g.files.length>1?'ชุดรูป '+g.files.length+' ไฟล์':'รูปภาพ');
    var frows=g.files.length>1?'<div class="fc-files">'+g.files.map((f,fi)=>'<div class="fc-frow"><span class="fc-frow-name">'+(f.name.length>30?f.name.slice(0,28)+'…':f.name)+'</span><span class="fc-frow-size">'+fmtSize(f.size)+'</span><button class="fc-frow-rm" onclick="rmFile('+gi+','+fi+')">'+xS+'</button></div>').join('')+'</div>':'';
    return '<div class="fc" id="gc'+gi+'"><div class="fc-head"><div class="fc-info"><div class="fc-ico '+(isV?'vid':'img')+'">'+(isV?vS:iS)+'</div><div class="fc-text"><div class="fc-name">'+sn+'</div><div class="fc-meta">'+lbl+' · '+fmtSize(ms)+'</div></div></div><button class="fc-rm" onclick="rmGroup('+gi+')">'+rmS+'</button></div>'+frows+'<div class="fc-prog" id="fprog'+gi+'"><div class="fc-pbar"><div class="fc-pfill" id="fpfill'+gi+'"></div></div><div class="fc-ppct" id="fppct'+gi+'"></div></div></div>';
  }).join('');
}
function doUpload(){
  if(!uploadGroups.length){toast('กรุณาเลือกไฟล์','err');return;}
  var btn=document.getElementById('ubtn');btn.classList.add('ld');btn.disabled=true;
  document.getElementById('gl').classList.add('uploading');
  var pbw=document.getElementById('pbw'),pbf=document.getElementById('pbf');pbw.classList.add('on');
  var total=uploadGroups.length,done=0,failed=0;
  var totalBytes=uploadGroups.reduce((a,g)=>a+g.files.reduce((b,f)=>b+f.size,0),0);
  var loadedBytes=new Array(total).fill(0),startTime=Date.now(),speedEl=document.getElementById('uploadSpeed');
  var _raf=null,_prog={},_pb=0;
  function flushProg(){_raf=null;Object.keys(_prog).forEach(k=>{var fill=document.getElementById('fpfill'+k),label=document.getElementById('fppct'+k);if(fill)fill.style.width=_prog[k]+'%';if(label){label.style.display='block';label.textContent=_prog[k]>=100?'⏳ บันทึก...':Math.round(_prog[k])+'%';}});pbf.style.width=Math.min(99,_pb)+'%';}
  function setFP(gi,pct){_prog[gi]=pct;if(!_raf)_raf=requestAnimationFrame(flushProg);}
  function setGP(pct){_pb=pct;if(!_raf)_raf=requestAnimationFrame(flushProg);}
  function onDone(){if(_raf){cancelAnimationFrame(_raf);_raf=null;}pbf.style.width='100%';setTimeout(()=>{pbw.classList.remove('on');pbf.style.width='0';btn.classList.remove('ld');btn.disabled=false;document.getElementById('gl').classList.remove('uploading');toast(failed===0?'บันทึก '+done+' รายการ':'สำเร็จ '+done+'/'+total,failed>0?'err':'ok');vaultDirty=true;uploadGroups=[];renderGroups();setTimeout(()=>goVault(),500);},280);}
  uploadGroups.forEach((g,gi)=>{
    var fd=new FormData();g.files.forEach(f=>fd.append('files',f));
    var gb=g.files.reduce((a,f)=>a+f.size,0);
    var xhr=new XMLHttpRequest();xhr.open('POST','/api/upload');xhr.timeout=0;
    xhr.upload.onprogress=e=>{if(!e.lengthComputable)return;setFP(gi,e.loaded/e.total*100);loadedBytes[gi]=e.loaded;if(totalBytes>0){var tl=loadedBytes.reduce((a,b)=>a+b,0);setGP(tl/totalBytes*100);if(speedEl){var el=(Date.now()-startTime)/1000;if(el>0.5){var bps=tl/el;speedEl.textContent=bps>=1048576?(bps/1048576).toFixed(1)+' MB/s':bps>=1024?(bps/1024).toFixed(0)+' KB/s':Math.round(bps)+' B/s';}}}};
    xhr.onload=()=>{if(xhr.status===200)done++;else failed++;loadedBytes[gi]=gb;setFP(gi,100);var card=document.getElementById('gc'+gi);if(card){card.style.opacity=xhr.status===200?'.5':'.3';card.style.borderColor=xhr.status===200?'rgba(255,115,0,.35)':'rgba(255,68,0,.35)';}if(done+failed===total)onDone();};
    xhr.onerror=()=>{failed++;if(done+failed===total)onDone();};
    xhr.send(fd);
  });
}
if(IS_ADMIN)initUpload();
updateSortUI();loadVault();
</script></body></html>`;
}

// ── Cached pages ──
const LOGIN_HTML = buildLoginHTML();
const ADMIN_HTML = buildHTML(true);
const GUEST_HTML = buildHTML(false);

// ── Upload priority gate ──
let _uploadActive = 0;
const isUploadReq = (p, m) => p === '/api/upload' && m === 'POST';
function deferUntilUploadDone(fn) { if (_uploadActive === 0) return fn(); const wait = () => _uploadActive === 0 ? fn() : setImmediate(wait); setImmediate(wait); }

const server = http.createServer(async (req, res) => {
    const url = new URL(req.url, 'http://localhost'), p = url.pathname;
    res.setHeader('Access-Control-Allow-Origin', '*'); res.setHeader('Connection', 'keep-alive');
    if (p === '/favicon.ico') { res.writeHead(204); return res.end(); }
    if (p === '/') { res.writeHead(302, { Location: '/guest' }); return res.end(); }
    if (!isUploadReq(p, req.method)) return deferUntilUploadDone(() => handleRequest(req, res, p, url));
    return handleUpload(req, res);
});

async function handleRequest(req, res, p, url) {
    if (p === '/login') { const s = getSession(req); if (s) { res.writeHead(302, { Location: '/admin' }); return res.end(); } return gzipSend(res, LOGIN_HTML); }
    if (p === '/admin') { const s = getSession(req); if (!s) { res.writeHead(302, { Location: '/login' }); return res.end(); } return gzipSend(res, ADMIN_HTML); }
    if (p === '/guest') return gzipSend(res, GUEST_HTML);
    if (p === '/status') { const s = getSession(req); if (!s) { res.writeHead(302, { Location: '/login' }); return res.end(); } setImmediate(() => gzipSend(res, buildStatusHTML())); return; }
    if (p === '/analytics') { const s = getSession(req); if (!s) { res.writeHead(302, { Location: '/login' }); return res.end(); } setImmediate(() => gzipSend(res, buildAnalyticsHTML())); return; }
    if (p === '/media-stats') { const s = getSession(req); if (!s) { res.writeHead(302, { Location: '/login' }); return res.end(); } setImmediate(() => gzipSend(res, buildMediaStatsHTML())); return; }

    if (p.startsWith('/thumbs/')) { const fp = path.join(THUMB_DIR, path.basename(p.slice(8))); if (!fs.existsSync(fp)) { res.writeHead(404); return res.end(); } const stat = fs.statSync(fp); const etag = '"t' + stat.mtimeMs.toString(36) + stat.size.toString(36) + '"'; if (req.headers['if-none-match'] === etag) { res.writeHead(304); return res.end(); } res.writeHead(200, { 'Content-Type': 'image/jpeg', 'Content-Length': stat.size, 'Cache-Control': 'public,max-age=604800', 'ETag': etag }); return fs.createReadStream(fp).pipe(res); }

    if (p.startsWith('/video/')) { const fp = path.join(VIDEO_DIR, path.basename(p.slice(7))); if (!fs.existsSync(fp)) { res.writeHead(404); return res.end(); } const stat = fs.statSync(fp), range = req.headers['range']; if (range) { const [s, e] = range.replace(/bytes=/, '').split('-'), start = parseInt(s, 10), end = e ? parseInt(e, 10) : stat.size - 1; res.writeHead(206, { 'Content-Range': 'bytes ' + start + '-' + end + '/' + stat.size, 'Accept-Ranges': 'bytes', 'Content-Length': end - start + 1, 'Content-Type': 'video/mp4', 'Cache-Control': 'public,max-age=86400' }); return fs.createReadStream(fp, { start, end }).pipe(res); } res.writeHead(200, { 'Content-Type': 'video/mp4', 'Content-Length': stat.size, 'Accept-Ranges': 'bytes', 'Cache-Control': 'public,max-age=86400' }); return fs.createReadStream(fp).pipe(res); }

    if (p === '/api/login' && req.method === 'POST') { const body = await collectBody(req); let pw = ''; try { pw = JSON.parse(body.toString()).password || ''; } catch { } if (pw === ADMIN_PASS) { const token = makeToken(); sessions.set(token, { role: 'admin', expires: Date.now() + 86400_000 }); setCookie(res, token, 86400); res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: true })); } res.writeHead(401, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: false })); }
    if (p === '/api/logout' && req.method === 'POST') { const m = (req.headers.cookie || '').match(/mvs=([a-f0-9]+)/); if (m) sessions.delete(m[1]); setCookie(res, '', 0); res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: true })); }

    if (p.startsWith('/uploads/')) { const fp = path.join(UPLOAD_DIR, path.basename(p.slice(9))); if (!fs.existsSync(fp)) { res.writeHead(404); return res.end('Not Found'); } const ext = path.extname(fp).toLowerCase(), mime = MIME[ext] || 'application/octet-stream', stat = fs.statSync(fp); const range = req.headers.range; if (range && mime.startsWith('video/')) { const [s, e] = range.replace(/bytes=/, '').split('-'), start = parseInt(s, 10), end = e ? parseInt(e, 10) : stat.size - 1; res.writeHead(206, { 'Content-Range': 'bytes ' + start + '-' + end + '/' + stat.size, 'Accept-Ranges': 'bytes', 'Content-Length': end - start + 1, 'Content-Type': mime, 'Cache-Control': 'public,max-age=86400' }); return fs.createReadStream(fp, { start, end }).pipe(res); } const etag = '"' + stat.mtimeMs.toString(36) + stat.size.toString(36) + '"'; if (req.headers['if-none-match'] === etag) { res.writeHead(304); return res.end(); } res.writeHead(200, { 'Content-Type': mime, 'Content-Length': stat.size, 'Accept-Ranges': 'bytes', 'Cache-Control': 'public,max-age=86400', 'ETag': etag }); return fs.createReadStream(fp).pipe(res); }

    if (p === '/api/posts' && req.method === 'GET') { const db = readDB(), posts = [...db.posts].reverse(), json = JSON.stringify(posts), ae = req.headers['accept-encoding'] || ''; if (ae.includes('gzip')) { zlib.gzip(Buffer.from(json), (err, buf) => { if (err) { res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-cache' }); return res.end(json); } res.writeHead(200, { 'Content-Type': 'application/json', 'Content-Encoding': 'gzip', 'Vary': 'Accept-Encoding', 'Cache-Control': 'no-cache' }); res.end(buf); }); } else { res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-cache' }); res.end(json); } return; }

    if (p === '/api/delete-by-date' && req.method === 'POST') { if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); } let dk = ''; try { const b = await collectBody(req); dk = JSON.parse(b.toString()).date || ''; } catch { } if (!dk) { res.writeHead(400); return res.end(); } const db = readDB(), toDel = db.posts.filter(post => { const d = new Date(post.createdAt); return (d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0')) === dk; }); toDel.forEach(deletePostFiles); db.posts = db.posts.filter(post => { const d = new Date(post.createdAt); return (d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0')) !== dk; }); writeDB(db); res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: true, deleted: toDel.length })); }

    if (p === '/api/file-audit' && req.method === 'GET') { if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); } const db = readDB(), posts = db.posts || [], dbFiles = new Set(), dbConvs = new Set(); posts.forEach(post => { (post.files || []).forEach(f => dbFiles.add(f)); if (post.convFile) dbConvs.add(post.convFile); }); const diskUploads = new Set(fs.readdirSync(UPLOAD_DIR).filter(f => !f.startsWith('.'))); const orphanUploads = [...diskUploads].filter(f => !dbFiles.has(f)); const missingUploads = [...dbFiles].filter(f => !diskUploads.has(f)); let orphanSize = 0; orphanUploads.forEach(f => { try { orphanSize += fs.statSync(path.join(UPLOAD_DIR, f)).size; } catch { } }); res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-cache' }); return res.end(JSON.stringify({ summary: { dbPosts: posts.length, dbFiles: dbFiles.size, diskUploads: diskUploads.size, orphanCount: orphanUploads.length, orphanSize, missingCount: missingUploads.length }, missing: { uploads: missingUploads }, orphan: { uploads: orphanUploads } })); }

    if (p.startsWith('/api/delete/') && req.method === 'DELETE') { if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); } const id = parseInt(p.slice(12)), db = readDB(), post = db.posts.find(x => x.id === id); if (post) { deletePostFiles(post); db.posts = db.posts.filter(x => x.id !== id); writeDB(db); } res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: true })); }

    if (p.startsWith('/api/convert/') && req.method === 'POST') { if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); } const id = parseInt(p.slice(13)), db = readDB(), post = db.posts.find(x => x.id === id); if (!post || post.type !== 'video') { res.writeHead(404); return res.end('Not found'); } if (post.convFile && fs.existsSync(path.join(VIDEO_DIR, post.convFile))) { res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: true, already: true, convFile: post.convFile })); } const aq = _processQueue.some(x => x.id === id) || _processCurrent.has(post.files[0]); if (!aq) { _processQueue.push(post); _processTotal++; if (!_processing) { _processing = true; setImmediate(() => processNext()); } } res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: true, queued: true })); }

    if (p.startsWith('/api/convert-status/') && req.method === 'GET') { if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); } const id = parseInt(p.slice(20)), db = readDB(), post = db.posts.find(x => x.id === id); if (!post) { res.writeHead(404); return res.end(); } const cf = post.convFile || null, done = !!(cf && fs.existsSync(path.join(VIDEO_DIR, cf))); res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-cache' }); return res.end(JSON.stringify({ done, failed: !!post.broken, running: _processCurrent.has(post.files[0]), convFile: done ? cf : null })); }

    if (p === '/api/status-data') { if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); } const db = readDB(), videos = db.posts.filter(x => x.type === 'video').reverse(), items = videos.map(x => { const cr = !!x.convFile && fs.existsSync(path.join(VIDEO_DIR, x.convFile)), fp = path.join(UPLOAD_DIR, x.files[0]), size = fs.existsSync(fp) ? fs.statSync(fp).size : 0; return { id: x.id, file: x.files[0], createdAt: x.createdAt, convReady: cr, inQueue: _processQueue.some(q => q.id === x.id), isCurrent: _processCurrent.has(x.files[0]), size, dur: x.meta?.dur || 0, convInfo: x.meta?.convInfo || '', broken: !!x.broken }; }); const done = items.filter(x => x.convReady).length, brokenCount = items.filter(x => x.broken).length; res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-cache' }); return res.end(JSON.stringify({ total: videos.length, done, running: _processing, currentFiles: [..._processCurrent], pct: videos.length ? Math.round(done / videos.length * 100) : 100, items, brokenCount })); }

    if (p === '/api/process' && req.method === 'POST') { if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); } const count = startProcessQueue(false); res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ queued: count })); }
    if (p === '/api/process-force' && req.method === 'POST') { if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); } const count = startProcessQueue(true); res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ queued: count })); }
    if (p === '/api/clear-broken' && req.method === 'POST') { if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); } const db = readDB(); let cleared = 0; db.posts.forEach(x => { if (x.broken) { delete x.broken; delete x.brokenReason; cleared++; } }); writeDB(db); res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: true, cleared })); }

    if (p === '/api/refetch-meta' && req.method === 'POST') { if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); } if (_metaRunning) { res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ queued: -1 })); } let force = false; try { const b = await collectBody(req); force = JSON.parse(b.toString()).force === true; } catch { } const db = readDB(), targets = db.posts.filter(x => { if (x.type !== 'video') return false; if (force) return true; return !x.meta || (x.meta.convInfo && x.meta.convInfo.includes('?')); }); res.writeHead(200, { 'Content-Type': 'application/json' }); res.end(JSON.stringify({ queued: targets.length })); if (!targets.length) return; _metaRunning = true; _metaTotal = targets.length; _metaDone = 0; (async () => { for (const post of targets) { const vp = path.join(UPLOAD_DIR, post.files[0]); if (!fs.existsSync(vp)) { const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); if (pp && !pp.meta) { pp.meta = { error: true, reason: 'file_missing' }; writeDB(db2); } _metaDone++; continue; } try { const info = await ffprobe(vp), vS = info?.streams?.find(s => s.codec_type === 'video'), aS = info?.streams?.find(s => s.codec_type === 'audio'), vC = vS?.codec_name || '', aC = aS?.codec_name || '', dur = Math.round(parseFloat(vS?.duration || info?.format?.duration || 0)), size = fs.statSync(vp).size, ci = vC + (vC === 'h264' ? '(copy)' : '→h264') + ' / ' + (aC ? aC + (aC === 'aac' ? '(copy)' : '→aac') : 'no audio'); const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); if (pp) { pp.meta = { vCodec: vC, aCodec: aC, dur, size, convInfo: ci }; writeDB(db2); } } catch (e) { console.error('refetch-meta', post.id, e.message); const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); if (pp && !pp.meta) { pp.meta = { error: true, reason: e.message }; writeDB(db2); } } _metaDone++; await new Promise(r => setImmediate(r)); } _metaRunning = false; })(); return; }
    if (p === '/api/meta-status') { if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); } res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-cache' }); return res.end(JSON.stringify({ running: _metaRunning, done: _metaDone, total: _metaTotal })); }

    if (p === '/api/generate-thumbs' && req.method === 'POST') { if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); } if (_thumbRunning) { res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ queued: -1 })); } const db = readDB(), targets = db.posts.filter(x => x.type === 'video' && !x.thumb); res.writeHead(200, { 'Content-Type': 'application/json' }); res.end(JSON.stringify({ queued: targets.length })); if (!targets.length) return; _thumbRunning = true; _thumbTotal = targets.length; _thumbDone = 0; (async () => { for (const post of targets) { const vp = path.join(UPLOAD_DIR, post.files[0]); if (!fs.existsSync(vp)) { const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); if (pp) { pp.thumb = '_failed'; writeDB(db2); } _thumbDone++; continue; } try { const out = await generateThumb(vp, post.id); if (out) { const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); if (pp) { pp.thumb = post.id + '.jpg'; writeDB(db2); } } else { const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); if (pp) { pp.thumb = '_failed'; writeDB(db2); } } } catch (e) { console.error('[gen-thumb]', post.id, e.message); const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); if (pp) { pp.thumb = '_failed'; writeDB(db2); } } _thumbDone++; await new Promise(r => setImmediate(r)); } _thumbRunning = false; console.log('[gen-thumbs] done'); })(); return; }
    if (p === '/api/force-generate-thumbs' && req.method === 'POST') { 
        if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); } 
        if (_thumbRunning) { res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ queued: -1 })); } 
        try { 
            if (fs.existsSync(THUMB_DIR)) { 
                const files = fs.readdirSync(THUMB_DIR); 
                for (const file of files) { 
                    try { 
                        fs.unlinkSync(path.join(THUMB_DIR, file)); 
                        logFFmpeg('force-thumbs', 'delete', `Deleted thumbnail: ${file}`); 
                    } catch (e) { 
                        logFFmpeg('force-thumbs-error', 'delete', `Failed to delete ${file}: ${e.message}`); 
                    } 
                } 
                logFFmpeg('force-thumbs', 'delete', `Deleted ${files.length} thumbnails from thumbs/`); 
            } else { 
                logFFmpeg('force-thumbs', 'delete', 'thumbs/ directory does not exist'); 
            } 
            const db = readDB(); 
            db.posts.forEach(x => { if (x.type === 'video') { delete x.thumb; } }); 
            writeDB(db); 
            const targets = db.posts.filter(x => x.type === 'video'); 
            res.writeHead(200, { 'Content-Type': 'application/json' }); 
            res.end(JSON.stringify({ queued: targets.length })); 
            if (!targets.length) return; 
            _thumbRunning = true; 
            _thumbTotal = targets.length; 
            _thumbDone = 0; 
            (async () => { 
                for (const post of targets) { 
                    const vp = path.join(UPLOAD_DIR, post.files[0]); 
                    if (!fs.existsSync(vp)) { 
                        const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); 
                        if (pp) { pp.thumb = '_failed'; writeDB(db2); } 
                        _thumbDone++; continue; 
                    } 
                    try { 
                        const out = await generateThumb(vp, post.id); 
                        if (out) { 
                            const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); 
                            if (pp) { pp.thumb = post.id + '.jpg'; writeDB(db2); } 
                        } else { 
                            const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); 
                            if (pp) { pp.thumb = '_failed'; writeDB(db2); } 
                        } 
                    } catch (e) { 
                        logFFmpeg('force-thumbs-error', post.id, e.message); 
                        const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); 
                        if (pp) { pp.thumb = '_failed'; writeDB(db2); } 
                    } 
                    _thumbDone++; 
                    await new Promise(r => setImmediate(r)); 
                } 
                _thumbRunning = false; 
                logFFmpeg('force-thumbs', 'complete', `Force regenerated ${targets.length} thumbnails`); 
            })(); 
            return; 
        } catch (e) { 
            logFFmpeg('force-thumbs-error', 'init', e.message); 
            res.writeHead(500, { 'Content-Type': 'application/json' }); 
            return res.end(JSON.stringify({ error: e.message })); 
        } 
    } else if (p === '/api/thumb-status') {
        if (!getSession(req)) {
            res.writeHead(401);
            return res.end('Unauthorized');
        }
        res.writeHead(200, {
            'Content-Type': 'application/json',
            'Cache-Control': 'no-cache'
        });
        return res.end(
            JSON.stringify({
                running: _thumbRunning,
                done: _thumbDone,
                total: _thumbTotal
            })
        );
    } else if (p === '/api/diagnostics') {
        if (!getSession(req)) {
            res.writeHead(401);
            return res.end('Unauthorized');
        }
        const db = readDB(), resData = { items: [] };

        const checkFfprobe = () => new Promise(r => execFile(FFPROBE, ['-version'], err => r(!err)));
        const checkFfmpeg = () => new Promise(r => execFile(FFMPEG, ['-version'], err => r(!err)));
        const checkDir = d => { try { fs.accessSync(d, fs.constants.R_OK | fs.constants.W_OK); return true; } catch { return false; } };
        const getDirSize = d => { let s = 0; try { fs.readdirSync(d).forEach(f => { try { s += fs.statSync(path.join(d, f)).size; } catch { } }); } catch { } return s; };

        const [ffmOk, ffpOk] = await Promise.all([checkFfmpeg(), checkFfprobe()]);

        if (!ffmOk || !ffpOk) resData.items.push({ type: 'error', id: 'ffmpeg', title: 'FFmpeg/FFprobe', msg: `ไม่พบคำสั่ง หรือเรียกใช้งานไม่ได้ (${FFMPEG}, ${FFPROBE})`, action: 'ติดตั้ง ffmpeg หรือแก้ตัวแปร FFMPEG/FFPROBE ในโค้ด', actBtn: null });
        else resData.items.push({ type: 'ok', id: 'ffmpeg', title: 'FFmpeg/FFprobe', msg: 'พร้อมใช้งาน', action: null });

        if (!checkDir(UPLOAD_DIR) || !checkDir(VIDEO_DIR) || !checkDir(THUMB_DIR)) resData.items.push({ type: 'error', id: 'dirs', title: 'โฟลเดอร์ระบบ', msg: 'อ่าน/เขียน โฟลเดอร์ uploads, video, หรือ thumbs ไม่ได้', action: 'เช็ค Permission หน้าโฟลเดอร์', actBtn: null });
        else resData.items.push({ type: 'ok', id: 'dirs', title: 'โฟลเดอร์ระบบ', msg: 'อ่านและเขียนได้ปกติ', action: null });

        try { fs.accessSync(DB_FILE, fs.constants.R_OK | fs.constants.W_OK); resData.items.push({ type: 'ok', id: 'db', title: 'ฐานข้อมูล (db.json)', msg: `อ่านเขียนได้ (${db.posts.length} โพสต์)`, action: null }); }
        catch { resData.items.push({ type: 'error', id: 'db', title: 'ฐานข้อมูล (db.json)', msg: 'อ่าน/เขียน db.json ไม่ได้', action: 'เช็ค Permission ไฟล์', actBtn: null }); }

        let missing = [];
        db.posts.forEach(p => { let f = p.files[0]; if (f && !fs.existsSync(path.join(UPLOAD_DIR, f))) missing.push(p.id); });
        if (missing.length > 0) resData.items.push({ type: 'error', id: 'missing', title: 'ไฟล์หาย', msg: `มี ${missing.length} โพสต์ที่ไฟล์ต้นฉบับหายไปจากดิสก์`, action: 'ลบโพสต์ที่ไฟล์หายทิ้ง', actBtn: 'fixMissing' });
        else resData.items.push({ type: 'ok', id: 'missing', title: 'ไฟล์บนดิสก์', msg: 'โพสต์ทั้งหมดมีไฟล์ต้นฉบับอยู่ครบ', action: null });

        let sz = getDirSize(UPLOAD_DIR) + getDirSize(VIDEO_DIR) + getDirSize(THUMB_DIR);
        resData.items.push({ type: 'info', id: 'storage', title: 'พื้นที่จัดเก็บ', msg: `ใช้พื้นที่ไปแล้ว ${(sz / (1024 * 1024)).toFixed(1)} MB`, action: null });

        let thumbFailed = db.posts.filter(x => x.type === 'video' && x.thumb === '_failed').length;
        let thumbMissing = db.posts.filter(x => x.type === 'video' && (!x.thumb || x.thumb === '_failed')).length;
        if (thumbMissing > 0) resData.items.push({ type: 'warn', id: 'thumb', title: 'หน้าปกวิดีโอ', msg: `ขาด ${thumbMissing} รูป, Error(สร้างไม่ได้) ${thumbFailed} รูป`, action: 'กดปุ่ม "สร้างปก" ด้านบน', actBtn: null });
        else resData.items.push({ type: 'ok', id: 'thumb', title: 'หน้าปกวิดีโอ', msg: 'วิดีโอทั้งหมดมีปกครบ (หรือพยายามสร้างครบแล้ว)', action: null });

        let metaFail = db.posts.filter(x => x.type === 'video' && x.meta && x.meta.error).length;
        let metaMissing = db.posts.filter(x => x.type === 'video' && (!x.meta || (x.meta.convInfo && x.meta.convInfo.includes('?')) || x.meta.error)).length;
        if (metaMissing > 0) resData.items.push({ type: 'warn', id: 'meta', title: 'ข้อมูล Meta', msg: `ไม่มี meta ${metaMissing} รายการ, Error ${metaFail} รายการ`, action: 'กดปุ่ม "รีเฟรช Meta"', actBtn: null });
        else resData.items.push({ type: 'ok', id: 'meta', title: 'ข้อมูล Meta', msg: 'มีข้อมูลครบทุกวิดีโอ', action: null });

        let brokenConv = db.posts.filter(x => x.type === 'video' && x.broken).length;
        let pendConv = db.posts.filter(x => x.type === 'video' && !x.broken && (!x.convFile || !fs.existsSync(path.join(VIDEO_DIR, x.convFile)))).length;
        if (brokenConv > 0) resData.items.push({ type: 'error', id: 'conv-broken', title: 'การแปลงวิดีโอ', msg: `มีไฟล์เสียแปลงไม่ได้ (Broken) ${brokenConv} ไฟล์`, action: 'กดลบ Broken ด้านบน', actBtn: null });
        else if (pendConv > 0) resData.items.push({ type: 'warn', id: 'conv', title: 'การแปลงวิดีโอ', msg: `รอแปลง ${pendConv} ไฟล์`, action: 'กดปุ่ม "เริ่มแปลง"', actBtn: null });
        else resData.items.push({ type: 'ok', id: 'conv', title: 'การแปลงวิดีโอ', msg: 'แปลงเสร็จสมบูรณ์ทุกไฟล์', action: null });

        let allDBFiles = new Set();
        db.posts.forEach(p => { p.files.forEach(f => allDBFiles.add(f)); if (p.convFile) allDBFiles.add(p.convFile); if (p.thumb && p.thumb !== '_failed') allDBFiles.add(p.thumb); });
        let orphansCount = 0;
        try { fs.readdirSync(UPLOAD_DIR).forEach(f => { if (!allDBFiles.has(f)) orphansCount++; }); } catch { }
        try { fs.readdirSync(VIDEO_DIR).forEach(f => { if (!allDBFiles.has(f)) orphansCount++; }); } catch { }
        try { fs.readdirSync(THUMB_DIR).forEach(f => { if (!allDBFiles.has(f)) orphansCount++; }); } catch { }
        if (orphansCount > 0) resData.items.push({ type: 'warn', id: 'orphan', title: 'ไฟล์ขยะ (Orphan)', msg: `พบไฟล์ที่ไม่มีใน DB ตกค้าง ${orphansCount} ไฟล์`, action: 'ลบไฟล์ขยะเพื่อคืนพื้นที่', actBtn: 'fixOrphan' });
        else resData.items.push({ type: 'ok', id: 'orphan', title: 'ไฟล์ขยะ (Orphan)', msg: 'ไม่พบไฟล์ตกค้าง', action: null });

        res.writeHead(200, { 'Content-Type': 'application/json', 'Cache-Control': 'no-cache' });
        return res.end(JSON.stringify(resData));
    }

    if (p === '/api/fix-missing' && req.method === 'POST') {
        if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); }
        const db = readDB(); let cleared = 0;
        db.posts = db.posts.filter(p => { let f = p.files[0]; if (f && !fs.existsSync(path.join(UPLOAD_DIR, f))) { cleared++; return false; } return true; });
        writeDB(db); res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: true, cleared }));
    }

    if (p === '/api/fix-orphan' && req.method === 'POST') {
        if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); }
        const db = readDB(); let allDBFiles = new Set(), cleared = 0;
        db.posts.forEach(p => { p.files.forEach(f => allDBFiles.add(f)); if (p.convFile) allDBFiles.add(p.convFile); if (p.thumb && p.thumb !== '_failed') allDBFiles.add(p.thumb); });
        try { fs.readdirSync(UPLOAD_DIR).forEach(f => { if (!allDBFiles.has(f)) { try { fs.unlinkSync(path.join(UPLOAD_DIR, f)); cleared++; } catch { } } }); } catch { }
        try { fs.readdirSync(VIDEO_DIR).forEach(f => { if (!allDBFiles.has(f)) { try { fs.unlinkSync(path.join(VIDEO_DIR, f)); cleared++; } catch { } } }); } catch { }
        try { fs.readdirSync(THUMB_DIR).forEach(f => { if (!allDBFiles.has(f)) { try { fs.unlinkSync(path.join(THUMB_DIR, f)); cleared++; } catch { } } }); } catch { }
        res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(JSON.stringify({ ok: true, cleared }));
    }

    res.writeHead(404); res.end('Not Found');
}

async function handleUpload(req, res) {
    if (!getSession(req)) { res.writeHead(401); return res.end('Unauthorized'); }
    const ct = req.headers['content-type'] || '', bm = ct.match(/boundary=(.+)$/);
    if (!bm) { res.writeHead(400); return res.end('Bad Request'); }
    _uploadActive++;
    let savedParts;
    try { savedParts = await streamMultipart(req, bm[1].trim(), UPLOAD_DIR); } catch (e) { _uploadActive--; console.error('[upload]', e.message); res.writeHead(500); return res.end('Upload failed'); }
    if (!savedParts.length) { _uploadActive--; res.writeHead(400); return res.end('No files'); }
    const saved = savedParts.map(p => p.fname), hasVideo = savedParts.some(p => p.contentType.startsWith('video/')), type = hasVideo ? 'video' : saved.length > 1 ? 'images' : 'image', id = Date.now(), db = readDB();
    db.posts.push({ id, files: saved, type, createdAt: new Date().toISOString() });
    writeDB(db); _uploadActive--;
    res.writeHead(200, { 'Content-Type': 'application/json' }); res.end(JSON.stringify({ ok: true }));
    if (hasVideo) { generateThumb(path.join(UPLOAD_DIR, saved[0]), id).then(out => { if (out) { const db2 = readDB(), pp = db2.posts.find(x => x.id === id); if (pp) { pp.thumb = id + '.jpg'; writeDB(db2); } } }).catch(() => { }); }
}

// ── Process queue ──
let _processing = false, _processQueue = [], _processTotal = 0;
let _metaRunning = false, _metaTotal = 0, _metaDone = 0;
let _thumbRunning = false, _thumbTotal = 0, _thumbDone = 0;
let _processDone = 0, _processCurrent = new Set(), _activeJobs = 0;

function startProcessQueue(forceAll) {
    if (_processing) return -1;
    const db = readDB(); let pending;
    if (forceAll) { try { fs.rmSync(VIDEO_DIR, { recursive: true, force: true }); } catch { } fs.mkdirSync(VIDEO_DIR, { recursive: true }); pending = db.posts.filter(x => x.type === 'video'); pending.forEach(x => { x.convFile = null; x.meta = null; }); writeDB(db); }
    else { pending = db.posts.filter(x => { if (x.type !== 'video' || x.broken) return false; return !x.convFile || !fs.existsSync(path.join(VIDEO_DIR, x.convFile)); }); pending.forEach(x => { if (x.convFile && !fs.existsSync(path.join(VIDEO_DIR, x.convFile))) x.convFile = null; }); writeDB(db); }
    if (!pending.length) return 0;
    _processQueue = pending.slice(); _processTotal = pending.length; _processDone = 0; _activeJobs = 0; _processCurrent = new Set(); _processing = true;
    for (let i = 0; i < Math.min(MAX_PARALLEL, pending.length); i++)setImmediate(() => processNext());
    return pending.length;
}
function processNext() { if (!_processQueue.length) { if (_activeJobs === 0) { _processing = false; _processCurrent = new Set(); flushDB(); } return; } _activeJobs++; processOne(_processQueue.shift()).then(() => { _activeJobs--; processNext(); }); }
async function processOne(post) {
    const vp = path.join(UPLOAD_DIR, post.files[0]); _processCurrent.add(post.files[0]);
    if (!fs.existsSync(vp)) { _processCurrent.delete(post.files[0]); _processDone++; return; }
    try {
        const info = await ffprobe(vp), vS = info?.streams?.find(s => s.codec_type === 'video'), aS = info?.streams?.find(s => s.codec_type === 'audio');
        const vC = vS?.codec_name || '', aC = aS?.codec_name || '', dur = parseFloat(vS?.duration || info?.format?.duration || 0), size = fs.statSync(vp).size;
        const ci = vC + (vC === 'h264' ? '(copy)' : '→h264') + ' / ' + (aC ? aC + (aC === 'aac' ? '(copy)' : '→aac') : 'no audio');
        if (!post.convFile) { const outFile = await makeMP4(vp, post.id); if (outFile) { const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); if (pp) { pp.convFile = post.id + '.mp4'; pp.meta = { vCodec: vC, aCodec: aC, dur: Math.round(dur), size, convInfo: ci }; writeDB(db2); } } }
        else if (!post.meta) { const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); if (pp) { pp.meta = { vCodec: vC, aCodec: aC, dur: Math.round(dur), size, convInfo: ci }; writeDB(db2); } }
        if (!post.thumb) { const thumbOut = await generateThumb(vp, post.id); if (thumbOut) { const db3 = readDB(), pp3 = db3.posts.find(x => x.id === post.id); if (pp3) { pp3.thumb = post.id + '.jpg'; writeDB(db3); } } }
        _processCurrent.delete(post.files[0]); _processDone++; console.log('[' + _processDone + '/' + _processTotal + '] ' + post.files[0]);
    } catch (e) {
        _processCurrent.delete(post.files[0]); _processDone++;
        if (e.broken) { console.warn('[BROKEN]', post.id); const db2 = readDB(), pp = db2.posts.find(x => x.id === post.id); if (pp) { pp.broken = true; pp.brokenReason = 'moov atom not found'; writeDB(db2); } }
        else console.error('[ERROR]', post.id, e.message);
    }
}

process.on('SIGTERM', () => { flushDB(); process.exit(0); });
process.on('SIGINT', () => { flushDB(); process.exit(0); });

server.on('connection', socket => { socket.setNoDelay(true); socket.setTimeout(0); socket.setKeepAlive(true, 5000); });

server.listen(PORT, () => {
    console.log('\nMyVault ready');
    console.log('  Guest : http://localhost:' + PORT + '/guest');
    console.log('  Admin : http://localhost:' + PORT + '/login');
    console.log('  Pass  : ' + ADMIN_PASS);
    console.log('  CPU   : ' + CPU_CORES + ' cores\n');
    const db = readDB(); let fixed = 0;
    db.posts.forEach(x => { if (x.thumb) { delete x.thumb; fixed++; } if (x.convFile && !fs.existsSync(path.join(VIDEO_DIR, x.convFile))) { x.convFile = null; fixed++; } });
    if (fixed) { writeDB(db); console.log('[startup] cleaned', fixed, 'stale fields'); }
});
