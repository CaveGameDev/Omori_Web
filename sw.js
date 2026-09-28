/* sw.js — zip-backed VFS
 *
 * The launcher (index.html) posts the assembled o.zip Blob to this worker
 * ({ type: 'MOUNT' }). The worker indexes ONLY the zip's central directory
 * (~1 MB for a 348 MB archive), keeps the Blob itself, and serves every path
 * inside the zip under /virtual/... on demand:
 *
 *   - STORED entries: byte range sliced straight off the Blob
 *   - DEFLATED entries: decompressed on demand with DecompressionStream('deflate-raw')
 *   - full paths (folders preserved), case-insensitive lookups, URI decoding
 *   - correct MIME types for html/js/css/wasm/audio/video/img/font/json/etc.
 *   - HTTP Range requests answered with real 206 + Content-Range responses
 *     (so <video> seeking and streaming work)
 *   - honest 404s for missing files, 503 while not yet mounted
 *
 * Nothing is decompressed ahead of time, so the 348 MB archive mounts in
 * milliseconds without ever being held fully in memory at once.
 */

const VFS_SCOPE_PATH = '/virtual/';

let zipBlob = null;                 // the assembled archive
let entries = new Map();            // normalized path -> entry record
let entriesInsensitive = new Map(); // lower-cased path -> canonical path

const textDecoder = new TextDecoder('utf-8');

/* ---- small helpers ----------------------------------------------------- */

function normalizePath(p) {
    let path = String(p).replace(/\\/g, '/');
    path = path.replace(/^[A-Za-z]:/, ''); // strip a drive-letter-ish prefix
    const parts = [];
    for (const seg of path.split('/')) {
        if (!seg || seg === '.') continue;
        if (seg === '..') { parts.pop(); continue; }
        parts.push(seg);
    }
    return parts.join('/');
}

function lookupPath(path) {
    const norm = normalizePath(path);
    if (entries.has(norm)) return norm;
    return entriesInsensitive.get(norm.toLowerCase()) || null;
}

/* ---- MIME -------------------------------------------------------------- */

const MIME = {
    html: 'text/html; charset=utf-8',
    htm: 'text/html; charset=utf-8',
    js: 'text/javascript; charset=utf-8',
    mjs: 'text/javascript; charset=utf-8',
    json: 'application/json; charset=utf-8',
    css: 'text/css; charset=utf-8',
    wasm: 'application/wasm',
    txt: 'text/plain; charset=utf-8',
    ini: 'text/plain; charset=utf-8',
    yaml: 'text/yaml; charset=utf-8',
    yml: 'text/yaml; charset=utf-8',
    xml: 'application/xml',
    png: 'image/png',
    jpg: 'image/jpeg',
    jpeg: 'image/jpeg',
    gif: 'image/gif',
    webp: 'image/webp',
    bmp: 'image/bmp',
    svg: 'image/svg+xml',
    ico: 'image/x-icon',
    ogg: 'audio/ogg',
    oga: 'audio/ogg',
    opus: 'audio/ogg',
    mp3: 'audio/mpeg',
    wav: 'audio/wav',
    m4a: 'audio/mp4',
    mp4: 'video/mp4',
    webm: 'video/webm',
    m4v: 'video/mp4',
    ttf: 'font/ttf',
    otf: 'font/otf',
    woff: 'font/woff',
    woff2: 'font/woff2',
    zip: 'application/zip'
};

function mimeFor(path) {
    const name = path.split('/').pop() || '';
    const dot = name.lastIndexOf('.');
    if (dot < 0) return 'application/octet-stream';
    return MIME[name.slice(dot + 1).toLowerCase()] || 'application/octet-stream';
}

/* ---- zip central directory --------------------------------------------- */

const SIG_EOCD = 0x06054b50;
const SIG_CD = 0x02014b50;
const SIG_LOCAL = 0x04034b50;
const SIG_Z64_EOCD = 0x06064b50;
const SIG_Z64_LOC = 0x07064b50;

function readU16(b, o) { return b[o] | (b[o + 1] << 8); }
function readU32(b, o) { return (b[o] | (b[o + 1] << 8) | (b[o + 2] << 16) | (b[o + 3] << 24)) >>> 0; }
function readU64(b, o) { return readU32(b, o) + readU32(b, o + 4) * 4294967296; }

async function indexZip(blob) {
    const size = blob.size;
    if (size < 22) throw new Error('not a zip (too small)');

    // find the End Of Central Directory record (allows a trailing comment)
    const tailLen = Math.min(65557, size);
    const tail = new Uint8Array(await blob.slice(size - tailLen).arrayBuffer());
    let eocd = -1;
    for (let i = tail.length - 22; i >= 0; i--) {
        if (readU32(tail, i) === SIG_EOCD) { eocd = i; break; }
    }
    if (eocd < 0) throw new Error('zip EOCD not found');

    let count = readU16(tail, eocd + 10);
    let cdSize = readU32(tail, eocd + 12);
    let cdOff = readU32(tail, eocd + 16);

    // zip64: real offsets/counts live in the zip64 EOCD record the locator points to
    if (cdOff === 0xffffffff || count === 0xffff || cdSize === 0xffffffff) {
        if (eocd >= 20 && readU32(tail, eocd - 20) === SIG_Z64_LOC) {
            const z64Off = readU64(tail, eocd - 20 + 8);
            const z64 = new Uint8Array(await blob.slice(z64Off, z64Off + 56).arrayBuffer());
            if (readU32(z64, 0) === SIG_Z64_EOCD) {
                count = readU64(z64, 32);
                cdSize = readU64(z64, 40);
                cdOff = readU64(z64, 48);
            }
        }
    }

    const cd = new Uint8Array(await blob.slice(cdOff, cdOff + cdSize).arrayBuffer());
    const map = new Map();
    const lower = new Map();
    let off = 0;

    for (let n = 0; n < count && off + 46 <= cd.length; n++) {
        if (readU32(cd, off) !== SIG_CD) break;
        const flags = readU16(cd, off + 8);
        const method = readU16(cd, off + 10);
        const csize = readU32(cd, off + 20);
        const usize = readU32(cd, off + 24);
        const nameLen = readU16(cd, off + 28);
        const extraLen = readU16(cd, off + 30);
        const commentLen = readU16(cd, off + 32);
        const lhOff32 = readU32(cd, off + 42);
        let name = textDecoder.decode(cd.subarray(off + 46, off + 46 + nameLen));
        const extraStart = off + 46 + nameLen;
        off += 46 + nameLen + extraLen + commentLen;

        if (!(flags & 0x800) && /%[0-9a-fA-F]{2}/.test(name)) {
            try { name = decodeURIComponent(name); } catch (e) {}
        }

        const normalized = normalizePath(name);
        if (!normalized || normalized.endsWith('/')) continue; // directory entry

        // zip64 extra field (0x0001) carries the real sizes/offsets
        let ucsize = usize, ccsize = csize, localOff = lhOff32;
        let extra = extraStart;
        const extraEnd = extraStart + extraLen;
        while (extra + 4 <= extraEnd) {
            const id = readU16(cd, extra);
            const sz = readU16(cd, extra + 2);
            if (id === 0x0001) {
                let p = extra + 4;
                if (usize === 0xffffffff) { ucsize = readU64(cd, p); p += 8; }
                if (csize === 0xffffffff) { ccsize = readU64(cd, p); p += 8; }
                if (lhOff32 === 0xffffffff) { localOff = readU64(cd, p); p += 8; }
                break;
            }
            extra += 4 + sz;
        }

        const record = { path: normalized, method, csize: ccsize, usize: ucsize, lhOff: localOff };
        map.set(normalized, record);
        const key = normalized.toLowerCase();
        if (!lower.has(key)) lower.set(key, normalized);
    }

    if (map.size === 0) throw new Error('zip central directory is empty');
    return { map, lower };
}

// Resolve an entry's data span from its local header (local name/extra lengths
// can differ from the central directory's, so they are read again here).
async function entryDataSpan(entry) {
    const head = new Uint8Array(await zipBlob.slice(entry.lhOff, entry.lhOff + 30).arrayBuffer());
    if (readU32(head, 0) !== SIG_LOCAL) throw new Error('bad local header for ' + entry.path);
    const nameLen = readU16(head, 26);
    const extraLen = readU16(head, 28);
    const dataOff = entry.lhOff + 30 + nameLen + extraLen;
    return { start: dataOff, end: dataOff + entry.csize }; // [start, end) on the blob
}

/* ---- serving ----------------------------------------------------------- */

function withCors(headers) {
    headers.set('Access-Control-Allow-Origin', '*');
    headers.set('Accept-Ranges', 'bytes');
    return headers;
}

function baseHeaders(path) {
    const h = new Headers();
    h.set('Content-Type', mimeFor(path));
    h.set('Cache-Control', 'no-cache');
    return withCors(h);
}

async function entryBytes(entry) {
    const span = await entryDataSpan(entry);
    const raw = await zipBlob.slice(span.start, span.end).arrayBuffer();

    if (entry.method === 0) return raw; // stored
    if (entry.method === 8) {           // deflate
        if (typeof DecompressionStream === 'undefined') {
            throw new Error('DecompressionStream unavailable in this browser');
        }
        const stream = new Blob([raw]).stream().pipeThrough(new DecompressionStream('deflate-raw'));
        return await new Response(stream).arrayBuffer();
    }
    throw new Error('unsupported zip compression method ' + entry.method + ' for ' + entry.path);
}

function parseRange(header, total) {
    const m = /^bytes=(\d*)-(\d*)$/.exec(String(header || '').trim());
    if (!m || (m[1] === '' && m[2] === '')) return null;
    let start, end;
    if (m[1] === '') {                  // suffix form: bytes=-N
        const n = parseInt(m[2], 10);
        if (n === 0) return { status: 416 };
        start = Math.max(0, total - n);
        end = total - 1;
    } else {
        start = parseInt(m[1], 10);
        end = m[2] === '' ? total - 1 : Math.min(parseInt(m[2], 10), total - 1);
    }
    if (start >= total || start > end) return { status: 416 };
    return { status: 206, start, end };
}

function notFound(path) {
    return new Response(JSON.stringify({ error: 'not found', path }), {
        status: 404,
        headers: withCors(new Headers({ 'Content-Type': 'application/json; charset=utf-8' }))
    });
}

async function serveVirtual(url, request) {
    if (!zipBlob || entries.size === 0) {
        return new Response('VFS not mounted', { status: 503, headers: { 'Content-Type': 'text/plain' } });
    }

    let rel = url.pathname;
    try { rel = decodeURIComponent(rel); } catch (e) {}
    if (rel.startsWith(VFS_SCOPE_PATH)) rel = rel.slice(VFS_SCOPE_PATH.length);
    else if (rel === '/virtual') rel = '';
    rel = rel.replace(/^\/+/, '');

    if (rel === '' || rel.endsWith('/')) rel += 'index.html';

    const canonical = lookupPath(rel);
    if (!canonical) return notFound(url.pathname);
    const entry = entries.get(canonical);
    if (!entry) return notFound(url.pathname);

    // Range support matters for <video> (the cutscenes) — answer real 206s.
    const rangeHeader = request.headers.get('range');
    if (rangeHeader) {
        const parsed = parseRange(rangeHeader, entry.usize);
        if (parsed && parsed.status === 416) {
            return new Response(null, {
                status: 416,
                headers: withCors(new Headers({ 'Content-Range': 'bytes */' + entry.usize }))
            });
        }
        if (parsed && parsed.status === 206) {
            const bytes = await entryBytes(entry);
            const body = bytes.slice(parsed.start, parsed.end + 1);
            const h = baseHeaders(canonical);
            h.set('Content-Range', 'bytes ' + parsed.start + '-' + parsed.end + '/' + entry.usize);
            h.set('Content-Length', String(body.byteLength));
            return new Response(body, { status: 206, headers: h });
        }
        // unrecognized range form: fall through to a full 200
    }

    const bytes = await entryBytes(entry);
    const h = baseHeaders(canonical);
    h.set('Content-Length', String(bytes.byteLength));
    return new Response(bytes, { status: 200, headers: h });
}

/* ---- lifecycle --------------------------------------------------------- */

self.addEventListener('install', () => self.skipWaiting());
self.addEventListener('activate', (event) => event.waitUntil(self.clients.claim()));

self.addEventListener('message', async (event) => {
    const data = event.data || {};
    if (data.type === 'MOUNT') {
        try {
            const blob = data.data instanceof Blob ? data.data : new Blob([data.data]);
            const indexed = await indexZip(blob);
            zipBlob = blob;
            entries = indexed.map;
            entriesInsensitive = indexed.lower;
            const msg = { type: 'MOUNTED', files: entries.size, bytes: blob.size };
            const all = await self.clients.matchAll();
            all.forEach((client) => client.postMessage(msg));
        } catch (err) {
            const all = await self.clients.matchAll();
            all.forEach((client) => client.postMessage({
                type: 'MOUNT_ERROR',
                error: String((err && err.message) || err)
            }));
        }
        return;
    }
    if (data.type === 'PING' && event.source) {
        event.source.postMessage({ type: 'PONG', mounted: !!(zipBlob && entries.size) });
    }
});

self.addEventListener('fetch', (event) => {
    const request = event.request;
    if (request.method !== 'GET' && request.method !== 'HEAD') return;

    const url = new URL(request.url);
    if (!url.pathname.startsWith(VFS_SCOPE_PATH) && url.pathname !== '/virtual') return;

    if (request.method === 'HEAD') {
        event.respondWith(serveVirtual(url, request).then((res) =>
            new Response(null, { status: res.status, headers: res.headers })
        ));
        return;
    }
    event.respondWith(serveVirtual(url, request));
});
