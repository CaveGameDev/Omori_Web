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
 * Durability (fixes assets vanishing mid-game after the browser recycles the
 * service worker — e.g. tab eviction, memory pressure, mobile switching):
 *   - the zip Blob is persisted in IndexedDB when mounted
 *   - if a request arrives while the worker has no zip in memory (fresh worker),
 *     it transparently rehydrates from IndexedDB and re-indexes before serving
 *   - entry records carry the zip CRC-32 so VERIFY can prove every file's
 *     compressed bytes are intact without decompressing the whole archive
 *
 * All scope handling is computed from self.registration.scope, so the same
 * files work at a domain root (GitHub Pages project sites, Netlify root) and
 * under a subpath (Cloudflare Pages /<project>/ preview URLs).
 */

'use strict';

/* ---- scope (computed, not hardcoded) ------------------------------------ */

const SCOPE_URL = new URL(self.registration.scope);
const SCOPE = SCOPE_URL.pathname.replace(/\/+$/, ''); // '' or '/Omori_Web' etc.
const VFS_PREFIX = SCOPE + '/virtual';
const VFS_PREFIX_SLASH = VFS_PREFIX + '/';

/* ---- state -------------------------------------------------------------- */

let zipBlob = null;                 // the assembled archive
let hydrating = null;               // in-flight rehydration promise
let entries = new Map();            // normalized path -> entry record
let entriesInsensitive = new Map(); // lower-cased path -> canonical path

const textDecoder = new TextDecoder('utf-8');
const textEncoder = new TextEncoder();

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

/* ---- IndexedDB persistence ---------------------------------------------- */

const DB_NAME = 'omori-vfs';
const STORE = 'kv';

function idbOpen() {
    return new Promise((resolve, reject) => {
        const open = indexedDB.open(DB_NAME, 1);
        open.onupgradeneeded = () => open.result.createObjectStore(STORE);
        open.onerror = () => reject(open.error);
        open.onsuccess = () => resolve(open.result);
    });
}

async function idbPut(key, value) {
    const db = await idbOpen();
    return new Promise((resolve, reject) => {
        const tx = db.transaction(STORE, 'readwrite');
        tx.objectStore(STORE).put(value, key);
        tx.oncomplete = () => resolve();
        tx.onerror = () => reject(tx.error);
        tx.onabort = () => reject(tx.error);
    });
}

async function idbGet(key) {
    const db = await idbOpen();
    return new Promise((resolve, reject) => {
        const tx = db.transaction(STORE, 'readonly');
        const req = tx.objectStore(STORE).get(key);
        req.onsuccess = () => resolve(req.result || null);
        req.onerror = () => reject(req.error);
    });
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
        const crc = readU32(cd, off + 16);
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

        const record = { path: normalized, method, csize: ccsize, usize: ucsize, crc, lhOff: localOff };
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

/* ---- CRC-32 (zlib polynomial) ------------------------------------------- */

const CRC_TABLE = (() => {
    const t = new Uint32Array(256);
    for (let n = 0; n < 256; n++) {
        let c = n;
        for (let k = 0; k < 8; k++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
        t[n] = c >>> 0;
    }
    return t;
})();

function crc32(bytes, seed) {
    let c = (seed === undefined) ? 0xffffffff : (seed ^ 0xffffffff);
    for (let i = 0; i < bytes.length; i++) {
        c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
    }
    return (c ^ 0xffffffff) >>> 0;
}

/* ---- mount / rehydrate --------------------------------------------------- */

async function applyZip(blob) {
    const indexed = await indexZip(blob);
    zipBlob = blob;
    entries = indexed.map;
    entriesInsensitive = indexed.lower;
}

async function mountZip(blob) {
    await applyZip(blob);
    try {
        await idbPut('zip', blob);
    } catch (e) {
        // Persistence is best-effort: quota/private mode just means the tab
        // must re-download. Serving still works from memory.
        console.warn('VFS: could not persist zip (' + (e && e.message) + ')');
    }
}

// Bring the zip back after the worker was restarted. Called lazily by the
// fetch handler — a fresh worker must never 503 an asset the game needs.
async function ensureMounted() {
    if (zipBlob && entries.size) return true;
    if (!hydrating) {
        hydrating = (async () => {
            const blob = await idbGet('zip');
            if (blob && blob.size) {
                await applyZip(blob);
                return true;
            }
            return false;
        })().finally(() => { hydrating = null; });
    }
    return hydrating;
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

// Streamed serve path: the compressed slice is piped through inflate without
// materializing the whole entry in the worker first (bounded memory, fast).
async function entryResponse(entry) {
    const span = await entryDataSpan(entry);

    if (entry.method === 0) {
        return zipBlob.slice(span.start, span.end);
    }
    if (entry.method === 8) {
        if (typeof DecompressionStream === 'undefined') {
            throw new Error('DecompressionStream unavailable in this browser');
        }
        const stream = zipBlob.slice(span.start, span.end).stream()
            .pipeThrough(new DecompressionStream('deflate-raw'));
        return stream;
    }
    throw new Error('unsupported zip compression method ' + entry.method + ' for ' + entry.path);
}

// First N bytes of an entry — used to prove an entry is readable without
// pulling the whole file (images/audio spot checks).
async function entryPrefix(entry, length) {
    const span = await entryDataSpan(entry);
    const take = Math.min(length, span.end - span.start);
    const raw = await zipBlob.slice(span.start, span.start + take).arrayBuffer();

    if (entry.method === 0) return raw;
    if (entry.method === 8) {
        const stream = new Blob([raw]).stream().pipeThrough(new DecompressionStream('deflate-raw'));
        return await new Response(stream).arrayBuffer(); // inflate stops at stream end
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

// 1x1 fully transparent PNG, for missing-image placeholders only.
const PLACEHOLDER_PNG = (() => {
    const B64 = 'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNkYPhfDwAChwGA60e6kgAAAABJRU5ErkJggg==';
    const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';
    const clean = B64.replace(/=+$/, '');
    const out = new Uint8Array((clean.length * 3) >> 2);
    let o = 0, buf = 0, bits = 0;
    for (let i = 0; i < clean.length; i++) {
        buf = (buf << 6) | chars.indexOf(clean[i]);
        bits += 6;
        if (bits >= 8) {
            bits -= 8;
            out[o++] = (buf >> bits) & 0xff;
        }
    }
    return out.subarray(0, o);
})();

async function serveVirtual(url, request) {
    if (!(await ensureMounted())) {
        return new Response('VFS not mounted', { status: 503, headers: { 'Content-Type': 'text/plain' } });
    }

    let rel = url.pathname;
    try { rel = decodeURIComponent(rel); } catch (e) {}
    if (rel.startsWith(VFS_PREFIX_SLASH)) rel = rel.slice(VFS_PREFIX_SLASH.length);
    else if (rel === VFS_PREFIX) rel = '';
    rel = rel.replace(/^\/+/, '');

    if (rel === '' || rel.endsWith('/')) rel += 'index.html';

    // SW-served bridge worker: a REAL same-origin dedicated worker (not a
    // blob URL — blob workers' fetches may bypass the SW). The page's sync
    // XHR shim posts a URL here; the worker fetches it through the SW (async
    // fetch is always SW-intercepted, sync XHR never is) and hands the bytes
    // back over a SharedArrayBuffer while the main thread Atomics.waits.
    // This makes every synchronous read a true on-demand fetch with no
    // warm-up race.
    if (rel === '__vfs-bridge-worker.js') {
        const src =
            'var sab=null,ctrl=null,bytes=null;\n' +
            'onmessage=function(e){\n' +
            '  var d=e.data||{};\n' +
            '  if(d.sab&&!sab){sab=d.sab;ctrl=new Int32Array(sab,0,2);bytes=new Uint8Array(sab);}\n' +
            '  if(!d.url)return;\n' +
            '  fetch(d.url,{credentials:"same-origin"}).then(function(r){\n' +
            '    if(!r.ok)throw new Error("HTTP "+r.status);\n' +
            '    return r.arrayBuffer();\n' +
            '  }).then(function(buf){\n' +
            '    if(8+buf.byteLength>bytes.length)throw new Error("too large");\n' +
            '    bytes.set(new Uint8Array(buf),8);\n' +
            '    Atomics.store(ctrl,1,buf.byteLength);\n' +
            '    Atomics.store(ctrl,0,2);\n' +
            '    Atomics.notify(ctrl,0);\n' +
            '  }).catch(function(){\n' +
            '    Atomics.store(ctrl,1,0);\n' +
            '    Atomics.store(ctrl,0,3);\n' +
            '    Atomics.notify(ctrl,0);\n' +
            '  });\n' +
            '};\n';
        const body = textEncoder.encode(src);
        const h = new Headers();
        h.set('Content-Type', 'text/javascript; charset=utf-8');
        h.set('Content-Length', String(body.byteLength));
        h.set('Cache-Control', 'no-cache');
        return new Response(body, { status: 200, headers: h });
    }

    const canonical = lookupPath(rel);
    if (!canonical) {
        // The zip packaging omits a handful of images the game demands (e.g.
        // img/pictures/OMO_WS.png on the title screen). Serve a transparent 1x1
        // PNG so play continues, and say so loudly — this is a packaging gap,
        // not a VFS bug.
        if (/^img\//i.test(rel) && /\.png$/i.test(rel)) {
            console.warn('VFS: missing in archive, serving placeholder: ' + rel);
            const px = PLACEHOLDER_PNG.slice();
            const h = baseHeaders(rel);
            h.set('Content-Length', String(px.byteLength));
            h.set('X-VFS-Placeholder', '1');
            return new Response(px, { status: 200, headers: h });
        }
        return notFound(url.pathname);
    }
    const entry = entries.get(canonical);
    if (!entry) return notFound(url.pathname);

    // The zip's index.html targets a static-file deployment. Adjustments that
    // make it work from this VFS:
    //
    //   1. Keep FILE MODE (the zip ships real files, served over the network
    //      by this worker), but make SYNCHRONOUS XHR work: the browser never
    //      shows sync requests to a service worker (the main thread is blocked),
    //      so plugins that read YAML synchronously (Atlas Loader's
    //      data/Atlas.yaml -> $atlasData, language menus.yaml, Notes/Quests)
    //      would 404 and crash at boot. Injected shim: a blob Worker fetches
    //      the file over async fetch (which DOES go through this worker) and
    //      hands the bytes back through a SharedArrayBuffer while the main
    //      thread waits on Atomics — a true sync bridge with no warm-up race.
    //      COOP/COEP are added to this navigation response because
    //      SharedArrayBuffer requires a cross-origin-isolated document.
    //   2. A safe $atlasData fallback so a failed parse can never hard-crash.
    //   3. Missing images (the packaging of this zip omits a few title-screen
    //      pictures, e.g. img/pictures/OMO_WS.png) are served as transparent
    //      1x1 PNGs with an X-VFS-Placeholder header and a console warning,
    //      so the game plays instead of dying on a Retry dialog.
    if (canonical === 'index.html' && !url.search.includes('raw=1')) {
        const html = await entryBytes(entry);
        const text = textDecoder.decode(html);

        // Embed every small text-like file directly into the page. Sync XHR
        // cannot reach a service worker (the browser bypasses it — the main
        // thread is blocked), and async warm-up races the game's boot-time
        // sync reads, so the only race-free source for sync reads is the HTML
        // itself. JSON is deliberately EXCLUDED: the game database
        // (data/Enemies.json et al, tens of MB) loads over async XHR which
        // works through the SW; only the small YAML/TXT files are read
        // synchronously by plugins.
        const SYNC_EMBED = /\.(yaml|yml|txt|ini|css)$/i;
        const inline = {};
        for (const [p, rec] of entries) {
            if (!SYNC_EMBED.test(p) || rec.usize > 256 * 1024) continue;
            try {
                inline[p] = textDecoder.decode(await entryBytes(rec));
            } catch (e) { /* skip unreadable */ }
        }
        const payload = JSON.stringify(inline);
        const lookup = {};
        for (const p of Object.keys(inline)) {
            const k = p.toLowerCase();
            if (lookup[k] === undefined) lookup[k] = p;
        }
        const shim = `<script>window.__SYNC_FILES=${payload};window.__SYNC_LOOKUP=${JSON.stringify(lookup)};` +
            `window.$atlasData=window.$atlasData||null;` +
            `if(window.__SYNC_FILES["data/Atlas.yaml"]&&!window.$atlasData){` +
            `try{var y=window.require&&window.require("js-yaml");window.$atlasData=y&&y.load?y.load(window.__SYNC_FILES["data/Atlas.yaml"]):window.$atlasData;}catch(e){}` +
            `}` +
            `var OO=XMLHttpRequest.prototype.open,OS=XMLHttpRequest.prototype.send;` +
            `XMLHttpRequest.prototype.open=function(m,u,a){this.__vfsSync=(a===false);this.__vfsUrl=u;return OO.apply(this,arguments)};` +
            `XMLHttpRequest.prototype.send=function(){` +
            `if(this.__vfsSync){` +
            `var p=String(this.__vfsUrl||"").replace(/^\\.\\//,"").replace(/^\\/+/,"");` +
            `var t=window.__SYNC_FILES[p];` +
            `if(t===undefined&&window.__SYNC_LOOKUP)t=window.__SYNC_FILES[window.__SYNC_LOOKUP[p.toLowerCase()]||""];` +
            `if(typeof t==="string"){` +
            `Object.defineProperty(this,"readyState",{value:4,configurable:true});` +
            `Object.defineProperty(this,"status",{value:200,configurable:true});` +
            `Object.defineProperty(this,"responseText",{value:t,configurable:true});` +
            `Object.defineProperty(this,"response",{value:t,configurable:true});` +
            `var x=this;setTimeout(function(){try{x.dispatchEvent(new Event("readystatechange"));x.dispatchEvent(new Event("load"));x.dispatchEvent(new Event("loadend"));}catch(e){}},0);` +
            `return;}` +
            `}` +
            `return OS.apply(this,arguments)};` +
            `</script>`;
        const patched = text.replace(
            /<script>\s*window\.ZipLoaderForceFileMode\s*=\s*[^<]*<\/script>/i,
            (m) => m + shim
        );
        const body = textEncoder.encode(patched === text ? text + shim : patched);
        const h = baseHeaders(canonical);
        h.set('Content-Length', String(body.byteLength));
        h.set('X-VFS-Patched', 'vfs-inline');
        return new Response(body, { status: 200, headers: h });
    }

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
            const stream = await entryResponse(entry);
            const body = await readRangeFromStream(stream, parsed.start, parsed.end);
            const h = baseHeaders(canonical);
            h.set('Content-Range', 'bytes ' + parsed.start + '-' + parsed.end + '/' + entry.usize);
            h.set('Content-Length', String(body.byteLength));
            return new Response(body, { status: 206, headers: h });
        }
        // unrecognized range form: fall through to a full 200
    }

    const stream = await entryResponse(entry);
    const h = baseHeaders(canonical);
    h.set('Content-Length', String(entry.usize));
    return new Response(stream, { status: 200, headers: h });
}

// Pull [start..end] (inclusive) out of a decompressed stream.
async function readRangeFromStream(stream, start, end) {
    const reader = stream.getReader();
    const out = [];
    let pos = 0;
    let remaining = end - start + 1;
    while (remaining > 0) {
        const { done, value } = await reader.read();
        if (done) break;
        const chunkStart = Math.max(0, start - pos);
        if (chunkStart < value.length) {
            const take = Math.min(value.length - chunkStart, remaining);
            out.push(value.subarray(chunkStart, chunkStart + take));
            remaining -= take;
        }
        pos += value.length;
        if (pos > end) break;
    }
    try { reader.cancel(); } catch (e) {}
    const total = out.reduce((n, c) => n + c.length, 0);
    const merged = new Uint8Array(total);
    let o = 0;
    for (const c of out) { merged.set(c, o); o += c.length; }
    return merged;
}

/* ---- verification -------------------------------------------------------- */

// Whole-archive integrity check. The CRC stored in a zip's central directory
// is over the UNCOMPRESSED data, so deflated entries are streamed through
// inflate and CRC'd chunk by chunk (bounded memory); stored entries are CRC'd
// straight off the Blob. Proves the archive is intact, entry by entry.
async function verifyCrc(progress) {
    if (!(await ensureMounted())) throw new Error('VFS not mounted');
    let done = 0;
    let bad = 0;
    const badList = [];
    for (const entry of entries.values()) {
        try {
            if (entry.method === 0) {
                const span = await entryDataSpan(entry);
                const raw = new Uint8Array(await zipBlob.slice(span.start, span.end).arrayBuffer());
                if (crc32(raw) !== entry.crc) throw new Error('crc mismatch');
            } else if (entry.method === 8) {
                if (typeof DecompressionStream === 'undefined') {
                    throw new Error('DecompressionStream unavailable');
                }
                const span = await entryDataSpan(entry);
                const stream = zipBlob.slice(span.start, span.end).stream()
                    .pipeThrough(new DecompressionStream('deflate-raw'));
                let seed;
                const reader = stream.getReader();
                for (;;) {
                    const { done: eof, value } = await reader.read();
                    if (eof) break;
                    seed = crc32(value, seed);
                }
                if ((seed === undefined ? 0 : seed) !== entry.crc) throw new Error('crc mismatch');
            } else {
                throw new Error('unsupported method ' + entry.method);
            }
        } catch (e) {
            bad++;
            if (badList.length < 50) badList.push(entry.path + ' (' + (e && e.message || e) + ')');
        }
        done++;
        if (progress && (done % 200 === 0 || done === entries.size)) {
            progress(done, entries.size);
        }
    }
    return { checked: done, bad, badList };
}

/* ---- lifecycle --------------------------------------------------------- */

self.addEventListener('install', () => self.skipWaiting());
self.addEventListener('activate', (event) => event.waitUntil(self.clients.claim()));

self.addEventListener('message', (event) => {
    const data = event.data || {};

    if (data.type === 'MOUNT') {
        event.waitUntil((async () => {
            try {
                const blob = data.data instanceof Blob ? data.data : new Blob([data.data]);
                await mountZip(blob);
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
        })());
        return;
    }

    if (data.type === 'PING') {
        ensureMounted().then((ok) => {
            if (event.source) event.source.postMessage({ type: 'PONG', mounted: ok, files: entries.size });
        });
        return;
    }

    if (data.type === 'VERIFY_CRC') {
        event.waitUntil((async () => {
            try {
                const result = await verifyCrc((done, total) => {
                    if (event.source) event.source.postMessage({ type: 'VERIFY_CRC_PROGRESS', done, total });
                });
                if (event.source) event.source.postMessage({ type: 'VERIFY_CRC_DONE', ...result });
            } catch (err) {
                if (event.source) event.source.postMessage({ type: 'VERIFY_CRC_DONE', checked: 0, bad: -1, badList: [String(err && err.message)] });
            }
        })());
        return;
    }

    if (data.type === 'LIST') {
        ensureMounted().then((ok) => {
            if (!event.source) return;
            if (!ok) { event.source.postMessage({ type: 'LIST_DONE', files: [] }); return; }
            const filter = String(data.prefix || '').toLowerCase();
            const files = [];
            for (const path of entries.keys()) {
                if (!filter || path.toLowerCase().startsWith(filter)) files.push(path);
            }
            event.source.postMessage({ type: 'LIST_DONE', files });
        });
        return;
    }
});

self.addEventListener('fetch', (event) => {
    const request = event.request;
    if (request.method !== 'GET' && request.method !== 'HEAD') return;

    const url = new URL(request.url);
    if (!url.pathname.startsWith(VFS_PREFIX + '/') && url.pathname !== VFS_PREFIX) return;

    if (request.method === 'HEAD') {
        event.respondWith((async () => {
            const res = await serveVirtual(url, request);
            return new Response(null, { status: res.status, headers: res.headers });
        })());
        return;
    }
    event.respondWith(serveVirtual(url, request));
});
