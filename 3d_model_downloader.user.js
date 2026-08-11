// ==UserScript==
// @name         AI 3D Model Downloader (Tripo / Hunyuan)
// @namespace    https://github.com/local/tripo3d-model-downloader
// @version      2.0.2
// @description  Captures the original model file off the network, or extracts it straight from the Three.js scene, and saves it as GLB or OBJ+MTL+texture.
// @author       local
// @match        https://studio.tripo3d.ai/*
// @match        https://www.tripo3d.ai/*
// @match        https://3d.hunyuan.tencent.com/*
// @match        https://hunyuan.tencent.com/*
// @icon         https://studio.tripo3d.ai/favicon.ico
// @run-at       document-start
// @grant        none
// ==/UserScript==

/* @grant none is deliberate: it runs the script in the page's own JS context,
   which is required to reach Vue's __vue_app__ internals and the Three.js scene.
   Requesting any GM_* API would move it into Tampermonkey's sandbox and break
   scene discovery. */

(function () {
  window.__TRIPO_NO_AUTOMOUNT = true;
})();

/**
 * tripo3d_model_downloader.js  —  v2
 * ─────────────────────────────────────────────────────────────────────────────
 * Extracts the loaded 3D model directly from the Three.js renderer on
 * studio.tripo3d.ai, bypasses the site's export tool entirely, and downloads it
 * as GLB (glTF 2.0 binary) or OBJ + MTL + PNG.
 *
 * HOW IT WORKS
 * ─────────────────────────────────────────────────────────────────────────────
 * 1. The site is a Nuxt 3 / Vue 3 app using TresJS (Vue wrapper for Three.js).
 * 2. The THREE.Scene is located by three strategies, tried in order:
 *      a) TresJS "Context" component provides.useTres  (fastest, most direct)
 *      b) any Vue component instance in the tree exposing a .isScene object
 *      c) brute-force walk of every canvas element's Three.js render state
 *    Strategy (a) alone was fragile — a TresJS version bump broke it.
 * 3. Every visible mesh is collected (not just the biggest one) so multi-part
 *    models export intact.
 * 4. Geometry is read through the BufferAttribute API (getX/getY/getZ), which
 *    handles interleaved buffers correctly, and each vertex is transformed by
 *    the mesh's matrixWorld so parent Group scale/rotation is baked in.
 * 5. Textures (ImageBitmap / HTMLImageElement / canvas) are drawn to an
 *    offscreen canvas and encoded as PNG. If the canvas is tainted by CORS the
 *    original image bytes are re-fetched instead.
 * 6. GLB is assembled manually chunk-by-chunk; OBJ/MTL are emitted as text.
 *
 * USAGE
 * ─────────────────────────────────────────────────────────────────────────────
 * Paste this entire file into the DevTools console on a Tripo Studio model page
 * *after* the model is visible in the viewport. A small panel appears in the
 * top-right corner with GLB / OBJ buttons.
 *
 * Or drive it from the console:
 *     await tripo.glb()                    // download GLB
 *     await tripo.obj()                    // download OBJ + MTL + PNG
 *     await tripo.glb({ includeNormals: true })
 *     await tripo.obj({ largestMeshOnly: true, scale: 100 })
 *     tripo.inspect()                      // list what was found, download nothing
 *
 * OPTIONS
 * ─────────────────────────────────────────────────────────────────────────────
 *   includeNormals   false  Tripo's AI-generated normals are often inconsistent;
 *                           omitting them lets Blender recalculate smooth ones.
 *   largestMeshOnly  false  Export only the highest-vertex-count mesh.
 *   bakeTransform    true   Apply matrixWorld to vertices.
 *   scale            1      Uniform scale multiplier applied after baking.
 *   flipUV           auto   OBJ uses bottom-left UV origin, glTF top-left;
 *                           handled per-format automatically.
 *   filename         auto   Base name without extension.
 *
 * TESTED ON
 * ─────────────────────────────────────────────────────────────────────────────
 * Three.js r183, TresJS, Nuxt 3, Pinia — 2026
 */

(function () {
  'use strict';

  const LOG = '[tripo]';
  const log  = (...a) => console.log(LOG, ...a);
  const warn = (...a) => console.warn(LOG, ...a);

  // ═══════════════════════════════════════════════════════════════════════════
  // 0. NETWORK CAPTURE
  // ═══════════════════════════════════════════════════════════════════════════
  // Most viewers fetch a finished asset from a CDN before rendering it. Grabbing
  // that response yields the pristine file — original normals, full PBR texture
  // set, correct scale — which always beats re-assembling it from the scene.
  // Scene extraction stays as the fallback for viewers that stream geometry.
  //
  // Only useful if installed BEFORE the request happens: the userscript build
  // runs at document-start. Pasted into the console it only sees later loads,
  // so reload the page (or open the model again) to catch one.

  const MODEL_URL_RE = /\.(glb|gltf|obj|fbx|ply|stl|usdz|drc|zip)(\?|#|$)/i;
  const MODEL_MIME_RE = /(model\/|application\/octet-stream|gltf|zip)/i;
  const CAPTURE_MAX_FILES = 24;
  const CAPTURE_MAX_BYTES = 512 * 1024 * 1024;

  const captured = [];
  let capturedBytes = 0;

  /** Identifies a model file from its leading bytes when the URL is opaque. */
  function sniffModelFormat(bytes) {
    if (bytes.length < 8) return null;
    const dv = new DataView(bytes.buffer, bytes.byteOffset, Math.min(bytes.byteLength, 64));
    if (dv.getUint32(0, true) === 0x46546C67) return 'glb';            // "glTF"
    const head = new TextDecoder().decode(bytes.subarray(0, 24));
    if (head.startsWith('Kaydara FBX')) return 'fbx';
    if (head.startsWith('ply')) return 'ply';
    if (head.startsWith('solid ')) return 'stl';
    if (/^\s*\{[\s\S]*"asset"/.test(head)) return 'gltf';
    if (/^(#|mtllib|v\s|o\s|g\s)/.test(head)) return 'obj';
    if (bytes[0] === 0x50 && bytes[1] === 0x4B) return 'zip';          // "PK"
    return null;
  }

  function nameFromURL(url, format) {
    let base = 'asset';
    try {
      base = decodeURIComponent(new URL(url, location.href).pathname.split('/').filter(Boolean).pop() || 'asset');
    } catch { /* opaque or blob: URL */ }
    base = base.replace(/\.[^.]{1,6}$/, '') || 'asset';
    return `${sanitize(base)}.${format}`;
  }

  function remember(url, bytes) {
    const format = sniffModelFormat(bytes);
    if (!format) return;
    if (captured.some(c => c.url === url)) return;
    if (captured.length >= CAPTURE_MAX_FILES || capturedBytes + bytes.byteLength > CAPTURE_MAX_BYTES) {
      const dropped = captured.shift();
      if (dropped) capturedBytes -= dropped.bytes.byteLength;
    }
    const entry = { url, bytes, format, filename: nameFromURL(url, format), size: bytes.byteLength };
    captured.push(entry);
    capturedBytes += bytes.byteLength;
    log(`captured ${entry.filename} — ${(entry.size / 1048576).toFixed(2)} MB from network`);
    document.dispatchEvent(new CustomEvent('tripo:captured', { detail: entry }));
  }

  /** Cheap pre-filter so ordinary JSON/image traffic is never buffered. */
  function looksLikeModel(url, contentType, contentLength) {
    if (MODEL_URL_RE.test(url || '')) return true;
    if (contentType && MODEL_MIME_RE.test(contentType)) return true;
    // Unlabelled binaries above 256 KB are worth a peek at their magic bytes.
    return !contentType && contentLength > 262144;
  }

  function installNetworkCapture() {
    if (window.__tripoNetHooked) return;
    window.__tripoNetHooked = true;

    const originalFetch = window.fetch;
    if (typeof originalFetch === 'function') {
      window.fetch = function (...args) {
        const promise = originalFetch.apply(this, args);
        promise.then(res => {
          try {
            const url = res.url || (typeof args[0] === 'string' ? args[0] : args[0]?.url) || '';
            const ct  = res.headers?.get('content-type') || '';
            const cl  = +(res.headers?.get('content-length') || 0);
            if (!res.ok || !looksLikeModel(url, ct, cl)) return;
            // clone() so the site still gets to consume the body itself.
            res.clone().arrayBuffer()
              .then(buf => remember(url, new Uint8Array(buf)))
              .catch(() => {});
          } catch { /* never let the hook break the page */ }
        }).catch(() => {});
        return promise;
      };
    }

    const origOpen = XMLHttpRequest.prototype.open;
    const origSend = XMLHttpRequest.prototype.send;
    XMLHttpRequest.prototype.open = function (method, url, ...rest) {
      this.__tripoURL = url;
      return origOpen.call(this, method, url, ...rest);
    };
    XMLHttpRequest.prototype.send = function (...args) {
      this.addEventListener('load', () => {
        try {
          const url = this.responseURL || this.__tripoURL || '';
          const ct  = this.getResponseHeader?.('content-type') || '';
          if (!looksLikeModel(url, ct, +(this.getResponseHeader?.('content-length') || 0))) return;
          const r = this.response;
          if (r instanceof ArrayBuffer)  remember(url, new Uint8Array(r));
          else if (r instanceof Blob)    r.arrayBuffer().then(b => remember(url, new Uint8Array(b))).catch(() => {});
        } catch { /* ignore */ }
      });
      return origSend.apply(this, args);
    };

    log('network capture armed');
  }

  // ═══════════════════════════════════════════════════════════════════════════
  // 1. SCENE DISCOVERY
  // ═══════════════════════════════════════════════════════════════════════════

  /** Walk a Vue vnode subtree, invoking cb on every component instance. */
  function walkVue(vnode, cb, depth = 0, seen = new Set()) {
    if (!vnode || depth > 60 || seen.has(vnode)) return null;
    seen.add(vnode);

    if (vnode.component) {
      const hit = cb(vnode.component);
      if (hit) return hit;
      const found = walkVue(vnode.component.subTree, cb, depth + 1, seen);
      if (found) return found;
    }
    if (Array.isArray(vnode.children)) {
      for (const child of vnode.children) {
        if (child && typeof child === 'object') {
          const found = walkVue(child, cb, depth + 1, seen);
          if (found) return found;
        }
      }
    }
    return null;
  }

  /** Unwrap a Vue ref if needed. */
  const unref = v => (v && typeof v === 'object' && 'value' in v ? v.value : v);

  /** Strategy (a): the documented TresJS Context provide. */
  function findSceneViaTresContext(rootVnode) {
    return walkVue(rootVnode, inst => {
      const name = inst.type?.name || inst.type?.__name || '';
      if (name !== 'Context' && name !== 'TresCanvas') return null;
      const tres = inst.provides?.useTres || inst.provides?.['useTres'];
      const scene = unref(tres?.scene);
      return scene?.isScene ? scene : null;
    });
  }

  /** Strategy (b): any component whose provides/setupState holds a Scene. */
  function findSceneViaAnyProvide(rootVnode) {
    return walkVue(rootVnode, inst => {
      for (const bag of [inst.provides, inst.setupState, inst.ctx]) {
        if (!bag || typeof bag !== 'object') continue;
        for (const key of Object.keys(bag)) {
          let v;
          try { v = unref(bag[key]); } catch { continue; }
          if (v?.isScene) return v;
          if (v && typeof v === 'object') {
            const nested = unref(v.scene);
            if (nested?.isScene) return nested;
          }
        }
      }
      return null;
    });
  }

  /** Pokes at an arbitrary object looking for a Scene one or two levels down. */
  function probeForScene(obj, depth = 0) {
    if (!obj || typeof obj !== 'object' || depth > 2) return null;
    try {
      if (obj.isScene) return obj;
      const direct = unref(obj.scene) ?? unref(obj._scene);
      if (direct?.isScene) return direct;
      // react-three-fiber keeps everything in a zustand store.
      if (typeof obj.getState === 'function') {
        const s = unref(obj.getState()?.scene);
        if (s?.isScene) return s;
      }
      if (depth < 2) {
        for (const key of ['store', 'root', 'state', 'renderer', 'viewer', 'engine', 'three', 'app']) {
          const nested = probeForScene(unref(obj[key]), depth + 1);
          if (nested) return nested;
        }
      }
    } catch { /* exotic getters */ }
    return null;
  }

  /**
   * Strategy (c): scene stashed on a DOM element. Covers Three.js renderer
   * back-references and react-three-fiber's `__r3f` expando.
   */
  function findSceneViaCanvas() {
    for (const canvas of document.querySelectorAll('canvas')) {
      const r3f = probeForScene(canvas.__r3f);
      if (r3f) return r3f;
      for (const key of Object.keys(canvas)) {
        const found = probeForScene(canvas[key]);
        if (found) return found;
      }
      const s = probeForScene(canvas.__three_renderer || canvas.__renderer);
      if (s) return s;
    }
    return null;
  }

  /**
   * Strategy (d): React apps (Hunyuan and friends) expose a fiber tree from any
   * mounted DOM node. Walking it reaches component state that holds the scene.
   */
  function findSceneViaReactFiber() {
    const hosts = document.querySelectorAll('canvas, #root, #__next, #app, body > div');
    for (const host of hosts) {
      const key = Object.keys(host).find(k =>
        k.startsWith('__reactFiber$') || k.startsWith('__reactInternalInstance$'));
      const props = Object.keys(host).find(k => k.startsWith('__reactProps$'));
      if (props) {
        const found = probeForScene(host[props]);
        if (found) return found;
      }
      if (!key) continue;
      const found = walkFiber(host[key]);
      if (found) return found;
    }
    return null;
  }

  function walkFiber(fiber, seen = new Set(), budget = { n: 20000 }) {
    while (fiber && budget.n-- > 0) {
      if (seen.has(fiber)) return null;
      seen.add(fiber);

      for (const bag of [fiber.stateNode, fiber.memoizedProps, fiber.memoizedState]) {
        const found = probeForScene(bag);
        if (found) return found;
      }
      // Hooks form a linked list hanging off memoizedState.
      let hook = fiber.memoizedState;
      let hops = 0;
      while (hook && typeof hook === 'object' && 'next' in hook && hops++ < 40) {
        const found = probeForScene(hook.memoizedState);
        if (found) return found;
        hook = hook.next;
      }

      const child = walkFiber(fiber.child, seen, budget);
      if (child) return child;
      fiber = fiber.sibling;
    }
    return null;
  }

  /** Strategy (e): plain globals — window.viewer, window.app, window.scene, … */
  function findSceneViaGlobals() {
    const skip = new Set(['window', 'self', 'top', 'parent', 'frames', 'document', 'location', 'tripo']);
    for (const key of Object.keys(window)) {
      if (skip.has(key)) continue;
      let value;
      try { value = window[key]; } catch { continue; }
      const found = probeForScene(value);
      if (found) return found;
    }
    return null;
  }

  function findScene() {
    const appEl = document.querySelector('[data-v-app]') || document.querySelector('#__nuxt');
    let rootVnode = null;

    if (appEl?.__vue_app__) {
      const vueApp = appEl.__vue_app__;
      const matched = vueApp.config?.globalProperties?.$router?.currentRoute?.value?.matched?.[0];
      rootVnode = matched?.instances?.default?._?.subTree || vueApp._instance?.subTree || null;
    }

    const strategies = [
      ['TresJS Context provide', () => (rootVnode ? findSceneViaTresContext(rootVnode) : null)],
      ['Vue component scan',     () => (rootVnode ? findSceneViaAnyProvide(rootVnode)  : null)],
      ['canvas back-reference',  findSceneViaCanvas],
      ['React fiber tree',       findSceneViaReactFiber],
      ['window globals',         findSceneViaGlobals],
    ];

    for (const [label, fn] of strategies) {
      let scene = null;
      try { scene = fn(); } catch (e) { warn(`strategy "${label}" threw:`, e.message); }
      if (scene?.isScene) {
        log(`scene found via ${label} — ${scene.children.length} root children`);
        return scene;
      }
    }
    throw new Error(
      'THREE.Scene not found. Make sure the model is fully rendered in the viewport, then retry. ' +
      (captured.length
        ? `${captured.length} file(s) were captured from the network — use tripo.saveCaptured() instead.`
        : 'If the page was just opened, reload it so the network capture can catch the asset.')
    );
  }

  // ═══════════════════════════════════════════════════════════════════════════
  // 2. MESH COLLECTION
  // ═══════════════════════════════════════════════════════════════════════════

  const SKIP_NAME = /grid|ground|floor|shadow|helper|gizmo|skybox|background|backdrop|outline|bbox/i;

  function collectMeshes(scene, { largestMeshOnly = false } = {}) {
    const out = [];
    scene.updateMatrixWorld(true);

    scene.traverseVisible(obj => {
      if (!obj.isMesh && !obj.isSkinnedMesh) return;
      const count = obj.geometry?.attributes?.position?.count ?? 0;
      if (count < 3) return;
      if (SKIP_NAME.test(obj.name)) { log(`skipping helper mesh "${obj.name}"`); return; }
      if (obj.material?.isShadowMaterial) return;
      out.push(obj);
    });

    if (!out.length) throw new Error('No exportable mesh found in the scene.');

    if (largestMeshOnly && out.length > 1) {
      const best = out.reduce((a, b) =>
        b.geometry.attributes.position.count > a.geometry.attributes.position.count ? b : a);
      log(`largestMeshOnly: keeping "${best.name || '(unnamed)'}" of ${out.length} meshes`);
      return [best];
    }
    return out;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  // 3. GEOMETRY EXTRACTION
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Reads a mesh into plain tightly-packed typed arrays.
   * Uses the BufferAttribute accessor API so interleaved and normalized
   * attributes are decoded correctly — reading `.array` directly does not.
   */
  function extractGeometry(mesh, { includeNormals = false, bakeTransform = true, scale = 1 } = {}) {
    const geo = mesh.geometry;
    const pos = geo.attributes.position;
    const nrm = includeNormals ? geo.attributes.normal : null;
    const uv  = geo.attributes.uv;
    const n   = pos.count;

    const positions = new Float32Array(n * 3);
    const normals   = nrm ? new Float32Array(n * 3) : null;
    const uvs       = uv  ? new Float32Array(n * 2) : null;

    const m  = mesh.matrixWorld;
    const e  = m.elements;
    // Normal matrix = transpose(inverse(upper-left 3x3)); computed inline to
    // avoid depending on a THREE global being reachable from the console.
    let nm = null;
    if (normals && bakeTransform) nm = normalMatrix3(e);

    for (let i = 0; i < n; i++) {
      let x = pos.getX(i), y = pos.getY(i), z = pos.getZ(i);
      if (bakeTransform) {
        const w = e[3] * x + e[7] * y + e[11] * z + e[15] || 1;
        const tx = (e[0] * x + e[4] * y + e[8]  * z + e[12]) / w;
        const ty = (e[1] * x + e[5] * y + e[9]  * z + e[13]) / w;
        const tz = (e[2] * x + e[6] * y + e[10] * z + e[14]) / w;
        x = tx; y = ty; z = tz;
      }
      positions[i * 3]     = x * scale;
      positions[i * 3 + 1] = y * scale;
      positions[i * 3 + 2] = z * scale;

      if (normals) {
        let nx = nrm.getX(i), ny = nrm.getY(i), nz = nrm.getZ(i);
        if (nm) {
          const tx = nm[0] * nx + nm[3] * ny + nm[6] * nz;
          const ty = nm[1] * nx + nm[4] * ny + nm[7] * nz;
          const tz = nm[2] * nx + nm[5] * ny + nm[8] * nz;
          const len = Math.hypot(tx, ty, tz) || 1;
          nx = tx / len; ny = ty / len; nz = tz / len;
        }
        normals[i * 3] = nx; normals[i * 3 + 1] = ny; normals[i * 3 + 2] = nz;
      }
      if (uvs) { uvs[i * 2] = uv.getX(i); uvs[i * 2 + 1] = uv.getY(i); }
    }

    // Indices: preserve the source width instead of assuming Uint32. Feeding a
    // Uint16 buffer to a 5125 accessor is what shredded models in v1.
    let indices = null;
    if (geo.index) {
      const src = geo.index;
      const Ctor = n > 65535 ? Uint32Array : Uint16Array;
      indices = new Ctor(src.count);
      for (let i = 0; i < src.count; i++) indices[i] = src.getX(i);
    } else {
      // Non-indexed geometry: synthesise a trivial index run so both exporters
      // can assume one code path.
      const Ctor = n > 65535 ? Uint32Array : Uint16Array;
      indices = new Ctor(n);
      for (let i = 0; i < n; i++) indices[i] = i;
    }

    // A mirrored (negative-determinant) transform flips winding order.
    if (bakeTransform && determinant3(e) < 0) {
      for (let i = 0; i + 2 < indices.length; i += 3) {
        const t = indices[i]; indices[i] = indices[i + 2]; indices[i + 2] = t;
      }
      log(`"${mesh.name || '(unnamed)'}": mirrored transform — winding order reversed`);
    }

    return { positions, normals, uvs, indices, name: mesh.name || 'tripo_mesh', material: mesh.material };
  }

  function determinant3(e) {
    return e[0] * (e[5] * e[10] - e[9] * e[6])
         - e[4] * (e[1] * e[10] - e[9] * e[2])
         + e[8] * (e[1] * e[6]  - e[5] * e[2]);
  }

  /** transpose(inverse(upper-left 3x3)) of a column-major mat4, as a mat3 array. */
  function normalMatrix3(e) {
    const a = [e[0], e[1], e[2], e[4], e[5], e[6], e[8], e[9], e[10]];
    const det = a[0] * (a[4] * a[8] - a[7] * a[5])
              - a[3] * (a[1] * a[8] - a[7] * a[2])
              + a[6] * (a[1] * a[5] - a[4] * a[2]);
    if (!det) return null;
    const id = 1 / det;
    // inverse, then transpose — combined into one index shuffle
    return [
      (a[4] * a[8] - a[5] * a[7]) * id, (a[5] * a[6] - a[3] * a[8]) * id, (a[3] * a[7] - a[4] * a[6]) * id,
      (a[2] * a[7] - a[1] * a[8]) * id, (a[0] * a[8] - a[2] * a[6]) * id, (a[1] * a[6] - a[0] * a[7]) * id,
      (a[1] * a[5] - a[2] * a[4]) * id, (a[2] * a[3] - a[0] * a[5]) * id, (a[0] * a[4] - a[1] * a[3]) * id,
    ];
  }

  // ═══════════════════════════════════════════════════════════════════════════
  // 4. TEXTURE EXTRACTION
  // ═══════════════════════════════════════════════════════════════════════════

  const textureCache = new Map(); // image object → Uint8Array PNG

  async function imageToPNG(image) {
    if (!image) return null;
    if (textureCache.has(image)) return textureCache.get(image);

    const w = image.width  || image.naturalWidth  || image.videoWidth;
    const h = image.height || image.naturalHeight || image.videoHeight;
    if (!w || !h) { warn('texture has zero dimensions; skipped'); return null; }

    let bytes = null;
    try {
      const canvas = document.createElement('canvas');
      canvas.width = w; canvas.height = h;
      canvas.getContext('2d').drawImage(image, 0, 0);
      const blob = await new Promise(r => canvas.toBlob(r, 'image/png'));
      if (!blob) throw new Error('toBlob returned null');
      bytes = new Uint8Array(await blob.arrayBuffer());
    } catch (e) {
      // Tainted canvas (cross-origin image without CORS headers). Re-fetching
      // the original URL usually works because the CDN does allow plain GETs.
      warn(`canvas export blocked (${e.name || e.message}); re-fetching source`);
      const src = image.src || image.currentSrc;
      if (!src) { warn('no source URL to fall back to; texture skipped'); return null; }
      try {
        const res = await fetch(src, { mode: 'cors', credentials: 'include' });
        if (!res.ok) throw new Error(`HTTP ${res.status}`);
        bytes = new Uint8Array(await res.arrayBuffer());
      } catch (e2) {
        warn('texture re-fetch failed:', e2.message, '— exporting without texture');
        return null;
      }
    }

    log(`texture ${w}x${h} -> ${(bytes.byteLength / 1024).toFixed(0)} KB`);
    textureCache.set(image, bytes);
    return bytes;
  }

  /** Sniffs the mime type from magic bytes so re-fetched JPEGs aren't mislabelled. */
  function sniffMime(bytes) {
    if (bytes[0] === 0x89 && bytes[1] === 0x50) return 'image/png';
    if (bytes[0] === 0xFF && bytes[1] === 0xD8) return 'image/jpeg';
    if (bytes[0] === 0x52 && bytes[1] === 0x49) return 'image/webp';
    return 'image/png';
  }

  const extForMime = m => (m === 'image/jpeg' ? 'jpg' : m === 'image/webp' ? 'webp' : 'png');

  /** Collects the unique base-color textures used by a set of materials. */
  async function collectTextures(parts) {
    const byImage = new Map(); // image → { index, bytes, mime }
    const perPart = [];

    for (const part of parts) {
      const mat = Array.isArray(part.material) ? part.material[0] : part.material;
      const image = mat?.map?.image;
      let ref = null;
      if (image) {
        if (byImage.has(image)) {
          ref = byImage.get(image);
        } else {
          const bytes = await imageToPNG(image);
          if (bytes) {
            ref = { index: byImage.size, bytes, mime: sniffMime(bytes) };
            byImage.set(image, ref);
          }
        }
      }
      perPart.push(ref);
    }
    if (!byImage.size) warn('no diffuse texture found; exporting geometry only');
    return { textures: [...byImage.values()], perPart };
  }

  // ═══════════════════════════════════════════════════════════════════════════
  // 5. GLB EXPORT
  // ═══════════════════════════════════════════════════════════════════════════

  const align4 = n => Math.ceil(n / 4) * 4;

  /** Accumulates 4-byte-aligned chunks and reports their offsets. */
  function BinaryPacker() {
    const chunks = [];
    let offset = 0;
    return {
      add(view) {
        const bytes = view instanceof Uint8Array
          ? view
          : new Uint8Array(view.buffer, view.byteOffset, view.byteLength);
        const at = offset;
        chunks.push({ bytes, at });
        offset = align4(offset + bytes.byteLength);
        return { byteOffset: at, byteLength: bytes.byteLength };
      },
      get length() { return align4(offset); },
      write(target, base) { for (const c of chunks) target.set(c.bytes, base + c.at); },
    };
  }

  function buildGLB(parts, textureInfo, { includeNormals }) {
    const packer      = BinaryPacker();
    const accessors   = [];
    const bufferViews = [];
    const meshes      = [];
    const nodes       = [];
    const materials   = [];
    const images      = [];
    const textures    = [];

    for (const tex of textureInfo.textures) {
      const bv = packer.add(tex.bytes);
      bufferViews.push({ buffer: 0, byteOffset: bv.byteOffset, byteLength: bv.byteLength });
      images.push({ mimeType: tex.mime, bufferView: bufferViews.length - 1 });
      textures.push({ source: images.length - 1 });
    }

    const addAccessor = (view, componentType, count, type, target, extra = {}) => {
      const bv = packer.add(view);
      bufferViews.push({ buffer: 0, byteOffset: bv.byteOffset, byteLength: bv.byteLength, target });
      accessors.push({ bufferView: bufferViews.length - 1, byteOffset: 0, componentType, count, type, ...extra });
      return accessors.length - 1;
    };

    parts.forEach((part, i) => {
      const { positions, normals, uvs, indices } = part;
      const count = positions.length / 3;

      const min = [Infinity, Infinity, Infinity];
      const max = [-Infinity, -Infinity, -Infinity];
      for (let k = 0; k < positions.length; k += 3) {
        for (let c = 0; c < 3; c++) {
          const v = positions[k + c];
          if (v < min[c]) min[c] = v;
          if (v > max[c]) max[c] = v;
        }
      }

      const attributes = { POSITION: addAccessor(positions, 5126, count, 'VEC3', 34962, { min, max }) };
      if (includeNormals && normals) attributes.NORMAL     = addAccessor(normals, 5126, count, 'VEC3', 34962);
      if (uvs)                       attributes.TEXCOORD_0 = addAccessor(uvs,     5126, count, 'VEC2', 34962);

      // Component type must match the actual index width — v1 hardcoded 5125.
      const idxComponentType = indices instanceof Uint32Array ? 5125
                             : indices instanceof Uint16Array ? 5123 : 5121;
      const primitive = {
        attributes,
        indices: addAccessor(indices, idxComponentType, indices.length, 'SCALAR', 34963),
      };

      const texRef = textureInfo.perPart[i];
      const srcMat = Array.isArray(part.material) ? part.material[0] : part.material;
      const color  = srcMat?.color;
      materials.push({
        name: srcMat?.name || `tripo_mat_${i}`,
        pbrMetallicRoughness: {
          ...(texRef ? { baseColorTexture: { index: texRef.index } } : {}),
          baseColorFactor: color
            ? [color.r, color.g, color.b, srcMat.opacity ?? 1]
            : [1, 1, 1, 1],
          metallicFactor:  srcMat?.metalness ?? 0,
          roughnessFactor: srcMat?.roughness ?? 0.5,
        },
        doubleSided: srcMat ? srcMat.side !== 0 : true,
      });
      primitive.material = materials.length - 1;

      meshes.push({ name: part.name, primitives: [primitive] });
      nodes.push({ name: part.name, mesh: meshes.length - 1 });
    });

    const totalBin = packer.length;
    const gltf = {
      asset: { version: '2.0', generator: 'tripo3d-browser-extractor v2' },
      scene: 0,
      scenes: [{ name: 'Scene', nodes: nodes.map((_, i) => i) }],
      nodes, meshes, accessors, bufferViews,
      buffers: [{ byteLength: totalBin }],
      materials,
      ...(images.length ? { images, textures } : {}),
    };

    const json       = new TextEncoder().encode(JSON.stringify(gltf));
    const jsonPadded = align4(json.length);
    const totalSize  = 12 + 8 + jsonPadded + 8 + totalBin;

    const glb = new ArrayBuffer(totalSize);
    const dv  = new DataView(glb);
    const buf = new Uint8Array(glb);
    let off = 0;

    dv.setUint32(off, 0x46546C67, true); off += 4;  // "glTF"
    dv.setUint32(off, 2,          true); off += 4;
    dv.setUint32(off, totalSize,  true); off += 4;

    dv.setUint32(off, jsonPadded, true); off += 4;
    dv.setUint32(off, 0x4E4F534A, true); off += 4;  // "JSON"
    buf.set(json, off);
    buf.fill(0x20, off + json.length, off + jsonPadded); // spec: pad JSON with spaces
    off += jsonPadded;

    dv.setUint32(off, totalBin,   true); off += 4;
    dv.setUint32(off, 0x004E4942, true); off += 4;  // "BIN\0"
    packer.write(buf, off);

    if (dv.getUint32(0, true) !== 0x46546C67) throw new Error('GLB magic mismatch — build failed.');
    return glb;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  // 6. OBJ / MTL EXPORT
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * OBJ indices are 1-based and global across the whole file, so each part's
   * indices are offset by the running vertex total.
   */
  function buildOBJ(parts, textureInfo, { includeNormals, mtlFilename }) {
    const obj = [
      '# Exported by tripo3d_model_downloader v2',
      `# ${new Date().toISOString()}`,
      `mtllib ${mtlFilename}`,
      '',
    ];

    let vertexBase = 0;
    const usedMaterials = [];

    parts.forEach((part, i) => {
      const { positions, normals, uvs, indices, name } = part;
      const count = positions.length / 3;

      obj.push(`o ${sanitize(name) || `tripo_part_${i}`}`);

      for (let k = 0; k < positions.length; k += 3) {
        obj.push(`v ${f(positions[k])} ${f(positions[k + 1])} ${f(positions[k + 2])}`);
      }
      // OBJ's UV origin is bottom-left, glTF/Three's is top-left — flip V.
      if (uvs) for (let k = 0; k < uvs.length; k += 2) {
        obj.push(`vt ${f(uvs[k])} ${f(1 - uvs[k + 1])}`);
      }
      if (includeNormals && normals) for (let k = 0; k < normals.length; k += 3) {
        obj.push(`vn ${f(normals[k])} ${f(normals[k + 1])} ${f(normals[k + 2])}`);
      }

      const matName = `tripo_mat_${i}`;
      usedMaterials.push({ name: matName, part, texture: textureInfo.perPart[i] });
      obj.push(`usemtl ${matName}`, 's 1');

      const hasUV = !!uvs;
      const hasN  = includeNormals && !!normals;
      for (let k = 0; k + 2 < indices.length; k += 3) {
        const a = indices[k] + 1 + vertexBase;
        const b = indices[k + 1] + 1 + vertexBase;
        const c = indices[k + 2] + 1 + vertexBase;
        obj.push(`f ${vref(a, hasUV, hasN)} ${vref(b, hasUV, hasN)} ${vref(c, hasUV, hasN)}`);
      }
      obj.push('');
      vertexBase += count;
    });

    const mtl = ['# Exported by tripo3d_model_downloader v2', ''];
    for (const { name, part, texture } of usedMaterials) {
      const src = Array.isArray(part.material) ? part.material[0] : part.material;
      const c = src?.color;
      mtl.push(
        `newmtl ${name}`,
        'Ka 0.000 0.000 0.000',
        `Kd ${c ? `${f(c.r)} ${f(c.g)} ${f(c.b)}` : '1.000 1.000 1.000'}`,
        'Ks 0.000 0.000 0.000',
        `d ${f(src?.opacity ?? 1)}`,
        'illum 2',
      );
      if (texture) mtl.push(`map_Kd ${texture.filename}`);
      mtl.push('');
    }

    return { obj: obj.join('\n'), mtl: mtl.join('\n') };
  }

  const f = v => (Number.isFinite(v) ? v.toFixed(6) : '0.000000');
  const sanitize = s => String(s || '').replace(/[^\w.-]+/g, '_');
  function vref(idx, hasUV, hasN) {
    if (hasUV && hasN) return `${idx}/${idx}/${idx}`;
    if (hasUV)         return `${idx}/${idx}`;
    if (hasN)          return `${idx}//${idx}`;
    return `${idx}`;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  // 7. DOWNLOAD PLUMBING
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * The anchor must be in the document for the click to register in Firefox and
   * some Chromium forks — v1 clicked a detached node, which silently no-oped.
   */
  function download(data, filename, mime) {
    const blob = data instanceof Blob ? data : new Blob([data], { type: mime });
    const url  = URL.createObjectURL(blob);
    const a    = document.createElement('a');
    a.href = url;
    a.download = filename;
    a.style.display = 'none';
    document.body.appendChild(a);
    a.click();
    setTimeout(() => { a.remove(); URL.revokeObjectURL(url); }, 10_000);
    log(`downloaded ${filename} (${(blob.size / 1048576).toFixed(2)} MB)`);
    return blob.size;
  }

  const sleep = ms => new Promise(r => setTimeout(r, ms));

  function defaultBaseName() {
    const id = location.pathname.split('/').filter(Boolean).pop() || 'model';
    const site = /hunyuan/i.test(location.hostname) ? 'hunyuan' : 'tripo';
    return `${site}_${sanitize(id)}`;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  // 8. PUBLIC API
  // ═══════════════════════════════════════════════════════════════════════════

  async function prepare(opts) {
    const scene = findScene();
    const meshes = collectMeshes(scene, opts);
    const parts = meshes.map(m => extractGeometry(m, opts));

    const totalV = parts.reduce((s, p) => s + p.positions.length / 3, 0);
    const totalT = parts.reduce((s, p) => s + p.indices.length / 3, 0);
    log(`${parts.length} mesh(es), ${totalV.toLocaleString()} vertices, ${totalT.toLocaleString()} triangles`);

    const textureInfo = await collectTextures(parts);
    return { parts, textureInfo, stats: { meshes: parts.length, vertices: totalV, triangles: totalT } };
  }

  const DEFAULTS = { includeNormals: false, largestMeshOnly: false, bakeTransform: true, scale: 1 };

  async function exportGLB(userOpts = {}) {
    const opts = { ...DEFAULTS, ...userOpts };
    const { parts, textureInfo, stats } = await prepare(opts);
    if (!opts.includeNormals) log('normals omitted — let Blender recalculate them (pass includeNormals:true to keep)');

    const glb = buildGLB(parts, textureInfo, opts);
    const filename = `${opts.filename || defaultBaseName()}.glb`;
    const size = download(glb, filename, 'model/gltf-binary');
    return { format: 'glb', filename, sizeMB: +(size / 1048576).toFixed(2), ...stats };
  }

  async function exportOBJ(userOpts = {}) {
    const opts = { ...DEFAULTS, ...userOpts };
    const { parts, textureInfo, stats } = await prepare(opts);

    const base = opts.filename || defaultBaseName();
    textureInfo.textures.forEach((t, i) => {
      t.filename = `${base}${textureInfo.textures.length > 1 ? `_${i}` : ''}.${extForMime(t.mime)}`;
    });

    const mtlFilename = `${base}.mtl`;
    const { obj, mtl } = buildOBJ(parts, textureInfo, { ...opts, mtlFilename });

    // Three separate files — no zipping without a bundled library. The browser
    // may prompt to allow multiple downloads; gaps keep the prompts orderly.
    let total = download(obj, `${base}.obj`, 'text/plain');
    await sleep(400);
    total += download(mtl, mtlFilename, 'text/plain');
    for (const t of textureInfo.textures) {
      await sleep(400);
      total += download(t.bytes, t.filename, t.mime);
    }

    const files = [`${base}.obj`, mtlFilename, ...textureInfo.textures.map(t => t.filename)];
    log('keep all files in the same folder — the .obj references the .mtl by name');
    return { format: 'obj', files, sizeMB: +(total / 1048576).toFixed(2), ...stats };
  }

  /** Saves a network-captured original file (index, or all of them). */
  function saveCaptured(index) {
    if (!captured.length) {
      warn('nothing captured yet — reload the page with the script active, then open the model');
      return [];
    }
    const list = index === undefined ? captured : [captured[index]].filter(Boolean);
    for (const entry of list) download(entry.bytes, entry.filename, 'application/octet-stream');
    return list.map(e => e.filename);
  }

  function listCaptured() {
    console.table(captured.map((c, i) => ({
      i, file: c.filename, format: c.format, MB: +(c.size / 1048576).toFixed(2), url: c.url.slice(0, 80),
    })));
    return captured.length;
  }

  /** Dry run: report what would be exported without downloading anything. */
  function inspect() {
    const scene = findScene();
    const meshes = collectMeshes(scene, {});
    const rows = meshes.map(m => ({
      name: m.name || '(unnamed)',
      vertices: m.geometry.attributes.position.count,
      triangles: (m.geometry.index?.count ?? m.geometry.attributes.position.count) / 3,
      uv: !!m.geometry.attributes.uv,
      normals: !!m.geometry.attributes.normal,
      texture: m.material?.map?.image
        ? `${m.material.map.image.width}x${m.material.map.image.height}`
        : 'none',
    }));
    console.table(rows);
    return rows;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  // 9. FLOATING PANEL
  // ═══════════════════════════════════════════════════════════════════════════

  // Preferences survive reloads — the panel is persistent under Tampermonkey,
  // so re-ticking the boxes on every page view would get old fast.
  const PREF_KEY = 'tripo-dl-prefs';
  const loadPrefs = () => {
    try { return JSON.parse(localStorage.getItem(PREF_KEY)) || {}; } catch { return {}; }
  };
  const savePrefs = p => {
    try { localStorage.setItem(PREF_KEY, JSON.stringify(p)); } catch { /* private mode */ }
  };

  function mountPanel() {
    document.getElementById('tripo-dl-panel')?.remove();
    const prefs = loadPrefs();

    const panel = document.createElement('div');
    panel.id = 'tripo-dl-panel';
    panel.style.cssText = `
      position:fixed; top:16px; right:16px; z-index:2147483647;
      background:#1b1b1f; color:#eee; border:1px solid #3a3a42; border-radius:10px;
      padding:12px 14px; font:13px/1.4 system-ui,sans-serif; width:210px;
      box-shadow:0 8px 28px rgba(0,0,0,.5);`;
    panel.innerHTML = `
      <div style="display:flex;justify-content:space-between;align-items:center;gap:8px">
        <b style="font-size:12px;letter-spacing:.4px;cursor:pointer" data-act="toggle">TRIPO EXPORT</b>
        <span style="display:flex;gap:2px">
          <span data-act="toggle" data-caret style="cursor:pointer;opacity:.55;padding:0 4px">&#9662;</span>
          <span data-act="close"  style="cursor:pointer;opacity:.55;padding:0 4px">&times;</span>
        </span>
      </div>
      <div data-act="body" style="margin-top:9px">
        <div style="display:flex;gap:7px;margin-bottom:9px">
          <button data-act="glb" style="flex:1">GLB</button>
          <button data-act="obj" style="flex:1">OBJ</button>
        </div>
        <label style="display:flex;gap:6px;align-items:center;font-size:12px;opacity:.85">
          <input type="checkbox" data-opt="includeNormals"> keep normals
        </label>
        <label style="display:flex;gap:6px;align-items:center;font-size:12px;opacity:.85">
          <input type="checkbox" data-opt="largestMeshOnly"> largest mesh only
        </label>
        <div data-act="captured" style="margin-top:9px"></div>
        <div data-act="status" style="margin-top:9px;font-size:11px;opacity:.7;min-height:15px">ready</div>
      </div>`;

    for (const b of panel.querySelectorAll('button')) {
      b.style.cssText += 'background:#2f6fed;border:0;color:#fff;border-radius:6px;padding:7px 0;cursor:pointer;font-size:12px;font-weight:600';
    }

    const status = panel.querySelector('[data-act="status"]');
    const optEls = [...panel.querySelectorAll('[data-opt]')];
    for (const el of optEls) {
      el.checked = !!prefs[el.dataset.opt];
      el.onchange = () => savePrefs({ ...loadPrefs(), ...readOpts() });
    }
    const readOpts = () => Object.fromEntries(optEls.map(el => [el.dataset.opt, el.checked]));

    const bodyEl = panel.querySelector('[data-act="body"]');
    const caret  = panel.querySelector('[data-caret]');
    const setCollapsed = c => {
      if (bodyEl) bodyEl.style.display = c ? 'none' : '';
      panel.style.width = c ? 'auto' : '210px';
      if (caret) caret.innerHTML = c ? '&#9656;' : '&#9662;';
    };
    setCollapsed(!!prefs.collapsed);
    for (const el of panel.querySelectorAll('[data-act="toggle"]')) {
      el.onclick = () => {
        const collapsed = bodyEl.style.display !== 'none';
        setCollapsed(collapsed);
        savePrefs({ ...loadPrefs(), ...readOpts(), collapsed });
      };
    }

    // Originals grabbed off the wire beat anything rebuilt from the scene, so
    // they get top billing whenever the capture hook caught something.
    const capturedEl = panel.querySelector('[data-act="captured"]');
    const renderCaptured = () => {
      if (!capturedEl) return;
      if (!captured.length) { capturedEl.innerHTML = ''; return; }
      capturedEl.innerHTML =
        `<div style="font-size:11px;opacity:.6;margin-bottom:4px">ORIGINAL FILES (${captured.length})</div>`;
      captured.forEach((c, i) => {
        const row = document.createElement('button');
        row.textContent = `${c.format.toUpperCase()} · ${(c.size / 1048576).toFixed(1)} MB`;
        row.title = c.filename;
        row.style.cssText = 'display:block;width:100%;margin-bottom:4px;background:#2a7d46;border:0;' +
          'color:#fff;border-radius:6px;padding:6px 0;cursor:pointer;font-size:11px;font-weight:600';
        row.onclick = () => { saveCaptured(i); status.textContent = `✓ ${c.filename}`; };
        capturedEl.appendChild(row);
      });
    };
    renderCaptured();
    document.addEventListener('tripo:captured', renderCaptured);

    panel.querySelector('[data-act="close"]').onclick = () => {
      document.removeEventListener('tripo:captured', renderCaptured);
      panel.remove();
    };

    for (const act of ['glb', 'obj']) {
      panel.querySelector(`[data-act="${act}"]`).onclick = async () => {
        status.textContent = 'extracting…';
        try {
          const res = act === 'glb' ? await exportGLB(readOpts()) : await exportOBJ(readOpts());
          status.textContent = `✓ ${res.vertices.toLocaleString()} verts, ${res.sizeMB} MB`;
        } catch (e) {
          status.textContent = `✗ ${e.message}`;
          console.error(LOG, e);
        }
      };
    }

    document.body.appendChild(panel);
  }

  window.tripo = {
    glb: exportGLB, obj: exportOBJ, inspect, panel: mountPanel, findScene,
    saveCaptured, listCaptured, get captured() { return captured; },
  };

  installNetworkCapture();

  // The Tampermonkey build sets this flag and mounts the panel itself, so it can
  // wait for an actual model page and re-mount across SPA navigations.
  if (!window.__TRIPO_NO_AUTOMOUNT) mountPanel();
  log('ready — tripo.glb() / tripo.obj() / tripo.inspect() / tripo.saveCaptured()');
})();

// ═══════════════════════════════════════════════════════════════════════════
// TAMPERMONKEY BOOTSTRAP
// ═══════════════════════════════════════════════════════════════════════════
(function bootstrap() {
  'use strict';

  const PANEL_ID = 'tripo-dl-panel';
  const hasViewport = () => !!document.querySelector('canvas');

  function sync() {
    if (!document.body) return; // @run-at document-start: DOM may not exist yet
    const panel = document.getElementById(PANEL_ID);
    if (hasViewport()) {
      if (!panel) window.tripo.panel();
    } else if (panel) {
      panel.remove();
    }
  }

  // Debounced so a busy Vue re-render does not thrash the panel.
  let timer = null;
  const scheduleSync = () => {
    clearTimeout(timer);
    timer = setTimeout(sync, 300);
  };

  // The site is a SPA: route changes never fire load, and pushState fires no
  // event at all, so it has to be patched to notify us.
  for (const method of ['pushState', 'replaceState']) {
    const original = history[method];
    history[method] = function (...args) {
      const result = original.apply(this, args);
      window.dispatchEvent(new Event('tripo:navigate'));
      return result;
    };
  }
  window.addEventListener('tripo:navigate', scheduleSync);
  window.addEventListener('popstate', scheduleSync);

  // Catches the canvas appearing after the model finishes loading.
  new MutationObserver(scheduleSync).observe(document.documentElement, {
    childList: true, subtree: true,
  });

  scheduleSync();
  console.log('[tripo] userscript v2.0.2 active on', location.hostname);
})();
