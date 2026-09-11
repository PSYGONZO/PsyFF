#!/usr/bin/env node
// PsyFF 4.1 — path-contained (reads input/ + output/, writes output/ only),
// symlink-escape guarded, house formats, monitor terminal, VMAF, probe_full.
// 4.1: stream-copy guard (mapped output + no codec flags → auto '-c copy'),
//      duration-based timeout floor (slow codecs ×4, others ×2), cleanup:
//      fixed broken string in probe_full arg-missing hint, removed dead
//      labeled statement in packetStats, deduped error-path helpers.
import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import { CallToolRequestSchema, ListToolsRequestSchema } from "@modelcontextprotocol/sdk/types.js";
import { spawn } from "child_process";
import { promises as fs } from "fs";
import path from "path";

const BASE = "/home/jim/Applications/LMStudio";
const INPUT = path.join(BASE, "input");
const OUTPUT = path.join(BASE, "output");
const LOGS = path.join(BASE, "logs");
const BIN_FFMPEG = "/usr/bin/ffmpeg";
const BIN_FFPROBE = "/usr/bin/ffprobe";
const BIN_MKVMERGE = "/usr/bin/mkvmerge";
const BIN_MKVINFO = "/usr/bin/mkvinfo";

const ALLOWED_ROOTS = [INPUT, OUTPUT];
const AUTO_STRIP_METADATA = true;
const AUTO_REINDEX_MKV = true;
const AUTO_STREAM_COPY = true;             // no codec flags on a mapped output → '-c copy'
const TIMEOUT_FLOOR_SLOW = 4, TIMEOUT_FLOOR_FAST = 2;   // × input duration, in minutes
const MAX_CAPTURE_BYTES = 256 * 1024;
const FULL_PROBE_CAPTURE = 8 * 1024 * 1024;
const FULL_DUMP_TEXT_CAP = 120_000;
const FRAME_SAMPLE_CAP = 150;

const OPEN_TERMINAL = true;
const TERMINAL_CANDIDATES = [
    { bin: "/usr/bin/konsole",        prefix: ["-e", "bash", "-c"] },
{ bin: "/usr/bin/gnome-terminal", prefix: ["--", "bash", "-c"] },
{ bin: "/usr/bin/xfce4-terminal", prefix: ["-e", "bash", "-c"] },
{ bin: "/usr/bin/tilix",          prefix: ["-e", "bash", "-c"] },
{ bin: "/usr/bin/xterm",          prefix: ["-e"] }
];

// --- Files, binaries & path containment -------------------------------------

async function verifyBin(bin) {
    try { await fs.access(bin); }
    catch { throw new Error(`Binary not found: ${bin}`); }
}

// The ONLY way any media file here is located. Plain filename → input/ then
// output/. Real path (symlinks followed) must stay inside the root.
// Fuzzy fallback for LLM typos: case-insensitive, then stem prefix match.
async function resolveMedia(raw) {
    const name = path.basename(String(raw).trim());
    if (!name || name === "." || name === "..") throw new Error("Invalid or empty filename");

    for (const base of ALLOWED_ROOTS) {
        const realBase = await fs.realpath(base).catch(() => "");
        if (!realBase) continue;
        const real = await fs.realpath(path.resolve(base, name)).catch(() => null);
        if (real && real.startsWith(realBase + path.sep)) return real;
    }

    const norm = name.toLowerCase();
    for (const base of ALLOWED_ROOTS) {
        const realBase = await fs.realpath(base).catch(() => "");
        if (!realBase) continue;
        const hit = (await fs.readdir(base).catch(() => []))
        .find(n => n.toLowerCase() === norm || n.toLowerCase().startsWith(norm) || norm.includes(n.toLowerCase()));
        if (hit) {
            const real = await fs.realpath(path.join(base, hit)).catch(() => null);
            if (real && real.startsWith(realBase + path.sep)) {
                console.error(`psyff: fuzzy-matched '${name}' -> '${hit}'`);
                return real;
            }
        }
    }

    const available = (await Promise.all(ALLOWED_ROOTS.map(d => fs.readdir(d).catch(() => [])))).flat();
    throw new Error(`'${name}' not found in input/ or output/. Available files: ${available.join(", ") || "(none)"}`);
}

// Outputs are ALWAYS basenamed and pinned into output/ (unique, never clobber).
async function getUniqueOutPath(raw) {
    const name = path.basename(String(raw).trim());
    if (!/\.[A-Za-z0-9]{2,5}$/.test(name)) throw new Error(`Output must be 'name.ext': '${name}'`);
    let base = path.join(OUTPUT, name);
    const ext = path.extname(base);
    const stem = base.slice(0, -ext.length);
    for (let counter = 2; ; counter++) {
        try { await fs.access(base); base = `${stem}_${counter}${ext}`; }
        catch { return base; }
    }
}

function formatBinary(bytes) {
    const gib = bytes / 1024 ** 3;
    if (gib >= 1.0) return `${gib.toFixed(2)}GiB`;
    const mib = bytes / 1024 ** 2;
    if (mib >= 1.0) return `${mib.toFixed(1)}MiB`;
    return `${(bytes / 1024).toFixed(0)}KiB`;
}

function fmtTs(sec) {
    if (!Number.isFinite(sec) || sec < 0) return "?";
    const m = Math.floor(sec / 60);
    return `${m}:${(sec - m * 60).toFixed(1).padStart(4, "0")}`;
}

const shArg = x => /\s/.test(x) ? `"${x.replace(/"/g, '\\"')}"` : x;
const cmdLine = (bin, args) => [bin, ...args.map(shArg)].join(" ");

function shellSplit(s) {
    const out = [];
    let cur = "", q = null;
    for (const ch of String(s)) {
        if (q) { if (ch === q) q = null; else cur += ch; }
        else if (ch === '"' || ch === "'") q = ch;
        else if (/\s/.test(ch)) { if (cur) { out.push(cur); cur = ""; } }
        else cur += ch;
    }
    if (cur) out.push(cur);
    return out;
}

// Accepts args as array, single string, or whatever shape the LLM invented.
function normalizeArgs(a) {
    let raw = a?.args ?? a?.command ?? a?.argv ?? null;
    if (raw === null && a && typeof a === "object" && !Array.isArray(a)) {
        const vals = Object.values(a);
        if (vals.length && vals.every(v => typeof v === "string")) raw = vals;
    }
    if (typeof raw === "string") return shellSplit(raw);
    if (!Array.isArray(raw)) return [];
    if (raw.length === 1 && /\s/.test(String(raw[0]))) return shellSplit(raw[0]);
    return raw.map(t => String(t).trim()).filter(Boolean);
}

const truthy = v => v === true || v === 1 || String(v).toLowerCase() === "true" || String(v) === "1";

function extractFilenameArg(a, keys = ["filename", "file", "name", "filename_0"]) {
    if (typeof a === "string") return a.trim();
    if (Array.isArray(a) && a.length) return String(a[0]).trim();
    if (a && typeof a === "object") {
        let f = keys.map(k => a[k]).find(v => typeof v === "string" && v.trim()) || "";
        if (!f) {
            const strs = Object.values(a).filter(v =>
            typeof v === "string" && v.trim() && !v.includes("/") && !v.startsWith("-") &&
            !/^(true|false|1|0)$/i.test(v.trim()));
            if (strs.length === 1) f = strs[0].trim();
        }
        return f.trim();
    }
    return "";
}

// --- Process runner ---------------------------------------------------------

async function runWithIncrementalLog(bin, args, logPath, timeoutMs = 1800000, onSpawn = null, capBytes = MAX_CAPTURE_BYTES) {
    await fs.mkdir(path.dirname(logPath), { recursive: true }).catch(() => {});
    return new Promise(res => {
        let c;
        try { c = spawn(bin, args, { stdio: ["ignore", "pipe", "pipe"] }); }
        catch (e) { res({ code: -1, out: "", err: `SPAWN THROW: ${e.message}`, logPath }); return; }
        if (onSpawn) { try { onSpawn(c); } catch { } }

        let out = "", err = "", settled = false;
        const cap = s => s.length > 2 * capBytes ? "[...earlier output truncated...]\n" + s.slice(-capBytes) : s;

        c.stdout.on("data", d => { const t = d.toString().replace(/\r/g, "\n"); out = cap(out + t); fs.appendFile(logPath, t).catch(() => {}); });
        c.stderr.on("data", d => { const t = d.toString().replace(/\r/g, "\n"); err = cap(err + t); fs.appendFile(logPath, t).catch(() => {}); });

        let killed = false;
        const timer = setTimeout(() => {
            killed = true;
            c.kill("SIGKILL");
            err += `\nTIMEOUT after ${Math.round(timeoutMs / 60000)}min`;
        }, Math.max(timeoutMs, 1));

        c.on("error", e => { err += `\nSPAWN: ${e.code || ""} ${e.message}`; });
        c.on("close", (code, signal) => {
            if (settled) return;
            settled = true;
            clearTimeout(timer);
            res({ logPath, out, err, code: killed ? -1 : code, signal, killed });
        });
    });
}

async function spawnMonitorTerminal(logPath, msg = "Job running.") {
    for (const cand of TERMINAL_CANDIDATES) {
        try {
            await fs.access(cand.bin);
            const pidFile = `${logPath}.pid`;
            const sh =
            `sleep 0.5; ` +
            `JPID=$(cat "${pidFile}" 2>/dev/null); ` +
            `if [ -z "$JPID" ]; then echo "No active job for this window."; read; exit 0; fi; ` +
            `echo "${msg} PID: $JPID — press q to STOP."; ` +
            `tail -f "${logPath}" & TP=$!; ` +
            `while kill -0 $JPID 2>/dev/null; do ` +
            `IFS= read -rsn1 -t 1 K || continue; ` +
            `if [ "$K" = q ] || [ "$K" = Q ]; then ` +
            `echo; echo ">>> STOP requested — killing job $JPID"; ` +
            `kill $JPID 2>/dev/null; sleep 1; kill -9 $JPID 2>/dev/null; ` +
            `fi; done; ` +
            `sleep 1; kill $TP 2>/dev/null; ` +
            `echo "--- last lines ---"; tail -n 12 "${logPath}"; ` +
            `echo "=== job finished. You can close this window. ==="; read`;
            const t = spawn(cand.bin, [...cand.prefix, sh], { detached: true, stdio: "ignore" });
            t.unref();
            return true;
        } catch { continue; }
    }
    return false;
}

// Missing-argument error that lists what IS available (used by all tools).
async function missingArgError(msg) {
    const files = await fs.readdir(INPUT).catch(() => []);
    return { content: [{ type: "text", text: `${msg}\nAvailable input files: ${files.join(", ") || "(none)"}` }], isError: true };
}

// --- Probing ----------------------------------------------------------------

async function ffprobeJson(target, sections, timeoutMs = 120000) {
    await verifyBin(BIN_FFPROBE);
    const args = ["-v", "error", "-print_format", "json"];
    for (const s of sections) args.push(`-${s}`);
    args.push(target);
    const r = await runWithIncrementalLog(BIN_FFPROBE, args,
                                          `${LOGS}/ffprobe_${Date.now()}_${sections.join("_").replace(/^-/g, "")}.log`,
                                          timeoutMs, null, FULL_PROBE_CAPTURE);
    if (r.code) throw new Error(r.err || "ffprobe failed");
    return JSON.parse(r.out);
}

async function summary(p) {
    // Defense in depth: never probe anything outside the roots.
    const real = await fs.realpath(p).catch(() => null);
    if (real !== null) {
        let ok = false;
        for (const base of ALLOWED_ROOTS) {
            const rb = await fs.realpath(base).catch(() => "");
            if (rb && real.startsWith(rb + path.sep)) { ok = true; break; }
        }
        if (!ok) throw new Error(`Access denied: '${path.basename(p)}' resolves outside input/ and output/`);
        p = real;
    }
    const j = await ffprobeJson(p, ["show_format", "show_streams"]);
    const f = j.format;
    const containerSize = Number(f.size || 0);
    const duration = Number(f.duration || 0);
    const streams = [];
    const streamInfo = {};

    j.streams.forEach(s => {
        const n = j.streams.slice(0, j.streams.indexOf(s)).filter(x => x.codec_type === s.codec_type).length;
        const label = `0:${s.codec_type[0]}:${n}`;
        let streamBytes = 0;
        if (s.tags?.BPS && duration) streamBytes = (parseInt(s.tags.BPS) * duration) / 8;
        else if (s.bit_rate && duration) streamBytes = (parseInt(s.bit_rate) * duration) / 8;
        const brInfo = s.tags?.BPS || s.bit_rate ? ` ${Math.round((s.tags?.BPS || s.bit_rate) / 1000)}kbps` : "";
        const details = [s.codec_name, s.channels ? `${s.channels}ch` : "", s.channel_layout ? `(${s.channel_layout})` : "",
                      s.codec_type === "video" && s.width ? `${s.width}x${s.height}` : "", brInfo].filter(Boolean).join(" ");
                      const lang = s.tags?.language ? ` [${s.tags.language}]` : "";
                      const sizeStr = streamBytes > 0 ? ` ${formatBinary(streamBytes)}` : "";
                      streams.push(`${label} ${details}${lang}${sizeStr}`);
                      streamInfo[label] = { bytes: streamBytes, codec_type: s.codec_type, codec_name: s.codec_name, channels: s.channels, channel_layout: s.channel_layout || "" };
    });

    return {
        json: j,
        text: `${path.basename(p)}: ${f.format_name}, ${duration.toFixed(1)}s, ${formatBinary(containerSize)} | ${streams.join(", ")}`,
        containerBytes: containerSize,
        streamInfo,
        duration
    };
}

// Packet-level ground truth: real per-stream bitrates, packet counts, keyframes.
// Container framing only — no decode, fast even on large files.
async function packetStats(p) {
    const j = await ffprobeJson(p, ["show_packets"]);
    const per = {};
    let totalPackets = 0;
    for (const pk of (j.packets || [])) {
        const i = Number(pk.stream_index ?? 0);
        const s = per[i] || (per[i] = { packets: 0, bytes: 0, keyframes: 0, first_ts: null, last_ts: null });
        s.packets++;
        totalPackets++;
        s.bytes += parseInt(pk.size || 0, 10);
        if ((pk.flags || "").includes("K")) s.keyframes++;
        const ts = pk.dts_time !== undefined ? Number(pk.dts_time) : (pk.pts_time !== undefined ? Number(pk.pts_time) : NaN);
        if (Number.isFinite(ts)) {
            if (s.first_ts === null) s.first_ts = ts;
            s.last_ts = ts;
        }
    }
    const rows = Object.entries(per).map(([idx, s]) => {
        const span = (s.last_ts ?? 0) - (s.first_ts ?? 0);
        const realBitrate = span > 0 ? Math.round((s.bytes * 8) / span / 1000) : null;
        return {
            stream_index: Number(idx),
                                         packets: s.packets,
                                         keyframes: s.keyframes,
                                         keyframe_interval_packets: s.keyframes ? Math.round(s.packets / s.keyframes) : null,
                                         payload_bytes: s.bytes,
                                         measured_bitrate_kbps: realBitrate
        };
    }).sort((a, b) => a.stream_index - b.stream_index);
    return { total_packets: totalPackets, per_stream: rows };
}

async function frameSample(p, maxFrames = FRAME_SAMPLE_CAP) {
    const j = await ffprobeJson(p, ["show_frames"]);
    const frames = Array.isArray(j.frames) ? j.frames : [];
    const videos = frames.filter(f => f.media_type === "video");
    return {
        total_frames_in_file: frames.length,
        video_frames: videos.length,
        sampled: videos.slice(0, maxFrames),
        truncated: videos.length > maxFrames
    };
}

function clipDurationFromArgs(args, inDur) {
    let t = null, to = null, ss = 0;
    for (let i = 0; i < args.length - 1; i++) {
        if (args[i] === "-t") t = parseFloat(args[i + 1]);
        if (args[i] === "-to") to = parseFloat(args[i + 1]);
        if (args[i] === "-ss") { const v = parseFloat(args[i + 1]); if (!isNaN(v)) ss = Math.max(ss, v); }
    }
    if (t !== null && !isNaN(t)) return Math.max(t - ss, 0);
    if (to !== null && !isNaN(to)) return Math.max(to - ss, 0);
    return Math.max(inDur - ss, 0);
}

function parseMapTargets(args) {
    const targets = [];
    for (let i = 0; i < args.length - 1; i++) {
        if (args[i] === "-map" && args[i + 1]) {
            const mt = args[i + 1].match(/^(\d+):(a|v|s)(?::(\d+))?$/);
            if (mt) targets.push({ label: args[i + 1], input: parseInt(mt[1], 10), type: mt[2], idx: mt[3] === undefined ? null : parseInt(mt[3], 10) });
        }
    }
    return targets;
}

function unmappedStreamNote(mapTargets, probeResults) {
    if (mapTargets.length === 0 || probeResults.length === 0) return "";
    let note = "";
    for (let inp = 0; inp < probeResults.length; inp++) {
        const pr = probeResults[inp];
        const exact = new Set(mapTargets.filter(t => t.input === inp && t.idx !== null).map(t => t.label));
        const wild = new Set(mapTargets.filter(t => t.input === inp && t.idx === null).map(t => t.type));
        const unmapped = Object.keys(pr.streamInfo).filter(l => !exact.has(l) && !wild.has(l.split(":")[1]));
        if (unmapped.length) note += `NOTE: input ${inp} has ${unmapped.join(", ")} but no -map covers it — these streams will be DROPPED.\n`;
    }
    return note;
}

// --- Argument analysis (4.1: copy-guard + timeout floor) --------------------

const hasCodecSelection = args => args.some(a => a === "-c" || /^-c:(v|a|s)$/.test(a));
const hasFilters = args => args.some(a => ["-vf", "-af", "-filter", "-filter_complex"].includes(a));

// House rule: a mapped output with no codec flags means lossless stream copy.
// Without this, ffmpeg silently re-encodes with defaults. Filters imply the
// user WANTS reprocessing — only warn there, never insert.
function applyCopyGuard(args) {
    if (!AUTO_STREAM_COPY) return "";
    if (!args.some(a => a === "-map")) return "";
    if (hasCodecSelection(args)) return "";
    if (hasFilters(args))
        return "NOTE: no -c flags with filters — ffmpeg will re-encode with DEFAULTS. Pass explicit -c:v/-c:a if that is not intended.\n";
    args.splice(args.length - 1, 0, "-c", "copy");
    return "STREAM COPY: no codec flags given — '-c copy' inserted (lossless mux). Pass explicit -c:v/-c:a to re-encode.\n";
}

// Slow codecs need far more than wall-clock; scale from measured input duration.
function computeTimeout(args, inDurSec, requested) {
    const joined = args.join(" ");
    const slow = /(libsvtav1|libaom-av1|av1|libx265|hevc|libvvenc)/i.test(joined);
    const mult = slow ? TIMEOUT_FLOOR_SLOW : TIMEOUT_FLOOR_FAST;
    let minutes = (Number.isFinite(requested) && requested > 0) ? Math.min(requested, 99) : 30;
    let note = "";
    if (inDurSec > 0 && !hasCodecSelection(args) === false || true) {
        const floorMin = Math.ceil((inDurSec / 60) * mult);
        if (minutes < floorMin) {
            note = `TIMEOUT: raised ${minutes} → ${Math.min(floorMin, 99)} min (input ${(inDurSec / 60).toFixed(1)}min × ${mult}${slow ? ", slow codec" : ""}).\n`;
            minutes = Math.min(floorMin, 99);
        }
    }
    return { minutes, note };
}

// --- VMAF helpers -----------------------------------------------------------

function fpsNumber(stream) {
    const [num, den] = (stream?.avg_frame_rate || stream?.r_frame_rate || "0/1").split("/").map(Number);
    return num && den ? num / den : 0;
}

function vmafVerdict(mean) {
    if (!Number.isFinite(mean)) return "Unknown — no valid scores";
    if (mean >= 95) return "Excellent — visually transparent";
    if (mean >= 80) return "Good — artifacts rarely noticeable in motion";
    if (mean >= 60) return "Fair — visible degradation on some scenes";
    return "Poor — heavy degradation";
}

// --- MKV reindex ------------------------------------------------------------

async function hasCueTable(mkvPath) {
    try { await verifyBin(BIN_MKVINFO); } catch { return null; }
    const r = await runWithIncrementalLog(BIN_MKVINFO, [mkvPath], `${LOGS}/mkvinfo_${Date.now()}.log`, 60000);
    if (r.code !== 0 || !r.out) return null;
    return /^\|*\s*\+*\s*Cues\s*$/m.test(r.out);
}

async function ensureMkvIndex(mkvPath) {
    const cues = await hasCueTable(mkvPath);
    if (cues === null) return { rebuilt: false, reason: "Cues not verifiable (mkvinfo unavailable) — skipped" };
    if (cues) return { rebuilt: false, reason: "Cue table present" };
    try {
        await verifyBin(BIN_MKVMERGE);
        const tmp = `${mkvPath}.reidx-${process.pid}`;
        const r = await runWithIncrementalLog(BIN_MKVMERGE, ["-o", tmp, mkvPath], `${LOGS}/mkvmerge_reindex_${Date.now()}.log`, 1800000);
        if (r.code === 0) { await fs.unlink(mkvPath); await fs.rename(tmp, mkvPath); return { rebuilt: true, reason: "Index rebuilt" }; }
        await fs.unlink(tmp).catch(() => {});
        return { rebuilt: false, reason: "Rebuild failed (see logs)" };
    } catch {
        return { rebuilt: false, reason: "Rebuild failed (mkvmerge unavailable)" };
    }
}

// ---------------------------------------------------------------------------

const tools = [
    {
        name: "list_media",
        description: "LIST MEDIA FILES: returns all files in input/ and output/ (names, sizes, mtime). Use FIRST whenever the user refers to files without exact names ('those videos', 'the output files'). No parameters.",
        inputSchema: { type: "object", properties: {}, required: [] }
    },
{
    name: "probe_media",
    description: "QUICK MEDIA INFO: pass filename as 'filename' (plain name, spaces OK). Searched in input/ then output/. Returns duration, container, streams with codec/layout/bitrate, per-stream sizes, and -map labels (0:v:0, 0:a:0 ...). Call BEFORE conversion planning. Fast, single pass. Wrong filename → error lists available files. For an exhaustive dump (chapters, measured bitrates) call probe_full instead.",
    inputSchema: {
        type: "object",
        properties: {
            filename: { "type": "string", description: "Filename in input/ or output/ (plain name, no path, spaces allowed)." }
        },
        required: []
    }
},
{
    name: "probe_full",
    description: "EXHAUSTIVE FILE DUMP: everything ffprobe knows. Sections: format, ALL streams with every field, chapters, programs. Optional: deep=true adds packet-level MEASURED stats (real bitrate, keyframe intervals — no decode); show_data=true dumps hex payload samples; frames=true includes per-frame data (sampled to 150). Use when the user asks for 'everything about' a file.",
    inputSchema: {
        type: "object",
        properties: {
            filename: { "type": "string", description: "Plain file name, no path, spaces allowed." },
            deep: { "type": "boolean", description: "Add packet-level measured stats. Recommended." },
            show_data: { "type": "boolean", description: "Include hex payload samples (very verbose)." },
            frames: { "type": "boolean", description: "Include per-frame data, sampled (first 150 video frames)." }
        },
        required: []
    }
},
{
    name: "run_ffmpeg",
    description: "EXECUTE a conversion: args=['-i','file.mkv','-map','<stream>','-c:v/a','codec','-b:v/a','value','out.ext'] — every item ONE string; filenames with spaces stay a single item (no quoting needed). Inputs looked up in input/ AND output/; outputs land in output/. Monitor terminal shows LIVE progress; press q there to STOP. Full conversion report on completion. HOUSE FORMATS: .mkv video, .mka audio-only, .flac only for FLAC. With -map but NO codec flags, '-c copy' is inserted automatically (lossless mux) — pass explicit -c:v/-c:a to re-encode. Timeout auto-raised to a duration-based floor. Metadata stripped automatically. For quality scoring use run_vmaf (never '-f null -' here).",
    inputSchema: {
        type: "object",
        properties: {
            args: { type: "array", items: { type: "string" } },
            timeout_minutes: { type: "number", description: "Timeout in minutes (default 30, max 99; auto-raised to duration-based floor)." }
        },
        required: ["args"]
    }
},
{
    name: "run_vmaf",
    description: "QUALITY SCORE: VMAF (+PSNR) of an encoded file vs its clean source. distorted = RE-ENCODED file, source = ORIGINAL — order matters. Both looked up in input/ AND output/. Returns mean/min/max VMAF and PSNR with a verdict. Requires identical resolution and frame rate (pre-checked; force=true to score anyway — unreliable). Use AFTER an encode.",
    inputSchema: {
        type: "object",
        properties: {
            distorted: { "type": "string", description: "Re-encoded file." },
            source: { "type": "string", description: "Original clean file." },
            extra_features: { "type": "string", description: "Extra libvmaf features, space-separated, e.g. 'name=float_ssim'." },
            model: { "type": "string", description: "Optional path to a VMAF model file (no spaces)." },
            force: { type: "boolean", description: "Run despite resolution/fps mismatch — unreliable." },
                timeout_minutes: { type: "number", description: "Default 60, max 99." }
        },
        required: ["distorted", "source"]
    }
}
];

const server = new Server({ name: "psyff", version: "4.1.0" }, { capabilities: { tools: {} } });
server.setRequestHandler(ListToolsRequestSchema, async () => ({ tools }));

server.setRequestHandler(CallToolRequestSchema, async ({ params: { name, arguments: a } }) => {
    try {
        switch (name) {

            case "list_files":
            case "list_media": {
                const parts = [];
                for (const [label, dir] of [["input", INPUT], ["output", OUTPUT]]) {
                    const entries = await fs.readdir(dir, { withFileTypes: true }).catch(() => []);
                    const lines = await Promise.all(entries.filter(e => e.isFile()).map(async e => {
                        const st = await fs.stat(path.join(dir, e.name)).catch(() => null);
                        const sz = st ? formatBinary(st.size) : "?";
                        const mt = st ? st.mtime.toISOString().slice(0, 16).replace("T", " ") : "?";
                        return `  ${e.name}  (${sz}, ${mt})`;
                    }));
                    parts.push(`${label}/:\n${lines.join("\n") || "  (empty)"}`);
                }
                return { content: [{ type: "text", text: `FILES:\n${parts.join("\n\n")}` }] };
            }

            case "probe_media": {
                await verifyBin(BIN_FFPROBE);
                const fname = extractFilenameArg(a);
                if (!fname) return await missingArgError(`MISSING FILENAME: pass 'filename' with the plain name, e.g. {"filename":"video.mkv"}.`);
                const p = await resolveMedia(fname);
                const s = await summary(p);
                const first = Object.keys(s.streamInfo)[0] || "0:v:0";
                return { content: [{ type: "text", text: `PROBE:\n${s.text}\n\nLabels map directly: e.g. -map '${first}'. Then call run_ffmpeg with -map and an output filename (prefer .mkv for video, .mka/.flac for audio).` }] };
            }

            case "probe_full": {
                await verifyBin(BIN_FFPROBE);
                const fname = extractFilenameArg(a);
                if (!fname) return await missingArgError(`MISSING FILENAME: pass 'filename' with the plain name, e.g. {"filename":"video.mkv","deep":true}.`);
                const p = await resolveMedia(fname);

                const sections = ["show_format", "show_streams", "show_chapters", "show_programs"];
                if (truthy(a.show_data)) sections.push("show_data");
                const j = await ffprobeJson(p, sections);

                let deepBlock = "";
                if (truthy(a.deep)) {
                    try {
                        const stats = await packetStats(p);
                        deepBlock = `\nPACKET-LEVEL MEASUREMENTS (ground truth, container framing only — no decode):\n` +
                        `total packets: ${stats.total_packets}\n` +
                        stats.per_stream.map(r =>
                        `  stream ${r.stream_index}: ${r.packets} packets, ${formatBinary(r.payload_bytes)} payload, ` +
                        `${r.keyframes} keyframes (1 per ~${r.keyframe_interval_packets ?? "?"} packets), ` +
                        `measured bitrate ${r.measured_bitrate_kbps !== null ? r.measured_bitrate_kbps + " kbps" : "n/a"}`
                        ).join("\n");
                    } catch (e) {
                        deepBlock = `\nPACKET ANALYSIS SKIPPED: ${e.message}`;
                    }
                }

                let frameBlock = "";
                if (truthy(a.frames)) {
                    try {
                        const fr = await frameSample(p, FRAME_SAMPLE_CAP);
                        frameBlock = `\nFRAME DATA: ${fr.video_frames} video frames total` +
                        (fr.truncated ? ` — showing first ${fr.sampled.length} (set of ${fr.total_frames_in_file} frames seen)` : "") + "\n" +
                        JSON.stringify(fr.sampled.slice(0, 20), null, 2) +
                        (fr.sampled.length > 20 ? `\n(...${fr.sampled.length - 20} more frames in raw JSON below)` : "");
                    } catch (e) {
                        frameBlock = `\nFRAME DATA SKIPPED: ${e.message}`;
                    }
                }

                const f = j.format || {};
                const header = [
                    `==================================================`,
                    `FULL PROBE: ${path.basename(p)}`,
                         `==================================================`,
                         `Container:   ${f.format_long_name || f.format_name || "?"}`,
                         `Duration:    ${Number(f.duration || 0).toFixed(3)}s   Size: ${formatBinary(Number(f.size || 0))}`,
                         `Overall:     ${f.bit_rate ? Math.round(f.bit_rate / 1000) + " kbps (as reported)" : "n/a"} — declared tag values, not measured`,
                         `Streams:     ${j.streams.length}   Chapters: ${(j.chapters || []).length}   Programs: ${(j.programs || []).length}`,
                         deepBlock, frameBlock,
                         ``,
                         `FULL FFPROBE JSON (complete, raw):`,
                         `--------------------------------------------------`
                ].filter(Boolean).join("\n");

                let jsonText = JSON.stringify(j, null, 2);
                if (jsonText.length > FULL_DUMP_TEXT_CAP) {
                    jsonText = jsonText.slice(0, FULL_DUMP_TEXT_CAP) +
                    `\n\n[...TRUNCATED at ${FULL_DUMP_TEXT_CAP} chars — full data in log files in logs/]`;
                }

                return { content: [{ type: "text", text: header + "\n" + jsonText }] };
            }

            case "run_ffmpeg": {
                await verifyBin(BIN_FFMPEG);
                await verifyBin(BIN_FFPROBE);

                const args = normalizeArgs(a);

                if (!args.length) {
                    const files = await fs.readdir(INPUT).catch(() => []);
                    const first = files[0] || "<filename>";
                    return { content: [{ type: "text", text: `ARGUMENTS MISSING: no 'args' array received.\n\nProbe first with probe_media("${first}"), then retry EXACTLY like this (array of separate strings):\n{"args":["-i","${first}","-map","0:v:0","-map","0:a:0","out.mkv"]}\n\nAvailable input files: ${files.join(", ") || "(none)"}` }], isError: true };
                }

                // Probe-only calls
                if (args.length === 2 && args[0] === "-i") {
                    const p = await resolveMedia(args[1]);
                    const s = await summary(p);
                    const first = Object.keys(s.streamInfo)[0] || "0:v:0";
                    return { content: [{ type: "text", text: `PROBE:\n${s.text}\n\nLabels map directly: e.g. -map '${first}'. For inspection call probe_media directly — run_ffmpeg is for conversions.` }] };
                }

                const hasMap = args.some(arg => arg === "-map");
                const last = args.at(-1);

                if ((args.includes("-f") && args[args.indexOf("-f") + 1] === "null") || last === "-") {
                    return { content: [{ type: "text", text: "REDIRECTED: '-f null -' metric runs are not accepted here. For VMAF/PSNR quality scoring call run_vmaf with distorted=<encoded file>, source=<original>." }], isError: true };
                }

                if (!hasMap) {
                    if (!args.some(arg => arg === "-i")) {
                        const files = await fs.readdir(INPUT).catch(() => []);
                        return { content: [{ type: "text", text: `NO INPUT: args contain no '-i <file>'. Available input files: ${files.join(", ") || "(none)"}.` }], isError: true };
                    }
                    if (last.startsWith("-")) return { content: [{ type: "text", text: `NO OUTPUT FILE: args end with '${last}', not a filename.` }], isError: true };
                }
                if (last.startsWith("-")) throw new Error("Last arg must be output filename");

                // Resolve inputs, probe, copy-guard, then pin the output.
                for (let i = 0; i < args.length - 1; i++) {
                    if (args[i] === "-i") args[i + 1] = await resolveMedia(args[i + 1]);
                }

                const probeResults = [];
                for (let i = 0; i < args.length - 1; i++) {
                    if (args[i] === "-i") probeResults.push(await summary(args[i + 1]));
                }
                const inDur = probeResults[0]?.duration || 0;

                const copyNote = applyCopyGuard(args);
                const mapTargets = parseMapTargets(args);
                const unmappedNote = unmappedStreamNote(mapTargets, probeResults);

                const outDest = await getUniqueOutPath(last);

                let metadataNote = "";
                const userManagesMetadata = args.some(arg => arg.startsWith("-map_metadata"));
                if (!userManagesMetadata && AUTO_STRIP_METADATA) {
                    args.splice(args.length - 1, 0, "-map_metadata", "-1", "-map_metadata:s", "-1");
                    metadataNote = "METADATA: source tags stripped (-map_metadata -1 -map_metadata:s -1)";
                }

                args[args.length - 1] = outDest;

                const { minutes: timeoutMinutes, note: timeoutNote } = computeTimeout(args, inDur, Number(a.timeout_minutes));

                const logPath = path.join(LOGS, `ffmpeg_${Date.now()}.log`);
                await fs.appendFile(logPath, `$ ${cmdLine(BIN_FFMPEG, args)}\nStarted: ${new Date().toISOString()}\n\n`).catch(() => {});
                const terminalSpawned = OPEN_TERMINAL ? await spawnMonitorTerminal(logPath) : false;

                const r = await runWithIncrementalLog(BIN_FFMPEG, args, logPath, timeoutMinutes * 60 * 1000,
                                                      child => { fs.writeFile(`${logPath}.pid`, String(child.pid)).catch(() => {}); });
                fs.appendFile(logPath, `\n=== psyff: job finished — exit ${r.code}${r.killed ? " (KILLED)" : ""} ===\n`).catch(() => {});

                const outExt = path.extname(outDest).toLowerCase();
                const codecs = {};
                for (let i = 0; i < args.length; i++) {
                    if (args[i] === "-c:a") codecs.a = args[i + 1];
                    if (args[i] === "-c:v") codecs.v = args[i + 1];
                    if (args[i] === "-b:a") codecs.abr = args[i + 1];
                    if (args[i] === "-b:v") codecs.vbr = args[i + 1];
                }

                const inSize = probeResults[0]?.containerBytes || 0;

                const streamBytesFor = (tgt) => {
                    const pr = probeResults[tgt.input] || probeResults[0];
                    if (!pr) return 0;
                    if (tgt.idx !== null) { const si = pr.streamInfo[tgt.label]; return si ? si.bytes : 0; }
                    return Object.entries(pr.streamInfo).filter(([k, v]) => k.startsWith(`${tgt.input}:`) && v.codec_type === tgt.type).reduce((s, [, v]) => s + v.bytes, 0);
                };
                let inputRefBytes = 0;
                mapTargets.forEach(t => { inputRefBytes += streamBytesFor(t); });
                if (mapTargets.length === 0 && probeResults.length > 0) inputRefBytes = probeResults[0].containerBytes;

                const lossless = /flac|alac|pcm_|ape|tta|wavpack|^copy$/.test(codecs.a || "") || codecs.a === undefined && codecs.v === undefined;

                let outExists = false, outSize = 0, outSizeStr = "?", outDur = 0;
                try {
                    const st = await fs.stat(outDest);
                    outExists = true; outSize = st.size; outSizeStr = formatBinary(st.size);
                } catch { }
                if (outExists) { try { outDur = (await summary(outDest)).duration; } catch { } }

                const bitrateMatch = r.err.match(/bitrate\s*=\s*(\d+)\s*kb\/s/i);
                const actualBitrate = bitrateMatch ? `${parseInt(bitrateMatch[1])}kbps` : null;

                let layoutHint = "";
                const layoutRejected = /(invalid|unsupported|not supported|rejected)[^.]*channel layout|channel layout[^.]*(invalid|unsupported|not supported)/i.test(r.err);
                if (layoutRejected && probeResults.length > 0) {
                    const layouts = mapTargets.map(t => {
                        const si = (probeResults[t.input] || probeResults[0])?.streamInfo[t.label];
                        return si?.channel_layout ? `${t.label} is ${si.channel_layout}` : null;
                    }).filter(Boolean).join(", ");
                    if (layouts.includes("(side)")) {
                        layoutHint = `HINT: ${layouts}. Encoder rejected '(side)' layout. Try '-af aformat=channel_layouts=5.1' or downmix with '-ac 2'.`;
                    } else if (layouts) {
                        layoutHint = `HINT: Input ${layouts}. Check encoder channel support, or downmix with '-ac 2'.`;
                    }
                }

                let subHint = "";
                if (/Subtitle encoding currently only possible/i.test(r.err)) {
                    subHint = "HINT: bitmap subtitles (PGS/VobSub) cannot be re-encoded as text. Add '-c:s copy' to mux them as-is, or drop the subtitle -map.";
                }

                let extNote = "";
                if (outExists && outExt === ".flac" && codecs.a && codecs.a.toLowerCase() !== "flac") {
                    extNote = `EXTENSION NOTE: '.flac' is only valid for -c:a flac; codec is '${codecs.a || "copy"}'. Prefer .mka for other audio codecs.`;
                }
                let prefNote = "";
                if (outExists && ![".mkv", ".mka", ".flac"].includes(outExt)) {
                    prefNote = "FORMAT NOTE: house preference is .mkv (video) / .mka (audio) / .flac (FLAC audio).";
                }

                const inputSizeStr = inputRefBytes > 0 ? formatBinary(inputRefBytes) : formatBinary(inSize);
                const sizeDeltaPct = inputRefBytes > 0 ? ((outSize - inputRefBytes) / inputRefBytes * 100).toFixed(1) : "N/A";
                const sizeSign = inputRefBytes > 0 && outSize < inputRefBytes ? "↓" : inputRefBytes > 0 && outSize > inputRefBytes ? "↑" : "—";

                const clipDur = clipDurationFromArgs(args, inDur);
                const effDur = outDur > 0 ? outDur : clipDur;

                let reindexResult = null;
                if (outExists && r.code === 0 && AUTO_REINDEX_MKV && (outExt === ".mkv" || outExt === ".mka")) {
                    try { reindexResult = await ensureMkvIndex(outDest); }
                    catch { reindexResult = { rebuilt: false, reason: "Reindex skipped" }; }
                }

                const codecLines = [];
                if (codecs.a) codecLines.push(`audio: ${codecs.a}${codecs.abr ? ` (${codecs.abr})` : ""}`);
                if (codecs.v) codecLines.push(`video: ${codecs.v}${codecs.vbr ? ` (${codecs.vbr})` : ""}`);
                const codecLine = codecLines.join(", ") || "copy (no re-encode)";

                let bitrateLabel;
                if (actualBitrate) bitrateLabel = `Bitrate: ${actualBitrate}`;
                else if (lossless) bitrateLabel = "Bitrate: Variable (lossless)";
                else if (codecs.abr || codecs.vbr) bitrateLabel = `Requested Bitrate: ${codecs.abr || codecs.vbr}`;
                else bitrateLabel = `Calculated Bitrate: ${(((outSize * 8) / (effDur > 0 ? effDur : 1)) / 1000).toFixed(0)}kbps over ${(effDur || inDur).toFixed(1)}s`;

                const reindexStatus = reindexResult
                ? `\nMKV INDEX: ${reindexResult.rebuilt ? "✓ Rebuilt" : `⚠ Skipped (${reindexResult.reason})`}` : "";
                const terminalNote = terminalSpawned ? `\n\nTERMINAL MONITOR: a window was watching this job. Close it manually.` : "";
                const usedCmd = cmdLine(BIN_FFMPEG, args);

                let report;
                if (r.code !== 0 || r.killed) {
                    try { await fs.unlink(outDest); } catch { }
                    report = `PRE-PROBE:\n${probeResults.map(pr => pr.text).join("\n")}\n\n` +
                    `❌ EXIT CODE: ${r.code ?? "null"}${r.signal ? ` (terminated by ${r.signal})` : ""}\n` +
                    `COMMAND: ${usedCmd}\n` +
                    `STDERR (tail):\n${(r.err || "").slice(-4000)}\n${layoutHint}${subHint}\n` +
                    `LOG: ${logPath}\n` +
                    (r.killed ? "NOTE: killed (timeout or manual q-stop) — this is NOT a codec error; raise the timeout and retry.\n" : "") +
                    `NOTE: partial output deleted.${terminalNote}`;
                } else if (!outExists) {
                    report = `PRE-PROBE:\n${probeResults.map(pr => pr.text).join("\n")}\n\n` +
                    `❌ FILE NOT CREATED (possible %-pattern image sequence — check output/ for numbered files.)\n` +
                    `COMMAND: ${usedCmd}\n` +
                    `CHECK LOG: ${logPath}${terminalNote}`;
                } else {
                    report = `==================================================\n` +
                    `✅ CONVERSION COMPLETE\n` +
                    `==================================================\n\n` +
                    `COMMAND USED:\n${usedCmd}\n\n` +
                    `INPUT:\n${probeResults.map(pr => pr.text).join("\n")}\n\n` +
                    `STREAMS MAPPED:\n${mapTargets.map(t => t.label).join(", ") || "all-streams"}\n\n` +
                    `CODEC CHANGES:\n${codecLine}\n\n` +
                    `SIZE COMPARISON:\n` +
                    `${inputSizeStr} → ${outSizeStr} (${sizeSign}${parseFloat(sizeDeltaPct)}%)\n` +
                    `Difference: ${formatBinary(Math.abs(outSize - inputRefBytes))}\n\n` +
                    `${bitrateLabel}\n\n` +
                    (unmappedNote ? unmappedNote + "\n" : "") +
                    [copyNote, timeoutNote, prefNote, metadataNote, extNote, reindexStatus.trim()].filter(Boolean).join("\n") + "\n" +
                    `LOG: ${logPath}\n` +
                    `==================================================${terminalNote}`;
                }

                return { content: [{ type: "text", text: report }], isError: r.code !== 0 || r.killed || !outExists };
            }

            case "run_vmaf": {
                await verifyBin(BIN_FFMPEG);
                await verifyBin(BIN_FFPROBE);

                const distName = path.basename(String(a.distorted || "").trim());
                const srcName = path.basename(String(a.source || "").trim());
                if (!distName || !srcName) return await missingArgError(`ARGUMENTS MISSING: pass BOTH "distorted" (re-encoded) and "source" (original).\nExample: {"distorted":"av1.mkv","source":"test.mkv"}`);

                const distPath = await resolveMedia(distName);
                const srcPath = await resolveMedia(srcName);
                const distPr = await summary(distPath);
                const srcPr = await summary(srcPath);

                const dV = distPr.json.streams.find(s => s.codec_type === "video");
                const sV = srcPr.json.streams.find(s => s.codec_type === "video");
                if (!dV || !sV) {
                    return { content: [{ type: "text", text: `❌ NO VIDEO STREAM: VMAF needs a video track in both files.\nDISTORTED: ${distPr.text}\nSOURCE: ${srcPr.text}` }], isError: true };
                }

                const dimOk = dV.width === sV.width && dV.height === sV.height;
                const fpsStrA = dV.avg_frame_rate || dV.r_frame_rate || "?";
                const fpsStrB = sV.avg_frame_rate || sV.r_frame_rate || "?";
                const fpsOk = fpsStrA === fpsStrB;
                const fpsNum = fpsNumber(sV) || fpsNumber(dV);

                if ((!dimOk || !fpsOk) && !truthy(a.force)) {
                    const reasons = [];
                    if (!dimOk) reasons.push(`  • resolution: distorted ${dV.width}x${dV.height} vs source ${sV.width}x${sV.height}`);
                    if (!fpsOk) reasons.push(`  • frame rate: distorted ${fpsStrA} vs source ${fpsStrB}`);
                    return { content: [{ type: "text", text: `❌ INPUT MISMATCH — libvmaf requires frame-aligned inputs. Not run.\n${reasons.join("\n")}\n\nFIX: re-encode the distorted file matching the source geometry, then retry. force=true overrides (scores unreliable).` }], isError: true };
                }

                const matchLine = dimOk && fpsOk
                ? `${dV.width}x${dV.height} @ ${fpsStrA} — ✓ matched`
                : `${dV.width}x${dV.height} @ ${fpsStrA} — ⚠ MISMATCHED (force=true)`;

                const vmafLog = path.join(LOGS, `vmaf_${Date.now()}.json`);
                const ffmpegLog = path.join(LOGS, `ffmpeg_vmaf_${Date.now()}.log`);
                await fs.mkdir(LOGS, { recursive: true }).catch(() => {});

                const feats = ["name=psnr"];
                for (const f of String(a.extra_features || "").trim().split(/\s+/)) if (f) feats.push(f);

                let lavfi = `[0:v][1:v]libvmaf=log_fmt=json:log_path=${vmafLog}:${feats.map(f => `feature=${f}`).join(":")}`;
                if (a.model) lavfi += `:model=path=${String(a.model).trim()}`;

                const tmRaw = Number(a.timeout_minutes);
                const timeoutMinutes = (Number.isFinite(tmRaw) && tmRaw > 0) ? Math.min(tmRaw, 99) : 60;
                const fargs = ["-hide_banner", "-stats_period", "1", "-i", distPath, "-i", srcPath, "-lavfi", lavfi, "-f", "null", "-"];
                const usedCmd = cmdLine(BIN_FFMPEG, fargs);
                await fs.appendFile(ffmpegLog, `$ ${usedCmd}\nStarted: ${new Date().toISOString()}\n\n`).catch(() => {});
                const terminalSpawned = OPEN_TERMINAL ? await spawnMonitorTerminal(ffmpegLog, "Analysis running.") : false;

                const r = await runWithIncrementalLog(BIN_FFMPEG, fargs, ffmpegLog, timeoutMinutes * 60 * 1000,
                                                      child => { fs.writeFile(`${ffmpegLog}.pid`, String(child.pid)).catch(() => {}); });
                fs.appendFile(ffmpegLog, `\n=== psyff: analysis finished — exit ${r.code}${r.killed ? " (KILLED)" : ""} ===\n`).catch(() => {});

                if (r.code !== 0 || r.killed) {
                    const e = r.err || "";
                    let hint = "";
                    if (/No such filter|Unknown filter|Invalid filter/i.test(e)) hint = "HINT: this ffmpeg build lacks libvmaf.";
                    else if (/frame size|different frame size|Changing video frame properties/i.test(e)) hint = `HINT: geometry drifted mid-stream. Distorted: ${dV.width}x${dV.height} @ ${fpsStrA}; Source: ${sV.width}x${sV.height} @ ${fpsStrB}. Re-encode for alignment.`;
                    else if (/Failed to open|Unable to open|No such file/i.test(e)) hint = a.model ? `HINT: model path '${a.model}' could not be opened.` : "HINT: vmaf model file missing — supply via 'model' parameter.";
                    else if (/Resolution/i.test(e)) hint = "HINT: input resolution mismatch.";

                    return { content: [{ type: "text", text: `❌ VMAF RUN FAILED\nEXIT: ${r.code ?? "null"}${r.signal ? ` (${r.signal})` : ""}\nCOMMAND: ${usedCmd}\n` +
                    (r.killed ? `NOTE: killed by timeout or q-stop — scoring decodes two streams (~2x encode cost).\n` : "") +
                    `STDERR (tail):\n${e.slice(-4000)}\n${hint}\nLOG: ${ffmpegLog}${terminalSpawned ? "\nTERMINAL MONITOR: close the window manually." : ""}` }], isError: true };
                }

                let pooled = null, framesScored = 0, framesArr = null;
                try {
                    const j = JSON.parse(await fs.readFile(vmafLog, "utf8"));
                    pooled = j.pooled_metrics || null;
                    framesArr = Array.isArray(j.frames) ? j.frames : null;
                    if (framesArr) framesScored = framesArr.length;
                } catch { }
                if (!pooled || !pooled.vmaf) {
                    const nums = [...(r.err || "").matchAll(/VMAF score:\s*([\d.]+)/g)].map(x => parseFloat(x[1]));
                    if (nums.length) {
                        pooled = { vmaf: { mean: nums.reduce((s, v) => s + v, 0) / nums.length, min: Math.min(...nums), max: Math.max(...nums) } };
                        framesScored = nums.length;
                    }
                }
                if (!pooled || !pooled.vmaf) {
                    return { content: [{ type: "text", text: `⚠️ VMAF finished (exit 0) but no scores parsed.\nCOMMAND: ${usedCmd}\nJSON LOG: ${vmafLog}\nFFMPEG LOG: ${ffmpegLog}` }], isError: true };
                }

                const f2 = v => Number.isFinite(Number(v)) ? Number(v).toFixed(2) : "?";
                const lines = [];
                lines.push(`==================================================`);
                lines.push(`✅ QUALITY ANALYSIS COMPLETE (VMAF)`);
                lines.push(`==================================================`);
                lines.push(`DISTORTED: ${distPr.text}`);
                lines.push(`SOURCE:    ${srcPr.text}`);
                lines.push(`GEOMETRY: ${matchLine}`);
                lines.push(`FRAMES SCORED: ${framesScored || "?"}`);
                lines.push(`VMAF:  mean ${f2(pooled.vmaf.mean)}  min ${f2(pooled.vmaf.min)}  max ${f2(pooled.vmaf.max)}`);
                if (pooled.psnr) lines.push(`PSNR:  mean ${f2(pooled.psnr.mean)}dB  min ${f2(pooled.psnr.min)}dB  max ${f2(pooled.psnr.max)}dB`);
                if (pooled.float_ssim || pooled.ssim) {
                    const ss = pooled.float_ssim || pooled.ssim;
                    lines.push(`SSIM:  mean ${f2(ss.mean)}  min ${f2(ss.min)}  max ${f2(ss.max)}`);
                }
                lines.push(`VERDICT: ${vmafVerdict(Number(pooled.vmaf.mean))}`);

                if (framesArr && framesArr.length && fpsNum > 0) {
                    let wIdx = -1, wVal = Infinity;
                    framesArr.forEach((fr, i) => {
                        const v = Number(fr?.metrics?.vmaf);
                        if (Number.isFinite(v) && v < wVal) { wVal = v; wIdx = i; }
                    });
                    if (wIdx >= 0 && wVal < Number(pooled.vmaf.mean) - 10) {
                        lines.push(`LOW-POINT WARNING: worst frame #${wIdx} (~${fmtTs(wIdx / fpsNum)}) scored ${wVal.toFixed(2)} — usually one scene the bitrate can't hold, not a global problem.`);
                    }
                } else if (framesScored && Number(pooled.vmaf.min) < Number(pooled.vmaf.mean) - 15) {
                    lines.push(`LOW-POINT WARNING: min ${f2(pooled.vmaf.min)} is far below the mean — some segments degrade much more than average.`);
                }
                if (Number(pooled.vmaf.mean) >= 98) lines.push(`NOTE: mean ≥ 98 means headroom — same visual quality likely possible at lower bitrate.`);

                lines.push(`COMMAND: ${usedCmd}`);
                lines.push(`JSON LOG: ${vmafLog}`);
                lines.push(`LOG: ${ffmpegLog}${terminalSpawned ? "\n\nTERMINAL MONITOR: close the window manually." : ""}`);

                return { content: [{ type: "text", text: lines.join("\n") }] };
            }

            default:
                throw new Error(`Unknown tool: ${name}`);
        }
    } catch (e) {
        return { content: [{ type: "text", text: `❌ ${name}: ${e.message}` }], isError: true };
    }
});

const main = async () => {
    for (const d of [INPUT, OUTPUT, LOGS])
        await fs.mkdir(d, { recursive: true }).catch(e => console.error(`psyff WARNING: cannot create '${d}': ${e.message}`));
    const shutdown = sig => { server.close().catch(() => {}); process.exit(0); };
    process.on("SIGINT", () => shutdown("SIGINT"));
    process.on("SIGTERM", () => shutdown("SIGTERM"));
    process.on("unhandledRejection", e => console.error(`psyff unhandledRejection: ${e?.message ?? e}`));
    await server.connect(new StdioServerTransport());
    console.error("PsyFF 4.1 on stdio");
};
main().catch(e => { console.error(e); process.exit(1); });
