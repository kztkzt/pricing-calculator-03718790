(() => {
'use strict';
const __m_calcEngine = (() => {
// Pricing calc engine. Pure functions, no UI, no floats: all math is exact BigInt fractions.
// No rounding in the math. Output strings only cut the exact fraction to 4 decimals for display (half up).
// IDR is not rounded unless the user sets idrStep > 0. Spec: docs/T1-formula-spec.md (v4).

// ---- exact fractions: { n: BigInt, d: BigInt > 0 } ----
const gcd = (a, b) => { a = a < 0n ? -a : a; while (b) [a, b] = [b, a % b]; return a; };
const fr = (n, d = 1n) => {
  if (d < 0n) { n = -n; d = -d; }
  const g = gcd(n, d) || 1n;
  return { n: n / g, d: d / g };
};
const add = (a, b) => fr(a.n * b.d + b.n * a.d, a.d * b.d);
const sub = (a, b) => fr(a.n * b.d - b.n * a.d, a.d * b.d);
const mul = (a, b) => fr(a.n * b.n, a.d * b.d);
const div = (a, b) => fr(a.n * b.d, a.d * b.n);
const ZERO = fr(0n);
const ONE = fr(1n);
const lt = (a, b) => a.n * b.d < b.n * a.d;
const sign = (a) => (a.n > 0n ? 1 : a.n < 0n ? -1 : 0);

// Decimal number/string -> exact fraction. Returns null when not a plain finite decimal.
// Blank (undefined, null, '') -> `blank` (null by default).
function parseDec(v, blank = null) {
  if (v === undefined || v === null || (typeof v === 'string' && v.trim() === '')) return blank;
  if (typeof v === 'number' && !Number.isFinite(v)) return null;
  if (typeof v !== 'number' && typeof v !== 'string') return null;
  const m = /^([+-]?)(\d*)(?:\.(\d*))?(?:[eE]([+-]?\d+))?$/.exec(String(v).trim());
  if (!m || (m[2] === '' && !m[3])) return null;
  const frac = m[3] || '';
  let n = BigInt(m[2] + frac || '0');
  let e = (m[4] ? parseInt(m[4], 10) : 0) - frac.length;
  if (m[1] === '-') n = -n;
  return e >= 0 ? fr(n * 10n ** BigInt(e)) : fr(n, 10n ** BigInt(-e));
}

// round half up (ties away from zero) to `dp` decimals -> BigInt scaled by 10^dp
function roundScaled(a, dp) {
  const scale = 10n ** BigInt(dp);
  const num = (a.n < 0n ? -a.n : a.n) * scale;
  let q = num / a.d;
  if ((num % a.d) * 2n >= a.d) q += 1n;
  return a.n < 0n ? -q : q;
}
function fmt(a, dp = 4) {
  const q = roundScaled(a, dp);
  const neg = q < 0n;
  const s = (neg ? -q : q).toString().padStart(dp + 1, '0');
  const out = dp ? s.slice(0, -dp) + '.' + s.slice(-dp) : s;
  return neg ? '-' + out : out;
}
// IDR: step 0 (default) = no rounding, shown to 4 decimals. step > 0: nearest `step`, half up, integer string.
const DEF_STEP = fr(0n);
const idr = (a, step = DEF_STEP) => (step.n === 0n ? fmt(a) : (roundScaled(div(a, step), 0) * step.n).toString());
const roundIdr = (raw, step) => idr(parseDec(raw), step === undefined ? DEF_STEP : parseDec(step));

const DEF_SPLIT = { A: fr(60n, 100n), B: fr(30n, 100n), C: fr(10n, 100n) };
const DEF_FX_BUFFER = fr(2n, 100n);
const splitOf = (net, sp = DEF_SPLIT) => ({ A: mul(net, sp.A), B: mul(net, sp.B), C: mul(net, sp.C) });

// Exact sum of three decimal parts, for the UI split check. Parts are decimals (0.6).
// Returns { text, ok }: text = sum in percent (exact), ok = sums to exactly 1. null if a part is not a plain decimal.
function splitSum(a, b, c) {
  const p = [a, b, c].map((v) => parseDec(v));
  if (p.some((v) => v === null)) return null;
  const t = mul(p.reduce(add), fr(100n));
  let dp = 0;
  while ((10n ** BigInt(dp)) % t.d !== 0n) dp++;
  return { text: fmt(t, dp), ok: t.n === 100n && t.d === 1n };
}
const fmtSplit = (sp) => ({ A: fmt(sp.A), B: fmt(sp.B), C: fmt(sp.C) });
const err = (error) => ({ ok: false, error });

// Reads a field. required: blank is an error. Otherwise blank -> 0. Negative rejected.
function field(src, key, { required = false } = {}) {
  const v = parseDec(src[key], required ? null : ZERO);
  if (v === null) return { error: `${key} ${required && (src[key] === undefined || src[key] === null || String(src[key]).trim() === '') ? 'required' : 'invalid'}` };
  if (sign(v) < 0) return { error: `${key} must be >= 0` };
  return { v };
}

const isBlank = (v) => v === undefined || v === null || (typeof v === 'string' && v.trim() === '');

// Optional globals: fxBuffer (default 0.02), idrStep (default 0 = no rounding), split {A,B,C} (default 0.6/0.3/0.1).
function parseExtras(g) {
  let fxBuffer = DEF_FX_BUFFER, idrStep = DEF_STEP, split = DEF_SPLIT;
  if (!isBlank(g.fxBuffer)) {
    const r = field(g, 'fxBuffer');
    if (r.error) return r;
    fxBuffer = r.v;
  }
  if (!isBlank(g.idrStep)) {
    const v = parseDec(g.idrStep);
    if (!v || v.d !== 1n || sign(v) < 0) return { error: 'idrStep must be an integer >= 0' };
    idrStep = v;
  }
  if (g.split !== undefined && g.split !== null) {
    split = {};
    for (const k of ['A', 'B', 'C']) {
      const r = field(g.split, k, { required: true });
      if (r.error) return { error: 'split ' + r.error };
      split[k] = r.v;
    }
    const sum = add(add(split.A, split.B), split.C);
    if (sum.n !== 1n || sum.d !== 1n) return { error: 'split must sum to 1' };
  }
  return { fxBuffer, idrStep, split };
}

// Parse + validate unit inputs. g = global { f, s }. Returns { ok, v } or { ok:false, error }.
function parseUnit(i, g) {
  const v = {};
  for (const [src, key, req] of [[i, 'c', true], [i, 'm', true], [g, 'f', true], [i, 'F'], [i, 'Sc'], [g, 's']]) {
    const r = field(src, key, { required: !!req });
    if (r.error) return err(r.error);
    v[key] = r.v;
  }
  // s default is 5% when blank (global default), not 0
  if (g.s === undefined || g.s === null || (typeof g.s === 'string' && g.s.trim() === '')) v.s = fr(5n, 100n);
  if (!lt(add(v.f, v.m), ONE)) return err('margin too high');
  const ex = parseExtras(g);
  if (ex.error) return err(ex.error);
  return { ok: true, v: { ...v, ...ex } };
}

function unitExact({ c, m, F, Sc, f, s, split }) {
  const P = div(add(c, F), sub(sub(ONE, f), m));
  const S = mul(Sc, add(ONE, s));
  const R = add(P, S);
  const paypal = add(mul(f, R), F);
  const profit = sub(sub(sub(R, paypal), c), Sc);
  return { P, S, R, paypal, profit, split: splitOf(profit, split) };
}

function unitOut(x, rates = {}, { fxBuffer, idrStep }) {
  const out = {
    ok: true,
    P: fmt(x.P), S: fmt(x.S), R: fmt(x.R), paypal: fmt(x.paypal), profit: fmt(x.profit),
    split: fmtSplit(x.split),
    cny: null, idr: null,
    exact: x, // BigInt fractions, for yearly sums / tests
  };
  const r = parseDec(rates.r), ix = parseDec(rates.x);
  if (r && sign(r) > 0) out.cny = fmt(mul(x.P, r));
  if (ix && sign(ix) > 0) out.idr = idr(mul(mul(x.P, ix), add(ONE, fxBuffer)), idrStep);
  return out;
}

// Per-unit price. input: { c, m, F?, Sc? }, globals: { f, s? (default 0.05), fxBuffer? (0.02), idrStep? (0 = no rounding), split? {A,B,C} (0.6/0.3/0.1, must sum to 1) }, rates: { r?, x? }
// Fractions as decimals (0.35 = 35%). Returns { ok:true, P, S, R, paypal, profit, split{A,B,C}, cny, idr, exact } or { ok:false, error }.
function calcUnit(input = {}, globals = {}, rates = {}) {
  const p = parseUnit(input, globals);
  if (!p.ok) return p;
  return unitOut(unitExact(p.v), rates, p.v);
}

// Same inputs for each margin in `margins` (array of decimals). Returns array of calcUnit results.
function sweepUnit(input, globals, margins, rates) {
  return margins.map((m) => ({ m, ...calcUnit({ ...input, m }, globals, rates) }));
}

// designs: [{ c, m, F?, Sc?, u?, K? }], globals: { f, s?, shared? }
function calcYearly(designs = [], globals = {}) {
  const sh = field(globals, 'shared');
  if (sh.error) return err(sh.error);
  const ex = parseExtras(globals);
  if (ex.error) return err(ex.error);
  let profitSum = ZERO, ksum = ZERO, rev = ZERO;
  const rows = [];
  for (let idx = 0; idx < designs.length; idx++) {
    const d = designs[idx];
    const p = parseUnit(d, globals);
    if (!p.ok) return err(`design ${idx + 1}: ${p.error}`);
    const K = field(d, 'K');
    if (K.error) return err(`design ${idx + 1}: ${K.error}`);
    const uRaw = d.u === undefined || d.u === null || String(d.u).trim() === '' ? ZERO : parseDec(d.u);
    if (!uRaw || uRaw.d !== 1n || sign(uRaw) < 0) return err(`design ${idx + 1}: u must be an integer >= 0`);
    const x = unitExact(p.v);
    const dp = mul(x.profit, uRaw);
    profitSum = add(profitSum, dp);
    ksum = add(ksum, K.v);
    rev = add(rev, mul(x.P, uRaw));
    rows.push({ P: fmt(x.P), profit: fmt(x.profit), designProfit: fmt(dp), K: fmt(K.v), afterK: fmt(sub(dp, K.v)) });
  }
  const net = sub(sub(profitSum, ksum), sh.v);
  const sp = splitOf(net, ex.split);
  return {
    ok: true,
    designs: rows,
    profitTotal: fmt(profitSum), // chart A: yearly profit vs expenses (K total + shared)
    expensesTotal: fmt(add(ksum, sh.v)),
    net: fmt(net),
    split: fmtSplit(sp),
    marginAfterShared: sign(rev) === 0 ? 'n/a' : fmt(mul(div(net, rev), fr(100n))) + '%',
    exact: { net, split: sp, revenue: rev },
  };
}

// Yearly result for each margin in `margins` applied to every design (charts C, D).
function sweepYearly(designs, globals, margins) {
  return margins.map((m) => ({ m, ...calcYearly(designs.map((d) => ({ ...d, m })), globals) }));
}

return { parseDec, roundIdr, splitSum, calcUnit, sweepUnit, calcYearly, sweepYearly };
})();
const __m_cnyRate = (() => {
// USD->CNY reference rate. Source: Frankfurter (ECB-based), free, no key, CORS open.
const SOURCE_URL = 'https://api.frankfurter.dev/v2/rate/USD/CNY';
const SOURCE_PAGE = 'https://frankfurter.dev';

// Never throws. Returns { rate, date, source, manual }.
// manual (number > 0) always wins and skips the network.
// Fetch failure / bad data => { rate: null, ... } so UI falls back to manual entry.
async function getCnyRate({ manual, fetchFn = globalThis.fetch, timeoutMs = 5000 } = {}) {
  if (typeof manual === 'number' && manual > 0) {
    return { rate: manual, date: null, source: 'manual', manual: true };
  }
  // Offline: skip the request so nothing fails in the network log; UI falls back to manual.
  if (globalThis.navigator?.onLine === false) return { rate: null, date: null, source: null, manual: false };
  try {
    const res = await fetchFn(SOURCE_URL, { signal: AbortSignal.timeout(timeoutMs) });
    if (!res.ok) throw new Error('HTTP ' + res.status);
    const d = await res.json();
    if (typeof d.rate !== 'number' || !(d.rate > 0) || d.quote !== 'CNY') throw new Error('bad data');
    return { rate: d.rate, date: d.date, source: SOURCE_PAGE, manual: false };
  } catch {
    return { rate: null, date: null, source: null, manual: false };
  }
}

return { SOURCE_URL, SOURCE_PAGE, getCnyRate };
})();
const __m_charts = (() => {
// Four charts as plain inline SVG (no library, works offline). No money math: every value is an engine string
// (plain decimal text); Number() is used only to place shapes, labels print the engine string via fmt.
const NS = 'http://www.w3.org/2000/svg';
const sv = (tag, attrs = {}, text) => {
  const e = document.createElementNS(NS, tag);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  if (text !== undefined) e.textContent = text;
  return e;
};
const h = (tag, attrs = {}, ...kids) => {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  for (const k of kids) e.append(k);
  return e;
};

const W = 560, H = 300, L = 74, R = 12, T = 18, B = 52;
const PAL = ['#2563eb', '#d97706', '#059669'];

function niceScale(vals) {
  let lo = Math.min(0, ...vals), hi = Math.max(0, ...vals);
  if (lo === hi) hi = 1;
  const raw = (hi - lo) / 5, p = 10 ** Math.floor(Math.log10(raw));
  const step = [1, 2, 5, 10].map((m) => m * p).find((s) => s >= raw);
  const first = Math.floor(lo / step), last = Math.ceil(hi / step), ticks = [];
  for (let i = first; i <= last; i++) ticks.push(Number((i * step).toPrecision(12)));
  return { min: ticks[0], max: ticks[ticks.length - 1], ticks };
}

function frame(vals, tickFmt) {
  const sc = niceScale(vals);
  const y = (v) => T + (H - T - B) * (1 - (v - sc.min) / (sc.max - sc.min));
  const s = sv('svg', { viewBox: `0 0 ${W} ${H}`, class: 'chartsvg', role: 'img' });
  for (const t of sc.ticks) {
    s.append(sv('line', { x1: L, x2: W - R, y1: y(t), y2: y(t), stroke: t === 0 ? '#555' : '#e3e3e8', 'stroke-width': t === 0 ? 1.5 : 1 }));
    s.append(sv('text', { x: L - 6, y: y(t) + 4, 'text-anchor': 'end', 'font-size': 11, fill: '#555' }, tickFmt(t)));
  }
  return { s, y };
}

const trunc = (t) => (t.length > 14 ? t.slice(0, 13) + '…' : t);
const tick = (n) => n.toLocaleString('en-US', { maximumFractionDigits: 4 });

// groups: [{ label, vals: [engine string per series] }], series: [{ name, color }]
function barChart(groups, series, fmt) {
  const all = groups.flatMap((g) => g.vals.map(Number));
  const { s, y } = frame(all, tick);
  const gw = (W - L - R) / groups.length, bw = Math.min(46, (gw * 0.8) / series.length);
  groups.forEach((g, gi) => {
    const x0 = L + gi * gw + (gw - bw * series.length) / 2;
    g.vals.forEach((v, si) => {
      const n = Number(v), x = x0 + si * bw, top = y(Math.max(n, 0)), bot = y(Math.min(n, 0));
      const bar = sv('rect', { x: x + 2, y: top, width: bw - 4, height: Math.max(bot - top, 1), fill: series[si].color });
      bar.append(sv('title', {}, `${g.label} · ${series[si].name}: ${fmt(v)}`));
      s.append(bar, sv('text', { x: x + bw / 2, y: n >= 0 ? top - 4 : bot + 12, 'text-anchor': 'middle', 'font-size': 10.5, fill: '#222' }, fmt(v)));
    });
    const lab = sv('text', { x: L + gi * gw + gw / 2, y: H - B + 18, 'text-anchor': 'middle', 'font-size': 12, fill: '#222' }, trunc(g.label));
    lab.append(sv('title', {}, g.label));
    s.append(lab);
  });
  return s;
}

// xs: [label], series: [{ name, color, pts: [engine string | null] }]
function lineChart(xs, series, fmt, xTitle) {
  const all = series.flatMap((r) => r.pts.filter((v) => v !== null).map(Number));
  const { s, y } = frame(all, tick);
  const x = (i) => L + 14 + (W - L - R - 28) * (i / (xs.length - 1));
  xs.forEach((t, i) => s.append(sv('text', { x: x(i), y: H - B + 18, 'text-anchor': 'middle', 'font-size': 11, fill: '#222' }, t)));
  s.append(sv('text', { x: (L + W - R) / 2, y: H - 8, 'text-anchor': 'middle', 'font-size': 12, fill: '#444' }, xTitle));
  series.forEach((r) => {
    let seg = [];
    const flush = () => { if (seg.length > 1) s.append(sv('polyline', { points: seg.join(' '), fill: 'none', stroke: r.color, 'stroke-width': 2 })); seg = []; };
    const last = r.pts.reduce((a, v, i) => (v !== null ? i : a), -1);
    r.pts.forEach((v, i) => {
      if (v === null) { flush(); return; }
      seg.push(`${x(i)},${y(Number(v))}`);
    });
    flush();
    r.pts.forEach((v, i) => {
      if (v === null) return;
      const c = sv('circle', { cx: x(i), cy: y(Number(v)), r: 3.5, fill: r.color });
      c.append(sv('title', {}, `${r.name} @ ${xs[i]}: ${fmt(v)}`));
      s.append(c);
      if (i === last) {
        s.append(sv('text', { x: x(i), y: y(Number(v)) - 8, 'text-anchor': 'end', 'font-size': 11, fill: r.color }, fmt(v)));
      }
    });
  });
  return s;
}

const legend = (series) => h('div', { class: 'legend' }, ...series.map((r) => h('span', {}, h('i', { style: `background:${r.color}` }), r.name)));
function card(en, zh, series, svgEl) {
  const t = h('h2', {}, en + ' ');
  t.append(h('small', {}, zh));
  return h('div', { class: 'card chart' }, t, legend(series), h('div', { class: 'scroll' }, svgEl));
}
const hint = (en, zh) => h('div', { class: 'card chart' }, h('p', { class: 'hint' }, `${en} ${zh}`));

// data: { names: [string], yearly: calcYearly result | null, margins: ['20%',...], price: [[str|null]], afterK: [[str|null]] }
function renderCharts(box, data, fmt) {
  box.replaceChildren();
  const { names, yearly, margins, price, afterK } = data;
  if (!names.length) { box.append(hint('Charts need at least one design.', '图表需要至少一个设计。')); return; }

  if (yearly) {
    const sA = [{ name: 'Profit / year 年度利润', color: '#059669' }, { name: 'Expenses: collab K (Yearly: K + shared) 开支:合作预算(全年:预算+共同开支)', color: '#dc2626' }];
    const groups = names.map((n, i) => ({ label: n, vals: [yearly.designs[i].designProfit, yearly.designs[i].K] }));
    groups.push({ label: 'Yearly 全年', vals: [yearly.profitTotal, yearly.expensesTotal] });
    box.append(card('A. Profit vs expenses', 'A. 利润与开支', sA, barChart(groups, sA, fmt)));
    const sB = [{ name: 'Net profit / year after collab & shared 扣除合作及共同开支后年度净利', color: '#2563eb' }];
    box.append(card('B. Yearly net profit split A / B / C', 'B. 年度净利分成 A / B / C', sB,
      barChart([{ label: 'A', vals: [yearly.split.A] }, { label: 'B', vals: [yearly.split.B] }, { label: 'C', vals: [yearly.split.C] }], sB, fmt)));
  } else {
    box.append(hint('Charts A and B need valid inputs.', '图表A和B需要有效输入。'));
  }
  const series = (rows) => names.map((n, i) => ({ name: n, color: PAL[i % PAL.length], pts: rows[i] }));
  const xt = 'Margin 利润率';
  const line = (en, zh, rows) => box.append(rows.some((r) => r.some((v) => v !== null))
    ? card(en, zh, series(rows), lineChart(margins, series(rows), fmt, xt))
    : hint(en + ': no valid values, check inputs.', zh + ':无有效数值,请检查输入。'));
  line('C. Price (USD) vs margin', 'C. 美元售价与利润率', price);
  line('D. Yearly net profit (after collab K) vs margin', 'D. 年度净利(扣合作预算后)与利润率', afterK);
}

return { renderCharts };
})();
const __m_defaults = (() => {
// Starting values of the three design cards. All three ship blank: no sample numbers.
const DESIGN_DEFAULTS = [
  { name: 'Design 1', c: '', m: '35', F: '0', Sc: '0', u: '0', K: '0' },
  { name: 'Design 2', c: '', m: '35', F: '0', Sc: '0', u: '0', K: '0' },
  { name: 'Design 3', c: '', m: '35', F: '0', Sc: '0', u: '0', K: '0' },
];

return { DESIGN_DEFAULTS };
})();
const __m_storage = (() => {
// Scenario save/load + export/import. No DOM here, so it runs in node tests.
// A scenario = the text of every input field, exactly as typed ({ fieldId: "text" }).
// Same text in => same engine numbers out (the engine is deterministic), so a reload is identical.
const APP = 'pricing-calculator';
const VERSION = 1;
const KEY = 'pricingCalc.scenarios.v1';

function makeSnapshot(name, fields) {
  return { app: APP, version: VERSION, name, saved: new Date().toISOString(), fields: { ...fields } };
}

// Returns { ok: true, snap } or { ok: false, error }. ids = every field id the page has.
function parseSnapshot(text, ids) {
  let o;
  try { o = JSON.parse(text); } catch { return { ok: false, error: 'Not a valid file 文件无效 (not JSON)' }; }
  if (!o || o.app !== APP || typeof o.fields !== 'object' || o.fields === null) {
    return { ok: false, error: 'Not a pricing calculator file 不是本计算器的文件' };
  }
  if (o.version !== VERSION) return { ok: false, error: `Unsupported file version 不支持的版本: ${o.version}` };
  const missing = ids.filter((id) => typeof o.fields[id] !== 'string');
  if (missing.length) return { ok: false, error: `File is missing fields 文件缺少字段: ${missing.join(', ')}` };
  const fields = {};
  for (const id of ids) fields[id] = o.fields[id];
  return { ok: true, snap: { ...o, name: typeof o.name === 'string' ? o.name : '', fields } };
}

// store = localStorage-like (getItem/setItem). Throws if the browser blocks storage.
function readAll(store) {
  const raw = store.getItem(KEY);
  if (!raw) return {};
  try { const o = JSON.parse(raw); return o && typeof o === 'object' ? o : {}; } catch { return {}; }
}
const listScenarios = (store) => Object.keys(readAll(store)).sort();
const getScenario = (store, name) => readAll(store)[name] ?? null;
function saveScenario(store, name, snap) {
  const all = readAll(store);
  all[name] = snap;
  store.setItem(KEY, JSON.stringify(all));
}
function deleteScenario(store, name) {
  const all = readAll(store);
  delete all[name];
  store.setItem(KEY, JSON.stringify(all));
}

return { APP, VERSION, makeSnapshot, parseSnapshot, listScenarios, getScenario, saveScenario, deleteScenario };
})();
const __m_ui = (() => {
// Input UI. Wires fields to calcEngine.js; no math here except "5" -> "5e-2" percent text conversion.
const { calcUnit, calcYearly, parseDec, splitSum, sweepUnit, sweepYearly } = __m_calcEngine;
const { getCnyRate, SOURCE_PAGE } = __m_cnyRate;
const { renderCharts } = __m_charts;
const { DESIGN_DEFAULTS } = __m_defaults;
const { makeSnapshot, parseSnapshot, listScenarios, getScenario, saveScenario, deleteScenario } = __m_storage;

const $ = (id) => document.getElementById(id);
const el = (tag, attrs = {}, ...kids) => {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === 'class') e.className = v; else e.setAttribute(k, v);
  }
  for (const k of kids) e.append(k);
  return e;
};
const lab = (en, zh) => [en, el('small', {}, zh)];

// type: 'pct' (typed as 5 for 5%), 'num', 'int', 'text', 'date'
const GLOBAL_FIELDS = [
  { id: 'paypalPct', en: 'PayPal fee %', zh: 'PayPal手续费 %', type: 'pct', value: '5' },
  { id: 'surcharge', en: 'Shipping surcharge %', zh: '运费附加费 %', type: 'pct', value: '5' },
  { id: 'alipayPct', en: 'Alipay fee % (placeholder)', zh: '支付宝手续费 %(占位)', type: 'pct', value: '0',
    note: ['not measured, ask C', '未实测,请询问C'] },
  { id: 'cnyManual', en: 'USD→CNY rate (manual, overrides live)', zh: '美元→人民币汇率(手动,优先于实时)', type: 'num', value: '' },
  { id: 'idrRate', en: 'USD→IDR rate (typed)', zh: '美元→印尼盾汇率(手动输入)', type: 'num', value: '' },
  { id: 'idrDate', en: 'IDR rate date', zh: '印尼盾汇率日期', type: 'date', value: '' },
  { id: 'fxBuffer', en: 'FX buffer %', zh: '汇率缓冲 %', type: 'pct', value: '2' },
  { id: 'idrStep', en: 'IDR rounding step (0 = no rounding)', zh: '印尼盾进位单位(0=不进位)', type: 'int', value: '0' },
  { id: 'shared', en: 'Other shared expenses per year (USD)', zh: '每年其他共同开支(美元)', type: 'num', value: '0' },
  { id: 'splitA', en: 'Split A %', zh: '分成 A %', type: 'pct', value: '60' },
  { id: 'splitB', en: 'Split B %', zh: '分成 B %', type: 'pct', value: '30' },
  { id: 'splitC', en: 'Split C %', zh: '分成 C %', type: 'pct', value: '10' },
];

const DESIGN_FIELDS = [
  { k: 'name', en: 'Name', zh: '名称', type: 'text' },
  { k: 'c', en: 'Unit cost c (USD, excl. shipping)', zh: '单位成本(美元,不含运费)', type: 'num' },
  { k: 'm', en: 'Target margin %', zh: '目标利润率 %', type: 'pct' },
  { k: 'F', en: 'PayPal fixed fee F (USD)', zh: 'PayPal固定费用(美元)', type: 'num' },
  { k: 'Sc', en: 'Real 4PX shipping cost Sc (USD)', zh: '4PX实际运费(美元)', type: 'num' },
  { k: 'u', en: 'Units per year', zh: '每年数量', type: 'int' },
  { k: 'K', en: 'Collab budget K (USD)', zh: '合作预算(美元)', type: 'num' },
];

const FIELD_NAMES = {
  c: 'Unit cost 单位成本', m: 'Margin 利润率', f: 'PayPal % PayPal手续费', F: 'PayPal fixed fee 固定费用',
  fxBuffer: 'FX buffer 汇率缓冲', idrStep: 'IDR rounding step 印尼盾进位单位', split: 'Split 分成',
  Sc: 'Shipping cost 运费', s: 'Surcharge 附加费', u: 'Units 数量', K: 'Collab K 合作预算', shared: 'Shared expenses 共同开支',
};
const NUM_RE = /^[+-]?(\d+\.?\d*|\.\d+)$/;
const blank = (v) => v === undefined || v === null || String(v).trim() === '';
const okFormat = (type, v) => blank(v) || type === 'text' || type === 'date' || NUM_RE.test(v.trim());
// percent text -> engine decimal text ("5" -> "5e-2"); bad text passes through so the engine rejects it
const pct = (v) => (blank(v) ? '' : NUM_RE.test(v.trim()) ? v.trim() + 'e-2' : v);
const niceErr = (msg) => msg.replace(/^(design \d+: )?(\w+)/, (m, p, k) => (p || '') + (FIELD_NAMES[k] || k))
  .replace('Split 分成 must sum to 1', 'Split A + B + C must be 100% 分成合计须为100%')
  .replace(' must be an integer >= 0', ' must be a whole number, 0 or more 必须是不小于0的整数')
  .replace('margin too high', 'Margin + PayPal % must be below 100% 利润率+PayPal手续费须低于100%')
  .replace(/ required$/, ' is required 必填').replace(/ invalid$/, ' is not a number 不是有效数字');
const commas = (s) => s.replace(/\B(?=(\d{3})+(?!\d))/g, ',');
const money = (s) => { const neg = s.startsWith('-'); const [i, d] = (neg ? s.slice(1) : s).split('.'); return (neg ? '-' : '') + commas(i) + (d === undefined ? '' : '.' + d); };

let live = { rate: null, date: null, source: null, done: false };

function buildInput(f, idAttr) {
  const i = el('input', { id: idAttr, type: 'text', inputmode: f.type === 'text' || f.type === 'date' ? 'text' : 'decimal', autocomplete: 'off' });
  if (f.type === 'date') i.type = 'date';
  i.dataset.type = f.type;
  i.value = f.value ?? '';
  return i;
}

function build() {
  const gf = $('globalFields');
  for (const f of GLOBAL_FIELDS) {
    const l = el('label', {}, ...lab(f.en, f.zh), buildInput(f, f.id));
    if (f.note) l.append(el('span', { class: 'err warn' }, f.note[0], el('small', {}, f.note[1])));
    gf.append(l);
  }
  DESIGN_DEFAULTS.forEach((d, n) => {
    const card = el('div', { class: 'card', id: 'design' + n });
    card.append(el('h2', {}, `Design ${n + 1} `, el('small', {}, `设计 ${n + 1}`)));
    const g = el('div', { class: 'grid' });
    for (const f of DESIGN_FIELDS) g.append(el('label', {}, ...lab(f.en, f.zh), buildInput({ ...f, value: d[f.k] }, `d${n}_${f.k}`)));
    card.append(g, el('div', { class: 'result', id: 'res' + n }));
    $('designs').append(card);
  });
  document.addEventListener('input', render);
}

const val = (id) => $(id).value;

function checkFormats() {
  let bad = false;
  document.querySelectorAll('input').forEach((i) => {
    const ok = okFormat(i.dataset.type, i.value);
    i.classList.toggle('bad', !ok);
    if (!ok) bad = true;
  });
  return bad;
}

function row(a, b, cls) { return el('tr', cls ? { class: cls } : {}, el('td', {}, a), el('td', {}, b)); }
const MARGINS = [20, 25, 30, 35, 40, 45, 50];
const SWEEP_HEAD = ['Margin 利润率', 'Price USD 美元售价', 'CNY 人民币', 'IDR 印尼盾', 'PayPal fee 手续费', 'Profit / unit 单件利润', 'Profit / year 年度利润', 'After collab K 扣合作预算'];

// Margin table 20-50% (step 5) for one design; all numbers come from sweepUnit / sweepYearly.
function sweepCard(d, n, g, rt) {
  const ms = MARGINS.map((p) => pct(String(p)));
  const us = sweepUnit(d, g, ms, rt);
  const ys = sweepYearly([d], g, ms);
  const t = el('table', { class: 'sweep' });
  t.append(el('thead', {}, el('tr', {}, ...SWEEP_HEAD.map((h) => el('th', {}, h)))));
  const body = el('tbody');
  us.forEach((u, i) => {
    const pctTxt = MARGINS[i] + '%';
    if (!u.ok) { body.append(el('tr', {}, el('td', {}, pctTxt), el('td', { colspan: '7', class: 'err' }, niceErr(u.error)))); return; }
    const y = ys[i].ok ? ys[i].designs[0] : null;
    body.append(el('tr', {}, el('td', {}, pctTxt), el('td', {}, money(u.P)), el('td', {}, u.cny ? money(u.cny) : '—'),
      el('td', {}, u.idr ? money(u.idr) : '—'), el('td', {}, money(u.paypal)), el('td', {}, money(u.profit)),
      el('td', {}, y ? money(y.designProfit) : '—'), el('td', {}, y ? money(y.afterK) : '—')));
  });
  t.append(body);
  const name = blank(d.name) ? `Design ${n + 1}` : d.name;
  return el('div', { class: 'card' }, el('h2', {}, `Margin table 利润率表: ${name}`), el('div', { class: 'scroll' }, t));
}
const errBox = (msg) => el('p', { class: 'err' }, msg);

// Same engine calls as the tables (calcYearly, sweepUnit, sweepYearly), so chart values equal table values.
function drawCharts(used, g, rt) {
  const ds = used.map(({ d }) => d);
  const ms = MARGINS.map((p) => pct(String(p)));
  const yr = ds.length ? calcYearly(ds, g) : null;
  const price = [], afterK = [];
  ds.forEach((d) => {
    const us = sweepUnit(d, g, ms, rt), ys = sweepYearly([d], g, ms);
    price.push(us.map((u) => (u.ok ? u.P : null)));
    afterK.push(ys.map((y) => (y.ok ? y.designs[0].afterK : null)));
  });
  renderCharts($('charts'), {
    names: used.map(({ d, n }) => (blank(d.name) ? `Design ${n + 1}` : d.name)),
    yearly: yr && yr.ok ? yr : null, margins: MARGINS.map((p) => p + '%'), price, afterK,
  }, money);
}

function rates() {
  const m = val('cnyManual').trim();
  let r = null, src = '';
  if (!blank(m)) {
    const p = parseDec(m);
    if (p && p.n > 0n) { r = m; src = 'manual 手动'; }
  } else if (live.rate) { r = String(live.rate); src = 'live 实时'; }
  const x = val('idrRate').trim();
  const xp = blank(x) ? null : parseDec(x);
  return { r, x: xp && xp.n > 0n ? x : null, src };
}

function renderCnyRef() {
  const box = $('cnyRef');
  box.replaceChildren();
  const { r, src } = rates();
  if (!live.done) box.append('Fetching live USD→CNY reference… 正在获取实时汇率…');
  else if (live.rate) {
    box.append(`Live reference 实时参考: ${live.rate} (ECB ${live.date}) · `, el('a', { href: SOURCE_PAGE, target: '_blank', rel: 'noopener' }, 'frankfurter.dev'));
  } else box.append(el('span', { class: 'warn' }, 'Live rate unavailable; type a rate manually. 无法获取实时汇率,请手动输入。'));
  const m = val('cnyManual').trim();
  if (!blank(m) && !r) box.append(el('div', { class: 'err' }, 'Manual CNY rate must be a number above 0 手动人民币汇率必须是大于0的数字'));
  box.append(el('div', {}, r ? `Using CNY rate 使用汇率: ${r} (${src})` : 'No CNY rate: CNY price not shown 无人民币汇率,不显示人民币价格'));
}

function render() {
  const formatBad = checkFormats();
  renderCnyRef();
  const rt = rates();
  const idrTxt = val('idrRate').trim();
  const sp = { A: pct(val('splitA')), B: pct(val('splitB')), C: pct(val('splitC')) };
  const ss = splitSum(sp.A, sp.B, sp.C);
  $('splitCheck').replaceChildren(ss
    ? el('span', { class: ss.ok ? 'ok' : 'err' }, `Split sum 分成合计: ${ss.text}%` + (ss.ok ? ' ✓' : ' — must be 100% 须为100%'))
    : el('span', { class: 'err' }, 'Split sum 分成合计: — (enter numbers 请输入数字)'));
  const g = { f: pct(val('paypalPct')), s: pct(val('surcharge')), shared: val('shared'), fxBuffer: pct(val('fxBuffer')), idrStep: val('idrStep'), split: sp };
  const designs = DESIGN_DEFAULTS.map((_, n) => {
    const o = {};
    for (const f of DESIGN_FIELDS) o[f.k] = val(`d${n}_${f.k}`);
    o.m = pct(o.m);
    return o;
  });

  designs.forEach((d, n) => {
    const box = $('res' + n);
    box.replaceChildren();
    if (blank(d.c)) { box.append(el('p', { class: 'hint' }, 'Enter unit cost to see a price. 输入单位成本以查看价格。')); return; }
    try {
      const r = calcUnit(d, g, { r: rt.r, x: rt.x });
      if (!r.ok) { box.append(errBox(niceErr(r.error))); return; }
      const yr = calcYearly([d], g);
      const yd = yr.ok ? yr.designs[0] : null;
      const t = el('table');
      t.append(row('Keyboard price P 键盘售价', 'USD ' + money(r.P)),
        row('CNY price 人民币价格', r.cny ? '¥ ' + money(r.cny) : '—'),
        row('IDR price 印尼盾价格', r.idr ? 'Rp ' + money(r.idr) : '—'),
        row('Shipping charged S 收取运费', 'USD ' + money(r.S)),
        row('Customer pays R 客户支付', 'USD ' + money(r.R)),
        row('PayPal fee (% + fixed) PayPal手续费(比例+固定)', 'USD ' + money(r.paypal)),
        row('Profit / unit 单件利润', 'USD ' + money(r.profit)),
        row('A / B / C per unit 单件分成', `${money(r.split.A)} / ${money(r.split.B)} / ${money(r.split.C)}`),
        row('Total profit / year 年度总利润', yd ? 'USD ' + money(yd.designProfit) : '—'),
        row('After collab budget 扣除合作预算后', yd ? 'USD ' + money(yd.afterK) : '—'));
      box.append(t);
    } catch (e) { box.append(errBox('Unexpected error 意外错误: ' + e.message)); }
  });

  const y = $('yearly');
  y.replaceChildren(el('h2', {}, 'Yearly result ', el('small', {}, '年度结果')));
  const used = designs.map((d, n) => ({ d, n })).filter(({ d }) => !blank(d.c));
  const sw = $('sweeps');
  sw.replaceChildren();
  used.forEach(({ d, n }) => { try { sw.append(sweepCard(d, n, g, { r: rt.r, x: rt.x })); } catch (e) { sw.append(errBox('Unexpected error 意外错误: ' + e.message)); } });
  try { drawCharts(used, g, rt); } catch (e) { $('charts').replaceChildren(errBox('Unexpected error 意外错误: ' + e.message)); }
  if (!used.length) { y.append(el('p', { class: 'hint' }, 'Fill at least one design. 请至少填写一个设计。')); return; }
  try {
    const r = calcYearly(used.map(({ d }) => d), g);
    if (!r.ok) {
      const msg = r.error.replace(/^design (\d+)/, (m, k) => 'design ' + (used[k - 1].n + 1));
      y.append(errBox(niceErr(msg)));
      return;
    }
    const t = el('table');
    used.forEach(({ d, n }, i) => {
      const nm = blank(d.name) ? `Design ${n + 1}` : d.name;
      t.append(row(`${nm}: profit / year, after collab 年度利润 / 扣合作预算后`, `USD ${money(r.designs[i].designProfit)} / ${money(r.designs[i].afterK)}`));
    });
    t.append(row('Net after collab & shared 扣除合作及共同开支后净利', 'USD ' + money(r.net)),
      row('A / B / C', `${money(r.split.A)} / ${money(r.split.B)} / ${money(r.split.C)}`),
      row('Margin after shared 共同开支后利润率', r.marginAfterShared));
    y.append(el('div', { class: 'result' }, t));
  } catch (e) { y.append(errBox('Unexpected error 意外错误: ' + e.message)); }
  if (formatBad) y.append(errBox('Some fields are not numbers (red). 部分字段不是数字(红色)。'));
}

// ---- Scenarios: save/load in the browser (localStorage) + export/import file ----
const fieldIds = () => [...GLOBAL_FIELDS.map((f) => f.id), ...DESIGN_DEFAULTS.flatMap((_, n) => DESIGN_FIELDS.map((f) => `d${n}_${f.k}`))];
const collect = () => Object.fromEntries(fieldIds().map((id) => [id, val(id)]));
const apply = (fields) => { for (const id of fieldIds()) $(id).value = fields[id]; render(); };
const store = () => { try { return window.localStorage; } catch { return null; } };

function buildScenarios() {
  const box = $('scenarios');
  const name = el('input', { type: 'text', autocomplete: 'off', placeholder: 'Scenario name 方案名称' });
  const pick = el('select');
  const status = el('div', { class: 'note' });
  name.dataset.type = 'text';
  const btn = (en, zh, fn) => { const b = el('button', { type: 'button' }, en, el('small', {}, zh)); b.addEventListener('click', fn); return b; };
  const say = (msg, bad) => status.replaceChildren(el('span', { class: bad ? 'err' : 'ok' }, msg));
  const refresh = (sel) => {
    let names = [];
    try { names = listScenarios(store()); } catch { /* storage blocked */ }
    pick.replaceChildren(...names.map((n) => el('option', { value: n }, n)));
    if (sel && names.includes(sel)) pick.value = sel;
  };
  // Freeze the CNY rate in use, so a later load gives the same numbers even offline or when the live rate moves.
  const snapshot = (n) => {
    const f = collect();
    if (blank(f.cnyManual) && live.rate) f.cnyManual = String(live.rate);
    return makeSnapshot(n, f);
  };

  const save = () => {
    const n = name.value.trim();
    if (!n) return say('Type a scenario name first. 请先输入方案名称。', true);
    try {
      if (getScenario(store(), n) && !window.confirm(`Overwrite "${n}"? 覆盖 "${n}"?`)) return;
      saveScenario(store(), n, snapshot(n));
    } catch { return say('Browser storage is blocked here. Use Export file. 浏览器存储被禁用,请用导出文件。', true); }
    refresh(n);
    say(`Saved 已保存: ${n}`);
  };
  const load = () => {
    let snap = null;
    try { snap = pick.value ? getScenario(store(), pick.value) : null; } catch { /* blocked */ }
    if (!snap) return say('Nothing to load. 没有可载入的方案。', true);
    const p = parseSnapshot(JSON.stringify(snap), fieldIds());
    if (!p.ok) return say(p.error, true);
    apply(p.snap.fields);
    name.value = pick.value;
    say(`Loaded 已载入: ${pick.value}`);
  };
  const del = () => {
    if (!pick.value || !window.confirm(`Delete "${pick.value}"? 删除 "${pick.value}"?`)) return;
    try { deleteScenario(store(), pick.value); } catch { return say('Browser storage is blocked here. 浏览器存储被禁用。', true); }
    say(`Deleted 已删除: ${pick.value}`);
    refresh();
  };
  const exportFile = () => {
    const n = name.value.trim() || 'scenario';
    const blob = new Blob([JSON.stringify(snapshot(n), null, 2)], { type: 'application/json' });
    const a = el('a', { href: URL.createObjectURL(blob), download: `pricing-${n.replace(/[^\w.-]+/g, '_')}.json` });
    document.body.append(a);
    a.click();
    a.remove();
    URL.revokeObjectURL(a.href);
    say('File exported 已导出文件');
  };
  const file = el('input', { type: 'file', accept: '.json,application/json' });
  file.dataset.type = 'text';
  file.addEventListener('change', async () => {
    const f = file.files[0];
    if (!f) return;
    const p = parseSnapshot(await f.text(), fieldIds());
    file.value = '';
    if (!p.ok) return say(p.error, true);
    apply(p.snap.fields);
    name.value = p.snap.name;
    say(`Imported 已导入: ${f.name}`);
  });

  box.append(el('h2', {}, 'Scenarios ', el('small', {}, '方案')),
    el('div', { class: 'toolbar' }, name, btn('Save', '保存', save)),
    el('div', { class: 'toolbar' }, pick, btn('Load', '载入', load), btn('Delete', '删除', del)),
    el('div', { class: 'toolbar' }, btn('Export file', '导出文件', exportFile),
      el('label', { class: 'filebtn' }, el('span', {}, 'Import file 导入文件'), file)),
    status);
  refresh();
}

$('pdfBtn').addEventListener('click', () => window.print()); // browser print view; user saves as PDF
build();
buildScenarios();
render();
getCnyRate().then((r) => { live = { ...r, done: true }; render(); });

return {  };
})();
})();
