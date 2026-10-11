(() => {
'use strict';
const __m_calcEngine = (() => {
// Pricing calc engine. Pure functions, no UI, no floats: all math is exact BigInt fractions.
// No rounding in the math. Output strings only cut the exact fraction to 4 decimals for display (half up).
// IDR is not rounded unless the user sets idrStep > 0. Spec: docs/spec-v5.md.

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
    exact: x, // BigInt fractions, for tests
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

// One design (spec v5): calcUnit fields plus total, K, net after collab, split of net, margin after collab.
// input: { c, m, F?, Sc?, u? (integer >= 0, blank = 0), K? (>= 0, blank = 0; total collab budget, subtracted once) }
// Returns calcUnit fields (split = per unit) + { u, K, total, net, netSplit{A,B,C}, marginAfterCollab ('n/a' if P*u = 0), exact }.
function calcDesign(input = {}, globals = {}, rates = {}) {
  const p = parseUnit(input, globals);
  if (!p.ok) return p;
  const K = field(input, 'K');
  if (K.error) return err(K.error);
  const u = parseDec(input.u, ZERO);
  if (!u || u.d !== 1n || sign(u) < 0) return err('u must be an integer >= 0');
  const x = unitExact(p.v);
  const total = mul(x.profit, u);
  const net = sub(total, K.v);
  const netSplit = splitOf(net, p.v.split);
  const rev = mul(x.P, u);
  const margin = sign(rev) === 0 ? null : mul(div(net, rev), fr(100n));
  return {
    ...unitOut(x, rates, p.v),
    u: fmt(u, 0), K: fmt(K.v), total: fmt(total), net: fmt(net),
    netSplit: fmtSplit(netSplit),
    marginAfterCollab: margin ? fmt(margin) + '%' : 'n/a',
    exact: { ...x, total, net, netSplit, margin },
  };
}

const SWEEP_MARGINS = [0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.5];

// calcDesign for each margin (default 20-50%, step 5). Same c, F, Sc, u, K for every row.
function sweepDesign(input, globals, margins = SWEEP_MARGINS, rates) {
  return margins.map((m) => ({ m, ...calcDesign({ ...input, m }, globals, rates) }));
}

return { parseDec, roundIdr, splitSum, calcUnit, sweepUnit, calcDesign, SWEEP_MARGINS, sweepDesign };
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

// W is set per chart to the real container width (px), so SVG text stays at its true size on a phone.
let W = 560;
const H = 280, R = 14, T = 20, B = 56;
let L = 68; // left margin, widened per chart when the y-axis numbers are long
const PAL = ['var(--chart-1)', 'var(--chart-2)', 'var(--chart-3)'];

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
  L = Math.max(60, Math.max(...sc.ticks.map((t) => tickFmt(t).length)) * 7 + 16);
  const y = (v) => T + (H - T - B) * (1 - (v - sc.min) / (sc.max - sc.min));
  const s = sv('svg', { viewBox: `0 0 ${W} ${H}`, class: 'chartsvg', role: 'img' });
  for (const t of sc.ticks) {
    s.append(sv('line', { x1: L, x2: W - R, y1: y(t), y2: y(t), class: t === 0 ? 'c-axis' : 'c-grid' }));
    s.append(sv('text', { x: L - 8, y: y(t) + 4, 'text-anchor': 'end', class: 'c-tick' }, tickFmt(t)));
  }
  return { s, y };
}

const trunc = (t) => (t.length > 14 ? t.slice(0, 13) + '…' : t);
const tick = (n) => n.toLocaleString('en-US', { maximumFractionDigits: 4 });

// groups: [{ label, vals: [engine string per series] }], series: [{ name, color }]
function barChart(groups, series, fmt) {
  const all = groups.flatMap((g) => g.vals.map(Number));
  const { s, y } = frame(all, tick);
  const gw = (W - L - R) / groups.length, bw = Math.min(96, (gw * 0.8) / series.length);
  groups.forEach((g, gi) => {
    const x0 = L + gi * gw + (gw - bw * series.length) / 2;
    g.vals.forEach((v, si) => {
      const n = Number(v), x = x0 + si * bw, top = y(Math.max(n, 0)), bot = y(Math.min(n, 0));
      const bar = sv('rect', { x: x + 2, y: top, width: bw - 4, height: Math.max(bot - top, 1), style: `fill:${series[si].color}` });
      bar.append(sv('title', {}, `${g.label} · ${series[si].name}: ${fmt(v)}`));
      const half = fmt(v).length * 3.6; // keep the value label inside the chart
      s.append(bar, sv('text', { x: Math.min(Math.max(x + bw / 2, half + 2), W - half - 2), y: n >= 0 ? top - 6 : bot + 14, 'text-anchor': 'middle', class: 'c-val' }, fmt(v)));
    });
    const lab = sv('text', { x: L + gi * gw + gw / 2, y: H - B + 20, 'text-anchor': 'middle', class: 'c-label' }, trunc(g.label));
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
  xs.forEach((t, i) => s.append(sv('text', { x: x(i), y: H - B + 20, 'text-anchor': 'middle', class: 'c-label' }, t)));
  s.append(sv('text', { x: (L + W - R) / 2, y: H - 10, 'text-anchor': 'middle', class: 'c-title' }, xTitle));
  series.forEach((r) => {
    let seg = [];
    const flush = () => { if (seg.length > 1) s.append(sv('polyline', { points: seg.join(' '), style: `fill:none;stroke:${r.color}`, 'stroke-width': 2.5 })); seg = []; };
    const last = r.pts.reduce((a, v, i) => (v !== null ? i : a), -1);
    r.pts.forEach((v, i) => {
      if (v === null) { flush(); return; }
      seg.push(`${x(i)},${y(Number(v))}`);
    });
    flush();
    r.pts.forEach((v, i) => {
      if (v === null) return;
      const c = sv('circle', { cx: x(i), cy: y(Number(v)), r: 4, style: `fill:${r.color}` });
      c.append(sv('title', {}, `${r.name} @ ${xs[i]}: ${fmt(v)}`));
      s.append(c);
      if (i === last) {
        s.append(sv('text', { x: x(i), y: y(Number(v)) - 10, 'text-anchor': 'end', class: 'c-val' }, fmt(v)));
      }
    });
  });
  return s;
}

const legend = (series) => h('div', { class: 'legend' }, ...series.map((r) => h('span', {}, h('i', { style: `background:${r.color}` }), r.name)));
function card(box, en, zh, series, draw) {
  const t = h('h2', {}, en + ' ');
  t.append(h('small', {}, zh));
  const wrap = h('div', { class: 'chartwrap' });
  box.append(h('div', { class: 'card chart' }, t, legend(series), wrap));
  W = Math.max(260, Math.floor(wrap.clientWidth)); // measure after insertion
  wrap.append(draw());
}
const hint = (en, zh) => h('div', { class: 'card chart' }, h('p', { class: 'hint' }, `${en} ${zh}`));

// data: { design: calcDesign result | null, margins: ['20%',...], price: [str|null], net: [str|null] }
function renderCharts(box, data, fmt) {
  box.replaceChildren();
  const { design, margins, price, net } = data;
  if (!price.length && !design) { box.append(hint('Charts need a unit cost.', '图表需要先输入单位成本。')); return; }

  if (design) {
    const sA = [{ name: 'Total profit 总利润', color: 'var(--chart-3)' }, { name: 'Expenses: collab K 开支:合作预算K', color: 'var(--chart-4)' }];
    card(box, 'A. Profit vs expenses', 'A. 利润与开支', sA, () => barChart([{ label: 'Design 设计', vals: [design.total, design.K] }], sA, fmt));
    const sB = [{ name: 'Net profit after collab K 扣除合作预算后净利', color: 'var(--chart-1)' }];
    card(box, 'B. Net profit split A / B / C', 'B. 净利分成 A / B / C', sB,
      () => barChart([{ label: 'A', vals: [design.netSplit.A] }, { label: 'B', vals: [design.netSplit.B] }, { label: 'C', vals: [design.netSplit.C] }], sB, fmt));
  } else {
    box.append(hint('Charts A and B need valid inputs.', '图表A和B需要有效输入。'));
  }
  const xt = 'Margin 利润率';
  const line = (en, zh, name, pts) => (pts.some((v) => v !== null)
    ? card(box, en, zh, [{ name, color: PAL[0] }], () => lineChart(margins, [{ name, color: PAL[0], pts }], fmt, xt))
    : box.append(hint(en + ': no valid values, check inputs.', zh + ':无有效数值,请检查输入。')));
  line('C. Price (USD) vs margin', 'C. 美元售价与利润率', 'Price USD 美元售价', price);
  line('D. Net profit (after collab K) vs margin', 'D. 净利(扣合作预算后)与利润率', 'Net after collab K 扣合作预算净利', net);
}

return { renderCharts };
})();
const __m_defaults = (() => {
// Starting values of the design card. Ships blank: no sample numbers.
const DESIGN_DEFAULT = { c: '', m: '35', F: '0', Sc: '0', u: '0', K: '0' };

return { DESIGN_DEFAULT };
})();
const __m_storage = (() => {
// Scenario save/load + export/import. No DOM here, so it runs in node tests.
// A scenario = the text of every input field, exactly as typed ({ fieldId: "text" }).
// Same text in => same engine numbers out (the engine is deterministic), so a reload is identical.
// File shape v2 (single design): { app, v: 2, name, saved, fields }. v1 (multi-design, `version: 1`) is migrated to Design 1.
const APP = 'pricing-calculator';
const VERSION = 2;
const KEY = 'pricingCalc.scenarios.v1'; // same key as v1 builds; each entry is a snapshot and carries its own version

function makeSnapshot(name, fields) {
  return { app: APP, v: VERSION, name, saved: new Date().toISOString(), fields: { ...fields } };
}

const V1_NOTICE = 'Old multi-design file (v1): only Design 1 and the global settings were loaded; Designs 2-3, shared expenses and yearly results were dropped. 旧版多设计文件(v1):仅载入设计1和全局设置,设计2-3、共同开支和年度结果已舍弃。';

// Returns { ok: true, snap, notice? } or { ok: false, error }. ids = every field id the page has.
function parseSnapshot(text, ids) {
  let o;
  try { o = JSON.parse(text); } catch { return { ok: false, error: 'Not a valid file 文件无效 (not JSON)' }; }
  if (!o || o.app !== APP || typeof o.fields !== 'object' || o.fields === null) {
    return { ok: false, error: 'Not a pricing calculator file 不是本计算器的文件' };
  }
  const v1 = o.v === undefined && o.version === 1;
  if (o.v !== VERSION && !v1) return { ok: false, error: `Unsupported file version 不支持的版本: ${o.v ?? o.version}` };
  let src = o.fields;
  if (v1) { // Design 1 fields d0_x become d_x; other designs and "shared" are simply not read
    src = { ...o.fields };
    for (const k of ['c', 'm', 'F', 'Sc', 'u', 'K']) src['d_' + k] = o.fields['d0_' + k];
  }
  const missing = ids.filter((id) => typeof src[id] !== 'string');
  if (missing.length) return { ok: false, error: `File is missing fields 文件缺少字段: ${missing.map((id) => (v1 ? id.replace(/^d_/, 'd0_') : id)).join(', ')}` };
  const fields = {};
  for (const id of ids) fields[id] = src[id];
  const snap = { app: APP, v: VERSION, name: typeof o.name === 'string' ? o.name : '', saved: o.saved, fields };
  return v1 ? { ok: true, snap, notice: V1_NOTICE } : { ok: true, snap };
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
const { calcDesign, parseDec, splitSum, sweepDesign } = __m_calcEngine;
const { getCnyRate, SOURCE_PAGE } = __m_cnyRate;
const { renderCharts } = __m_charts;
const { DESIGN_DEFAULT } = __m_defaults;
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
const lab = (en, zh) => [el('span', { class: 'lbl' }, el('span', { class: 'en' }, en), el('small', {}, zh))];

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
  { id: 'splitA', en: 'Split A %', zh: '分成 A %', type: 'pct', value: '60' },
  { id: 'splitB', en: 'Split B %', zh: '分成 B %', type: 'pct', value: '30' },
  { id: 'splitC', en: 'Split C %', zh: '分成 C %', type: 'pct', value: '10' },
];

const DESIGN_FIELDS = [
  { k: 'c', en: 'Unit cost c (USD, excl. shipping)', zh: '单位成本(美元,不含运费)', type: 'num' },
  { k: 'm', en: 'Target margin %', zh: '目标利润率 %', type: 'pct' },
  { k: 'F', en: 'PayPal fixed fee F (USD)', zh: 'PayPal固定费用(美元)', type: 'num' },
  { k: 'Sc', en: 'Real 4PX shipping cost Sc (USD)', zh: '4PX实际运费(美元)', type: 'num' },
  { k: 'u', en: 'Units for this design / release', zh: '本设计/本次发售数量', type: 'int' },
  { k: 'K', en: 'Collab budget K (USD, total for this design / release)', zh: '合作预算K(美元,本设计/本次发售合计)', type: 'num' },
];

const FIELD_NAMES = {
  c: 'Unit cost 单位成本', m: 'Margin 利润率', f: 'PayPal % PayPal手续费', F: 'PayPal fixed fee 固定费用',
  fxBuffer: 'FX buffer 汇率缓冲', idrStep: 'IDR rounding step 印尼盾进位单位', split: 'Split 分成',
  Sc: 'Shipping cost 运费', s: 'Surcharge 附加费', u: 'Units 数量', K: 'Collab K 合作预算',
};
const NUM_RE = /^[+-]?(\d+\.?\d*|\.\d+)$/;
const blank = (v) => v === undefined || v === null || String(v).trim() === '';
const okFormat = (type, v) => blank(v) || type === 'text' || type === 'date' || NUM_RE.test(v.trim());
// percent text -> engine decimal text ("5" -> "5e-2"); bad text passes through so the engine rejects it
const pct = (v) => (blank(v) ? '' : NUM_RE.test(v.trim()) ? v.trim() + 'e-2' : v);
const niceErr = (msg) => msg.replace(/^(\w+)/, (m, k) => FIELD_NAMES[k] || k)
  .replace('Split 分成 must sum to 1', 'Split A + B + C must be 100% 分成合计须为100%')
  .replace(' must be an integer >= 0', ' must be a whole number, 0 or more 必须是不小于0的整数')
  .replace(' must be >= 0', ' must be 0 or more 必须不小于0')
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
    const l = el('label', { class: 'field' }, ...lab(f.en, f.zh), buildInput(f, f.id));
    if (f.note) l.append(el('span', { class: 'err warn' }, f.note[0], el('small', {}, f.note[1])));
    gf.append(l);
  }
  const card = $('design');
  card.append(el('h2', {}, 'Design ', el('small', {}, '设计')));
  const g = el('div', { class: 'grid' });
  for (const f of DESIGN_FIELDS) g.append(el('label', { class: 'field' }, ...lab(f.en, f.zh), buildInput({ ...f, value: DESIGN_DEFAULT[f.k] }, 'd_' + f.k)));
  card.append(g);
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
const SWEEP_HEAD = ['Margin 利润率', 'Price USD 美元售价', 'CNY 人民币', 'IDR 印尼盾', 'PayPal fee 手续费', 'Profit / unit 单件利润', 'Total profit 总利润', 'Net after collab K 扣合作预算净利'];

// Margin table 20-50% (step 5) for the design; every number comes from sweepDesign.
function sweepCard(rows) {
  const t = el('table', { class: 'sweep' });
  t.append(el('thead', {}, el('tr', {}, ...SWEEP_HEAD.map((h) => el('th', {}, h)))));
  const body = el('tbody');
  rows.forEach((r, i) => {
    const pctTxt = MARGINS[i] + '%';
    if (!r.ok) { body.append(el('tr', {}, el('td', { 'data-label': SWEEP_HEAD[0] }, pctTxt), el('td', { colspan: '7', class: 'err' }, niceErr(r.error)))); return; }
    const cells = [pctTxt, money(r.P), r.cny ? money(r.cny) : '—', r.idr ? money(r.idr) : '—', money(r.paypal), money(r.profit), money(r.total), money(r.net)];
    body.append(el('tr', {}, ...cells.map((c, k) => el('td', { 'data-label': SWEEP_HEAD[k] }, c))));
  });
  t.append(body);
  return el('div', { class: 'card' }, el('h2', {}, 'Margin table ', el('small', {}, '利润率表')), el('div', { class: 'scroll' }, t));
}
const errBox = (msg) => el('p', { class: 'err' }, msg);

// Chart values come from the same calcDesign / sweepDesign results as the tables.
function drawCharts(r, rows) {
  renderCharts($('charts'), {
    design: r && r.ok ? r : null,
    margins: MARGINS.map((p) => p + '%'),
    price: rows.map((x) => (x.ok ? x.P : null)),
    net: rows.map((x) => (x.ok ? x.net : null)),
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
  const sp = { A: pct(val('splitA')), B: pct(val('splitB')), C: pct(val('splitC')) };
  const ss = splitSum(sp.A, sp.B, sp.C);
  $('splitCheck').replaceChildren(ss
    ? el('span', { class: ss.ok ? 'ok' : 'err' }, `Split sum 分成合计: ${ss.text}%` + (ss.ok ? ' ✓' : ' — must be 100% 须为100%'))
    : el('span', { class: 'err' }, 'Split sum 分成合计: — (enter numbers 请输入数字)'));
  const g = { f: pct(val('paypalPct')), s: pct(val('surcharge')), fxBuffer: pct(val('fxBuffer')), idrStep: val('idrStep'), split: sp };
  const d = {};
  for (const f of DESIGN_FIELDS) d[f.k] = val('d_' + f.k);
  d.m = pct(d.m);

  const box = $('res'), sw = $('sweeps');
  box.replaceChildren();
  sw.replaceChildren();
  if (blank(d.c)) {
    box.append(el('p', { class: 'hint' }, 'Enter unit cost to see a price. 输入单位成本以查看价格。'));
    drawCharts(null, []);
  } else {
    try {
      const rs = { r: rt.r, x: rt.x };
      const r = calcDesign(d, g, rs);
      if (!r.ok) box.append(errBox(niceErr(r.error)));
      else {
        const cur = (c, v) => [el('span', { class: 'cur' }, c), v];
        const stat = (en, zh, value, cls) => el('div', { class: 'stat' + (cls ? ' ' + cls : '') }, el('span', { class: 'stat-k' }, en, el('small', {}, zh)), el('strong', { class: 'stat-v' }, ...value));
        box.append(
          el('div', { class: 'hero' },
            stat('Price USD', '美元售价', cur('USD', money(r.P)), 'hero-main'),
            stat('Price CNY', '人民币价格', r.cny ? cur('¥', money(r.cny)) : ['—']),
            stat('Price IDR', '印尼盾价格', r.idr ? cur('Rp', money(r.idr)) : ['—'])),
          el('div', { class: 'stats' },
            stat('Profit / unit', '单件利润', cur('USD', money(r.profit))),
            stat('Total profit', '总利润', cur('USD', money(r.total))),
            stat('Net after collab K', '扣除合作预算后净利', cur('USD', money(r.net)), 'stat-key'),
            stat('Margin after collab', '扣除后利润率', [String(r.marginAfterCollab)])),
          el('div', { class: 'splits' },
            el('h3', {}, 'Split A / B / C ', el('small', {}, '分成')),
            el('table', {},
              el('thead', {}, el('tr', {}, el('th', {}), el('th', {}, 'Per unit 单件'), el('th', {}, 'Net split 净利分成'))),
              el('tbody', {},
                ...['A', 'B', 'C'].map((k) => el('tr', {}, el('td', {}, k), el('td', {}, money(r.split[k])), el('td', {}, money(r.netSplit[k]))))))));
        const t = el('table', { class: 'details' });
        t.append(row('Shipping charged S 收取运费', 'USD ' + money(r.S)),
          row('Customer pays R 客户支付', 'USD ' + money(r.R)),
          row('PayPal fee (% + fixed) PayPal手续费(比例+固定)', 'USD ' + money(r.paypal)),
          row('Units 数量', r.u),
          row('Collab budget K 合作预算', 'USD ' + money(r.K)));
        box.append(t);
      }
      const rows = sweepDesign(d, g, MARGINS.map((p) => pct(String(p))), rs);
      sw.append(sweepCard(rows));
      drawCharts(r, rows);
    } catch (e) { box.append(errBox('Unexpected error 意外错误: ' + e.message)); drawCharts(null, []); }
  }
  if (formatBad) box.append(errBox('Some fields are not numbers (red). 部分字段不是数字(红色)。'));
}

// ---- Scenarios: save/load in the browser (localStorage) + export/import file ----
const fieldIds = () => [...GLOBAL_FIELDS.map((f) => f.id), ...DESIGN_FIELDS.map((f) => 'd_' + f.k)];
const collect = () => Object.fromEntries(fieldIds().map((id) => [id, val(id)]));
const apply = (fields) => { for (const id of fieldIds()) $(id).value = fields[id]; render(); };
const store = () => { try { return window.localStorage; } catch { return null; } };

function buildScenarios() {
  const box = $('scenarios');
  const name = el('input', { type: 'text', autocomplete: 'off', placeholder: 'Scenario name 方案名称' });
  const pick = el('select');
  const status = el('div', { class: 'note' });
  name.dataset.type = 'text';
  const btn = (en, zh, fn, primary) => { const b = el('button', { type: 'button', class: 'btn ' + (primary ? 'btn-primary' : 'btn-secondary') }, en, el('small', {}, zh)); b.addEventListener('click', fn); return b; };
  const say = (msg, bad, notice) => status.replaceChildren(el('span', { class: bad ? 'err' : 'ok' }, msg), ...(notice ? [el('div', { class: 'warn' }, notice)] : []));
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
    say(`Loaded 已载入: ${pick.value}`, false, p.notice);
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
    say(`Imported 已导入: ${f.name}`, false, p.notice);
  });

  box.append(el('h2', {}, 'Scenarios ', el('small', {}, '方案')),
    el('div', { class: 'toolbar' }, name, btn('Save', '保存', save, true)),
    el('div', { class: 'toolbar' }, pick, btn('Load', '载入', load), btn('Delete', '删除', del)),
    el('div', { class: 'toolbar' }, btn('Export file', '导出文件', exportFile),
      el('label', { class: 'btn btn-secondary' }, el('span', {}, 'Import file'), el('small', {}, '导入文件'), file)),
    status);
  refresh();
}

// ---- Theme: system by default; the button switches light/dark and the choice is remembered (pc-theme). The inline script in <head> sets the first value before paint.
const themeBtn = $('themeBtn');
const setTheme = (t) => { document.documentElement.setAttribute('data-theme', t); themeBtn.setAttribute('aria-pressed', String(t === 'dark')); };
setTheme(document.documentElement.getAttribute('data-theme') === 'dark' ? 'dark' : 'light');
themeBtn.addEventListener('click', () => {
  const t = document.documentElement.getAttribute('data-theme') === 'dark' ? 'light' : 'dark';
  setTheme(t);
  try { localStorage.setItem('pc-theme', t); } catch { /* storage blocked: choice lasts until reload */ }
});
window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', (e) => {
  let saved = null;
  try { saved = localStorage.getItem('pc-theme'); } catch { /* ignore */ }
  if (saved !== 'light' && saved !== 'dark') setTheme(e.matches ? 'dark' : 'light');
});
$('pdfBtn').addEventListener('click', () => window.print()); // browser print view; user saves as PDF
build();
buildScenarios();
render();
getCnyRate().then((r) => { live = { ...r, done: true }; render(); });
let lastW = window.innerWidth; // charts are drawn to the container width, so redraw when the width changes
window.addEventListener('resize', () => { if (window.innerWidth !== lastW) { lastW = window.innerWidth; render(); } });

return {  };
})();
})();
