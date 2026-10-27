/* =====================================================================
   VITALX — محرك التحليل (مولّد البيانات + الكشف + المقاييس)
   ترجمة JavaScript للنسخة المصححة من robust_z و cusum_two_sided.
   لا يحتاج تعديلاً عادةً؛ الأرقام كلها في content.js
   ===================================================================== */
(function (root) {
  "use strict";

  // ---------- أدوات ----------
  function mulberry32(a) {
    return function () {
      a |= 0; a = (a + 0x6D2B79F5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }
  function gauss(r) {
    let u = 0, v = 0;
    while (u === 0) u = r();
    while (v === 0) v = r();
    return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
  }
  function median(a) {
    const s = a.slice().sort((x, y) => x - y), n = s.length;
    if (!n) return NaN;
    return n % 2 ? s[(n - 1) / 2] : (s[n / 2 - 1] + s[n / 2]) / 2;
  }
  function mean(a) { return a.length ? a.reduce((s, v) => s + v, 0) / a.length : NaN; }

  // ---------- robust_z (مطابق للنسخة المصححة) ----------
  function baselineStats(base, minScale) {
    const med = median(base);
    const mad = median(base.map(v => Math.abs(v - med))) * 1.4826;
    let ms;
    if (minScale && minScale.type === "absolute") ms = minScale.value;   // مثل النوم بالساعات
    else ms = med !== 0 ? (minScale ? minScale.value : 0.05) * Math.abs(med) : 1e-3;
    return { med, mad, scale: Math.max(mad, ms) };
  }
  function robustZ(x, st) { return (x - st.med) / st.scale; }

  // ---------- CUSUM ثنائي الاتجاه مع إعادة التصفير ----------
  function makeCusum(k, h) {
    let sp = 0, sn = 0;
    return function step(v) {
      sp = Math.max(0, sp + v - k);
      sn = Math.max(0, sn - v - k);
      const up = sp > h, dn = sn > h;
      const rec = { fired: up || dn, side: up ? 1 : dn ? -1 : 0, sp, sn };
      if (rec.fired) { sp = 0; sn = 0; }
      return rec;
    };
  }
  function cusumTwoSided(z, k, h) { const s = makeCusum(k, h); return z.map(v => s(v).fired); }

  // ---------- مولّد البيانات الصناعية بمرحلة تكيف ----------
  function generateAstronaut(sim, rng, opt) {
    opt = opt || {};
    const driftMult = opt.driftMult == null ? 1 : opt.driftMult;
    const noiseMult = opt.noiseMult == null ? 1 : opt.noiseMult;
    const D = sim.missionDays, P = sim.preflightDays;
    const onset = opt.onset != null ? opt.onset
      : Math.round(sim.onsetRange[0] + rng() * (sim.onsetRange[1] - sim.onsetRange[0]));
    const tau = sim.adaptation.tau;
    const out = { onset, truth: {}, obs: {}, pre: {}, personal: {}, rad: [] };
    for (const id in sim.channels) {
      const c = sim.channels[id];
      const personal = c.popMean + c.popSd * gauss(rng);
      const preOffset = c.preflightOffsetSd * gauss(rng);  // الأرض ليست الفضاء تماماً
      out.personal[id] = personal;
      out.pre[id] = Array.from({ length: P }, () => personal + preOffset + c.noiseSd * noiseMult * gauss(rng));
      const truth = [], obs = [];
      for (let t = 0; t < D; t++) {
        const adapt = c.adaptAmp * Math.exp(-t / tau);
        const drift = t >= onset ? c.drift * driftMult * (t - onset) : 0;
        const v = personal + adapt + drift;
        truth.push(v);
        obs.push(v + c.noiseSd * noiseMult * gauss(rng));
      }
      out.truth[id] = truth; out.obs[id] = obs;
    }
    let cum = 0;
    for (let t = 0; t < D; t++) { cum += Math.max(0, sim.radiation.dailyMean + sim.radiation.dailySd * gauss(rng)); out.rad.push(cum); }
    return out;
  }

  // ---------- الطريقة الشخصية ----------
  function activeChannels(sim) {
    return Object.keys(sim.channels).filter(id => id !== "chem" || sim.personal.includeChem);
  }
  function runPersonal(ast, sim) {
    const p = sim.personal, D = sim.missionDays, ign = sim.adaptation.days;
    const ids = activeChannels(sim);
    let initStart, active;
    if (p.baselineMode === "naive") { initStart = 0; active = p.stableWindow; }
    else if (p.baselineMode === "preflight") { initStart = null; active = ign; }
    else { initStart = ign; active = ign + p.stableWindow; }

    const st = {}, anchor = {}, win = {}, z = {}, chCus = {}, band = {};
    ids.forEach(id => {
      const c = sim.channels[id];
      const base = initStart == null ? ast.pre[id] : ast.obs[id].slice(initStart, initStart + p.stableWindow);
      st[id] = baselineStats(base, c.minScale);
      anchor[id] = Object.assign({}, st[id]);
      win[id] = base.slice();
      z[id] = new Array(D).fill(null);
      band[id] = new Array(D).fill(null);
      chCus[id] = makeCusum(p.k, p.h);
    });
    const comp = makeCusum(p.k, p.h);
    const wsum = Math.sqrt(ids.reduce((s, id) => s + sim.channels[id].weight ** 2, 0)) || 1;
    const level = new Array(D).fill(0), composite = new Array(D).fill(null), compS = new Array(D).fill(null);
    const explain = new Array(D).fill(null);

    for (let t = 0; t < D; t++) {
      ids.forEach(id => { band[id][t] = { med: st[id].med, scale: st[id].scale }; });
      if (t < active) continue;
      let zc = 0, chFired = 0, bigCount = 0;
      const contrib = [];
      ids.forEach(id => {
        const c = sim.channels[id];
        const zi = robustZ(ast.obs[id][t], st[id]);
        z[id][t] = zi;
        if (chCus[id](zi).fired) chFired++;
        const bad = c.direction * zi;          // موجب = في الاتجاه السيئ
        if (bad > p.urgentZ) bigCount++;
        zc += c.weight * bad;
        contrib.push({ id, z: zi, bad, w: c.weight });
      });
      zc /= wsum;
      composite[t] = zc;
      const cr = comp(zc);
      compS[t] = cr.sp;
      let lv = chFired > 0 ? 1 : 0;
      if (cr.fired && cr.side === 1) lv = bigCount >= 2 ? 3 : 2;
      level[t] = lv;
      if (lv > 0) explain[t] = contrib;

      // تحديث خط الأساس المتحرك مع الحماية
      if (p.baselineMode === "rolling") {
        ids.forEach(id => {
          const zi = z[id][t];
          if (Math.abs(zi) <= p.guardZ) {
            win[id].push(ast.obs[id][t]);
            if (win[id].length > p.rollingWindow) win[id].shift();
          }
          const ns = baselineStats(win[id], sim.channels[id].minScale);
          if (p.useAnchor) {
            const lim = p.anchorMaxShiftZ * anchor[id].scale;
            ns.med = Math.min(anchor[id].med + lim, Math.max(anchor[id].med - lim, ns.med));
          }
          st[id] = ns;
        });
      }
    }
    return { level, z, composite, compS, band, explain, active };
  }

  // ---------- الطريقة الثابتة العامة ----------
  function runFixed(ast, sim) {
    const f = sim.fixed, D = sim.missionDays;
    const active = f.ignoreAdaptation ? sim.adaptation.days : 0;
    const ids = Object.keys(f.thresholds);
    const run = {}; ids.forEach(id => run[id] = 0);
    const level = new Array(D).fill(0);
    for (let t = active; t < D; t++) {
      let n = 0;
      ids.forEach(id => {
        const th = f.thresholds[id], v = ast.obs[id][t];
        const over = th.op === ">" ? v > th.value : v < th.value;
        run[id] = over ? run[id] + 1 : 0;
        if (run[id] >= f.persistenceDays) n++;
      });
      level[t] = n >= 2 ? 3 : n === 1 ? 2 : 0;
    }
    return { level, active };
  }

  // ---------- المقاييس ----------
  function scoreRun(level, onset, active, sim) {
    // الكشف = أول نوبة تنبيه تبدأ في يوم البدء أو بعده. إنذار مستمر من قبل البدء لا يُحسب كشفاً
    let det = null;
    for (let t = Math.max(onset, active); t < level.length; t++) {
      if (level[t] >= 2 && (t === active || level[t - 1] < 2 || t === onset && level[t - 1] < 2)) { det = t; break; }
    }
    let fa = 0, prev = 0;
    for (let t = active; t < onset; t++) { const on = level[t] >= 2 ? 1 : 0; if (on && !prev) fa++; prev = on; }
    const delay = det == null ? null : det - onset;
    return { detected: delay != null && delay <= sim.detectWindow, delay, falseAlarms: fa, preDays: Math.max(0, onset - active) };
  }

  // ---------- إسقاط الاتجاه ----------
  function linfit(ys, xs) {
    const mx = mean(xs), my = mean(ys);
    let num = 0, den = 0;
    xs.forEach((x, i) => { num += (x - mx) * (ys[i] - my); den += (x - mx) ** 2; });
    const b = den ? num / den : 0;
    return { slope: b, at: x => my + b * (x - mx) };
  }
  function projectCrossing(series, t, w, thr, dir) {
    if (t - w + 1 < 0) return null;
    const xs = [], ys = [];
    for (let i = t - w + 1; i <= t; i++) { xs.push(i); ys.push(series[i]); }
    const f = linfit(ys, xs);
    const s = f.slope * dir, gap = (thr - f.at(t)) * dir;
    if (gap <= 0) return { day: t, slope: f.slope, fit: f };
    if (s <= 0) return null;
    return { day: t + gap / s, slope: f.slope, fit: f };
  }
  function projectionFor(ast, sim, pers) {
    const c = sim.channels.hr, pr = sim.projection;
    const at = pers.active;
    const b = pers.band.hr[at] || pers.band.hr[pers.band.hr.length - 1];
    const thr = b.med + c.direction * pr.monitorZ * b.scale;
    let trueCross = null;
    for (let t = at; t < sim.missionDays; t++) if ((ast.truth.hr[t] - thr) * c.direction >= 0) { trueCross = t; break; }
    let detDay = null;
    for (let t = ast.onset; t < sim.missionDays; t++) if (pers.level[t] >= 2) { detDay = t; break; }
    // نقيم الإسقاط عند لحظة أول تنبيه، ثم بعدها بأيام (offsets)، قبل العبور الحقيقي فقط
    const evals = (pr.evalOffsets || [0]).map(off => {
      const d = detDay != null ? detDay + off : null;
      if (d == null || d >= sim.missionDays || (trueCross != null && d >= trueCross)) return { off, day: d, proj: null, error: null };
      const proj = projectCrossing(ast.obs.hr, d, pr.window, thr, c.direction);
      return { off, day: d, proj, error: proj && trueCross != null ? proj.day - trueCross : null };
    });
    return { thr, trueCross, detDay, evals };
  }

  // ---------- مونت كارلو ----------
  function cohort(sim, opt) {
    opt = opt || {};
    const rng = mulberry32(opt.seed != null ? opt.seed : sim.seed);
    const n = opt.n || sim.cohortSize;
    const acc = { personal: [], fixed: [], projErr: [] };
    for (let i = 0; i < n; i++) {
      const a = generateAstronaut(sim, rng, opt);
      const pr = runPersonal(a, sim), fx = runFixed(a, sim);
      acc.personal.push(scoreRun(pr.level, a.onset, pr.active, sim));
      acc.fixed.push(scoreRun(fx.level, a.onset, fx.active, sim));
      if (!opt.skipProjection) projectionFor(a, sim, pr).evals.forEach((e, j) => {
        (acc.projErr[j] = acc.projErr[j] || { off: e.off, errs: [] });
        if (e.error != null) acc.projErr[j].errs.push(e.error);
      });
    }
    return { personal: summarize(acc.personal), fixed: summarize(acc.fixed), projection: acc.projErr.map(p => Object.assign({ off: p.off }, summarizeProj(p.errs))), n };
  }
  function summarize(rs) {
    const det = rs.filter(r => r.detected), delays = det.map(r => r.delay);
    const fa = rs.reduce((s, r) => s + r.falseAlarms, 0), days = rs.reduce((s, r) => s + r.preDays, 0);
    return {
      rate: det.length / rs.length,
      medianDelay: delays.length ? median(delays) : null,
      meanDelay: delays.length ? mean(delays) : null,
      faPer100: days ? (fa / days) * 100 : 0,
      faRuns: rs.filter(r => r.falseAlarms > 0).length / rs.length
    };
  }
  function summarizeProj(errs) {
    if (!errs.length) return { n: 0 };
    const abs = errs.map(Math.abs);
    return { n: errs.length, medAbs: median(abs), bias: median(errs), within5: abs.filter(e => e <= 5).length / abs.length };
  }

  const api = { mulberry32, gauss, median, baselineStats, robustZ, makeCusum, cusumTwoSided,
    generateAstronaut, runPersonal, runFixed, scoreRun, projectCrossing, projectionFor, cohort, activeChannels };
  root.VITALX_ENGINE = api;
  if (typeof module !== "undefined") module.exports = api;
})(typeof window !== "undefined" ? window : globalThis);
