"""Full diagnostic run for one modulus: every object of the catalogue through every decomposition.

run(m) writes data/report_<m>.json (small) and fig/<m>_*.png, and returns the results dict. It is what
`python3 -m phaselab report <m>` calls; FINDINGS.md was produced from these outputs.
"""
from __future__ import annotations

import json
import math
import os
import time

import numpy as np

from . import blocks, decomp, dynamics, phases, sets
from .core import Problem
from .group import UnitGroup
from .objects import catalogue

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _divisors(n):
    ds = [1]
    from .group import factorize
    for p, k in factorize(n):
        ds = [d * p ** e for d in ds for e in range(k + 1)]
    return sorted(ds)


def coset_specs(G: UnitGroup, n: int = 6) -> list:
    """pow:d for ~n divisors d of the exponent L, log-spaced in [2, L/2] (H^perp = chars of order | d)."""
    ds = [d for d in _divisors(G.L) if 2 <= d <= G.L // 2]
    if not ds:
        return []
    targets = np.exp(np.linspace(np.log(2), np.log(G.L / 2), n))
    pick = []
    for t in targets:
        d = min(ds, key=lambda x: abs(math.log(x) - math.log(t)))
        if d not in pick:
            pick.append(d)
    return [f"coset:pow:{d}" for d in pick]


def groupings(G: UnitGroup) -> list:
    g = ["order", "parity", "quantile:20"]
    if len(G.factors) > 1 or G.factors[0][1] > 1:
        g.insert(1, "conductor")
    return g + coset_specs(G)


def _clean(x):
    if isinstance(x, dict):
        return {str(k): _clean(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [_clean(v) for v in x]
    if isinstance(x, np.ndarray):
        return _clean(x.tolist())
    if isinstance(x, (np.floating, float)):
        return None if not np.isfinite(x) else float(x)
    if isinstance(x, (np.integer,)):
        return int(x)
    if isinstance(x, complex):
        return [x.real, x.imag]
    return x


def run(m: int, a: int = None, seed: int = 1, figs: bool = True, n_worst: int = 200, dyn: bool = True,
        verbose: bool = True) -> dict:
    t0 = time.time()
    G = UnitGroup(m)
    cat = catalogue(m, a=a, seed=seed, G=G)
    a = cat["P"].a
    res = dict(m=m, phi=G.phi, shape=G.shape, a=a, objects={}, groupings=groupings(G))
    log = print if verbose else (lambda *x, **k: None)
    log(f"m={m} phi={G.phi} shape={G.shape} a={a}  groupings={res['groupings']}")

    P = cat["P"].prob
    worst = P.worst_a(n_worst)
    for name, o in cat.items():
        pr = o.prob
        r = dict(desc=o.desc, a=o.a, main=pr.main, E=pr.E(o.a), E_over_main=pr.E(o.a) / pr.main,
                 E_over_sd=pr.E(o.a) / pr.rms_E(), A_over_main=pr.parseval_mass() / pr.main,
                 size_max_over_rms=pr.summary()["max_size_over_rms"])
        r["moments"] = phases.moments(pr)
        ps = phases.phase_stats(pr, o.a)
        r["phase"] = {k: ps[k] for k in ("c_w", "c_u", "z_w", "z_u", "kuiper", "kuiper_p", "bias_by_quantile",
                                        "share_by_quantile", "hist_w", "hist_u")}
        pc = phases.psi_correlation(pr, 12)
        r["psi"] = dict(max_Cw_sqrt_n=max(abs(x[2]) for x in pc["rows"]) * math.sqrt(pc["n"]),
                        max_Cu_over_sd=max(abs(x[3]) for x in pc["rows"]) / pc["sd_null_u"],
                        rows=[(s, o_, abs(c), cu) for s, o_, c, cu in pc["rows"]][:40])
        r["decomp"] = {}
        for by in res["groupings"]:
            lab = decomp.make_labels(pr, by)
            d = decomp.decompose(pr, lab, o.a, n_surr=4)
            r["decomp"][by] = {k: d[k] for k in ("ngroups", "within", "within_surr", "across", "total", "W",
                                                 "W_surr", "W_cond", "W_over_Wcond", "chi2_dof", "sdE", "A")}
        lab = decomp.by_quantile(pr, 10)
        al = decomp.allocation(pr, lab, worst if name == "P_worst" else [o.a])
        r["allocation_decile"] = {k: al[k] for k in ("share", "share_gauss", "share_L1")}
        if name not in ("conj", "toy"):
            wU = pr.weights[-1]
            r["blocks"] = [blocks.block_moments(G, wU, M, a=o.a) for M in (m ** 0.4, m ** 0.5)]
        res["objects"][name] = r
        log(f"  {name:14s} E/main={r['E_over_main']:+.4f} E/sd={r['E_over_sd']:+.1f} kurt={r['moments']['kurt']:.2f} "
            f"Wcond(order)={r['decomp']['order']['W_over_Wcond']:.3f}  [{time.time() - t0:.0f}s]")

    # range X > m for the primes
    res["range"] = []
    for f in (1, 2, 4, 10, 30):
        for wt in ("1", "cesaro"):
            w = sets.prime_weights(m, f * m, wt)
            pr = Problem(G, [w, w])
            N = pr.N_flat()
            mu = pr.main
            res["range"].append(dict(X_over_m=f, weight=wt, A_over_main=pr.parseval_mass() / mu,
                                     maxE_over_main=float(np.abs(N - mu).max() / mu),
                                     rms_over_main=pr.rms_E() / mu, minN_over_main=float(N.min() / mu)))

    if dyn:
        res["dynamics"] = dynamics_block(G, cat, seed)
    if figs:
        make_figs(res, cat, G)
    path = os.path.join(HERE, "data", f"report_{m}.json")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        json.dump(_clean(res), f, indent=1)
    log(f"wrote {path}  ({time.time() - t0:.0f}s)")
    return res


def dynamics_block(G, cat, seed):
    m = G.m
    rng = np.random.default_rng(seed + 7)
    P = cat["P"].prob
    S = P.spectra[0]
    canon = np.nonzero(np.arange(G.phi) < G.neg)[0]          # one character per conjugate pair
    top = canon[np.argsort(-np.abs(S[canon]))[:8]]
    rnd = rng.integers(1, G.phi, 24)
    js = np.concatenate([top, rnd])
    ps = sets.primes_upto(4 * m)
    red = np.nonzero(cat["redacted"].prob.weights[0])[0]
    cr = dynamics.cramer(m, m, rng)
    Xg = dynamics.log_grid(m ** 0.5, m, 2500)
    Xg4 = dynamics.log_grid(m ** 0.5, 4 * m, 3000)
    out = dict(js=js.tolist(), rates={})
    trajs = {}
    for name, ns, X in (("P", ps, Xg), ("P_to_4m", ps, Xg4), ("redacted", red, Xg), ("cramer", cr, Xg)):
        for wt in ("1", "log*cesaro"):
            tr = dynamics.trajectories(G, ns, js, X, wt)
            r = dynamics.phase_rate(tr, X)
            out["rates"][f"{name}|{wt}"] = dict(mean_abs_speed=float(np.abs(r["speed"]).mean()),
                                               path_speed=float(r["abs_speed"].mean()), autocorr=r["autocorr"])
            trajs[(name, wt)] = (X, tr)
    # coherence of chi and chi*psi along X, psi of small order, versus unrelated pairs
    coh = {}
    for d in (2, 3, 4, 6):
        sel = np.nonzero(G.order == d)[0]
        if sel.size == 0:
            continue
        s = int(sel[0])
        sh = phases.shift_index(G, s)
        X = Xg
        for name, ns in (("P", ps), ("redacted", red), ("cramer", cr)):
            ta = dynamics.trajectories(G, ns, js[8:], X, "log*cesaro")
            tb = dynamics.trajectories(G, ns, sh[js[8:]], X, "log*cesaro")
            tc = dynamics.trajectories(G, ns, np.roll(js[8:], 1), X, "log*cesaro")
            cc = [dynamics.cross_corr(ta[i], tb[i]) for i in range(ta.shape[0])]
            cu = [dynamics.cross_corr(ta[i], tc[i]) for i in range(ta.shape[0])]
            coh[f"order{d}|{name}"] = dict(mean=float(np.mean(cc)), sd=float(np.std(cc)),
                                           unrelated_mean=float(np.mean(cu)), unrelated_sd=float(np.std(cu)))
    out["coherence"] = coh
    out["_trajs"] = trajs
    return out


# ----------------------------------------------------------------------------------------------- figures
def make_figs(res, cat, G):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    m = res["m"]
    figdir = os.path.join(HERE, "fig")
    os.makedirs(figdir, exist_ok=True)
    O = res["objects"]
    names = [n for n in ("P", "P_worst", "redacted", "redacted_half", "pairing", "astar", "conj", "random", "toy")
             if n in O]
    colors = dict(P="#1f5fa8", P_worst="#3b8fd9", redacted="#c0392b", redacted_half="#e67e22", pairing="#8e44ad",
                  astar="#16a085", conj="#7f8c8d", random="#95a5a6", toy="#2c3e50")

    # 1. allocation of E(a) across |S| deciles
    fig, ax = plt.subplots(figsize=(8, 4.2))
    x = np.arange(10)
    for n in ("P_worst", "redacted", "pairing", "astar", "conj"):
        if n in O:
            ax.plot(x, O[n]["allocation_decile"]["share"], "-o", ms=3.5, color=colors[n], label=n)
    ax.plot(x, O["P"]["allocation_decile"]["share_gauss"], "k--", lw=1.4, label="Gaussian-conditional  V_g/V")
    ax.plot(x, O["P"]["allocation_decile"]["share_L1"], "k:", lw=1.4, label="uniform phase bias  A_g/A")
    ax.set_xlabel("|S(χ)| decile (0 = smallest)")
    ax.set_ylabel("share of E(a) carried by the decile")
    ax.set_title(f"m = {m}: where the deficit sits (P_worst: mean over {200} worst a)")
    ax.legend(fontsize=8, frameon=False)
    ax.grid(alpha=0.25)
    fig.tight_layout()
    fig.savefig(os.path.join(figdir, f"{m}_allocation.png"), dpi=110)
    plt.close(fig)

    # 2. weighted phase histograms at the target a
    fig, axs = plt.subplots(2, 3, figsize=(10, 5.2), sharex=True)
    for ax, n in zip(axs.ravel(), ("P", "P_worst", "redacted", "pairing", "conj", "toy")):
        if n not in O:
            continue
        h = np.asarray(O[n]["phase"]["hist_w"])
        edges = np.linspace(0, np.pi, h.size + 1)
        ax.bar(edges[:-1], h, width=np.diff(edges), align="edge", color=colors[n], alpha=0.85)
        ax.axhline(1 / np.pi, color="k", lw=1)
        ax.set_title(f"{n}: c1 = E/A = {O[n]['phase']['c_w'][0]:+.4f}", fontsize=9)
        ax.set_ylim(0, max(0.6, h.max() * 1.05) if n != "conj" else h.max() * 1.05)
    for ax in axs[-1]:
        ax.set_xlabel("|arg conj(χ(a)) T(χ)|  (weighted by |T|)")
    fig.suptitle(f"m = {m}: phase distribution of the terms of E(a); line = uniform", fontsize=10)
    fig.tight_layout()
    fig.savefig(os.path.join(figdir, f"{m}_phase_hist.png"), dpi=110)
    plt.close(fig)

    # 3. within-group cancellation vs group size (Xie cosets + order + quantile)
    fig, axs = plt.subplots(1, 2, figsize=(10, 4.2))
    for n in ("P", "P_worst", "redacted", "pairing", "astar", "random"):
        if n not in O:
            continue
        keys = [k for k in res["groupings"] if k.startswith("coset")]
        hs = [G.phi / O[n]["decomp"][k]["ngroups"] for k in keys]
        axs[0].plot(hs, [O[n]["decomp"][k]["within"] for k in keys], "-o", ms=3, color=colors[n], label=n)
        axs[1].plot(hs, [O[n]["decomp"][k]["W_over_Wcond"] for k in keys], "-o", ms=3, color=colors[n], label=n)
    keys = [k for k in res["groupings"] if k.startswith("coset")]
    hs = [G.phi / O["P"]["decomp"][k]["ngroups"] for k in keys]
    axs[0].plot(hs, [O["P"]["decomp"][k]["within_surr"] for k in keys], "k--", label="random phases")
    axs[0].plot(hs, 0.5 * np.log(hs), "k:", label="½ log(group size)")
    for ax in axs:
        ax.set_xscale("log")
        ax.set_xlabel("coset size (characters per merged coset χH⊥ ∪ χ̄H⊥)")
        ax.grid(alpha=0.25)
    axs[0].set_ylabel("within-coset cancellation  log(A/W)")
    axs[1].set_ylabel("W / W_cond  (1 = random phases given E)")
    axs[1].set_ylim(0.7, 1.4)
    axs[0].legend(fontsize=8, frameon=False)
    fig.suptitle(f"m = {m}: Xie coset decomposition", fontsize=10)
    fig.tight_layout()
    fig.savefig(os.path.join(figdir, f"{m}_cosets.png"), dpi=110)
    plt.close(fig)

    # 4. distribution of E(b)/sd over b
    fig, ax = plt.subplots(figsize=(8, 4))
    bins = np.linspace(-90, 12, 205)
    for n in ("P", "redacted", "pairing", "astar", "toy"):
        if n not in cat:
            continue
        pr = cat[n].prob
        E = pr.N_flat() - pr.main
        z = E / E.std()
        h, _ = np.histogram(z, bins=bins)
        ax.step(bins[:-1], np.maximum(h, 0.5), where="post", color=colors[n],
                label=f"{n}: kurt {O[n]['moments']['kurt']:.2f}")
    zz = np.linspace(-8, 8, 200)
    ax.plot(zz, G.phi * np.diff(bins)[0] * np.exp(-zz ** 2 / 2) / math.sqrt(2 * math.pi), "k--", lw=1,
            label="Gaussian")
    ax.set_yscale("log")
    ax.set_ylim(0.4, None)
    ax.set_xlabel("E(b) / sd over all b")
    ax.set_ylabel("number of classes b")
    ax.legend(fontsize=8, frameon=False)
    ax.set_title(f"m = {m}: the barrier deficit is a single isolated spike", fontsize=10)
    fig.tight_layout()
    fig.savefig(os.path.join(figdir, f"{m}_Edist.png"), dpi=110)
    plt.close(fig)

    # 5. dynamics
    if "dynamics" in res:
        tr = res["dynamics"]["_trajs"]
        fig, axs = plt.subplots(1, 3, figsize=(12, 3.8))
        for name, c in (("P", colors["P"]), ("cramer", "#95a5a6"), ("redacted", colors["redacted"])):
            X, T = tr[(name, "log*cesaro")]
            u = T[8] ** 2
            axs[0].plot(np.log(X), np.unwrap(np.angle(u)), color=c, lw=1, label=name)
        axs[0].set_xlabel("log X")
        axs[0].set_ylabel("unwrapped arg S_X(χ)²  (Cesàro, log)")
        axs[0].legend(fontsize=8, frameon=False)
        X, T = tr[("P_to_4m", "log*cesaro")]
        for i in range(4):
            axs[1].plot(np.log(X / m), np.abs(T[i]) / np.sqrt(X), lw=1)
        axs[1].axvline(0, color="k", lw=0.8)
        axs[1].set_xlabel("log(X/m)")
        axs[1].set_ylabel("|S_X(χ)|/√X, top-4 χ at X = m")
        lags = sorted(res["dynamics"]["rates"]["P|log*cesaro"]["autocorr"].keys(), key=float)
        for key, c in (("P|log*cesaro", colors["P"]), ("cramer|log*cesaro", "#95a5a6"),
                       ("redacted|log*cesaro", colors["redacted"]), ("P|1", colors["P"]), ("cramer|1", "#95a5a6")):
            ac = res["dynamics"]["rates"][key]["autocorr"]
            axs[2].plot([float(l) for l in lags], [ac[l] for l in lags], "-o" if "|1" in key else "--s", ms=3,
                        color=c, label=key)
        axs[2].set_xscale("log")
        axs[2].set_xlabel("lag in log X")
        axs[2].set_ylabel("phase autocorrelation of S_X(χ)²")
        axs[2].legend(fontsize=7, frameon=False)
        fig.suptitle(f"m = {m}: phase dynamics in X", fontsize=10)
        fig.tight_layout()
        fig.savefig(os.path.join(figdir, f"{m}_dynamics.png"), dpi=110)
        plt.close(fig)
        del res["dynamics"]["_trajs"]

    # 6. range X > m
    fig, ax = plt.subplots(figsize=(6.5, 4))
    for wt, ls in (("1", "-"), ("cesaro", "--")):
        rr = [r for r in res["range"] if r["weight"] == wt]
        f = [r["X_over_m"] for r in rr]
        ax.plot(f, [r["A_over_main"] for r in rr], "o" + ls, color="#c0392b", label=f"Parseval mass A/μ ({wt})")
        ax.plot(f, [r["maxE_over_main"] for r in rr], "s" + ls, color="#1f5fa8", label=f"max_a |E|/μ ({wt})")
        ax.plot(f, [r["rms_over_main"] for r in rr], "^" + ls, color="#16a085", label=f"rms_a E/μ ({wt})")
    ax.axhline(1, color="k", lw=0.8)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("X/m")
    ax.legend(fontsize=7, frameon=False)
    ax.set_title(f"m = {m}: the wall (A/μ > 1) against range X", fontsize=10)
    fig.tight_layout()
    fig.savefig(os.path.join(figdir, f"{m}_range.png"), dpi=110)
    plt.close(fig)


def table(res) -> str:
    """Markdown separation table."""
    O = res["objects"]
    rows = ["| object | a | E(a)/μ | E/sd | max|S|/rms | W/W_cond (order, quantile, median coset) | chi²/dof (median) | "
            "unweighted c₁ z | Kuiper p | kurt E(b) | z_min | ψ-corr max|C_w|√n | arc/arc_rand (M=√m) |",
            "|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for n, r in O.items():
        D = r["decomp"]
        cos = [D[k]["W_over_Wcond"] for k in D if k.startswith("coset")]
        chi = [D[k]["chi2_dof"] for k in D]
        arc = r.get("blocks", [None, None])[1]
        arcs = f"{arc['arc'] / arc['arc_random']:.2f}" if arc else "–"
        rows.append(f"| {n} | {r['a']} | {r['E_over_main']:+.3f} | {r['E_over_sd']:+.1f} | {r['size_max_over_rms']:.2f} | "
                    f"{D['order']['W_over_Wcond']:.2f}, {D['quantile:20']['W_over_Wcond']:.2f}, "
                    f"{np.median(cos) if cos else float('nan'):.2f} | {np.median(chi):.2f} | "
                    f"{r['phase']['z_u'][0]:+.1f} | {r['phase']['kuiper_p']:.2g} | {r['moments']['kurt']:.2f} | "
                    f"{r['moments']['zmin']:.1f} | {r['psi']['max_Cw_sqrt_n']:.1f} | {arcs} |")
    return "\n".join(rows)


def scan(ms, seed: int = 1, verbose: bool = True) -> list:
    """Scaling table over several moduli: P (tails, kurtosis, worst-a decomposition), barriers (spike size,
    kurtosis, saturation of Xie within-coset cancellation), toy (shape)."""
    rows = []
    for m in ms:
        G = UnitGroup(m)
        cat = catalogue(m, seed=seed, G=G, which=["P", "P_worst", "pairing", "redacted", "toy"])
        P = cat["P"].prob
        mo = phases.moments(P)
        w = cat["P_worst"]
        dq = decomp.decompose(P, decomp.by_quantile(P, 20), w.a, n_surr=0)
        do = decomp.decompose(P, decomp.by_order(G), w.a, n_surr=0)
        pa = cat["pairing"].prob
        mu_over_sd = pa.main / pa.rms_E()
        moP = phases.moments(pa)
        toy = cat["toy"].prob
        mt = phases.moments(toy)
        V = np.abs(toy.T[1:]) ** 2
        Vs = np.sort(V)[::-1]
        VP = np.sort(np.abs(P.T[1:]) ** 2)[::-1]
        k = max(1, int(1e-3 * V.size))
        r = dict(m=m, phi=G.phi, A_over_mu=P.parseval_mass() / P.main, minN_over_mu=mo["minN_over_main"],
                 kurt_P=mo["kurt"], zmin_P=mo["zmin"], lower4=mo["tails"]["lower4"], upper4=mo["tails"]["upper4"],
                 lower3=mo["tails"]["lower3"], Wc_order_worst=do["W_over_Wcond"], Wc_quant_worst=dq["W_over_Wcond"],
                 mu_over_sd_pairing=mu_over_sd, kurt_pairing=moP["kurt"],
                 kurt_pred_pairing=3 + mu_over_sd ** 4 / G.phi,
                 hsat=(P.parseval_mass() / P.main) ** 2,
                 kurt_toy=mt["kurt"], skew_toy=mt["skew"], zmin_toy=mt["zmin"],
                 top_share_toy=float(Vs[:k].sum() / Vs.sum()), top_share_P=float(VP[:k].sum() / VP.sum()))
        rows.append(r)
        if verbose:
            print(" ".join(f"{k_}={v:.4g}" if isinstance(v, float) else f"{k_}={v}" for k_, v in r.items()), flush=True)
    return rows


def scan_figure(rows, path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    ms = np.array([r["m"] for r in rows], dtype=float)
    g = lambda k: np.array([r[k] for r in rows])
    fig, axs = plt.subplots(1, 4, figsize=(15, 3.6))
    ax = axs[0]
    ax.plot(ms, g("kurt_P"), "o", color="#1f5fa8", label="P")
    ax.plot(ms, g("kurt_pairing"), "s", color="#8e44ad", label="pairing barrier")
    ax.plot(ms, g("kurt_pred_pairing"), "k--", lw=1, label="3 + (μ/σ)⁴/φ  (one spike)")
    ax.set_yscale("log"); ax.set_ylabel("kurtosis of E(b) over b"); ax.legend(fontsize=7, frameon=False)
    ax = axs[1]
    ax.plot(ms, g("mu_over_sd_pairing"), "s", color="#8e44ad", label="μ/σ: barrier spike in sd units")
    ax.plot(ms, g("A_over_mu"), "o", color="#c0392b", label="A/μ: the wall")
    ax.plot(ms, np.sqrt(g("hsat")) * 0 + g("hsat"), "^", color="#16a085", label="(A/μ)²: coset size where barriers saturate")
    ax.set_yscale("log"); ax.legend(fontsize=7, frameon=False)
    ax = axs[2]
    ax.plot(ms, g("lower3"), "o", color="#1f5fa8", label="P lower tail z<−3")
    ax.plot(ms, g("lower4"), "s", color="#3b8fd9", label="P lower tail z<−4")
    ax.plot(ms, g("upper4"), "^", color="#e67e22", label="P upper tail z>4")
    ax.axhline(1, color="k", lw=0.8)
    ax.set_ylabel("count / Gaussian expectation"); ax.legend(fontsize=7, frameon=False)
    ax = axs[3]
    ax.plot(ms, g("top_share_toy"), "o-", color="#2c3e50", label="toy")
    ax.plot(ms, g("top_share_P"), "s-", color="#1f5fa8", label="P")
    ax.set_ylabel("share of Σ|T|² in the top 0.1% of χ"); ax.legend(fontsize=7, frameon=False)
    for ax in axs:
        ax.set_xscale("log"); ax.set_xlabel("m (prime)"); ax.grid(alpha=0.25)
    fig.tight_layout()
    fig.savefig(path, dpi=110)
    plt.close(fig)
