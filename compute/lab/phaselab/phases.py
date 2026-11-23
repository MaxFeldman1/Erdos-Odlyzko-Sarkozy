"""Phase statistics of the terms t_chi(a) = conj(chi(a)) T(chi)/phi, and a-independent phase statistics.

phase_stats(prob, a)      harmonics c_k = <cos k theta> (weighted by |t| and unweighted), folded histogram,
                          Kuiper test of the unweighted angles against the uniform law, bias by |T| quantile.
                          The weighted c_1 is exactly E(a)/A (A = Parseval mass).
psi_correlation(prob, d)  for every psi of order <= d: C_w(psi) = sum T(chi) conj(T(chi psi)) / sum |T|^2
                          and C_u(psi) = mean cos(arg T(chi) - arg T(chi psi)).
                          Identity: sum_chi T(chi) conj(T(chi psi)) = phi sum_b N(b)^2 conj(psi(b)) (twisted energy).
moments(prob)             distribution of E(b) over all b: skewness, kurtosis, 6th moment, min, z of the min.
"""
from __future__ import annotations

import math

import numpy as np

from .core import Problem


def kuiper(u: np.ndarray) -> tuple:
    """Kuiper statistic of samples u in [0,1] against U[0,1]; returns (V*sqrt(n) corrected, p-value)."""
    u = np.sort(u)
    n = u.size
    i = np.arange(1, n + 1)
    V = (i / n - u).max() + (u - (i - 1) / n).max()
    lam = (math.sqrt(n) + 0.155 + 0.24 / math.sqrt(n)) * V
    if lam < 0.4:
        return lam, 1.0
    p = 0.0
    for k in range(1, 100):
        p += 2 * (4 * k * k * lam * lam - 1) * math.exp(-2 * k * k * lam * lam)
    return lam, float(min(max(p, 0.0), 1.0))


def phase_stats(prob: Problem, a: int, K: int = 8, nbins: int = 36, qbins: int = 10) -> dict:
    G = prob.G
    t = prob.terms(a)
    idx = np.arange(1, G.phi)
    half = idx[idx <= G.neg[idx]]          # one representative per conjugate pair (and real characters)
    th = np.abs(np.angle(t[half]))         # folded to [0, pi]
    w = np.abs(t[half]) * np.where(G.neg[half] == half, 1.0, 2.0)
    ks = np.arange(1, K + 1)
    cosk = np.cos(np.outer(ks, th))
    c_w = (cosk * w).sum(axis=1) / w.sum()
    c_u = cosk.mean(axis=1)
    sd_w = math.sqrt(0.5 * (w ** 2).sum()) / w.sum()
    sd_u = math.sqrt(0.5 / th.size)
    hist_u, edges = np.histogram(th, bins=nbins, range=(0, np.pi), density=True)
    hist_w, _ = np.histogram(th, bins=nbins, range=(0, np.pi), weights=w, density=True)
    lam, p = kuiper(th / np.pi)
    # bias by size quantile: weighted mean cos within each |T| quantile bin
    v = np.abs(prob.T[half])
    r = np.argsort(np.argsort(v, kind="stable"), kind="stable")
    qb = (r * qbins) // v.size
    cq = np.array([(w[qb == b] * np.cos(th[qb == b])).sum() / w[qb == b].sum() for b in range(qbins)])
    share_q = np.array([(w[qb == b] * np.cos(th[qb == b])).sum() for b in range(qbins)])
    share_q = share_q / share_q.sum()
    return dict(a=int(a), E=prob.E(a), A=prob.parseval_mass(), c_w=c_w, c_u=c_u, sd_w=sd_w, sd_u=sd_u,
                z_w=c_w / sd_w, z_u=c_u / sd_u, hist_u=hist_u, hist_w=hist_w, edges=edges,
                kuiper=lam, kuiper_p=p, bias_by_quantile=cq, share_by_quantile=share_q)


def small_order_psis(G, dmax: int) -> np.ndarray:
    """Flat indices of all nontrivial characters of order <= dmax."""
    return np.nonzero((G.order <= dmax) & (G.order > 1))[0]


def shift_index(G, s: int) -> np.ndarray:
    """Flat index of chi_j * psi_s for every j."""
    if G.cyclic:
        return (np.arange(G.phi) + s) % G.phi
    jv = G.jvec
    sv = jv[s]
    return np.ravel_multi_index(tuple(((jv + sv) % np.array(G.shape)).T), G.shape)


def psi_correlation(prob: Problem, dmax: int = 12, T=None) -> dict:
    G = prob.G
    T = prob.T if T is None else T
    out = []
    keep = np.ones(G.phi, dtype=bool)
    keep[0] = False
    for s in small_order_psis(G, dmax):
        sh = shift_index(G, s)
        k = keep & (sh != 0)
        X, Y = T[k], T[sh[k]]
        Cw = (X * np.conj(Y)).sum() / np.sqrt((np.abs(X) ** 2).sum() * (np.abs(Y) ** 2).sum())
        Cu = np.cos(np.angle(X) - np.angle(Y)).mean()
        out.append((int(s), int(G.order[s]), complex(Cw), float(Cu)))
    n = keep.sum()
    return dict(rows=out, sd_null_u=math.sqrt(1.0 / n), n=int(n))


def moments(prob: Problem) -> dict:
    """Distribution of E(b) over all b in G."""
    N = prob.N_flat()
    E = N - prob.main
    sd = E.std()
    z = E / sd
    from math import erfc
    tails = {}
    for t in (3.0, 4.0):
        g = prob.phi * 0.5 * erfc(t / math.sqrt(2))
        tails[f"lower{t:g}"] = float((z < -t).sum() / g)
        tails[f"upper{t:g}"] = float((z > t).sum() / g)
    return dict(sd=float(sd), sd_over_main=float(sd / prob.main), skew=float((z ** 3).mean()), tails=tails,
                kurt=float((z ** 4).mean()), m6=float((z ** 6).mean()), zmin=float(z.min()), zmax=float(z.max()),
                minN_over_main=float(N.min() / prob.main),
                gauss_zmin=-math.sqrt(2 * math.log(prob.phi)))
