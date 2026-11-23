"""Decompositions of E(a) = sum_{chi != chi0} t_chi(a),  t_chi(a) = conj(chi(a)) T(chi)/phi.

A grouping is an int label per character (flat j); label -1 means "excluded". The principal character is
always excluded. Groups are merged with their conjugates by default, so every partial sum T_g(a) is real.

Labelers
  by_order(G)              character order
  by_conductor(G)          conductor (composite m)
  by_parity(G)             chi(-1)
  by_coset(G, spec)        cosets chi H^perp for a subgroup H (spec as in UnitGroup.subgroup_gens);
                           this is Xie's decomposition: the coset of chi restricts the convolution to aH
  by_quantile(prob, q)     q quantile bins of |T(chi)| (= |S(chi)|^2 for the binary problem)

Cancellation accounting (decompose):
  A = sum_chi |t_chi|      (Parseval mass; for the binary prime problem A = |P|(1 - rho): the wall)
  W = sum_g |T_g|          (what is left after cancellation *within* groups)
  E = sum_g T_g
  within = log(A/W), across = log(W/|E|), total = log(A/|E|).  The same numbers for a random-phase surrogate
  (same |t_chi|, independent uniform phases, conjugate symmetry kept) calibrate what "random" looks like.
"""
from __future__ import annotations

import numpy as np

from .core import Problem, inverse


# ------------------------------------------------------------------------------------------------ labels
def by_order(G):
    return G.order.copy()


def by_conductor(G):
    return G.conductor.copy()


def by_parity(G):
    """0 for even characters, 1 for odd ones (labels must be >= 0)."""
    return (1 - G.parity) // 2


def by_coset(G, spec: str):
    gens, _ = G.subgroup_gens(spec)
    return G.subgroup_labels(gens)


def by_quantile(prob: Problem, q: int = 10, values=None):
    """Bin j != 0 into q equal-count bins of |T(chi)| (bin 0 = smallest). Conjugates share |T|."""
    v = np.abs(prob.T) if values is None else values
    lab = np.full(v.size, -1, dtype=np.int64)
    ranks = np.argsort(np.argsort(v[1:], kind="stable"), kind="stable")
    lab[1:] = (ranks * q) // (v.size - 1)
    return lab


def by_order_bucket(G, edges=(2, 3, 7, 31, 10**18)):
    """Coarse order buckets: [1,2], (2,3]... handy for very many orders."""
    return np.searchsorted(np.asarray(edges), G.order, side="left")


def merge_conjugates(G, lab: np.ndarray) -> np.ndarray:
    out = np.minimum(lab, lab[G.neg])
    out[(lab < 0) | (lab[G.neg] < 0)] = -1
    return out


def make_labels(prob: Problem, by: str) -> np.ndarray:
    """Labels from a string: order | conductor | parity | coset:<spec> | quantile:<q>."""
    G = prob.G
    kind, _, arg = by.partition(":")
    if kind == "order":
        return by_order(G)
    if kind == "conductor":
        return by_conductor(G)
    if kind == "parity":
        return by_parity(G)
    if kind == "coset":
        return by_coset(G, arg)
    if kind == "quantile":
        return by_quantile(prob, int(arg or 10))
    raise ValueError(f"unknown grouping {by}")


# ------------------------------------------------------------------------------------------------ surrogate
def random_phases(G, rng) -> np.ndarray:
    """Unit complex numbers u_j with u_{-j} = conj(u_j) and u_j = +-1 on real characters."""
    th = rng.uniform(0, 2 * np.pi, G.phi)
    lo = np.arange(G.phi) < G.neg
    th[G.neg[lo]] = -th[lo]
    selfc = np.arange(G.phi) == G.neg
    th[selfc] = np.pi * (rng.random(selfc.sum()) < 0.5)
    return np.exp(1j * th)


# ------------------------------------------------------------------------------------------------ main tool
def _group_sums(t, inv, ng):
    Tre = np.bincount(inv, weights=t.real, minlength=ng)
    Tim = np.bincount(inv, weights=t.imag, minlength=ng)
    return Tre + 1j * Tim


def decompose(prob: Problem, labels: np.ndarray, a: int, merge_conj: bool = True, n_surr: int = 8,
              rng=None) -> dict:
    """Partial sums of E(a) by group, with cancellation accounting and a random-phase surrogate."""
    G = prob.G
    rng = rng or np.random.default_rng(12345)
    lab = labels.astype(np.int64).copy()
    lab[0] = -1
    if merge_conj:
        lab = merge_conjugates(G, lab)
    keep = lab >= 0
    t = prob.terms(a)[keep]
    keys, inv = np.unique(lab[keep], return_inverse=True)
    ng = keys.size
    T = _group_sums(t, inv, ng)
    at = np.abs(t)
    Ag = np.bincount(inv, weights=at, minlength=ng)
    Vg = np.bincount(inv, weights=at ** 2, minlength=ng)
    size = np.bincount(inv, minlength=ng)
    E = float(T.real.sum())
    A = float(at.sum())
    W = float(np.abs(T).sum())
    # surrogate
    Ws, Es = [], []
    for _ in range(n_surr):
        u = random_phases(G, rng)[keep]
        Ts = _group_sums(at * u, inv, ng)
        Ws.append(np.abs(Ts).sum())
        Es.append(abs(Ts.real.sum()))
    Ws, Es = np.array(Ws), np.array(Es)
    V = float(Vg.sum())
    sdE = float(np.sqrt(V))
    # Gaussian surrogate *conditioned on the observed total E*: T_g ~ N(E V_g/V, V_g (1 - V_g/V)).
    # This is what independent random phases predict for the group sums once the total is known.
    cond_mean = E * Vg / V
    cond_var = Vg * (1 - Vg / V)
    Wc = []
    for _ in range(max(n_surr, 4)):
        Z = rng.normal(0, 1, ng) * np.sqrt(Vg)
        Tc = Z + (E - Z.sum()) * Vg / V
        Wc.append(np.abs(Tc).sum())
    resid = (T.real - cond_mean) ** 2 / np.maximum(cond_var, 1e-300)
    out = dict(a=int(a), E=E, main=prob.main, A=A, W=W, sdE=sdE, ngroups=int(ng),
               W_cond=float(np.mean(Wc)), W_over_Wcond=float(W / np.mean(Wc)),
               chi2_dof=float(resid[cond_var > 0].sum() / max((cond_var > 0).sum() - 1, 1)),
               corr_T_V=float(np.corrcoef(T.real, Vg)[0, 1]) if ng > 2 else float("nan"),
               within=float(np.log(A / W)), across=float(np.log(W / max(abs(E), 1e-300))),
               total=float(np.log(A / max(abs(E), 1e-300))),
               W_surr=float(Ws.mean()) if n_surr else None,
               within_surr=float(np.log(A / Ws.mean())) if n_surr else None,
               across_surr=float(np.mean(np.log(Ws / np.maximum(Es, 1e-300)))) if n_surr else None,
               imag_residual=float(np.abs(T.imag).max()) if merge_conj else None,
               groups=dict(key=keys, size=size, A=Ag, V=Vg, T=T.real if merge_conj else T,
                           z=T.real / np.sqrt(np.maximum(Vg, 1e-300))))
    return out


def partial_sums_all_a(prob: Problem, labels: np.ndarray, merge_conj: bool = True, max_groups: int = 400):
    """T_g(a) for every group g and every a (one inverse FFT per group). Returns (keys, M) with M[g, flat a].

    Use for groupings with few groups (orders, conductors, quantiles, parity)."""
    G = prob.G
    lab = labels.astype(np.int64).copy()
    lab[0] = -1
    if merge_conj:
        lab = merge_conjugates(G, lab)
    keys = np.unique(lab[lab >= 0])
    if keys.size > max_groups:
        raise ValueError(f"{keys.size} groups > max_groups; use decompose() per a instead")
    M = np.empty((keys.size, G.phi))
    for i, k in enumerate(keys):
        Tk = np.where(lab == k, prob.T, 0)
        M[i] = inverse(G, Tk).real
    return keys, M


def allocation(prob: Problem, labels: np.ndarray, a_list, merge_conj: bool = True) -> dict:
    """Share of E(a) carried by each group, compared with the Gaussian-conditional share V_g/V
    (what independent random phases predict for a large deviation) and the L1 share A_g/A
    (what a uniform phase bias would give)."""
    rows = [decompose(prob, labels, a, merge_conj, n_surr=0) for a in a_list]
    g = rows[0]["groups"]
    Tsum = np.sum([r["groups"]["T"] for r in rows], axis=0)
    Esum = sum(r["E"] for r in rows)
    return dict(key=g["key"], size=g["size"], share=Tsum / Esum, share_gauss=g["V"] / g["V"].sum(),
                share_L1=g["A"] / g["A"].sum(), E_mean=Esum / len(rows))


def coset_profile(prob: Problem, spec: str, a: int, n_surr: int = 4, rng=None) -> dict:
    """Xie's decomposition for H given by spec: within-coset vs across-coset cancellation at a.

    For chi in a coset chi H^perp the coset sum equals (1/|H|) sum_{h in H} N(ah) conj(xi(h)) (xi = chi|_H),
    the twisted count of the coset aH."""
    G = prob.G
    gens, order = G.subgroup_gens(spec)
    lab = G.subgroup_labels(gens)
    d = decompose(prob, lab, a, merge_conj=True, n_surr=n_surr, rng=rng)
    d["H_order"] = int(np.unique(lab).size)
    d["Hperp_size"] = G.phi // d["H_order"]
    return d
