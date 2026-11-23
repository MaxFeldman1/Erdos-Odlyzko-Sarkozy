"""Phase dynamics in X: S_X(chi) = sum_{n <= X, n in set} w(n) chi(n) as X runs.

trajectories(G, ns, js, Xgrid, weight)  complex array (len(js), len(Xgrid)); ns = sorted integers (e.g. primes),
                                        weight '1' | 'log' | 'cesaro' | 'log*cesaro' (Cesaro weights 1 - n/X are
                                        handled exactly with two cumulative sums).
phase_rate(traj, Xgrid)                 unwrapped arg S_X^2 against t = log X: mean angular speed and the
                                        decorrelation of u(t) = S^2/|S^2| in t.
cross_corr(traj_a, traj_b)              mean over t of Re(u_a conj(u_b)) (phase coherence of chi and chi psi in X)
cramer(m, Xmax, rng)                    Cramer random model: n coprime to m kept with probability 1/log n.
"""
from __future__ import annotations

import numpy as np


def char_values(G, ns: np.ndarray, j: int) -> np.ndarray:
    """chi_j(n) for integers n (units mod m)."""
    ex = G.exps(ns % G.m)
    jv = G.jvec[j] if G.r > 1 else np.array([j])
    F = np.zeros(ns.size, dtype=np.int64)
    for i, n in enumerate(G.shape):
        c = (int(jv[i]) * (G.L // n)) % G.L
        F = (F + ex[:, i] * c) % G.L
    return np.exp(-2j * np.pi * F / G.L)


def trajectories(G, ns: np.ndarray, js, Xgrid: np.ndarray, weight: str = "1", w0=None) -> np.ndarray:
    ns = np.asarray(ns, dtype=np.int64)
    ns = ns[np.gcd(ns, G.m) == 1]
    base = np.ones(ns.size) if w0 is None else w0
    parts = weight.split("*")
    if "log" in parts:
        base = base * np.log(ns)
    ces = "cesaro" in parts
    pos = np.searchsorted(ns, Xgrid, side="right")      # number of n <= X
    out = np.empty((len(js), len(Xgrid)), dtype=complex)
    for r, j in enumerate(js):
        c = char_values(G, ns, int(j)) * base
        A = np.concatenate([[0], np.cumsum(c)])[pos]
        if ces:
            B = np.concatenate([[0], np.cumsum(c * ns)])[pos]
            out[r] = A - B / Xgrid
        else:
            out[r] = A
    return out


def phase_rate(traj: np.ndarray, Xgrid: np.ndarray, lags=(0.05, 0.1, 0.2, 0.5, 1.0)) -> dict:
    """Per trajectory: total winding of arg S^2 per unit log X, and phase autocorrelation at lags in log X."""
    t = np.log(Xgrid)
    dt = np.diff(t).mean()
    u = traj ** 2
    u = u / np.maximum(np.abs(u), 1e-300)
    ph = np.unwrap(np.angle(u), axis=1)
    speed = (ph[:, -1] - ph[:, 0]) / (t[-1] - t[0])
    absspeed = np.abs(np.diff(ph, axis=1)).sum(axis=1) / (t[-1] - t[0])
    ac = {}
    for L in lags:
        k = max(1, int(round(L / dt)))
        ac[L] = float(np.real(u[:, k:] * np.conj(u[:, :-k])).mean())
    return dict(speed=speed, abs_speed=absspeed, autocorr=ac)


def cross_corr(ta: np.ndarray, tb: np.ndarray) -> float:
    ua = ta ** 2 / np.maximum(np.abs(ta) ** 2, 1e-300)
    ub = tb ** 2 / np.maximum(np.abs(tb) ** 2, 1e-300)
    return float(np.real(ua * np.conj(ub)).mean())


def cramer(m: int, Xmax: int, rng) -> np.ndarray:
    n = np.arange(3, int(Xmax) + 1, dtype=np.int64)
    keep = rng.random(n.size) < 1.0 / np.log(n)
    n = n[keep]
    return n[np.gcd(n, m) == 1]


def log_grid(X0: float, X1: float, n: int) -> np.ndarray:
    return np.unique(np.round(np.exp(np.linspace(np.log(X0), np.log(X1), n))).astype(np.int64)).astype(float)
