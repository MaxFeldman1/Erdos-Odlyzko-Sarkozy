"""Weight vectors on Z/mZ: the primes and the barrier objects.

Every constructor returns a float64 array w of length m indexed by residue (w[x] = total weight of the
residue class x; only units are used). Weights for integers > m accumulate in their residue class, so the
range X > m is supported directly.

Barrier objects (notes/01-parseval-wall.md, notes/routes/A-typeII.md):
  redacted(G, wP, a)          P minus {p : a p^-1 in P}             N(a) = 0, density rho(1 - rho)
  redacted_half(G, wP, a)     remove only the larger element of each pair {p, a p^-1} in P   N(a) = 0
  pairing_avoiding(G, a, d)   random set with at most one element of each pair {x, a x^-1}   N(a) = 0
  random_subset(G, d)         uniformly random set of density d (null model)
  astar(G, wP, a, D)          route A's P* = a (A*)^-1, A* = boosted D-rough composites, no primes > D
  The conjugate problem (|S|^2, a = -1) is not a set: build it with core.Problem(conj=[False, True]).
"""
from __future__ import annotations

import math

import numpy as np


# ----------------------------------------------------------------------------------------------- sieves
def prime_mask(N: int) -> np.ndarray:
    """Boolean array isp[0..N]."""
    N = int(N)
    isp = np.ones(N + 1, dtype=bool)
    isp[:2] = False
    isp[4::2] = False
    for i in range(3, math.isqrt(N) + 1, 2):
        if isp[i]:
            isp[i * i::2 * i] = False
    return isp


def primes_upto(N: int) -> np.ndarray:
    return np.nonzero(prime_mask(N))[0].astype(np.int64)


def _weights(ns: np.ndarray, X: float, weight: str) -> np.ndarray:
    """weight is '1', 'log', 'cesaro', or a '*'-product such as 'log*cesaro'."""
    w = np.ones(ns.size)
    for part in weight.split("*"):
        part = part.strip()
        if part in ("1", "", "unit"):
            continue
        if part == "log":
            w *= np.log(ns)
        elif part == "cesaro":
            w *= 1.0 - ns / float(X)
        else:
            raise ValueError(f"unknown weight {part}")
    return w


# ----------------------------------------------------------------------------------------------- primes
def prime_weights(m: int, X: float = None, weight: str = "1") -> np.ndarray:
    """w[x] = sum_{p <= X, p prime, p not | m, p = x mod m} w(p)."""
    X = m if X is None else X
    ps = primes_upto(int(X))
    ps = ps[m % ps != 0]
    return np.bincount(ps % m, weights=_weights(ps, X, weight), minlength=m)


def integer_weights(m: int, Y: float, weight: str = "1") -> np.ndarray:
    """w[x] = #{1 <= n <= Y : (n, m) = 1, n = x mod m} (the smooth toy uses Y = sqrt(m))."""
    ns = np.arange(1, int(Y) + 1, dtype=np.int64)
    ns = ns[np.gcd(ns, m) == 1]
    return np.bincount(ns % m, weights=_weights(ns, Y, weight), minlength=m)


def subset_weights(m: int, residues) -> np.ndarray:
    """Indicator of an arbitrary set of residues (duplicates add up)."""
    r = np.asarray(residues, dtype=np.int64) % m
    return np.bincount(r, minlength=m).astype(float)


# ----------------------------------------------------------------------------------------------- barriers
def redacted(G, wP: np.ndarray, a: int) -> np.ndarray:
    """P minus {p : a p^-1 in P}. Both elements of every pair with product a are removed."""
    inv = G.inverse_table()
    x = G.units
    partner = (a * inv[x]) % G.m
    w = wP.copy()
    kill = x[(wP[x] > 0) & (wP[partner] > 0)]
    w[kill] = 0
    return w


def redacted_half(G, wP: np.ndarray, a: int) -> np.ndarray:
    """Remove from each pair {p, q} in P with pq = a only the larger residue (and fixed points p^2 = a)."""
    inv = G.inverse_table()
    x = G.units
    partner = (a * inv[x]) % G.m
    w = wP.copy()
    kill = x[(wP[x] > 0) & (wP[partner] > 0) & (x >= partner)]
    w[kill] = 0
    return w


def random_subset(G, density: float, rng) -> np.ndarray:
    w = np.zeros(G.m)
    x = G.units
    w[x[rng.random(x.size) < density]] = 1.0
    return w


def pairing_avoiding(G, a: int, density: float, rng) -> np.ndarray:
    """Random set containing at most one element of each pair {x, a x^-1}; fixed points x^2 = a excluded.

    Each pair is used with probability density*phi/#pairs and then one of its two elements is chosen."""
    inv = G.inverse_table()
    x = G.units
    y = (a * inv[x]) % G.m
    lo = x[x < y]
    hi = y[x < y]
    npairs = lo.size
    pin = min(1.0, density * G.phi / npairs)
    use = rng.random(npairs) < pin
    pick_hi = rng.random(npairs) < 0.5
    chosen = np.where(pick_hi, hi, lo)[use]
    w = np.zeros(G.m)
    w[chosen] = 1.0
    return w


def astar(G, wP: np.ndarray, a: int, D: float = None, rng=None, return_A=False):
    """Route A's barrier (notes/routes/A-typeII.md, Theorem B, simplified as in typeII_vaughan.py).

    A* is a random subset of {1 <= n < m, (n, m) = 1}: probability rho on ordinary n, 0 on primes > D,
    rho(1 + kappa) on D-rough composites (all prime factors > D), kappa = #{primes > D}/#{rough composites},
    so that |A*| ~ |P| and A* has the Type I data of A_a to level D. Returns w for P* = a (A*)^-1 in G.
    The bilinear count #{p in P, x in P* : p x = a} = #{primes in A*} is O(pi(D))."""
    m = G.m
    rng = rng or np.random.default_rng(0)
    D = D if D is not None else m ** (1.0 / 3.0)
    rho = wP[G.units].astype(bool).sum() / G.phi
    isp = prime_mask(m)[:m]
    n = np.arange(m, dtype=np.int64)
    unit = np.gcd(n, m) == 1
    rough = unit.copy()
    rough[:2] = False
    for p in primes_upto(int(D)):
        rough[p::p] = False
    big = isp & (n > D) & unit
    rc = rough & ~isp
    kappa = big.sum() / max(rc.sum(), 1)
    prob = np.where(unit, rho, 0.0)
    prob[rc] = rho * (1 + kappa)
    prob[big] = 0.0
    prob[0] = 0.0
    A = n[rng.random(m) < prob]
    inv = G.inverse_table()
    Pstar = (a * inv[A]) % m
    w = np.bincount(Pstar, minlength=m).astype(float)
    return (w, A) if return_A else w


def density_of(G, w: np.ndarray) -> float:
    return float((w[G.units] > 0).sum()) / G.phi
