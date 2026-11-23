"""The unit group G = (Z/mZ)^* as a product of cyclic groups, and its characters.

Conventions (identical to compute/src/eos_char.c, extended to non-cyclic G):

* G is written as prod_i C_{n_i} via CRT over the prime powers q_i || m. Each odd q = p^k gives one cyclic
  factor with a primitive root g; 4 gives C_2 = <-1>; 2^k (k >= 3) gives C_2 x C_{2^{k-2}} = <-1> x <5>.
  e(x) = (e_1(x), ..., e_r(x)) is the exponent vector ("discrete log") of a unit x.
* The grid index of x is the C-order flat index of e(x) in an array of shape (n_1, ..., n_r).
* Characters are indexed by j in the same grid:  chi_j(x) = exp(-2 pi i sum_i j_i e_i(x) / n_i).
  Hence numpy.fft.fftn(f)[j] = sum_x f(x) chi_j(x) = S(chi_j), and chi_0 is the principal character.
  conj(chi_j) = chi_{-j}.
* For a fraction-valued phase we use integers mod L = lcm(n_i):  chi_j(x) = exp(-2 pi i F_j(x) / L).
"""
from __future__ import annotations

import math
from functools import reduce

import numpy as np


# ----------------------------------------------------------------------------------------------- arithmetic
def factorize(n: int) -> list:
    """Trial-division factorisation; returns [(p, k), ...] sorted by p."""
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            k = 0
            while n % d == 0:
                n //= d
                k += 1
            out.append((d, k))
        d += 1 if d == 2 else 2
    if n > 1:
        out.append((n, 1))
    return out


def _powers(g: int, n: int, q: int) -> np.ndarray:
    """Array [g^0, g^1, ..., g^{n-1}] mod q, vectorised in sqrt(n) blocks (q < 3e9)."""
    B = int(math.isqrt(n)) + 1
    small = np.empty(B, dtype=np.int64)
    x = 1
    for i in range(B):
        small[i] = x
        x = x * g % q
    gB = x
    nb = (n + B - 1) // B
    big = np.empty(nb, dtype=np.int64)
    y = 1
    for i in range(nb):
        big[i] = y
        y = y * gB % q
    return ((big[:, None] * small[None, :]) % q).ravel()[:n]


def primitive_root_prime_power(p: int, k: int) -> int:
    """A generator of (Z/p^k)^* for odd p."""
    fac = [f for f, _ in factorize(p - 1)]
    g = 2
    while any(pow(g, (p - 1) // f, p) == 1 for f in fac):
        g += 1
    if k >= 2 and pow(g, p - 1, p * p) == 1:
        g += p
    return g


def _vp(x: np.ndarray, p: int, cap: int) -> np.ndarray:
    """p-adic valuation of nonzero entries, capped at cap (zeros get cap)."""
    v = np.zeros(x.shape, dtype=np.int64)
    y = x.copy()
    for _ in range(cap):
        mask = (y % p == 0)
        if not mask.any():
            break
        v += mask
        y = np.where(mask, y // p, y)
    return np.minimum(v, cap)


class _Comp:
    """One cyclic factor C_n of G, living in (Z/q)^*."""

    def __init__(self, p, k, q, n, role, table, gen_mod_q):
        self.p, self.k, self.q, self.n, self.role = p, k, q, n, role
        self.table = table          # residue mod q -> exponent (-1 for non-units)
        self.gen_mod_q = gen_mod_q  # residue mod q of the generator of this factor


# ----------------------------------------------------------------------------------------------- the group
class UnitGroup:
    """(Z/mZ)^* with discrete logs, grid layout and character attributes.

    Main attributes
      m, phi, shape (n_1..n_r), L (exponent of G)
      flat_of_res[x]   grid index of the unit x (-1 for non-units), length m
      res_of_flat[i]   unit at grid index i, length phi
      neg[j]           flat index of the conjugate character -j
    Character attributes (arrays over flat j, computed lazily): order, conductor, parity (chi(-1)).
    """

    def __init__(self, m: int):
        if m < 3:
            raise ValueError("m >= 3 required")
        self.m = int(m)
        self.factors = factorize(self.m)
        comps = []
        for p, k in self.factors:
            q = p ** k
            if p == 2:
                if k == 1:
                    continue
                if k == 2:
                    tab = np.full(4, -1, dtype=np.int64)
                    tab[1], tab[3] = 0, 1
                    comps.append(_Comp(2, 2, 4, 2, "2^2", tab, 3))
                    continue
                n5 = q // 4
                pw = _powers(5, n5, q)
                ts = np.full(q, -1, dtype=np.int64)
                tt = np.full(q, -1, dtype=np.int64)
                ts[pw] = 0
                ts[(q - pw) % q] = 1
                tt[pw] = np.arange(n5)
                tt[(q - pw) % q] = np.arange(n5)
                comps.append(_Comp(2, k, q, 2, "2sign", ts, q - 1))
                comps.append(_Comp(2, k, q, n5, "2five", tt, 5))
            else:
                g = primitive_root_prime_power(p, k)
                n = q // p * (p - 1)
                pw = _powers(g, n, q)
                tab = np.full(q, -1, dtype=np.int64)
                tab[pw] = np.arange(n)
                comps.append(_Comp(p, k, q, n, "odd", tab, g))
        self.comps = comps
        self.shape = tuple(c.n for c in comps) if comps else (1,)
        self.r = len(self.shape)
        self.phi = int(np.prod(self.shape))
        self.L = int(reduce(math.lcm, self.shape, 1))
        self.cyclic = (self.r == 1)

        x = np.arange(self.m, dtype=np.int64)
        unit = np.gcd(x, self.m) == 1
        self.units = x[unit]
        ex = self.exps(self.units)
        flat = np.ravel_multi_index(tuple(ex.T), self.shape)
        self.flat_of_res = np.full(self.m, -1, dtype=np.int64)
        self.flat_of_res[self.units] = flat
        self.res_of_flat = np.empty(self.phi, dtype=np.int64)
        self.res_of_flat[flat] = self.units
        assert len(self.units) == self.phi

        jv = self.jvec
        negv = (-jv) % np.array(self.shape)
        self.neg = np.ravel_multi_index(tuple(negv.T), self.shape)
        self._order = self._conductor = self._parity = None
        self._inv = None

    # ------------------------------------------------------------------------------------------ elements
    def exps(self, x) -> np.ndarray:
        """Exponent vectors (len(x), r) of units x (array of residues)."""
        x = np.asarray(x, dtype=np.int64) % self.m
        out = np.empty((x.size, self.r), dtype=np.int64)
        for i, c in enumerate(self.comps):
            out[:, i] = c.table[x % c.q]
        if (out < 0).any():
            raise ValueError("non-unit passed to exps")
        return out

    @property
    def jvec(self) -> np.ndarray:
        """(phi, r) array of character indices j in flat order (cached)."""
        if getattr(self, "_jvec", None) is None:
            self._jvec = np.indices(self.shape).reshape(self.r, -1).T.astype(np.int64)
        return self._jvec

    def generators(self) -> list:
        """Residues mod m of the generators of the cyclic factors (unit exponent vectors)."""
        out = []
        for i in range(self.r):
            e = [0] * self.r
            e[i] = 1
            out.append(int(self.res_of_flat[np.ravel_multi_index(tuple(e), self.shape)]))
        return out

    def inverse_table(self) -> np.ndarray:
        """inv[x] = x^{-1} mod m for units, 0 otherwise."""
        if self._inv is None:
            inv = np.zeros(self.m, dtype=np.int64)
            fl = self.flat_of_res[self.units]
            negf = self.neg[fl]          # exponent -e(x) has the same flat index as character -j
            inv[self.units] = self.res_of_flat[negf]
            self._inv = inv
        return self._inv

    # ------------------------------------------------------------------------------------------ characters
    def char_frac(self, x: int) -> np.ndarray:
        """Integer array F_j(x) mod L for all j, with chi_j(x) = exp(-2 pi i F_j(x)/L)."""
        e = self.exps([x])[0]
        acc = np.zeros(self.phi, dtype=np.int64)
        jv = self.jvec if self.r > 1 else None
        for i, n in enumerate(self.shape):
            c = (int(e[i]) * (self.L // n)) % self.L
            if c == 0:
                continue
            ji = jv[:, i] if jv is not None else np.arange(self.phi, dtype=np.int64)
            acc = (acc + ji * c) % self.L
        return acc

    def chi(self, x: int) -> np.ndarray:
        """chi_j(x) for all j."""
        return np.exp(-2j * np.pi * self.char_frac(x) / self.L)

    def chibar(self, x: int) -> np.ndarray:
        """conj(chi_j(x)) for all j."""
        return np.exp(2j * np.pi * self.char_frac(x) / self.L)

    @property
    def order(self) -> np.ndarray:
        if self._order is None:
            jv = self.jvec
            o = np.ones(self.phi, dtype=np.int64)
            for i, n in enumerate(self.shape):
                o = np.lcm(o, n // np.gcd(jv[:, i], n))
            self._order = o
        return self._order

    @property
    def parity(self) -> np.ndarray:
        """chi_j(-1) in {+1, -1}."""
        if self._parity is None:
            f = self.char_frac(self.m - 1)
            self._parity = np.where(f == 0, 1, -1).astype(np.int64)
        return self._parity

    @property
    def conductor(self) -> np.ndarray:
        if self._conductor is None:
            jv = self.jvec
            cond = np.ones(self.phi, dtype=np.int64)
            for i, c in enumerate(self.comps):
                ji = jv[:, i]
                if c.role == "odd":
                    v = _vp(ji, c.p, c.k - 1)
                    e = np.where(ji == 0, 0, c.k - v)
                    cond *= c.p ** e
                elif c.role == "2^2":
                    cond *= np.where(ji == 0, 1, 4)
                elif c.role == "2sign":
                    js = ji
                    jt = jv[:, i + 1]
                    v = _vp(jt, 2, c.k - 2)
                    e = np.where(jt == 0, np.where(js == 0, 0, 2), c.k - v)
                    cond *= 2 ** e
                # "2five" handled together with "2sign"
            self._conductor = cond
        return self._conductor

    # ------------------------------------------------------------------------------------------ subgroups
    def subgroup_labels(self, gens) -> np.ndarray:
        """Label each character by its restriction to H = <gens>. Equal labels <=> same coset of H^perp.

        Returns int labels 0..|H|-1 (the number of distinct labels equals |H|)."""
        cols = [self.char_frac(int(h)) for h in gens]
        if not cols:
            return np.zeros(self.phi, dtype=np.int64)
        M = np.stack(cols, axis=1)
        _, lab = np.unique(M, axis=0, return_inverse=True)
        return lab.ravel().astype(np.int64)

    def subgroup_gens(self, spec: str, rng=None) -> tuple:
        """Generators and order of a subgroup H from a spec string.

        'pow:d'      H = G^d (d-th powers); H^perp = characters of order dividing d.
        'mod:m1'     H = {x = 1 mod m1} (m1 | m); H^perp = characters of conductor dividing m1.
        'gens:a,b,..' H generated by the given residues.
        """
        kind, _, arg = spec.partition(":")
        if kind == "pow":
            d = int(arg)
            gens = [pow(g, d, self.m) for g in self.generators()]
            order = int(np.prod([n // math.gcd(n, d) for n in self.shape]))
            return gens, order
        if kind == "mod":
            m1 = int(arg)
            if self.m % m1:
                raise ValueError("m1 must divide m")
            phi1 = UnitGroup(m1).phi if m1 >= 3 else 1
            order = self.phi // phi1
            rng = rng or np.random.default_rng(0)
            gens = []
            while True:
                for _ in range(2 * self.r + 4):
                    while True:
                        y = 1 + m1 * int(rng.integers(0, self.m // m1))
                        if math.gcd(y, self.m) == 1:
                            break
                    gens.append(y % self.m)
                if len(np.unique(self.subgroup_labels(gens))) == order:
                    return gens, order
        if kind == "gens":
            gens = [int(s) % self.m for s in arg.split(",")]
            return gens, None
        raise ValueError(f"unknown subgroup spec {spec}")

    def __repr__(self):
        return f"UnitGroup(m={self.m}, phi={self.phi}, shape={self.shape})"
