"""Fourier transforms on G and the counting problem N(a) = (1/phi) sum_chi conj(chi(a)) prod_k S_k(chi).

A Problem is a list of weight vectors w_1..w_K on Z/mZ, each optionally conjugated:
  T(chi) = prod_k S_k(chi)   (or conj(S_k(chi)) where conj[k] is True),  S_k(chi) = sum_x w_k(x) chi(x).
  N(a)   = (1/phi) sum_chi conj(chi(a)) T(chi)
         = sum over x_1...x_K with x_1^{+-1} ... x_K^{+-1} = a of prod w_k(x_k).
Examples
  primes, binary:           Problem(G, [wP, wP])                     N(a) = #{pq = a}
  conjugate problem:        Problem(G, [wP, wP], conj=[False, True]) N(b) = #{p q^-1 = b}; use b = -1
  bilinear (route A's A*):  Problem(G, [wP, wPstar])
  smooth toy:               Problem(G, [wI]*4), wI = integers <= sqrt(m)
E(a) = N(a) - main, main = T(chi_0)/phi. terms(a)[j] = conj(chi_j(a)) T(chi_j)/phi, so E(a) = sum_{j != 0} terms.
"""
from __future__ import annotations

import numpy as np

from .group import UnitGroup


def fourier(G: UnitGroup, w: np.ndarray) -> np.ndarray:
    """S(chi_j) for all j (flat complex array of length phi) via one FFT on the discrete-log grid."""
    grid = np.zeros(G.phi)
    grid[G.flat_of_res[G.units]] = w[G.units]
    return np.fft.fftn(grid.reshape(G.shape)).ravel()


def inverse(G: UnitGroup, T: np.ndarray) -> np.ndarray:
    """(1/phi) sum_j conj(chi_j(a)) T_j for every a, returned on the flat grid (index = G.flat_of_res[a])."""
    return np.fft.ifftn(T.reshape(G.shape)).ravel()


class Problem:
    def __init__(self, G: UnitGroup, factors, conj=None, name: str = ""):
        self.G = G
        self.name = name
        self.K = len(factors)
        conj = conj or [False] * self.K
        self.conj = list(conj)
        self.weights = list(factors)
        self.spectra = [fourier(G, w) for w in factors]
        T = np.ones(G.phi, dtype=complex)
        for s, c in zip(self.spectra, self.conj):
            T = T * (np.conj(s) if c else s)
        self.T = T
        self._N = None

    # -------------------------------------------------------------------------------------- basic numbers
    @property
    def phi(self):
        return self.G.phi

    @property
    def main(self) -> float:
        """Principal-character term mu = T(chi_0)/phi (= |P|^2/phi for the binary prime problem)."""
        return float(self.T[0].real) / self.phi

    @property
    def size(self) -> np.ndarray:
        """|T(chi)|^(1/K): the common 'size' |S(chi)| used for quantile groupings."""
        return np.abs(self.T) ** (1.0 / self.K)

    def N_flat(self) -> np.ndarray:
        """N(a) for all a, indexed by flat grid index."""
        if self._N is None:
            self._N = inverse(self.G, self.T).real
        return self._N

    def N_res(self) -> np.ndarray:
        """N(a) indexed by residue a (NaN at non-units)."""
        out = np.full(self.G.m, np.nan)
        out[self.G.res_of_flat] = self.N_flat()
        return out

    def N(self, a: int) -> float:
        return float(self.N_flat()[self.G.flat_of_res[a % self.G.m]])

    def E(self, a: int) -> float:
        return self.N(a) - self.main

    def terms(self, a: int) -> np.ndarray:
        """conj(chi_j(a)) T_j / phi for all j (j = 0 included; it is the main term)."""
        return self.G.chibar(a % self.G.m) * self.T / self.phi

    def parseval_mass(self) -> float:
        """A = sum_{chi != chi0} |T(chi)|/phi: the triangle-inequality bound for |E(a)| (the wall)."""
        return float(np.abs(self.T[1:]).sum() / self.phi)

    def rms_E(self) -> float:
        """sqrt(mean_a E(a)^2) = sqrt(sum_{chi != chi0} |T|^2)/phi (Parseval in a)."""
        return float(np.sqrt((np.abs(self.T[1:]) ** 2).sum()) / self.phi)

    def worst_a(self, k: int = 1) -> np.ndarray:
        """Residues of the k smallest N(a)."""
        idx = np.argsort(self.N_flat())[:k]
        return self.G.res_of_flat[idx]

    def with_point_mass(self, a: int, c: float, name: str = None) -> "Problem":
        """A copy with N(a) replaced by N(a) + c, i.e. T(chi) -> T(chi) + c chi(a).

        Used to 'repair' a barrier (c = main - N(a)) and test whether anything except the spike at a
        distinguishes it from P."""
        new = object.__new__(Problem)
        new.__dict__.update(self.__dict__)
        new.T = self.T + c * self.G.chi(a % self.G.m)
        new._N = None
        new.name = name or (self.name + "+spike")
        return new

    def summary(self) -> dict:
        N = self.N_flat()
        mu = self.main
        E = N - mu
        sd = E.std()
        return dict(name=self.name, m=self.G.m, phi=self.phi, main=mu, parseval_mass=self.parseval_mass(),
                    rms_E=self.rms_E(), minN_over_main=float(N.min() / mu) if mu else float("nan"),
                    argmin=int(self.G.res_of_flat[int(np.argmin(N))]),
                    skew=float(((E / sd) ** 3).mean()) if sd else 0.0,
                    kurt=float(((E / sd) ** 4).mean()) if sd else 0.0,
                    max_size_over_rms=float(self.size[1:].max() / np.sqrt((self.size[1:] ** 2).mean())))


def binary(G: UnitGroup, w: np.ndarray, name: str = "") -> Problem:
    return Problem(G, [w, w], name=name)


def conjugate(G: UnitGroup, w: np.ndarray, name: str = "conj") -> Problem:
    return Problem(G, [w, w], conj=[False, True], name=name)
