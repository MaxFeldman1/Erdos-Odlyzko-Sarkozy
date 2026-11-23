"""Route A / H4 block statistics (notes/routes/A-typeII.md section 6, notes/brainstorm/r3-synthesis.md).

For a block I of primes u in (M, M2] (u not dividing m) and a set U on G (P or a barrier object):
  nu_I(c)    = #{u in I : c u^-1 in U}          (computed for all c at once by FFT)
  delta_I(c) = nu_I(c) - |U||I|/phi
block_moments returns sum_c delta^2, the kurtosis phi sum delta^4/(sum delta^2)^2 (Gaussian: 3), the H4 ratio
sum_c delta^4 / (phi (rho|I|)^4), and the route A arc statistic
  arc(a) = sum_{k <= K} delta_I(a k^-1)^2 / (K (rho|I|)^2),  K = m/M,
which route A identifies as the place where its barrier A* fails.
"""
from __future__ import annotations

import numpy as np

from .core import Problem
from .sets import primes_upto


def block_weights(G, M: float, M2: float) -> tuple:
    """Indicator of the primes u in (M, M2], u not dividing m, and their number."""
    ps = primes_upto(int(M2))
    ps = ps[(ps > M) & (G.m % ps != 0)]
    return np.bincount(ps % G.m, minlength=G.m).astype(float), ps.size


def block_moments(G, wU: np.ndarray, M: float, M2: float = None, a: int = None, K: int = None) -> dict:
    M2 = 2 * M if M2 is None else M2
    wI, nI = block_weights(G, M, M2)
    pr = Problem(G, [wU, wI])          # N(c) = #{x in U, u in I : x u = c} = #{u in I : c u^-1 in U}
    nu = pr.N_flat()
    delta = nu - pr.main
    s2 = (delta ** 2).sum()
    s4 = (delta ** 4).sum()
    rho = (wU[G.units] > 0).sum() / G.phi
    out = dict(M=M, M2=M2, nI=nI, mean_nu=pr.main, var_ratio=s2 / (G.phi * pr.main),
               kurt=G.phi * s4 / s2 ** 2, H4_ratio=s4 / (G.phi * (rho * nI) ** 4),
               max_abs_delta=float(np.abs(delta).max() / (rho * nI)))
    if a is not None:
        K = int(G.m // M) if K is None else K
        ks = np.arange(1, K + 1)
        ks = ks[np.gcd(ks, G.m) == 1]
        inv = G.inverse_table()
        c = (a * inv[ks]) % G.m
        d = delta[G.flat_of_res[c]]
        out["arc"] = float((d ** 2).sum() / (ks.size * (rho * nI) ** 2))
        out["arc_random"] = float(s2 / G.phi / (rho * nI) ** 2)
    return out
