"""phaselab: where does the phase cancellation in E(a) = (1/phi) sum_{chi != chi0} conj(chi(a)) S(chi)^2 come from?

Modules
  group     UnitGroup(m): discrete logs on (Z/m)^* = prod C_{n_i}, characters, order/conductor/parity, subgroups
  sets      weight vectors: primes (weights 1, log p, Cesaro; any range X), integers, barrier objects
  core      Problem: N(a) = (1/phi) sum conj(chi(a)) prod_k S_k(chi) for products of (conjugated) sets
  decomp    groupings of characters and the within/across cancellation accounting, Xie coset sums
  phases    phase harmonics/histograms at a, psi-shift phase correlations, moments of E(b)
  dynamics  S_X(chi) as X runs (phase winding, decorrelation, coherence of chi and chi psi)
  blocks    route A / H4 block statistics delta_I(c)
  objects   the standard catalogue (P, barriers, toy) used by the CLI
See compute/lab/README.md.
"""
from .group import UnitGroup, factorize
from .core import Problem, fourier, inverse, binary, conjugate
from . import sets, decomp, phases, dynamics, blocks

__all__ = ["UnitGroup", "factorize", "Problem", "fourier", "inverse", "binary", "conjugate",
           "sets", "decomp", "phases", "dynamics", "blocks"]
