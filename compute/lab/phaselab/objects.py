"""The standard catalogue of objects compared by the lab.

catalogue(m, a, ...) returns an ordered dict name -> Obj(problem, a_target, description). The barrier objects are
built for the class a; 'conj' always uses a = -1 (odd m), and 'P' uses the given a (see also P.worst_a()).
"""
from __future__ import annotations

import math
from collections import OrderedDict
from dataclasses import dataclass

import numpy as np

from . import sets
from .core import Problem
from .group import UnitGroup


@dataclass
class Obj:
    prob: Problem
    a: int
    desc: str


DESCRIPTIONS = {
    "P": "primes p <= X (X = m by default), binary count pq = a",
    "P_worst": "primes, at the class a minimising N(a)",
    "conj": "conjugate problem |S|^2 at a = -1: N(-1) = #{p + q = m}",
    "redacted": "P minus {p : a/p in P} (both elements of each pair removed)",
    "redacted_half": "P minus the larger element of each pair {p, a/p}",
    "pairing": "random set, at most one element of each pair {x, a/x}, density rho",
    "random": "uniformly random set of density rho (null model, N(a) > 0)",
    "astar": "route A's A*: bilinear count P x P*, P* = a (A*)^-1, A* without primes > m^(1/3)",
    "toy": "smooth toy: n1 n2 n3 n4 = a with n_i <= sqrt(m), coefficients (sum_{n <= sqrt m} chi(n))^4",
}


def catalogue(m: int, a: int = None, X: float = None, weight: str = "1", seed: int = 1, which=None,
              G: UnitGroup = None) -> "OrderedDict[str, Obj]":
    G = G or UnitGroup(m)
    rng = np.random.default_rng(seed)
    if a is None:
        a = int(G.units[rng.integers(0, G.phi)])
    if math.gcd(a, m) != 1:
        raise ValueError("a must be a unit")
    which = which or ["P", "P_worst", "conj", "redacted", "redacted_half", "pairing", "random", "astar", "toy"]
    wP = sets.prime_weights(m, X, weight)
    rho = sets.density_of(G, wP)
    out = OrderedDict()
    P = Problem(G, [wP, wP], name="P")
    for name in which:
        if name == "P":
            out[name] = Obj(P, a, DESCRIPTIONS[name])
        elif name == "P_worst":
            out[name] = Obj(P, int(P.worst_a()[0]), DESCRIPTIONS[name])
        elif name == "conj":
            if m % 2:
                out[name] = Obj(Problem(G, [wP, wP], conj=[False, True], name=name), m - 1, DESCRIPTIONS[name])
        elif name == "redacted":
            w = sets.redacted(G, wP, a)
            out[name] = Obj(Problem(G, [w, w], name=name), a, DESCRIPTIONS[name])
        elif name == "redacted_half":
            w = sets.redacted_half(G, wP, a)
            out[name] = Obj(Problem(G, [w, w], name=name), a, DESCRIPTIONS[name])
        elif name == "pairing":
            w = sets.pairing_avoiding(G, a, rho, rng)
            out[name] = Obj(Problem(G, [w, w], name=name), a, DESCRIPTIONS[name])
        elif name == "random":
            w = sets.random_subset(G, rho, rng)
            out[name] = Obj(Problem(G, [w, w], name=name), a, DESCRIPTIONS[name])
        elif name == "astar":
            w = sets.astar(G, wP, a, rng=rng)
            out[name] = Obj(Problem(G, [wP, w], name=name), a, DESCRIPTIONS[name])
        elif name == "toy":
            wI = sets.integer_weights(m, math.isqrt(m))
            T = Problem(G, [wI] * 4, name=name)
            out[name] = Obj(T, int(T.worst_a()[0]), DESCRIPTIONS[name])
        else:
            raise ValueError(name)
    return out
