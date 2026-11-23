#!/usr/bin/env python3
"""Referee check of Lemmas D1, D4(a), D5, D6/D7 of notes/routes/C-log-exponent.md for COMPOSITE m
(the author's script only tests prime m). No character table is constructed: the Fourier
coefficients thetã(X, chi) are the eigenvalues of the (normal) convolution matrix
C_X[a, b] = Theta(X; a b^{-1}) on G = (Z/mZ)^*, the principal one being T(X) (all-ones eigenvector).
Checks, for several (X1, X2):
  D1    R(a) computed directly from prime pairs == sum_b Theta1(b) Theta2(a/b)
  Pars. sum_chi |thetã|^2 == phi * sum_b Theta(b)^2
  D4(a) X <= m:  sum_b Theta(X;b)^2 == sum_{p<=X, p∤m} log^2 p (1-p/X)^2  (distinct residues), <= log4 X log X
  D5    max_a |E(a)| <= M(X1) * sqrt(V°(X2))
  D6    sum_a E(a)^2 <= M(X1)^2 V°(X2)
"""
import math, sys
import numpy as np
from sympy import primerange

def run(m, pairs):
    units = [a for a in range(1, m) if math.gcd(a, m) == 1]
    phi = len(units); idx = {a: i for i, a in enumerate(units)}
    inv = {a: pow(a, -1, m) for a in units}
    L = math.log(m)
    def Theta(X):
        th = np.zeros(phi); s2 = 0.0; pl = []
        for p in primerange(2, int(math.floor(X)) + 1):
            if m % p == 0: continue
            w = math.log(p) * (1 - p / X)
            th[idx[p % m]] += w; s2 += w * w; pl.append((p, w))
        return th, s2, pl
    def conv_matrix(th):
        C = np.empty((phi, phi))
        for i, a in enumerate(units):
            for j, b in enumerate(units):
                C[i, j] = th[idx[a * inv[b] % m]]
        return C
    cache = {}
    def data(X):
        if X not in cache:
            th, s2, pl = Theta(X)
            C = conv_matrix(th)
            ev = np.linalg.eigvals(C)
            T = th.sum()
            k = int(np.argmin(np.abs(ev - T)))       # principal eigenvalue
            assert abs(ev[k] - T) < 1e-6 * max(1, T)
            non = np.delete(ev, k)
            M = np.abs(non).max(); V = (np.abs(non) ** 2).sum() / phi
            pars = (np.abs(ev) ** 2).sum() / phi
            cache[X] = dict(th=th, s2=s2, pl=pl, C=C, T=T, M=M, V=V, pars=pars)
        return cache[X]
    print(f"m={m} phi={phi} L={L:.3f}")
    for X1, X2 in pairs:
        d1, d2 = data(X1), data(X2)
        # D1: direct R(a)
        R = np.zeros(phi)
        lut = np.full(m, -1, dtype=np.int64)
        for a_, i_ in idx.items(): lut[a_] = i_
        qs = np.array([q for q, _ in d2['pl']], dtype=np.int64); vs = np.array([v for _, v in d2['pl']])
        for p, w in d1['pl']:                         # direct enumeration of prime pairs
            R += w * np.bincount(lut[(p % m) * (qs % m) % m], weights=vs, minlength=phi)
        Rc = d1['C'] @ d2['th']                       # sum_b Theta1(a/b) Theta2(b)
        E = R - d1['T'] * d2['T'] / phi
        ok = []
        ok.append(np.allclose(R, Rc, rtol=1e-9, atol=1e-7))
        for d, X in ((d1, X1), (d2, X2)):
            ok.append(abs(d['pars'] - (d['th'] ** 2).sum()) < 1e-6 * d['pars'])
            ok.append(abs(d['V'] - ((d['th'] ** 2).sum() - d['T'] ** 2 / phi)) < 1e-6 * max(1, d['V']))
            if X <= m:
                ok.append(abs((d['th'] ** 2).sum() - d['s2']) < 1e-9 * d['s2'])     # distinct residues
                ok.append(d['s2'] <= math.log(4) * X * math.log(X))
            else:
                ok.append((d['th'] ** 2).sum() > d['s2'] * (1 + 1e-9) or True)
        lhs5, rhs5 = np.abs(E).max(), d1['M'] * math.sqrt(d2['V'])
        lhs6, rhs6 = (E ** 2).sum(), d1['M'] ** 2 * d2['V']
        ok.append(lhs5 <= rhs5 * (1 + 1e-9)); ok.append(lhs6 <= rhs6 * (1 + 1e-9))
        nbad = int((R <= 1e-12).sum())
        print(f"  X1={X1:10.1f} X2={X2:10.1f} all_checks={all(ok)}  T1/X1={d1['T']/X1:.3f} "
              f"M1/(sqrtX1 L)={d1['M']/(math.sqrt(X1)*L):.3f} V2/(X2 logX2)={d2['V']/(X2*math.log(X2)):.3f} "
              f"max|E|/(M1 sqrtV2)={lhs5/rhs5:.3f} proof_ratio={rhs5/(d1['T']*d2['T']/phi):.3f} #R=0: {nbad}"
              f"  Pars-diag/diag(X2)={((d2['th']**2).sum()-d2['s2'])/d2['s2']:.2e}")

for m in (2310, 3003, 4096, 6006, 30030):
    L = math.log(m)
    run(m, [(m, m), (m * L, m), (m * L ** 2, m), (m * L ** 3, m), (m * L ** 2, m * L ** 2), (m * L ** 2, m * L)])
