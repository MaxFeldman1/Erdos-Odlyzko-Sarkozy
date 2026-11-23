#!/usr/bin/env python3
"""If H^m(X_a)_var were a multiple of the regular representation of S_{2m} (free-quotient heuristic), the number
of Frobenius eigenvalues in the EOS error term would be  chi_orb * W(m),  W(m) = sum_{nu, l(nu)<=m-1} |chi^nu(m,m)| f^nu,
against Sawin-style bookkeeping  chi_orb * binom(2m,m) * (2^{m-1}-1)^2  (signs between hook pairs discarded).
Print W(m)/binom(2m,m) and its growth rate."""
import sys, math
from schur_count import chars

def dim(nu):
    n = sum(nu); conj = [sum(1 for x in nu if x > j) for j in range(nu[0])]
    h = 1
    for i, row in enumerate(nu):
        for j in range(row):
            h *= (row - j - 1) + (conj[j] - i - 1) + 1
    return math.factorial(n) // h

M = int(sys.argv[1]) if len(sys.argv) > 1 else 14
prev = None
print(" m   W(m)/binom(2m,m)   ratio to previous   (2^(m-1)-1)^2   max f^nu/binom(2m,m)")
for m in range(2, M + 1):
    ch = {nu: v for nu, v in chars(m, (m, m)).items() if len(nu) <= m - 1}
    W = sum(abs(v) * dim(nu) for nu, v in ch.items())
    b = math.comb(2 * m, m)
    rho = W / b
    print(f"{m:2d} {rho:16.3f} {'' if prev is None else f'{rho/prev:12.3f}':>12} {(2**(m-1)-1)**2:16d} "
          f"{max(dim(nu) for nu in ch)/b:14.3f}")
    prev = rho
