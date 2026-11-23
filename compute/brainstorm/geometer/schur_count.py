#!/usr/bin/env python3
"""Schur-Mellin bookkeeping for the function-field EOS error term.

p_m(theta)^2 = sum_{nu |- 2m} chi^nu(m,m) s_nu(theta)   (Frobenius), theta in U(N), N = m-1 = deg L(u,chi).
Only nu with at most N rows survive.  We list them by Murnaghan-Nakayama on beta-sets and print
  #nu          number of nu with chi^nu(m,m) != 0 and l(nu) <= N
  V(m)         sum chi^2  = int_{U(N)} |Tr theta^m|^4   (predicted variance of m^2 E(a) / Q^{m/2} as Q -> oo)
  sum|chi|     l^1 norm (what a termwise Deligne bound has to pay, times the ranks r_nu)
Also the smooth toy: e_k(theta)^4, k = m/2: number of constituents and int |e_k|^4.
"""
import sys
from collections import defaultdict

def add_hook(beta, m):
    """all ways to add an m-rim-hook to the partition with beta-set `beta` (frozenset), with sign"""
    out = []
    for b in beta:
        if b + m not in beta:
            ht = sum(1 for c in beta if b < c < b + m)
            out.append((frozenset(beta - {b} | {b + m}), (-1) ** ht))
    return out

def to_partition(beta):
    bs = sorted(beta)
    return tuple(sorted((b - i for i, b in enumerate(bs) if b - i > 0), reverse=True))

def chars(m, cyc):
    L = sum(cyc) + 1
    cur = {frozenset(range(L)): 1}
    for c in cyc:
        nxt = defaultdict(int)
        for beta, v in cur.items():
            for b2, s in add_hook(beta, c):
                nxt[b2] += v * s
        cur = nxt
    return {to_partition(b): v for b, v in cur.items() if v != 0}

if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    print(" m  #nu(all) #nu(l<=m-1)  V(m)=sum chi^2  sum|chi|  max|chi|   2(m-1)^2")
    for m in range(2, M + 1):
        ch = chars(m, (m, m))
        tot = sum(v * v for v in ch.values())
        assert tot == 2 * m * m, (m, tot)          # centraliser order of type (m,m)
        r = {nu: v for nu, v in ch.items() if len(nu) <= m - 1}
        print(f"{m:2d} {len(ch):8d} {len(r):10d} {sum(v*v for v in r.values()):12d} "
              f"{sum(abs(v) for v in r.values()):9d} {max(abs(v) for v in r.values()):8d} {2*(m-1)**2:10d}")
