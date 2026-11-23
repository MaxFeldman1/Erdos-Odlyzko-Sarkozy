#!/usr/bin/env python3
"""Route D, experiment 3: Postnikov linearisation for m = r^2 (r prime).

For p = b + r u, q = c + r v (0 <= u,v < r, b,c units mod r):
    p q = a (mod r^2)  <=>  b c = a (mod r)  and  b v + c u = (a - b c)/r (mod r).
(1) verify  N(a) = sum over fibres (b, c = a/b mod r) of the linear counts, for sampled a;
(2) single fibre b = 1: for every unit c mod r and every e mod r count
        n(c,e) = #{(u,v) in U_1 x U_c : v + c u = e (mod r)},  U_b = {u < r : b + r u prime}.
    Every a mod r^2 with a = c (mod r) corresponds to exactly one e.  Report min, zeros, mean.
Usage: square_fibers.py r1 r2 ...
"""
import sys, random
import numpy as np
from sympy import isprime, primerange

def run(r):
    assert isprime(r) and r > 2
    m = r * r
    isp = np.zeros(m + 1, dtype=bool)
    isp[list(primerange(2, m + 1))] = True
    isp[r] = False                                   # p | m excluded
    U = [None] * r                                   # U[b] = indicator on Z/r of {u : b + r u prime}
    for b in range(1, r):
        U[b] = isp[b + r * np.arange(r)].astype(float)
    primes = np.nonzero(isp)[0]
    # (1) identity check on random a
    prodcount = np.bincount((primes[:, None] * primes[None, :] % m).ravel(), minlength=m) if len(primes) < 6000 else None
    random.seed(0)
    ok = True
    for _ in range(20 if prodcount is not None else 0):
        a = random.randrange(1, m)
        if a % r == 0: continue
        tot = 0
        for b in range(1, r):
            c = a * pow(b, -1, r) % r
            d = ((a - b * c) // r) % r
            ub = np.nonzero(U[b])[0]; vc = np.nonzero(U[c])[0]
            tot += int(((b * vc[None, :] + c * ub[:, None]) % r == d).sum())
        ok &= (tot == prodcount[a])
    # (2) single fibre b = 1
    F1 = np.fft.fft(U[1])
    mins = []; zeros = 0; tot = 0
    k = np.arange(r)
    for c in range(1, r):
        # n(c,e) = sum_u U1[u] Uc[e - c u]; substitute w = c u: U1 dilated
        dil = np.zeros(r); dil[(c * k) % r] = U[1]
        n = np.rint(np.fft.ifft(np.fft.fft(dil) * np.fft.fft(U[c])).real).astype(int)
        zeros += int((n == 0).sum()); mins.append(n.min()); tot += n.sum()
    s1 = U[1].sum(); mean = tot / ((r - 1) * r)
    print(f"r={r} m={m}: identity N(a)=sum of fibres on 20 random a: {('OK' if ok else 'FAIL') if prodcount is not None else 'skipped'};"
          f" |U_1|={int(s1)}, single-fibre count: mean={mean:.2f}, min={min(mins)}, #(c,e) with no solution={zeros} of {(r-1)*r}"
          f" (Poisson guess {(r-1)*r*np.exp(-mean):.1f})")

if __name__ == "__main__":
    for s in sys.argv[1:]:
        run(int(s))
