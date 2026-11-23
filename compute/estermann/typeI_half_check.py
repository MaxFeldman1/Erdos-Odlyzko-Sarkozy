#!/usr/bin/env python3
"""Checks for section 2 of notes/routes/F-estermann-sumsquares.md (odd prime m).
For a few units a:
 (1) TypeIHalf error  T(a) = sum_{d < sqrt m, d odd} |N_d - |P|(m-d^2)/(4dm)|,
     N_d = #{n in A_a : n = 1 mod 4, d | n, n > d^2}; reported as T/|P| (hypothesis: <= 1/log m),
     also truncated at d <= m^0.25 and m^0.4, and the random-model size sum_d sqrt(expected)/|P|.
 (2) R(a) = sum_{n in A_a, n=1 mod 4} r(n), r = 1*chi_4, against (pi/8)|P|.
 (3) window sums: mean over n in A_a (n = 1 mod 4) of |Delta(n)|, Delta(n) = sum_{d|n, m^(1/2-eps) < d < sqrt n} chi_4(d),
     and the same mean over all integers n < m, n = 1 mod 4.
Usage: python3 typeI_half_check.py m [a1 a2 ...]
"""
import sys, math, numpy as np
from sympy import isprime

def run(m, alist):
    assert isprime(m) and m % 2 == 1
    sieve = np.ones(m, dtype=bool); sieve[:2] = False
    for i in range(2, int(m**0.5) + 1):
        if sieve[i]: sieve[i*i::i] = False
    primes = np.nonzero(sieve)[0]
    P = len(primes)
    inv = np.array([pow(int(p), -1, m) for p in primes], dtype=np.int64)
    rt = math.isqrt(m - 1)
    chi = lambda d: 0 if d % 2 == 0 else (1 if d % 4 == 1 else -1)
    L = math.log(m)
    print(f"m={m} |P|={P} 1/log m={1/L:.4f}  (pi/8)|P|={math.pi/8*P:.1f}")
    allint = np.zeros(m, dtype=np.int64); allint[1::4] = 1
    def window_means(member, eps_list):
        out = []
        tot = member.sum()
        for eps in eps_list:
            D = m ** (0.5 - eps)
            delta = np.zeros(m, dtype=np.int64)
            for d in range(int(D) + 1, rt + 1):
                c = chi(d)
                if c: delta[d*(d+1)::d] += c
            out.append((np.abs(delta) * member).sum() / tot)
        return out
    eps_list = [0.2, 0.1, 0.05, 0.02]
    wm = window_means(allint, eps_list)
    print("  integers n=1 mod 4: mean|Delta_W| for eps=" + ", ".join(f"{e}: {w:.4f}" for e, w in zip(eps_list, wm)))
    for a in alist:
        n = (a * inv) % m
        mem = np.zeros(m, dtype=np.int64); mem[n[n % 4 == 1]] = 1
        T = 0.0; T25 = 0.0; T40 = 0.0; rnd = 0.0; R = 0
        for d in range(1, rt + 1, 2):
            Nd = int(mem[d*(d+1)::d].sum())
            e = P * (m - d*d) / (4.0 * d * m)
            err = abs(Nd - e)
            T += err; rnd += math.sqrt(e)
            if d <= m**0.25: T25 += err
            if d <= m**0.4: T40 += err
            R += 2 * chi(d) * Nd
        sq = sum(chi(d) for d in range(1, rt + 1) if mem[d*d])
        R += sq
        wa = window_means(mem, eps_list)
        print(f"  a={a}: T/|P|={T/P:.4f} (d<=m^.25: {T25/P:.4f}, d<=m^.4: {T40/P:.4f}; random model {rnd/P:.4f}); "
              f"R={R}, R/((pi/8)|P|)={R/(math.pi/8*P):.4f}")
        print("       A_a: mean|Delta_W| for eps=" + ", ".join(f"{e}: {w:.4f}" for e, w in zip(eps_list, wa)))

m = int(sys.argv[1])
alist = [int(x) for x in sys.argv[2:]] or [1, 2, m - 1, 12345 % m]
run(m, alist)
