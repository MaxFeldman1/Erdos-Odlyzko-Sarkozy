#!/usr/bin/env python3
"""Route D, experiment 1: the conjugation barrier.

Product count   N(a)  = #{(p,q) in P^2 : p*q   = a (mod m)} = (1/phi) sum_chi conj(chi(a)) S(chi)^2
Quotient count  Nm(a) = #{(p,q) in P^2 : p/q   = a (mod m)} = (1/phi) sum_chi conj(chi(a)) |S(chi)|^2
P = primes <= m not dividing m.  Both counts see the same |S(chi)|, Parseval, energy.
For odd m: Nm(-1) = #{p+q=m} = 2*[m-2 prime].

Prime m only (discrete log + FFT).  Usage: conj_barrier.py m1 m2 ...
"""
import sys
import numpy as np
from sympy import primitive_root, isprime, primerange

def run(m):
    assert isprime(m)
    g = primitive_root(m)
    n = m - 1
    ind = np.zeros(m, dtype=np.int64)
    x = 1
    for i in range(n):
        ind[x] = i
        x = x * g % m
    primes = np.array(list(primerange(2, m)), dtype=np.int64)
    f = np.zeros(n)
    f[ind[primes]] = 1.0
    F = np.fft.fft(f)                       # F[k] = sum_p e(-k ind(p)/n) = S(chi_k)
    N = np.rint(np.fft.ifft(F * F).real).astype(np.int64)            # index = ind(a), product
    Nm = np.rint(np.fft.ifft(F * np.conj(F)).real).astype(np.int64)  # index = ind(a), a = p/q
    P = len(primes); phi = n; lam = P * P / phi; L = np.log(m)
    assert N.sum() == P * P and Nm.sum() == P * P
    half = n // 2                            # ind(-1)
    k = np.arange(n)
    even = (k % 2 == 0); even[0] = False     # chi(-1)=+1, chi != chi0
    odd = (k % 2 == 1)
    A2 = np.abs(F) ** 2
    me, mo = A2[even].mean(), A2[odd].mean()
    # identity: sum_{chi != chi0} chi(-1)|S|^2 = phi*Nm(-1) - P^2
    lhs = A2[even].sum() - A2[odd].sum()
    rhs = phi * Nm[half] - P * P
    prod_tw = ((F ** 2).real[even].sum() - (F ** 2).real[odd].sum())  # = phi*N(-1) - P^2
    print(f"m={m}  |P|={P}  lambda={lam:.2f}  m-2 prime: {isprime(m-2)}")
    print(f"  product : min N/lam = {N.min()/lam:.3f}   N(-1)/lam = {N[half]/lam:.3f}   #zeros = {(N==0).sum()}")
    print(f"  quotient: Nm(-1) = {Nm[half]}   Nm(1) = {Nm[0]} (=|P|)   #zeros = {(Nm==0).sum()}   min over a!=+-1 of Nm/lam = {np.delete(Nm,[0,half]).min()/lam:.3f}")
    print(f"  mean|S|^2: even(non-principal) = {me:.2f}  odd = {mo:.2f}  diff/(2|P|^2/phi) = {(mo-me)/(2*P*P/phi):.4f}  rel.bias (mo-me)/|P| = {(mo-me)/P:.4f}  (2/log m = {2/L:.4f})")
    print(f"  identity check: sum chi(-1)|S|^2 = {lhs:.1f}  vs phi*Nm(-1)-|P|^2 = {rhs}")
    print(f"  product analogue: sum_(chi!=chi0) chi(-1) Re S^2 / |P|^2 = {prod_tw/(P*P):+.4f}   (quotient: {lhs/(P*P):+.4f}; EOS at a=-1 fails iff this is -1)")
    # singular-series structure of the quotient problem at small-height a = u/v
    def idx(a): return ind[a % m]
    rows = []
    for (u, v) in [(2,1),(-2,1),(3,1),(-3,1),(1,2),(-1,2),(3,2),(-3,2),(5,1),(-5,1),(6,1),(-6,1)]:
        a = u * pow(v, -1, m) % m
        rows.append(f"{u}/{v}: {Nm[idx(a)]/lam:.2f} | {N[idx(a)]/lam:.2f}")
    print("  a = u/v : Nm/lam | N/lam   " + "   ".join(rows))
    print(f"  spread: std(N/lam) = {N.std()/lam:.4f}   std(Nm/lam, a != 1) = {np.delete(Nm,[0]).std()/lam:.4f}   random-set prediction sqrt(2/lam)*(1-delta) = {np.sqrt(2/lam)*(1-P/phi):.4f}")
    # threshold: with range X = (1+eps) m the quotient problem at a=-1 is p+q in {m, 2m}
    for eps in (0.02, 0.1):
        X = int((1 + eps) * m)
        cnt = sum(1 for p in primerange(2, X + 1) if p != m and 0 < 2 * m - p <= X and isprime(2 * m - p))
        print(f"  range X=(1+{eps})m: #{{p+q=2m, p,q<=X}} = {cnt}")

if __name__ == "__main__":
    for s in sys.argv[1:]:
        run(int(s)); print()
