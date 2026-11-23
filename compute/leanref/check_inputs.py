"""Referee checks of the Lean hypotheses on small/edge cases, using the Lean definitions literally.
minFac follows Nat.minFac: minFac(0)=2, minFac(1)=1."""
import math, sys
import numpy as np
from math import gcd, log, ceil, sqrt, exp

def minfac_table(N):
    mf = np.arange(N + 1, dtype=np.int64)
    mf[0] = 2
    for p in range(2, int(N**0.5) + 1):
        if mf[p] == p:
            sl = mf[p*p::p]
            sl[sl == np.arange(p*p, N + 1, p)] = p
    return mf

def sieve_upper(Hmax=300, amax=40000):
    mf = minfac_table(amax + Hmax + 5)
    primes = [p for p in range(2, Hmax + 1) if mf[p] == p]
    worst = (0, None)
    for H in range(2, Hmax + 1):
        ys = sorted(set([float(p) for p in primes if p <= H] + [float(H), 2.0]))
        for y in ys:
            ok = ((mf >= y) | (np.arange(len(mf)) == 1)).astype(np.int64)
            cs = np.concatenate([[0], np.cumsum(ok)])   # cs[k] = #ok in [0,k)
            a = np.arange(0, amax + 1)
            cnt = cs[a + H + 1] - cs[a + 1]              # n in (a, a+H]
            i = int(np.argmax(cnt)); r = cnt[i] * log(y) / H
            if r > worst[0]: worst = (r, (int(a[i]), H, y, int(cnt[i])))
    print("SieveUpperBound: sup count*log(y)/H over H<=%d, a<=%d, y in primes<=H or H: %.4f at (a,H,y,count)=%s"
          % (Hmax, amax, worst[0], worst[1]))

def typeI(m, eta, eps=0.01):
    mf = minfac_table(m + 1)
    y = m ** eta
    P = [p for p in range(2, m + 1) if mf[p] == p and m % p != 0]
    units = [n for n in range(1, m) if gcd(n, m) == 1]
    phi = len(units) if m > 1 else 1
    rho = len(P) / phi
    rough = np.zeros(m, dtype=np.int64)
    for n in units:
        if n == 1 or mf[n] >= y: rough[n] = 1
    PhiCop = int(rough.sum())            # n=m is not coprime to m for m>=2
    pim = sum(1 for p in range(2, m + 1) if mf[p] == p)
    # S(A_a) for all units a: S(a) = sum_{q in P} rough[a * q^{-1} mod m]
    S = {}
    invP = [pow(q, -1, m) for q in P]
    ua = np.array(units, dtype=np.int64)
    tot = np.zeros(len(ua), dtype=np.int64)
    for qi in invP:
        tot += rough[(ua * qi) % m]
    rhs = rho * ((1 - eps * eta) * PhiCop - eps * pim)
    print("m=%d eta=%.2f: |P|=%d phi=%d rho=%.5f PhiCop=%d pi(m)=%d | mean S(A_a)=%.4f rho*PhiCop=%.4f | min S=%d max S=%d std=%.2f | TypeISifted RHS(eps=.01)=%.2f, #a violating=%d of %d"
          % (m, eta, len(P), phi, rho, PhiCop, pim, tot.mean(), rho * PhiCop, tot.min(), tot.max(), tot.std(), rhs, int((tot < rhs).sum()), len(ua)))

def rough_mertens(N=10**7):
    mf = minfac_table(N)
    isp = (mf == np.arange(N + 1)); isp[:2] = False
    pic = np.cumsum(isp)
    g = exp(-0.5772156649015329)
    for m in [10**4, 10**5, 10**6, 10**7]:
        row = []
        for eta in [0.5, 0.4, 0.3, 0.25, 0.2, 0.15, 0.1, 0.05]:
            y = m ** eta
            Phi = int((mf[1:m + 1] >= y).sum()) + (1 if y > 1 else 0)   # n=1 counted via 'n = 1'
            row.append("%.2f:%.4f" % (eta, eta * Phi / pic[m]))
        print("RoughMertens m=%d  eta*Phi(m,m^eta)/pi(m) [e^-gamma=%.4f]: %s" % (m, g, "  ".join(row)))

if __name__ == "__main__":
    sieve_upper()
    for m in [1, 2, 3, 4, 6, 30, 210, 2310, 10007, 30030, 100003]:
        if m >= 2: typeI(m, 0.2)
    typeI(100003, 0.1); typeI(99990, 0.25)
    rough_mertens()
