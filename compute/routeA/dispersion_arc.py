#!/usr/bin/env python3
"""Route A, dispersion form (notes/routes/A-typeII.md, section 6).

delta_M(c) = sum_{u in (M,2M]} Lambda(u) (1_P(c*ubar mod m) - rho).
Type II block needs  R_M(a) := sum_{k<=K} delta_M(a kbar)^2 / (K (rho M)^2)  <<  1/log^2 m,  K = m/(2M).
Compare: actual primes (arc {a kbar}), the global average over all classes c, the random-model
prediction log(M)/(rho M), and the barrier sequence A* (rough k carry a deviation ~ kappa rho M).
Also the 4th moment over all c:  E4 = sum_c delta^4 / (m M^2)  vs trivial (rho M)^2 * var.
Usage: python3 dispersion_arc.py [m_lower] [n_a]
"""
import sys, math
import numpy as np

def sieve(N):
    isp = np.ones(N + 1, dtype=bool); isp[:2] = False
    for i in range(2, int(N**0.5) + 1):
        if isp[i]: isp[i*i::i] = False
    return isp

lo = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**6
n_a = int(sys.argv[2]) if len(sys.argv) > 2 else 5
isp = sieve(lo + 1000)
m = int(np.nonzero(isp[lo:])[0][0]) + lo
isp = isp[:m + 1].copy(); isp[m] = False
primes = np.nonzero(isp)[0]; nP = len(primes); rho = nP / (m - 1); L = math.log(m)
inv = np.zeros(m, dtype=np.int64); inv[1] = 1
for i in range(2, m): inv[i] = (-(m // i) * inv[m % i]) % m
rng = np.random.default_rng(7)
D = int(round(m ** (1/3)))
rough = np.ones(m + 1, dtype=bool); rough[:2] = False; rough[m] = False
for p in primes[primes <= D]: rough[p::p] = False
RC = rough & ~isp; bigP = isp.copy(); bigP[:D + 1] = False; kappa = bigP.sum() / RC.sum()
print(f"m={m} rho={rho:.4f} log m={L:.2f} D={D} kappa={kappa:.2f}  threshold 1/log^2 m = {1/L**2:.5f}")
print(" M      K     | global var/(rho M)^2  E4/(m M^2)  E4_trivial/(m M^2) | random pred | R_M(a) primes: mean, max over a | R_M A* | max_k |delta|/(rho M): primes, A*")
for e in (0.3, 0.4, 0.5, 0.6, 0.7):
    M = int(m ** e); us = primes[(primes > M) & (primes <= 2 * M)]; K = m // (2 * M)
    lam = np.log(us); tot = lam.sum()
    # global: delta(c) for all c  (nu(c) = sum_u Lambda(u) 1_P(c ubar))
    nu = np.zeros(m)
    for u, l in zip(us, lam):
        nu[(primes * int(u)) % m] += l          # c = p*u
    dl = nu[1:] - rho * tot
    var = (dl**2).mean(); e4 = (dl**4).sum() / (m * M**2)
    Rs = []; mx = []; RsS = []; mxS = []
    ks = np.arange(1, K + 1)
    for t in range(n_a):
        a = int(rng.integers(2, m - 1))
        arc = (a * inv[ks]) % m
        d = dl[arc - 1]
        Rs.append((d**2).sum() / (K * (rho * tot)**2)); mx.append(abs(d).max() / (rho * tot))
        if t == 0:   # barrier sequence A*: 1_{P*}(c ubar) = 1_{A*}(a u cbar) -> on arc c = a kbar: 1_{A*}(u k)
            prob = np.full(m + 1, rho); prob[RC] = rho * (1 + kappa); prob[bigP] = 0; prob[0] = prob[m] = 0
            Fs = (rng.random(m + 1) < prob).astype(float)
            dS = np.array([ (lam * Fs[us * k]).sum() for k in ks ]) - rho * tot
            RsS = (dS**2).sum() / (K * (rho * tot)**2); mxS = abs(dS).max() / (rho * tot)
    print(f"{M:6d} {K:6d} | {var/(rho*tot)**2:.5f}  {e4:.3f}  {(4*rho*tot)**2*var/M**2:.1f} | {math.log(M)/(rho*M):.5f} | "
          f"{np.mean(Rs):.5f} {np.max(Rs):.5f} | {RsS:.5f} | {np.max(mx):.3f} {mxS:.3f}")
