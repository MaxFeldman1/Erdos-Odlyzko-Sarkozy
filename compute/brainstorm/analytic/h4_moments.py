#!/usr/bin/env python3
"""Route 1 (analytic persona, round 1): fourth moment / large deviations of
   delta_I(c) = sum_{u in I} Lambda(u) (1_P(c*ubar mod m) - rho),  I = (M, (1+lam) M],
over ALL classes c in G, for prime m.  Also the conjugate version
   delta^-_I(c) = sum_u Lambda(u) (1_P(c*u mod m) - rho)   (quotient problem, Thm G).
Reports: variance / (rho(1-rho) sum Lambda^2), kurtosis vs Gaussian+Poisson prediction,
max|delta|/sigma vs sqrt(2 log phi), tail counts, and the H4 ratio
   Q = sum_c delta^4 / (lam^4 rho^4 m M^3 / log M)      (H4(eta) asks Q <= eta^4/16).
Usage: python3 h4_moments.py m_lower
"""
import sys, math
import numpy as np

def sieve(N):
    s = np.ones(N + 1, dtype=bool); s[:2] = False
    for i in range(2, int(N**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return s

lo = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**6
isp = sieve(lo + 2000)
m = int(np.nonzero(isp[lo:])[0][0]) + lo
isp = isp[:m].copy()
P = np.nonzero(isp)[0].astype(np.int64); nP = len(P); phi = m - 1; rho = nP / phi; L = math.log(m)
print(f"m={m} |P|={nP} rho={rho:.5f} log m={L:.3f} sqrt(2 log phi)={math.sqrt(2*math.log(phi)):.3f}")
print("  e   lam      M   #u | var/pred  kurt  kurt_pred | max|d|/sig  #>4sig (gauss) #>5sig (gauss) | max|d|/(rho*SumLam) | Q=H4 ratio | conj: var/pred kurt max/sig")
for e in (0.25, 1/3, 0.4, 0.5):
    for lam in (1.0, 0.1):
        M = int(m ** e); us = P[(P > M) & (P <= (1 + lam) * M)]
        if len(us) < 20: continue
        lg = np.log(us); S1 = lg.sum(); S2 = (lg**2).sum(); S4 = (lg**4).sum()
        out = []
        for conj in (False, True):
            nu = np.zeros(m)
            for u, l in zip(us, lg):
                mult = pow(int(u), -1, m) if conj else int(u)
                # c = p*u  <=>  p = c*ubar  (direct);  c = p*ubar <=> p = c*u (conjugate)
                nu[(P * mult) % m] += l
            d = nu[1:] - rho * S1
            var = (d**2).mean(); sig = math.sqrt(var); k = (d**4).mean() / var**2
            mx = np.abs(d).max()
            out.append((d, var, sig, k, mx))
        d, var, sig, k, mx = out[0]
        vpred = rho * (1 - rho) * S2
        kpred = 3 + (rho*(1-rho)*(1-3*rho+3*rho*rho) * S4 - 3*(rho*(1-rho))**2 * S4) / vpred**2
        n4 = int((np.abs(d) > 4*sig).sum()); n5 = int((np.abs(d) > 5*sig).sum())
        g4 = phi * math.erfc(4/math.sqrt(2)); g5 = phi * math.erfc(5/math.sqrt(2))
        Q = (d**4).sum() / (lam**4 * rho**4 * m * M**3 / math.log(M))
        d2, var2, sig2, k2, mx2 = out[1]
        print(f"{e:.2f} {lam:4.1f} {M:6d} {len(us):4d} | {var/vpred:.4f}  {k:.3f}  {kpred:.3f} | {mx/sig:.2f}  {n4:5d} ({g4:.0f}) {n5:3d} ({g5:.1f}) | {mx/(rho*S1):.3f} | {Q:.3e} | {var2/vpred:.4f} {k2:.3f} {mx2/sig2:.2f}")
