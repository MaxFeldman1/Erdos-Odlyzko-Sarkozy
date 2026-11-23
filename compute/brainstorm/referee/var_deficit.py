#!/usr/bin/env python3
"""Referee check: the 'unexplained 4% variance deficit' of r1-analytic section 4.1.
delta_I(c) = sum_{u in I prime} Lambda(u) (1_P(c ubar) - rho), I = (M,(1+lam)M].
Var/pred with pred = rho(1-rho) sum Lambda^2.  Claim tested: deficit = -C * lam * rho * (log-free const), i.e. linear in lam
(the Montgomery-Soundararajan -1/2 log H defect of the singular-series average / missing integer diagonal j=0).
Also prints the variance with prime-count weights and the mean off-diagonal N^-(u1/u2)/lambda0."""
import numpy as np, math, sys
def sieve(n):
    s = np.ones(n + 1, bool); s[:2] = False
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
def proot(m):
    n = m - 1; fs = [q for q in sieve(int(n ** .5) + 1) if n % q == 0]
    t = n
    for q in fs:
        while t % q == 0: t //= q
    if t > 1: fs.append(t)
    g = 2
    while any(pow(g, n // int(q), m) == 1 for q in fs): g += 1
    return g
def run(m, cases):
    n = m - 1; g = proot(m)
    log = np.zeros(m, np.int64); x = 1
    ex = np.empty(n, np.int64)
    for k in range(n): ex[k] = x; x = x * g % m
    log[ex] = np.arange(n)
    pr = sieve(m); pr = pr[pr != m]
    f = np.zeros(n); f[log[pr]] = 1
    S2 = np.abs(np.fft.fft(f)) ** 2; S2[0] = 0
    rho = len(pr) / n
    for M, lam in cases:
        us = pr[(pr > M) & (pr <= (1 + lam) * M)]
        for name, w in (("Lambda", np.log(us)), ("count", np.ones(len(us)))):
            u = np.zeros(n); np.add.at(u, log[us], w)
            U2 = np.abs(np.fft.fft(u)) ** 2
            var = (S2 * U2).sum() / n / n          # mean over c of delta^2
            pred = rho * (1 - rho) * (w ** 2).sum()
            print(f"m={m} M={M} lam={lam:<5} #u={len(us):4d} {name:6s} var/pred={var/pred:.4f}  deficit/(lam*rho)={(1-var/pred)/(lam*rho):.3f}", flush=True)
m = int(sys.argv[1])
run(m, [(1000, 1), (1000, .5), (1000, .25), (1000, .1), (300, 1), (300, .5), (3000, 1), (3000, .25), (30000, 1), (30000, .25)])
