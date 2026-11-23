#!/usr/bin/env python3
"""Referee check of geometer E2 (odd characteristic). m=2, f=t^2-d over F_p.
D4'(a) = #{(al_1..al_4) in F_p^4 : prod (tau+al_i) = a} for ALL a in F_{p^2}^*, by FFT on the cyclic group.
t(a) = (D4'(a) - p^2)/p.  Report range and moments, against SU(2) (1,2,5,14), SO(3)=Sym^2 (1,3,15,91), Gaussian (1,3,15,105)."""
import numpy as np, sys
def run(p):
    d = next(x for x in range(2, p) if pow(x, (p - 1) // 2, p) == p - 1)
    n = p * p - 1
    mul = lambda x, y: ((x[0]*y[0] + d*x[1]*y[1]) % p, (x[0]*y[1] + x[1]*y[0]) % p)
    # find generator
    fac = []; t = n; q = 2
    while q * q <= t:
        if t % q == 0:
            fac.append(q)
            while t % q == 0: t //= q
        q += 1
    if t > 1: fac.append(t)
    def pw(x, e):
        r = (1, 0)
        while e:
            if e & 1: r = mul(r, x)
            x = mul(x, x); e >>= 1
        return r
    g = None
    for u in range(1, p):
        for v in range(1, 4):
            c = (u, v)
            if all(pw(c, n // q) != (1, 0) for q in fac): g = c; break
        if g: break
    log = np.zeros((p, p), dtype=np.int64); x = (1, 0)
    for k in range(n):
        log[x[0], x[1]] = k; x = mul(x, g)
    c = np.zeros(n); 
    for al in range(p): c[log[al, 1]] += 1     # tau + al = (al, 1)
    F = np.fft.rfft(c); D4 = np.rint(np.fft.irfft(F ** 4, n)).astype(np.int64)
    assert D4.sum() == p ** 4
    t = (D4 - p * p) / p
    v = (t ** 2).mean()
    # subfield classes a in F_p^*
    sub = np.array([log[u, 0] for u in range(1, p)])
    mask = np.ones(n, bool); mask[sub] = False
    tg = t[mask]
    print(f"p={p}: all a: mean={t.mean():.4f} var={v:.4f} m4={(t**4).mean()/v**2:.3f} m6={(t**6).mean()/v**3:.2f} m8={(t**8).mean()/v**4:.1f} range=[{t.min():.3f},{t.max():.3f}]")
    v = (tg**2).mean()
    print(f"      a not in F_p: var={v:.4f} m4={(tg**4).mean()/v**2:.3f} m6={(tg**6).mean()/v**3:.2f} m8={(tg**8).mean()/v**4:.1f} range=[{tg.min():.3f},{tg.max():.3f}];  a in F_p^*: range=[{t[sub].min():.3f},{t[sub].max():.3f}] mean={t[sub].mean():.3f}")
    # raw moments of t (not variance-normalised), to compare with trace laws having nonzero mean
    print("      raw moments E t^k, k=1..6 (a not in F_p):", " ".join(f"{(tg**k).mean():.3f}" for k in range(1, 7)))
    h, edges = np.histogram(tg, bins=12)
    print("      hist:", list(zip(np.round(edges[:-1],2), h)))
for p in map(int, sys.argv[1:]): run(p)
