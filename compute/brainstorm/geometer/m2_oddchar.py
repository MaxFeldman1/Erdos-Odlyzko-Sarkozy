#!/usr/bin/env python3
"""m = 2 in odd characteristic (prime field F_p, f = t^2 - d, d a non-residue): moments of
e(a) = 4 (N(a) - lam)/p over random a in (F_p[t]/f)^*.  Compare with char 2 (tower_eos.py, m=2: moments 1,2,5 = SU(2))."""
import sys, numpy as np
def run(p, na, rng):
    d = next(x for x in range(2, p) if pow(x, (p - 1) // 2, p) == p - 1)
    qr = np.zeros(p, dtype=np.int8); qr[(np.arange(1, p) ** 2) % p] = 1; 
    chi = 2 * qr.astype(np.int64) - 1; chi[0] = 0
    U, V = np.meshgrid(np.arange(p), np.arange(p), indexing="ij"); U = U.ravel()[1:]; V = V.ravel()[1:]   # x = u + v tau != 0
    # g <-> g(tau) = (c + d) + b tau ; disc = b^2 - 4c = v^2 - 4(u - d)
    irr = lambda u, v: chi[(v * v - 4 * (u - d)) % p] == -1
    ix = irr(U, V)
    nrm = (U * U - d * V * V) % p
    inv = np.array([pow(int(z), p - 2, p) for z in range(p)]); ninv = inv[nrm]
    xu = (U * ninv) % p; xv = (-V * ninv) % p          # 1/x
    nP = int(ix.sum()); lam = nP * nP / (p * p - 1)
    es = []
    for _ in range(na):
        a0, a1 = int(rng.integers(p)), int(rng.integers(p))
        if a0 == 0 and a1 == 0: continue
        yu = (a0 * xu + d * a1 * xv) % p; yv = (a0 * xv + a1 * xu) % p
        N = int((ix & irr(yu, yv)).sum())
        es.append(4 * (N - lam) / p)
    e = np.array(es); v = (e ** 2).mean()
    print(f"p={p} samples={len(e)} |P|={nP} var={v:.3f} m4/var^2={(e**4).mean()/v**2:.3f} m6/var^3={(e**6).mean()/v**3:.3f} "
          f"max|e|={np.abs(e).max():.3f} mean={e.mean():.3f}", flush=True)
rng = np.random.default_rng(7)
for p, na in ((101, 20000), (211, 8000), (401, 3000)):
    run(p, na, rng)
