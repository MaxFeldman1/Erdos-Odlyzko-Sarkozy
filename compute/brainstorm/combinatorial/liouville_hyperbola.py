"""Liouville on the modular hyperbola: C(a) = sum_{n<=m,(n,m)=1} lambda(n) lambda([a n^{-1}]_m), prime m, all a (FFT in dlog coordinates).
Weak lambda-EOS asks |C(a)| < phi; 'Chowla on the hyperbola' asks C(a) = o(m)."""
import sys, numpy as np
from coset_certificate import primitive_root
for m in [int(x) for x in sys.argv[1:]]:
    phi = m - 1
    lam = np.ones(m, dtype=np.int64)
    n = np.arange(m)
    rem = n.copy(); rem[0] = 1
    for p in range(2, int(m**0.5) + 1):
        while True:
            idx = np.nonzero(rem % p == 0)[0]
            idx = idx[idx > 0]
            if len(idx) == 0: break
            rem[idx] //= p; lam[idx] *= -1
    lam[rem > 1] *= -1
    g = primitive_root(m); dlog = np.zeros(m, dtype=np.int64); x = 1
    for k in range(phi):
        dlog[x] = k; x = x * g % m
    f = np.zeros(phi); f[dlog[1:]] = lam[1:]
    F = np.fft.rfft(f)
    C = np.rint(np.fft.irfft(F * F, n=phi))          # C(g^k) = sum_{x y = g^k} lam(x) lam(y)
    print(f'm={m}: sum lam={int(f.sum())}, max C/phi={C.max()/phi:.4f}, min C/phi={C.min()/phi:.4f}, '
          f'max|C|/sqrt(2 phi log phi)={np.abs(C).max()/np.sqrt(2*phi*np.log(phi)):.3f}, rms C/sqrt(phi)={np.sqrt((C**2).mean()/phi):.3f}')
