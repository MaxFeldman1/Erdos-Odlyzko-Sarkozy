#!/usr/bin/env python3
"""Sanity checks for notes/routes/F-estermann-sumsquares.md (prime moduli m).
For every unit a (via FFT on the cyclic group G = (Z/m)^*):
  Nsf(a)  = #{p in P : a*p^{-1} mod m squarefree}
  Ns2(a)  = #{p in P : a*p^{-1} mod m a sum of two squares}
  Nd(a)   = #{p in P : d | (a*p^{-1} mod m)} for d = 4, 9, 25  (Type I at small moduli)
and the L1/L2 ratio of Q(chi) = sum_{s squarefree} chi(s) over nonprincipal chi (section 1.4 item 3).
Usage: python3 estermann_check.py m1 m2 ...
"""
import sys, numpy as np
from sympy import primitive_root, isprime

def run(m):
    assert isprime(m)
    g = primitive_root(m)
    n = m - 1
    # discrete log table: ind[g^k] = k
    ind = np.zeros(m, dtype=np.int64)
    x = 1
    pw = np.empty(n, dtype=np.int64)
    for k in range(n):
        pw[k] = x; x = x * g % m
    ind[pw] = np.arange(n)
    N = np.arange(m)
    sieve = np.ones(m, dtype=bool); sieve[:2] = False
    for i in range(2, int(m**0.5) + 1):
        if sieve[i]: sieve[i*i::i] = False
    sqf = np.ones(m, dtype=bool); sqf[0] = False
    d = 2
    while d*d < m:
        sqf[d*d::d*d] = False; d += 1
    # sums of two squares (n>=1), including x or y = 0
    s2 = np.zeros(m, dtype=bool)
    r = int(m**0.5) + 1
    xs = np.arange(r)
    for xx in range(r):
        v = xx*xx + xs*xs
        v = v[(v < m) & (v > 0)]
        s2[v] = True
    def onG(mask):           # function on Z/n indexed by discrete log
        f = np.zeros(n); f[ind[np.nonzero(mask)[0]]] = 1.0; return f
    fP = onG(sieve)          # all primes < m (m prime so p∤m)
    P = int(fP.sum())
    FP = np.fft.rfft(fP)
    def conv_quot(fW):       # N(a) = sum_p W(a p^{-1}) = sum_k fP[k] fW[l-k]: plain cyclic convolution
        return np.rint(np.fft.irfft(FP * np.fft.rfft(fW), n)).astype(np.int64)
    L = np.log(m)
    print(f"m={m}  |P|={P}  m/|P|={m/P:.3f} log m={L:.3f}")
    fQ = onG(sqf); Q = int(fQ.sum())
    Nsf = conv_quot(fQ)
    exp = P * Q / n
    print(f"  squarefree: |Q|/phi={Q/n:.4f}  min Nsf/exp={Nsf.min()/exp:.4f} max={Nsf.max()/exp:.4f} "
          f"std/exp={Nsf.std()/exp:.5f}  (sqrt(|P|)/exp={P**0.5/exp:.5f})")
    for dd in (4, 9, 25, 49):
        Nd = conv_quot(onG((N % dd == 0) & (N > 0)))
        e = P / dd
        print(f"  d={dd:3d}: #{{n in A_a: d|n}} / (|P|/d): min={Nd.min()/e:.4f} max={Nd.max()/e:.4f}")
    # level-1/2 probe: moduli near sqrt(m)
    for dd in sorted({int(m**0.25), int(m**0.4), int(m**0.5), int(m**0.6)}):
        Nd = conv_quot(onG((N % dd == 0) & (N > 0)))
        e = P / dd
        print(f"  d={dd:5d} (m^{np.log(dd)/L:.2f}): rms dev of #{{d|n}} over a = {np.sqrt(((Nd-e)**2).mean()):.3f}, "
              f"max dev={np.abs(Nd-e).max():.1f}, |P|/d={e:.2f}, sqrt(|P|/d)={e**0.5:.2f}")
    f2 = onG(s2); B2 = int(f2.sum())
    Ns2 = conv_quot(f2)
    exp2 = P * B2 / n
    print(f"  two squares: |B|/phi={B2/n:.4f} min Ns2/exp={Ns2.min()/exp2:.4f} max={Ns2.max()/exp2:.4f} "
          f"std/exp={Ns2.std()/exp2:.5f}")
    # L1 / L2 of Q(chi), chi nonprincipal (full complex FFT)
    FQ = np.abs(np.fft.fft(fQ))[1:]
    l1 = FQ.mean(); l2 = np.sqrt((FQ**2).mean())
    FS = np.abs(np.fft.fft(fP))[1:]
    print(f"  Q(chi): L1 mean={l1:.2f}, L2 mean={l2:.2f}, L1/L2={l1/l2:.4f}, sup/sqrt(m)={FQ.max()/m**0.5:.3f}; "
          f"needed for sup(S)xL1(Q): L1 <= sqrt(m)/log^2 m = {m**0.5/L**2:.2f}")
    print(f"  S(chi): sup/(sqrt(m))={FS.max()/m**0.5:.3f}  Parseval deficit phi/sqrt(|P||Q|)={n/(P*Q)**0.5:.3f}, sqrt(log m)={L**0.5:.3f}")
    # F0: for a sample of a, least K such that some n_p + j m (j<K) is squarefree is 1 iff Nsf>0
    print(f"  Nsf(a)>0 for all a: {bool(Nsf.min()>0)};  Ns2(a)>0 for all a: {bool(Ns2.min()>0)}")

for arg in sys.argv[1:]:
    run(int(arg))
