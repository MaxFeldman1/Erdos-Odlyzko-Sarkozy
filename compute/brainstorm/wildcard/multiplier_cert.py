#!/usr/bin/env python3
"""Route W1 experiment (wildcard, round 1).

For prime m: S(chi) = sum_{p<m} chi(p), W(chi) = sum_{s in Wset} chi(s), Wset = first Y primes.
Checks, for the ternary count N3(a) = #{(p,q,s): pqs = a mod m} = (1/phi) sum_chi chibar(a) S^2 W:
  (1) energy lemma:   (1/phi) sum_chi |W|^{2k} = k! Y^k (1+o(1)) as long as y^k < m   [exact identity + unique factorisation]
  (2) certificate:    Q(Y) = sum_{chi != chi0} |S|^2 |W| / (|P|^2 Y)   (Q < 1 proves every a is pqs, s in Wset)
  (3) Hoelder bound:  Q <= H_k := (phi/|P|) (M^2/|P|)^{1/2k} (E_k)^{1/2k} / Y,  M = max_{chi!=chi0}|S|, E_k = (1/phi) sum_chi |W|^{2k}
  (4) truth:          min_a N3(a) / (lambda Y)
Usage: multiplier_cert.py m [m ...]
"""
import sys, math
import numpy as np

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

def prim_root(m):
    fac, n, d = [], m - 1, 2
    while d * d <= n:
        if n % d == 0:
            fac.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: fac.append(n)
    g = 2
    while any(pow(g, (m - 1) // f, m) == 1 for f in fac): g += 1
    return g

def dlog_table(m, g):
    pw = np.array([1], dtype=np.int64)
    while len(pw) < m - 1:
        mult = pow(g, len(pw), m)
        pw = np.concatenate([pw, pw * mult % m])
    pw = pw[:m - 1]
    dl = np.empty(m, dtype=np.int64); dl[pw] = np.arange(m - 1)
    return dl

def run(m):
    phi = m - 1
    g = prim_root(m); dl = dlog_table(m, g)
    pr = primes_upto(m - 1)
    f = np.zeros(phi); f[dl[pr]] = 1.0
    F = np.fft.fft(f); P = len(pr); lam = P * P / phi
    A2 = np.abs(F)**2
    M = math.sqrt(A2[1:].max())
    Lp = phi / P
    print(f"\nm={m}  |P|={P}  phi/|P|={Lp:.3f}  lambda={lam:.1f}  M/sqrt(m)={M/math.sqrt(m):.3f}  M^2/|P|={M*M/P:.2f}  log m={math.log(m):.2f}")
    print(f"   predicted certificate threshold Y* = (0.886 phi/|P|)^2 = {(0.8862*Lp)**2:.1f}")
    print("     Y      y  Q=cert   0.886(phi/P)/sqrtY   minN3/(lamY)  maxN3/(lamY)  [E_k/(k!Y^k), H_k for k=1,2,3,4]")
    N2 = np.fft.ifft(F * F).real
    print(f"     (Y=0 baseline, EOS itself: Q = {(A2[1:].sum())/(P*P):.3f}, min N/lambda = {N2.min()/lam:.3f})")
    for Y in [4, 16, 64, 128, 256, 512, 1024, 2048]:
        ws = pr[:Y]; y = int(ws[-1])
        w = np.zeros(phi); w[dl[ws]] = 1.0
        Wh = np.fft.fft(w); aW = np.abs(Wh)
        Q = (A2[1:] * aW[1:]).sum() / (P * P * Y)
        N3 = np.fft.ifft(F * F * Wh).real
        out = []
        for k in (1, 2, 3, 4):
            Ek = (aW**(2 * k)).sum() / phi
            ok = (y**k < m)
            Hk = Lp * (M * M / P)**(1 / (2 * k)) * Ek**(1 / (2 * k)) / Y
            out.append(f"{Ek/(math.factorial(k)*Y**k):.3f}{'' if ok else '*'}/{Hk:.2f}")
        print(f"  {Y:5d} {y:6d}  {Q:6.3f}   {0.8862*Lp/math.sqrt(Y):6.3f}             {N3.min()/(lam*Y):.4f}        {N3.max()/(lam*Y):.4f}    " + "  ".join(out))

if __name__ == "__main__":
    for a in sys.argv[1:]:
        run(int(a))
