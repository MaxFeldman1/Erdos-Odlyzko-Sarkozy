#!/usr/bin/env python3
"""
Kloosterman-dual expansion of N(a) for prime m  (round 1, automorphic persona).

Identity tested (Lemma K of notes/brainstorm/r1-automorphic.md), m prime:
    N(a) = (m+1)|P|^2/m^2 + m^{-2} sum_{c != 0} Pi(c) K(ac),
    Pi(c) = sum_{hl = c, h,l != 0} Phat(h) Phat(l),   Phat(h) = sum_{p in P} e(hp/m),
    K(t)  = S(1,t;m) = sum_{x != 0} e((x + t xbar)/m).
Questions:
  (1) is the identity exact (sanity)?
  (2) is Pi sparse, i.e. is E(a)=N(a)-mean a short combination of Kloosterman sums K(ac)?
  (3) are the large Pi(c) at c of small height u/v, and are they produced by major arcs of Phat?
  (4) scan of the other "Gauss-sum bases": Xi_k = inverse Mellin of S(chi)^2 * conj(eps_chi)^k.
Usage: python3 kl_dual.py m [R]
"""
import sys, math
import numpy as np

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

def primitive_root(m):
    fs, n, d = [], m - 1, 2
    while d * d <= n:
        if n % d == 0:
            fs.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: fs.append(n)
    g = 2
    while any(pow(g, (m - 1) // f, m) == 1 for f in fs): g += 1
    return g

def ratrec(c, m):
    """(u,v) with c*v = u mod m and max(|u|,|v|) (nearly) minimal."""
    r0, r1, t0, t1 = m, c % m, 0, 1
    best = (r1, 1)
    while r1:
        if max(abs(r1), abs(t1)) < max(abs(best[0]), abs(best[1])): best = (r1, t1)
        q = r0 // r1
        r0, r1, t0, t1 = r1, r0 - q * r1, t1, t0 - q * t1
    u, v = best
    if v < 0: u, v = -u, -v
    return u, v

def main():
    m = int(sys.argv[1]); R = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    L = math.log(m)
    pr = primes_upto(m); pr = pr[pr < m]; assert pr[-1] != m and all(m % q for q in pr[:50])
    nP = len(pr); n = m - 1
    ind = np.zeros(m, dtype=np.int64); exp = np.zeros(n, dtype=np.int64)
    g = primitive_root(m); x = 1
    for k in range(n):
        exp[k] = x; ind[x] = k; x = x * g % m
    one = np.zeros(m); one[pr] = 1.0
    # multiplicative transforms: for f on units, F[j] = sum_k f(g^k) e(-jk/n)
    def mell(f): return np.fft.fft(f[exp])
    def imell(F):
        out = np.zeros(m, dtype=complex); out[exp] = np.fft.ifft(F); return out
    Sx = mell(one)                         # S(chi_j)
    N = imell(Sx * Sx).real                # N(a), a = 1..m-1  (index 0 unused)
    lam = nP * nP / n
    E = N[1:] - lam
    print(f"m={m} |P|={nP} lambda={lam:.3f} L={L:.3f}  min N={N[1:].min():.0f} max N={N[1:].max():.0f} std E={E.std():.3f} sqrt(lam)={math.sqrt(lam):.3f}")
    # additive transform Phat(h) = sum_p e(hp/m)
    Ph = np.conj(np.fft.fft(one))
    Pi = imell(mell(Ph) ** 2)              # Pi(c) = sum_{hl=c} Phat(h)Phat(l)
    print("max |Im Pi| =", np.abs(Pi.imag).max(), "(Pi is real)")
    Pi = Pi.real
    # Kloosterman sums K(t) = sum_x e((xbar + t x)/m)
    xs = np.arange(1, m); inv = np.zeros(m, dtype=np.int64); inv[exp] = exp[(-np.arange(n)) % n]
    f = np.zeros(m, dtype=complex); f[xs] = np.exp(2j * np.pi * inv[xs] / m)
    K = np.conj(np.fft.fft(np.conj(f)))    # K(t) = sum_x f(x) e(tx/m)
    K = K.real
    print("Weil check: max |K(t)|/(2 sqrt m), t!=0 =", np.abs(K[1:]).max() / (2 * math.sqrt(m)))
    # (1) identity: sum_c Pi(c) K(ac) = sum over ind: correlation.  a c = t  -> conv of Pi with K(1/.) ...
    # sum_c Pi(c) K(a c): put c = g^k, a = g^j: sum_k Pi[g^k] K[g^{j+k}]  = cross-correlation
    FPi = np.fft.fft(Pi[exp]); FK = np.fft.fft(K[exp])
    T = np.zeros(m); T[exp] = np.fft.ifft(np.conj(FPi) * FK).real      # T(a) = sum_c Pi(c) K(ac)
    Nrec = (m + 1) * nP * nP / m**2 + T / m**2
    print("(1) identity max error |N - Nrec| =", np.abs(N[1:] - Nrec[1:]).max())
    # (2) sparsity of Pi
    Pc = Pi[1:] - Pi[1:].mean()
    rms = math.sqrt((Pc**2).mean())
    print(f"(2) Pi: mean={Pi[1:].mean():.4g} rms={rms:.4g}  predicted rms sqrt(2 m)|P|={math.sqrt(2*m)*nP:.4g}  (m/L)^2={(m/L)**2:.4g}")
    order = np.argsort(-np.abs(Pc)); tot = (Pc**2).sum()
    cum = np.cumsum(Pc[order]**2) / tot
    def gauss_frac(fr):  # real Gaussian: fraction of energy in the top fraction fr of entries
        from scipy.stats import norm, chi2
        tq = norm.isf(fr / 2); return chi2.sf(tq * tq, 3)
    Eo = np.sort(E**2)[::-1]; cumE = np.cumsum(Eo) / Eo.sum()
    S2 = np.abs(Sx[1:])**4; S2 = np.sort(S2)[::-1]; cumS = np.cumsum(S2) / S2.sum()
    print("    top-K energy fraction:   K | Kloosterman basis Pi | delta basis E(a) | character basis |S|^4 | real-Gaussian benchmark")
    for Kk in [1, 10, 100, 1000, 10000, 100000]:
        if Kk < n:
            print(f"    {Kk:7d} | {cum[Kk-1]:.5f} | {cumE[Kk-1]:.5f} | {cumS[Kk-1]:.5f} | {gauss_frac(Kk/n):.5f}")
    kurt = lambda v: ((v - v.mean())**4).mean() / ((v - v.mean())**2).mean()**2
    print(f"    kurtosis: Pi {kurt(Pi[1:]):.2f}   E(a) {kurt(E):.2f}   (Gaussian 3)")
    # (3) heights of the peaks, and major-arc explanation
    # major arcs: h = round(b m / r) + t, r <= R, (b,r)=1, |t| <= J
    J = 3; maj = np.zeros(m, dtype=bool)
    for r in range(1, R + 1):
        for b in range(0, r):
            if math.gcd(b, r) != 1: continue
            h0 = (b * m + r // 2) // r
            for t in range(-J, J + 1):
                h = (h0 + t) % m
                if h: maj[h] = True
    PhM = np.where(maj, Ph, 0); PhM[0] = 0
    en = (np.abs(Ph[1:])**2).sum()
    print(f"(3) major arcs r<={R}, |t|<={J}: #h={maj.sum()}  share of ||Phat||^2 = {(np.abs(PhM)**2).sum()/en:.4f}   (log R/log m = {math.log(R)/L:.4f})")
    PiM = imell(mell(PhM) ** 2).real
    PiMm = imell(mell(PhM) * mell(Ph - PhM - np.where(np.arange(m) == 0, Ph, 0))).real * 2
    print("    top peaks of Pi:  c  u/v  Pi/rms  Pi/(m/L)^2  share from major x major  share major x minor")
    for i in order[:25]:
        c = i + 1; u, v = ratrec(c, m)
        print(f"    c={c:9d} = {u}/{v}   {Pc[i]/rms:8.2f}  {Pi[c]/(m/L)**2:8.4f}   {PiM[c]/Pi[c]:6.3f}  {PiMm[c]/Pi[c]:6.3f}")
    # heights of top-1000
    hts = np.array([max(abs(a_) for a_ in ratrec(int(i) + 1, m)) for i in order[:1000]])
    print(f"    heights max(|u|,|v|) of the top 1000 peaks: median {np.median(hts):.0f}, 90% quantile {np.quantile(hts,0.9):.0f}, sqrt(m)={math.sqrt(m):.0f}")
    print(f"    energy share of Pi carried by major x major part: {((PiM[1:]-PiM[1:].mean())**2).sum()/tot:.5f}")
    # small heights table
    print("    Pi at small heights: u/v  Pi/rms  corr(E(a), K(a u/v)) ")
    Kn = K / (math.sqrt(m))
    for (u, v) in [(1,1),(-1,1),(2,1),(1,2),(-2,1),(3,1),(1,3),(3,2),(2,3),(-3,2),(4,1),(1,4),(6,1),(1,6),(5,1),(1,5),(6,5),(5,6),(10,3),(15,2)]:
        c = u * pow(v, -1, m) % m
        Ka = Kn[(np.arange(1, m) * c) % m]
        cor = np.corrcoef(E, Ka)[0, 1]
        print(f"    {u:3d}/{v:<3d} {Pc[c-1]/rms:8.2f}   {cor:+.5f}   (noise 1/sqrt(phi) = {1/math.sqrt(n):.5f})")
    # (4) scan Gauss-sum bases: Xi_k = inverse Mellin of S^2 * conj(eps)^k,  eps = tau/sqrt(m)
    add = np.zeros(m, dtype=complex); add[xs] = np.exp(2j * np.pi * xs / m)
    tau = mell(add)                      # tau(chi-bar_j) up to convention; |tau| = sqrt m for j != 0
    eps = tau / math.sqrt(m); eps[0] = 0
    print("(4) bases S^2 * eps^k (k<0: conj):   k  max|Xi_k|/rms  kurtosis(|Xi|)")
    S2c = Sx * Sx; S2c[0] = 0
    for k in range(-4, 5):
        mult = eps**k if k >= 0 else np.conj(eps)**(-k)
        mult[0] = 0
        Xi = np.fft.ifft(S2c * mult)
        a_ = np.abs(Xi); r_ = math.sqrt((a_**2).mean())
        print(f"    k={k:+d}   {a_.max()/r_:8.2f}   {(a_**4).mean()/r_**4:8.2f}")
    # same for |S|^2 (quotient problem, Thm G side)
    A2 = np.abs(Sx)**2; A2[0] = 0
    print("    quotient data |S|^2 * eps^k:")
    for k in range(-2, 3):
        mult = eps**k if k >= 0 else np.conj(eps)**(-k)
        mult[0] = 0
        Xi = np.fft.ifft(A2 * mult); Xi[0] = 0   # drop the class a=1 (diagonal |P|)
        a_ = np.abs(Xi); r_ = math.sqrt((a_**2).mean())
        print(f"    k={k:+d}   {a_.max()/r_:8.2f}   {(a_**4).mean()/r_**4:8.2f}")

if __name__ == "__main__":
    main()
