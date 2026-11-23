"""Route C numerical checks (prime moduli m, Cesaro weights).

For a prime m and ranges X1, X2 define
  Theta(X; b) = sum_{p <= X, p = b mod m} log p * (1 - p/X)            (b in G = (Z/m)^*)
  thetaT(X, chi) = sum_b Theta(X; b) chi(b)                            (FFT over G, via a primitive root)
  R(a) = sum_b Theta(X1; b) Theta(X2; a/b) = T1 T2/phi + E(a).
Checked / reported:
  (1) H-constant:  M(X) = max_{chi != chi0} |thetaT(X,chi)| / (sqrt(X) log m)
  (2) variance:    V0(X) = (1/phi) sum_{chi != chi0} |thetaT|^2,  reported as V0/(X log m) and V0/(X^2/phi)
  (3) the inequality chain of Lemma D5:  max_a |E(a)| <= M1 * sqrt(V0(X2))   (must hold exactly)
  (4) min_a R(a) / (T1 T2 / phi) and the number of a with R(a) = 0
  (5) the 'proof ratio'  M1 sqrt(V0_2) / (T1 T2 / phi)   (<1 means the proof certifies all a at this (X1,X2))
Usage: python3 routeC_check.py [m ...]
"""
import sys, math
import numpy as np

def sieve(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i * i::i] = False
    return np.nonzero(s)[0]

def primitive_root(m):
    phi = m - 1; fs = []; n = phi; d = 2
    while d * d <= n:
        if n % d == 0:
            fs.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: fs.append(n)
    for g in range(2, m):
        if all(pow(g, phi // f, m) != 1 for f in fs): return g

def dlog_table(m, g):
    t = np.zeros(m, dtype=np.int64); x = 1
    for k in range(m - 1):
        t[x] = k; x = x * g % m
    return t

def theta_vec(primes, X, m, dl):
    p = primes[primes <= X]; p = p[p != m]
    w = np.log(p) * (1.0 - p / X)
    return np.bincount(dl[p % m], weights=w, minlength=m - 1)

def run(m, primes_all):
    phi = m - 1; L = math.log(m)
    g = primitive_root(m); dl = dlog_table(m, g)
    ranges = [("m/L", m / L), ("m", m), ("m L", m * L), ("m L^2", m * L * L), ("m L^3", m * L ** 3)]
    ranges = [(n, X) for n, X in ranges if X <= primes_all[-1]]
    data = {}
    print(f"\n=== m = {m} (prime), log m = {L:.3f} ===")
    print(f"{'X':>8} {'T/(X/2)':>9} {'M=max|th|/(sqrtX logm)':>24} {'V0/(X log m)':>13} {'V0/(X^2/phi)':>13} {'#empty classes':>15}")
    for name, X in ranges:
        Th = theta_vec(primes_all, X, m, dl)
        F = np.fft.fft(Th)
        T = F[0].real
        M = np.abs(F[1:]).max()
        V0 = (np.abs(F[1:]) ** 2).sum() / phi
        data[name] = (X, Th, F, T, M, V0)
        print(f"{name:>8} {T / (X / 2):9.4f} {M / (math.sqrt(X) * L):24.4f} {V0 / (X * L):13.4f} {V0 / (X * X / phi):13.4f} {(Th == 0).sum():15d}")
    print(f"{'(X1,X2)':>16} {'min R/main':>11} {'max|E|/main':>12} {'proof ratio M1 sqrtV2/main':>27} {'chain ok':>9} {'#a: R=0':>8}")
    names = [n for n, _ in ranges]
    for n1 in names:
        for n2 in names:
            if names.index(n2) > names.index(n1): continue
            X1, Th1, F1, T1, M1, V1 = data[n1]; X2, Th2, F2, T2, M2, V2 = data[n2]
            R = np.fft.ifft(F1 * F2).real          # cyclic convolution in the dlog index = R(a)
            main = T1 * T2 / phi
            E = R - main
            ok = np.abs(E).max() <= M1 * math.sqrt(V2) * (1 + 1e-9)
            nz = int((R < 1e-7 * main).sum())
            print(f"{'(' + n1 + ', ' + n2 + ')':>16} {R.min() / main:11.4f} {np.abs(E).max() / main:12.4f} {M1 * math.sqrt(V2) / main:27.4f} {str(ok):>9} {nz:8d}")

if __name__ == "__main__":
    ms = [int(a) for a in sys.argv[1:]] or [10007, 100003]
    lim = int(max(m * math.log(m) ** 3 for m in ms if m < 200000) if any(m < 200000 for m in ms) else 0)
    lim = max(lim, int(max(m * math.log(m) ** 2 for m in ms))) + 10
    P = sieve(lim)
    for m in ms: run(m, P)
