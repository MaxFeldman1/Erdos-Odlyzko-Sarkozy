#!/usr/bin/env python3
"""Route 1, Buchstab form, for prime m and ALL classes a at once (discrete log + FFT).
   A_a = {a*pbar mod m : p in P}.   For z = m^eta:
     S_z(a)   = #{n in A_a : P^-(n) >= z}                = (1_P * 1_Rough)(a)
     N_z(a)   = #{n in A_a : n prime >= z}                = (1_P * 1_{P>=z})(a)
     Buch(a)  = S_z(a) - N_z(a) = sum_{z<=p1<sqrt m} S(A_{p1}, p1) + (primes of A in [z, sqrt m))
   and per block of the least prime factor p1 in (M, 2M]:  B_M(a) = #{n in A_a: n composite, P^-(n) in (M,2M]}.
   EOS at a  <=>  Buch(a) < S_z(a).  With E[.] = rho * (size of the integer set), report the relative
   deviations over all a and the 'allowed' one-sided Type II error theta0 = #primes / #rough composites.
Usage: python3 buchstab_all_a.py m_lower
"""
import sys, math
import numpy as np
from sympy import primitive_root

def spf_sieve(N):
    spf = np.zeros(N + 1, dtype=np.int32)
    for i in range(2, N + 1):
        if spf[i] == 0:
            sl = spf[i::i]; sl[sl == 0] = i
    return spf

lo = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**6
spf = spf_sieve(lo + 2000)
m = next(n for n in range(lo, lo + 2000) if spf[n] == n)
spf = spf[:m]; n_arr = np.arange(m)
isp = (spf == n_arr) & (n_arr > 1)
g = int(primitive_root(m)); phi = m - 1
# powers of g by doubling
pw = np.ones(phi, dtype=np.int64); ln = 1; gp = g
while ln < phi:
    k = min(ln, phi - ln); pw[ln:ln + k] = (pw[:k] * gp) % m; gp = (gp * gp) % m; ln += k
ind = np.zeros(m, dtype=np.int64); ind[pw] = np.arange(phi)
def vec(mask):
    v = np.zeros(phi); v[ind[np.nonzero(mask)[0]]] = 1.0; return v
FP = np.fft.rfft(vec(isp)); nP = int(isp.sum()); rho = nP / phi; L = math.log(m)
def conv(mask):
    return np.rint(np.fft.irfft(FP * np.fft.rfft(vec(mask)), n=phi))   # indexed by ind(a)
print(f"m={m} g={g} |P|={nP} rho={rho:.5f} log m={L:.2f}")
for eta in (1/6, 1/4, 1/3):
    z = m ** eta
    rough = (spf >= z) & (n_arr > 1)
    bigp = isp & (n_arr >= z)
    comp = rough & ~isp
    S = conv(rough); N = conv(bigp); B = S - N
    eS = rho * rough.sum(); eN = rho * bigp.sum(); eB = rho * comp.sum()
    theta0 = bigp.sum() / comp.sum()
    print(f"\neta={eta:.3f} z={z:.1f}: #rough={int(rough.sum())} #primes>=z={int(bigp.sum())} #rough composites={int(comp.sum())}  theta0=primes/composites={theta0:.4f}")
    print(f"  S_z(a)/E : min {S.min()/eS:.4f} max {S.max()/eS:.4f} sd {S.std()/eS:.4f}   (Type I quantity)")
    print(f"  Buch(a)/E: min {B.min()/eB:.4f} max {B.max()/eB:.4f} sd {B.std()/eB:.4f}   EOS needs Buch/E < (S/E)(1+theta0) ~ {1+theta0:.4f}")
    print(f"  N_z(a)/E : min {N.min()/eN:.4f} max {N.max()/eN:.4f} sd {N.std()/eN:.4f}   poisson sd {1/math.sqrt(eN):.4f}")
    print(f"  worst margin over a: max (Buch - S)/E_N = {((B - S)/eN).max():.4f} (negative means EOS holds), corr(S,B)={np.corrcoef(S,B)[0,1]:.4f}")
    M = int(z)
    print("  block (M,2M] of least prime factor: #composites, E, max rel dev, sd rel dev, poisson sd, share of allowed error theta0*E_B")
    while M < math.sqrt(m):
        blk = comp & (spf > M) & (spf <= 2 * M)
        if blk.sum() > 0:
            Bm = conv(blk); e = rho * blk.sum()
            print(f"   M={M:5d}: {int(blk.sum()):8d} {e:9.1f}  max {Bm.max()/e - 1:+.4f} min {Bm.min()/e - 1:+.4f} sd {Bm.std()/e:.4f} ({1/math.sqrt(e):.4f})")
        M *= 2
