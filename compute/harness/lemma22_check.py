#!/usr/bin/env python3
"""Numerical check of Lemma 2.2 of notes/routes/E-buchstab-H4.md:
   sum_j iota_j |K_j|  <=  (1 + C1 lam) B0 + C5 log(2/lam) m / log^2 m,
with B0 = #{n < m, (n,m)=1, z <= lpf(n) < sqrt m}, blocks tiling [z, sqrt m) with ratio 1+lam_m <= 1+lam.
Prints maj/B0 - 1, split into bulk blocks (M_{j+1} <= sqrt(lam m)/2) and top blocks, and the
normalised quantities (maj_bulk/B0_bulk - 1)/lam and maj_top / (m / log^2 m).
Usage: python3 lemma22_check.py m eta
"""
import sys, math
import numpy as np

m = int(float(sys.argv[1])); eta = float(sys.argv[2]) if len(sys.argv) > 2 else 0.25
L = math.log(m)
lpf = np.zeros(m + 1, dtype=np.int32)
for i in range(2, m + 1):
    if lpf[i] == 0:
        sl = lpf[i::i]; sl[sl == 0] = i
n = np.arange(m + 1)
unit = np.gcd(n, m) == 1; unit[0] = False; unit[m] = False
z = m ** eta; rt = math.sqrt(m)
isP = (lpf == n) & unit
P = np.nonzero(isP)[0]
# cnt[y] helper: number of unit k <= x with lpf(k) >= y  (plus k = 1), by direct count
order = np.argsort(lpf[1:m], kind="stable") + 1          # units sorted by lpf
print(f"m={m} eta={eta} z={z:.1f} omega(m)={len(set(int(lpf[p]) for p in P[:0]))}")
print(" lam   J  | maj/B0-1 | bulk: #blk (maj/B0-1)/lam | top: #blk maj_top/(m/L^2)  maj_top/B0")
for lam in (1.0, 0.5, 0.25, 0.1, 0.05):
    J = max(1, math.ceil((0.5 - eta) * L / math.log(1 + lam)))
    q = math.exp((0.5 - eta) * L / J)
    Ms = [z * q ** j for j in range(J)] + [rt]
    Ystar = math.sqrt(lam * m) / 2
    mb = bb = mt = bt = 0; nb = nt = 0
    for j in range(J):
        Ij = P[(P >= Ms[j]) & (P < Ms[j + 1])]
        kk = np.arange(1, int(m // Ms[j]) + 1)
        nK = int((unit[kk] & ((kk == 1) | (lpf[kk] >= Ms[j]))).sum())
        b0 = 0
        for p in Ij:
            k2 = np.arange(1, (m - 1) // int(p) + 1)
            b0 += int((unit[k2] & ((k2 == 1) | (lpf[k2] >= p))).sum())
        if Ms[j + 1] <= Ystar:
            mb += len(Ij) * nK; bb += b0; nb += 1
        else:
            mt += len(Ij) * nK; bt += b0; nt += 1
    B0 = bb + bt
    print(f"{lam:5.2f} {J:3d} | {(mb+mt)/B0-1:8.4f} | {nb:3d} {((mb/bb-1)/lam if bb else float('nan')):8.3f}"
          f" | {nt:3d} {mt/(m/L**2):8.3f} {mt/B0:8.4f}")
