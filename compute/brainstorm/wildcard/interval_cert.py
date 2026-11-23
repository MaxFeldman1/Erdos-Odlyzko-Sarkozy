#!/usr/bin/env python3
"""Route W2 experiment: additive intervals as multipliers, and shape diagnostics of E(a).

For prime m and the set I = {a0+1,...,a0+H} of residues:
  Q_I   = sum_{chi != chi0} |S|^2 |1_I^(chi)| / (|P|^2 H)       (Q_I < 1 proves I meets P.P)
  E2/2H^2, E3/6H^3 = normalised multiplicative energies of I    (near 1 = 'generic', no structure)
  min over all a0 of #{(p,q,r): pq = a0 + r, 1<=r<=H}/(lambda H)  (truth, all windows at once)
Also: kurtosis of N(a), and how much of -E(a_min) is carried by the top characters.
"""
import sys, math
import numpy as np
from multiplier_cert import primes_upto, prim_root, dlog_table

def run(m, seed=1):
    rng = np.random.default_rng(seed)
    phi = m - 1; g = prim_root(m); dl = dlog_table(m, g)
    pr = primes_upto(m - 1); P = len(pr); lam = P * P / phi
    f = np.zeros(phi); f[dl[pr]] = 1.0
    F = np.fft.fft(f); A2 = np.abs(F)**2
    N = np.fft.ifft(F * F).real                      # indexed by dlog
    Nres = np.zeros(m); Nres[1:] = N[dl[1:]]         # indexed by residue
    print(f"\nm={m} |P|={P} phi/|P|={phi/P:.3f} lambda={lam:.1f}")
    E = N - lam
    print(f"  E(a): std/sqrt(2 lam (1-d)^2)={E.std()/math.sqrt(2*lam)/(1-P/phi):.4f}  skew={((E/E.std())**3).mean():.4f}  kurtosis={((E/E.std())**4).mean():.4f}  min E/std={E.min()/E.std():.2f}  lam/std={lam/E.std():.1f}")
    i0 = int(np.argmin(N))
    terms = (F * F * np.exp(2j * np.pi * np.arange(phi) * i0 / phi)).real / phi; terms[0] = 0
    order = np.argsort(terms)
    tot = terms.sum()
    print(f"  worst class: E={tot:.1f}; share of E carried by the most negative 1%,10%,50% of characters: "
          + ", ".join(f"{terms[order[:int(phi*q)]].sum()/tot:.2f}" for q in (0.01, 0.1, 0.5))
          + f"; Gaussian-model shares would be large too (sum of signed terms)")
    cs = np.concatenate([[0.0], np.cumsum(Nres)])
    print("      H   minwin/(lamH)  maxwin/(lamH) |  a0: Q_I, E2/2H^2, E3/6H^3 for a0=0, a0=(m-1)/2 (=-1/2), 3 random a0")
    for H in [16, 64, 256, 1024, 4096]:
        win = cs[H + 1:] - cs[1:-H]                  # windows a0+1..a0+H inside [1,m-1]
        row = []
        for a0 in [0, (m - 1) // 2] + [int(x) for x in rng.integers(1, m - H - 1, 3)]:
            w = np.zeros(phi); w[dl[a0 + 1:a0 + H + 1]] = 1.0
            Wh = np.abs(np.fft.fft(w))
            Q = (A2[1:] * Wh[1:]).sum() / (P * P * H)
            E2 = (Wh**4).sum() / phi / (2 * H * H); E3 = (Wh**6).sum() / phi / (6 * H**3)
            row.append(f"{Q:.3f},{E2:.2f},{E3:.2f}")
        print(f"  {H:5d}   {win.min()/(lam*H):.4f}        {win.max()/(lam*H):.4f}      | " + "  ".join(row))

if __name__ == "__main__":
    for a in sys.argv[1:]: run(int(a))
