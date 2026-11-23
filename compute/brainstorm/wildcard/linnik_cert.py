#!/usr/bin/env python3
"""Route W2 experiment: 'Goldbach-Linnik format' targets  a = p q g^j s  (0<=j<J, s in R = first |R| primes).

Fourier side: 1_S^(chi) = D_J(theta_chi) * R^(chi), chi(g) = e(theta_chi).
  Qcert(J,R) = sum_{chi != chi0} |S|^2 |D_J| |R^| / (|P|^2 J |R|)     (< 1 proves every a is p q g^j s)
  flat      = (phi/|P|) * mean|D_J| * mean|R^| / (J|R|) prediction if |S|^2 were independent of theta and of R^
  truth     = min_a  #{(p,q,j,s)} / (lambda J |R|)
Also prints C_s = max_{b != 1} N^-(b)/lambda, the quotient-count constant that the sieve has to bound,
and the Bohr-mass ratio  mass(delta)/(phi(2 delta |P| + lambda))  for delta = 1/J.
"""
import sys, math
import numpy as np
from multiplier_cert import primes_upto, prim_root, dlog_table

def run(m):
    phi = m - 1; gp = prim_root(m); dl = dlog_table(m, gp)
    pr = primes_upto(m - 1); P = len(pr); lam = P * P / phi; Lp = phi / P
    f = np.zeros(phi); f[dl[pr]] = 1.0
    F = np.fft.fft(f); A2 = np.abs(F)**2
    Nm = np.fft.ifft(A2).real                    # N^-(b), b = g^i
    Nm1 = Nm.copy(); Nm1[0] = 0
    ib = int(np.argmax(Nm1)); b = pow(gp, ib, m)
    print(f"\nm={m} |P|={P} phi/|P|={Lp:.3f} lambda={lam:.1f}")
    print(f"  quotient counts: max_(b!=1) N^-(b)/lambda = {Nm1.max()/lam:.3f} at b={b} (b^-1={pow(b,-1,m)}); mean = {Nm1.sum()/(phi-1)/lam:.4f};"
          f" #{{b: N^- > 2 lam}} = {(Nm1 > 2*lam).sum()}, #{{b: N^- > 3 lam}} = {(Nm1 > 3*lam).sum()}")
    jj = np.arange(phi)
    for g in (2, 3, gp):
        e = int(dl[g]); order = phi // math.gcd(e, phi)
        theta = (jj * e % phi) / phi             # chi_j(g) = exp(-2 pi i j e/phi)
        print(f"  g={g} (order {order})")
        print("      J  |R|  |S|=J|R|   Qcert    flat    truth_min   bohr(1/J)   max_{0<h<J} N^-(g^h)/lam")
        for J in (16, 32, 64, 128, 256):
            s = np.sin(np.pi * theta); D = np.full(phi, float(J)); nz = np.abs(s) > 1e-12
            D[nz] = np.abs(np.sin(np.pi * J * theta[nz]) / s[nz])
            hs = (np.arange(1, J) * e) % phi
            mx = Nm[hs].max() / lam
            tt = np.minimum(theta, 1 - theta); bohr = A2[tt <= 1.0 / J].sum() / (phi * (2 * P / J + lam))
            dj = np.zeros(phi); dj[(np.arange(J) * e) % phi] += 1.0
            for R in (1, 4, 16):
                ws = pr[:R]; w = np.zeros(phi); w[dl[ws]] = 1.0
                Wh = np.fft.fft(w); aW = np.abs(Wh)
                Q = (A2[1:] * D[1:] * aW[1:]).sum() / (P * P * J * R)
                flat = Lp * D[1:].mean() * aW[1:].mean() / (J * R)
                cnt = np.fft.ifft(F * F * np.fft.fft(dj) * Wh).real
                print(f"   {J:4d} {R:3d}  {J*R:6d}   {Q:6.3f}  {flat:6.3f}   {cnt.min()/(lam*J*R):.4f}     {bohr:.3f}        {mx:.3f}")

if __name__ == "__main__":
    for a in sys.argv[1:]: run(int(a))
