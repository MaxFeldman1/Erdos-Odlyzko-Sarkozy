#!/usr/bin/env python3
"""Route D, experiment 2: EOS over F_2[t] (small fixed field, large degree) as a test bed.

Modulus f irreducible of degree n with t a generator of (F_2[t]/f)^* (f primitive).
P = irreducible polynomials of degree exactly n, other than f  (analogue of primes in (m/2, m]);
they are distinct nonzero residues mod f (reduce g -> g + f).
N(a) = #{(g1,g2) in P^2 : g1 g2 = a mod f}, computed by FFT over the cyclic group of order 2^n - 1.
Sawin's theorem covers q > 7567 only; this is q = 2.
Usage: ff2_eos.py nmin nmax [moduli_per_degree]
"""
import sys
import numpy as np

def clmul_shift(g, p):
    """carry-less product p*g for an int64 array g and python int p"""
    acc = np.zeros_like(g)
    i = 0
    while p >> i:
        if (p >> i) & 1:
            acc ^= (g << i)
        i += 1
    return acc

def irreducible_table(D):
    """is_irr[x] for polynomials x (bitmask) of degree <= D"""
    size = 1 << (D + 1)
    comp = np.zeros(size, dtype=bool)
    comp[0] = comp[1] = True
    for d in range(1, D // 2 + 1):
        for p in range(1 << d, 1 << (d + 1)):
            if comp[p]:
                continue
            # multiples p*g with deg g >= d (g >= p suffices up to symmetry; take all g of degree in [d, D-d])
            g = np.arange(1 << d, 1 << (D - d + 1), dtype=np.int64)
            comp[clmul_shift(g, p)] = True
    return ~comp

def log_table(f, n):
    """discrete logs base t in F_2[t]/f; returns None if t is not a generator"""
    order = (1 << n) - 1
    lg = np.full(1 << n, -1, dtype=np.int64)
    x = 1
    top = 1 << n
    for i in range(order):
        if lg[x] != -1:
            return None
        lg[x] = i
        x <<= 1
        if x & top:
            x ^= f
    return lg if x == 1 else None

def run(n, irr, how_many, rng):
    order = (1 << n) - 1
    cands = np.nonzero(irr[(1 << n):(1 << (n + 1))])[0] + (1 << n)
    rng.shuffle(cands)
    done = 0
    for f in cands:
        f = int(f)
        lg = log_table(f, n)
        if lg is None:
            continue
        P = cands[cands != f] ^ f          # residues of the other degree-n irreducibles
        ind = lg[P]
        v = np.zeros(order)
        v[ind] = 1.0
        F = np.fft.fft(v)
        N = np.rint(np.fft.ifft(F * F).real).astype(np.int64)
        assert N.sum() == len(P) ** 2
        lam = len(P) ** 2 / order
        delta = len(P) / order
        R = N.min() / lam
        Rrand = 1 - 2 * (1 - delta) * np.sqrt(np.log(order) / lam)
        A = np.abs(F[1:])
        exc = ((N - lam) ** 2).sum() / (2 * len(P) ** 2 * (1 - delta) ** 2)
        print(f"n={n:2d} f={f:#x} |P|={len(P):6d} lam={lam:9.2f} zeros={(N==0).sum():5d} "
              f"minN/lam={R:6.3f} Rrand={Rrand:6.3f} depth={(1-R)/(1-Rrand) if Rrand<1 else float('nan'):5.2f} "
              f"max|S|/sqrt|P|={A.max()/np.sqrt(len(P)):5.2f} max|S|/(n 2^(n/2))={A.max()/(n*2**(n/2)):6.4f} "
              f"energy-excess/random={exc:5.3f}", flush=True)
        done += 1
        if done >= how_many:
            break

if __name__ == "__main__":
    nmin, nmax = int(sys.argv[1]), int(sys.argv[2])
    k = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    rng = np.random.default_rng(1)
    irr = irreducible_table(nmax)
    # sanity: number of irreducibles of degree d
    cnt = [int(irr[(1 << d):(1 << (d + 1))].sum()) for d in range(1, min(nmax, 12) + 1)]
    assert cnt[:8] == [2, 1, 2, 3, 6, 9, 18, 30], cnt
    for n in range(nmin, nmax + 1):
        run(n, irr, k, rng)
