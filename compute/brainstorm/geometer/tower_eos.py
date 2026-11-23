#!/usr/bin/env python3
"""Constant-field tower experiment: the 'second expansion' of the EOS count, seen from F_2.

Fix f in F_2[t] irreducible of degree m.  For r coprime to m, f stays irreducible over F_Q, Q = 2^r, and
B_r = F_Q[t]/f = F_{2^{rm}} =: K.  Evaluation g -> g(tau) (tau a root of f in K) is a bijection
{monic g in F_Q[t] of degree m} -> K, with f -> 0.  Put
   P_r = {g(tau) : g monic irreducible of degree m over F_Q, g != f},
   N_r(a) = #{(x,y) in P_r^2 : xy = a},   lam = |P_r|^2/(|K|-1),
   e_r(a) = m^2 (N_r(a) - lam) / Q^{m/2}.
Lefschetz (Sawin): for a in a fixed finite field, r -> N_r(a) - (constant part) is a signed sum of r-th powers
of Frobenius eigenvalues of weights <= m and <= m+1 on two cohomology groups of the fibre X_a.
Character side: e_r(a) = (Q^m/phi) sum_chi chibar(a) Tr(theta_chi^m)^2 + small.
We print, for all a in K^* at once (FFT on the cyclic group K^*):
   var e, kurtosis, max|e|, max|e|/sqrt(2 var log phi), #a with N=0, and the top of the tail.
Usage: tower_eos.py m r1 r2 ...
"""
import sys, math
import numpy as np

PRIM = {2:0x7,3:0xB,4:0x13,5:0x25,6:0x43,7:0x83,8:0x11D,9:0x211,10:0x409,11:0x805,12:0x1053,13:0x201B,
        14:0x4443,15:0x8003,16:0x1100B,17:0x20009,18:0x40081,19:0x80027,20:0x100009,21:0x200005,
        22:0x400003,23:0x800021,24:0x1000087}
IRR2 = {2:0x7,3:0xB,4:0x13,5:0x25,7:0x83}       # f over F_2

def field(n):
    """exp/log tables of F_{2^n} = F_2[y]/PRIM[n]; asserts primitivity"""
    P = PRIM[n]; order = (1 << n) - 1
    ex = np.empty(order, dtype=np.int64)
    x = 1; top = 1 << n
    for i in range(order):
        ex[i] = x
        x <<= 1
        if x & top: x ^= P
    assert x == 1
    lg = np.full(1 << n, -1, dtype=np.int64)
    lg[ex] = np.arange(order)
    assert (lg[1:] >= 0).all(), "not primitive"
    return ex, lg, order

def run(m, r):
    n = r * m; Q = 1 << r
    ex, lg, order = field(n)
    def mul(a, b):            # arrays of field elements (broadcast), 0 allowed
        a = np.asarray(a); b = np.asarray(b)
        out = ex[(lg[a] + lg[b]) % order]
        return np.where((a == 0) | (b == 0), 0, out)
    # tau: a root of f (f in F_2[t]) inside K
    f = IRR2[m]; step = order // ((1 << m) - 1)
    tau = None
    for j in range(1, (1 << m) - 1):
        t = int(ex[j * step]); val = 0; pw = 1
        for i in range(m + 1):
            if (f >> i) & 1: val ^= pw
            pw = int(mul(pw, t))
        if val == 0: tau = t; break
    assert tau is not None
    # F_Q inside K
    FQ = np.concatenate(([0], ex[(np.arange(Q - 1) * (order // (Q - 1)))]))
    taupow = [1]
    for i in range(m): taupow.append(int(mul(taupow[-1], tau)))
    def monic(d):             # all u(tau), u monic of degree d over F_Q   (Q^d elements)
        acc = np.array([taupow[d]], dtype=np.int64)
        for i in range(d):
            acc = (acc[:, None] ^ mul(FQ, taupow[i])[None, :]).ravel()
        return acc
    red = np.zeros(1 << n, dtype=bool); red[0] = True          # 0 <-> f itself, excluded
    for d in range(1, m // 2 + 1):
        U = monic(d); V = monic(m - d)
        lu = lg[U]; lv = lg[V]
        # products u(tau) v(tau); deg < m so none of them is 0
        for chunk in np.array_split(lu, max(1, len(lu) * len(lv) // (1 << 22))):
            red[ex[(chunk[:, None] + lv[None, :]).ravel() % order]] = True
    irr = ~red
    nP = int(irr.sum())
    # count of monic irreducibles of degree m over F_Q, minus f
    mob = lambda k: 0 if any(k % (p*p) == 0 for p in range(2, k+1)) else (-1) ** sum(1 for p in range(2, k+1) if k % p == 0 and all(p % s for s in range(2, p)))
    expected = sum(mob(d) * Q ** (m // d) for d in range(1, m + 1) if m % d == 0) // m - 1
    assert nP == expected, (nP, expected)
    v = np.zeros(order); v[lg[np.nonzero(irr)[0]]] = 1.0
    F = np.fft.fft(v)
    N = np.rint(np.fft.ifft(F * F).real).astype(np.int64)
    assert N.sum() == nP * nP
    lam = nP * nP / order
    e = m * m * (N - lam) / Q ** (m / 2)
    var = float((e ** 2).mean()); kurt = float((e ** 4).mean()) / var ** 2
    mx = float(np.abs(e).max()); gauss = math.sqrt(2 * var * math.log(order))
    srt = np.sort(np.abs(e))[::-1]
    print(f"m={m} r={r:2d} Q={Q:5d} |K*|={order:8d} |P|={nP:7d} lam={lam:10.3f} zeros={(N==0).sum():6d} "
          f"minN/lam={N.min()/lam:6.3f} var(e)={var:7.3f} kurt={kurt:6.3f} max|e|={mx:7.3f} "
          f"max/gauss={mx/gauss:5.3f} max/sqrtQ={mx/math.sqrt(Q):6.3f} top5={np.round(srt[:5],2).tolist()}", flush=True)
    return e, lg, ex, order

if __name__ == "__main__":
    m = int(sys.argv[1])
    for r in map(int, sys.argv[2:]):
        assert math.gcd(r, m) == 1
        run(m, r)
