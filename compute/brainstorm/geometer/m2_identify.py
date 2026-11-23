#!/usr/bin/env python3
"""m = 2, char 2: identify the rank-2 object.  K = F_{Q^2}, Q = 2^r (r odd), tau^2 + tau + 1 = 0, U = tau + F_Q.
D4'(a) = #{(al_1..al_4) in F_Q^4 : prod (tau + al_i) = a}.  Compare the values of D4'(a) - Q^2 with Kloosterman sums
Kl_Q(c) = sum_{x in F_Q^*} psi(x + c/x), and look for the invariant c(a)."""
import sys, numpy as np
import tower_eos as T
def tr(x, n):                       # absolute trace of field element given as bitmask, via repeated squaring (python ints)
    raise NotImplementedError
for r in (3, 5, 7):
    m = 2; n = 2 * r; Q = 1 << r
    ex, lg, order = T.field(n)
    step = order // 3; tau = int(ex[step])        # element of order 3
    sub = order // (Q - 1)
    FQ = np.concatenate(([0], ex[np.arange(Q - 1) * sub]))
    U = FQ ^ tau
    v = np.zeros(order); v[lg[U]] = 1
    F = np.fft.fft(v); D4 = np.rint(np.fft.ifft(F ** 4).real).astype(np.int64)
    t = D4 - Q * Q
    # absolute trace on F_Q elements: psi(x) = (-1)^{Tr x}; compute Tr via logs: Tr(x) = sum x^{2^i}
    def trace_Q(x):                 # x array of elements of F_Q (as elements of K)
        acc = np.zeros_like(x); y = x.copy()
        for _ in range(r):
            acc ^= y
            y = np.where(y == 0, 0, ex[(2 * lg[y]) % order])
        return acc                  # 0 or 1
    assert set(np.unique(trace_Q(FQ))) <= {0, 1}
    xs = FQ[1:]
    kl = {}
    for c in FQ[1:]:
        cx = ex[(lg[c] - lg[xs]) % order]
        kl[int(c)] = int((1 - 2 * trace_Q(xs ^ cx)).sum())
    klvals = sorted(set(kl.values()))
    vals, cnt = np.unique(t, return_counts=True)
    print(f"r={r} Q={Q}: distinct values of D4'-Q^2: {len(vals)}; range [{vals.min()},{vals.max()}]; 2Q={2*Q}")
    print("   values:", vals.tolist()[:40])
    print("   Kl_Q values:", klvals[:40])
    # candidate invariants: N(a) = a^(Q+1) in F_Q ; Tr(a) = a + a^Q
    idx = np.arange(order)
    a = ex[idx]; aQ = ex[(Q * idx) % order]
    Nm = ex[((Q + 1) * idx) % order]; Tra = a ^ aQ
    for name, inv in (("N(a)", Nm), ("Tr(a)", Tra), ("N(a)+Tr(a)", Nm ^ Tra), ("N(a)+Tr(a)+1", Nm ^ Tra ^ 1)):
        const = all(len(set(t[inv == c].tolist())) == 1 for c in np.unique(inv))
        print(f"   t is a function of {name}: {const}")
        if const:
            pairs = sorted({(int(c), int(t[inv == c][0])) for c in np.unique(inv)})
            match = [(c, tv, kl.get(c)) for c, tv in pairs][:8]
            print("      (c, t, Kl(c)) samples:", match)
