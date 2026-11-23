#!/usr/bin/env python3
"""Referee check of hypothesis H (GRHSmoothBound) from notes/routes/C-log-exponent.md.

For every q in QS and every Dirichlet character chi mod q, and x in [1, XMAX], compute

    ratio(q, chi, x) = | psiC(x, chi) - [chi = principal] x/2 | / ( sqrt(x) * log(2q) ),
    psiC(x, chi)     = sum_{n <= x} Lambda(n) chi(n) (1 - n/x)        (exactly the Lean definition).

psiC is continuous in x, and on [N, N+1) it equals A_N - B_N / x with
A_N = sum_{n<=N} Lambda(n) chi(n), B_N = sum_{n<=N} Lambda(n) chi(n) n.  We evaluate the ratio
  * at every integer x = N in [1, XMAX], and
  * at SUB equally spaced interior points of each interval [N, N+1) (SUB = 64 for N < 2000,
    SUB = 4 beyond), plus the left limit x -> (N+1)^-,
so the supremum over real x is captured up to a negligible discretisation error
(|d/dx| of the numerator is <= 1/2 + |B_N|/x^2 <= 1.1).

Characters are built from the group structure, so all q are handled (complex values for q = 5).
Arithmetic: numpy float64 with Kahan-free cumsum is accurate to ~1e-9 relative here; a second pass
with mpmath (50 digits) re-evaluates the worst points found and a sample of points exactly.
"""
import sys, math, cmath, itertools
import numpy as np
import mpmath as mp

XMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
QS = [1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 15, 16, 24, 30, 60, 101, 210, 2310, 30030]


def mangoldt_table(N):
    """lam[n] = Lambda(n) as float64; also returns (p, k) info for exact recomputation."""
    lam = np.zeros(N + 1)
    base = np.zeros(N + 1, dtype=np.int64)
    sieve = np.ones(N + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    for p in np.nonzero(sieve)[0]:
        p = int(p)
        lp = math.log(p)
        pk = p
        while pk <= N:
            lam[pk] = lp
            base[pk] = p
            pk *= p
    return lam, base


def characters(q):
    """All Dirichlet characters mod q as dict: list of (name, values array length q, is_principal)."""
    if q == 1:
        return [("triv", np.ones(1, dtype=complex), True)]
    units = [a for a in range(q) if math.gcd(a, q) == 1]
    phi = len(units)
    # brute-force: find generators of the abelian group greedily, build characters as homs
    # method: characters = common eigen-structure; use decomposition by repeatedly adjoining elements
    order = {}
    for a in units:
        k, t = 1, a
        while t != 1:
            t = t * a % q
            k += 1
        order[a] = k
    gens, sub = [], {1}
    rel = []  # (g, index of <g> over previous subgroup)
    for a in sorted(units, key=lambda u: -order[u]):
        if a in sub:
            continue
        # smallest k>0 with a^k in sub
        k, t = 1, a
        while t not in sub:
            t = t * a % q
            k += 1
        new = set()
        t = 1
        for j in range(k):
            for s in sub:
                new.add(s * t % q)
            t = t * a % q
        gens.append(a)
        rel.append(k)
        sub = new
        if len(sub) == phi:
            break
    # general hom: brute force over assignments g -> root of unity of order dividing order[g],
    # keep those that are consistent (well defined) -- check by building the table.
    chars = []
    for exps in itertools.product(*[range(order[g]) for g in gens]):
        table = {1: 1 + 0j}
        ok = True
        frontier = [1]
        vals = [cmath.exp(2j * math.pi * e / order[g]) for e, g in zip(exps, gens)]
        while frontier and ok:
            nxt = []
            for s in frontier:
                for g, v in zip(gens, vals):
                    t = s * g % q
                    w = table[s] * v
                    if t in table:
                        if abs(table[t] - w) > 1e-9:
                            ok = False
                            break
                    else:
                        table[t] = w
                        nxt.append(t)
                if not ok:
                    break
            frontier = nxt
        if not ok:
            continue
        arr = np.zeros(q, dtype=complex)
        for a, v in table.items():
            # snap to exact roots of unity where possible
            arr[a] = complex(round(v.real, 12), round(v.imag, 12))
        chars.append(arr)
    # dedupe
    uniq = []
    for c in chars:
        if not any(np.allclose(c, d, atol=1e-8) for d in uniq):
            uniq.append(c)
    assert len(uniq) == phi, (q, len(uniq), phi)
    out = []
    for i, c in enumerate(uniq):
        princ = all(abs(c[a] - 1) < 1e-9 for a in units)
        out.append((f"chi{i}", c, princ))
    # orthogonality sanity check
    M = np.array([c[units] for _, c, _ in out])
    assert np.allclose(M @ M.conj().T, phi * np.eye(phi), atol=1e-6)
    assert sum(p for _, _, p in out) == 1
    return out


def scan(q, name, chi, princ, lam, N):
    """Return (max ratio, x at max, max over integers only, x)."""
    n = np.arange(N + 1)
    w = lam * chi[n % q]
    A = np.cumsum(w)
    B = np.cumsum(w * n)
    lq = math.log(2 * q)
    best = (0.0, None)
    besti = (0.0, None)

    def upd(xs, Aseg, Bseg):
        nonlocal best
        val = Aseg - Bseg / xs - (xs / 2 if princ else 0.0)
        r = np.abs(val) / (np.sqrt(xs) * lq)
        j = int(np.argmax(r))
        if r[j] > best[0]:
            best = (float(r[j]), float(xs[j]))
        return r

    # integers
    xs = n[1:].astype(float)
    r = upd(xs, A[1:], B[1:])
    j = int(np.argmax(r))
    besti = (float(r[j]), float(xs[j]))
    # interior points
    def interior(lo, hi, SUB):
        NN = np.arange(lo, hi)
        for t in list((np.arange(1, SUB) / SUB)) + [1 - 1e-12]:
            upd(NN + t, A[lo:hi], B[lo:hi])
    cut = min(2000, N)
    interior(1, cut, 64)
    if N > cut:
        interior(cut, N, 4)
    return best, besti


def exact_ratio(q, chi_mp, princ, x, base):
    """50-digit recomputation at a single real x."""
    mp.mp.dps = 50
    x = mp.mpf(x)
    s = mp.mpc(0)
    for nn in range(2, int(mp.floor(x)) + 1):
        p = int(base[nn])
        if p:
            s += mp.log(p) * chi_mp[nn % q] * (1 - mp.mpf(nn) / x)
    if princ:
        s -= x / 2
    return abs(s) / (mp.sqrt(x) * mp.log(2 * q))


def main():
    lam, base = mangoldt_table(XMAX)
    print(f"# XMAX = {XMAX}")
    print("# q  phi  worst_ratio  at_x  character  principal  | worst over integer x  at")
    overall = (0.0, None)
    worst_nonprinc = (0.0, None)
    for q in QS:
        chars = characters(q)
        qbest = (0.0, None, None, None)
        qbesti = (0.0, None)
        for name, chi, princ in chars:
            b, bi = scan(q, name, chi, princ, lam, XMAX)
            if b[0] > qbest[0]:
                qbest = (b[0], b[1], name, princ, chi)
            if bi[0] > qbesti[0]:
                qbesti = bi
            if not princ and b[0] > worst_nonprinc[0]:
                worst_nonprinc = (b[0], (q, name, b[1]))
        r, x, name, princ, chi = qbest
        # high-precision recheck of the worst point (cap the cost)
        chk = ""
        if x <= 200000:
            chi_mp = [mp.mpc(complex(v)) for v in chi]
            e = exact_ratio(q, chi_mp, princ, x, base)
            chk = f"  mp50={mp.nstr(e, 12)}"
        print(f"{q:6d} {len(chars):5d}  {r:.6f}  x={x:.6f}  {name:6s} princ={princ}"
              f"  | int: {qbesti[0]:.6f} at {qbesti[1]:.0f}{chk}")
        sys.stdout.flush()
        if r > overall[0]:
            overall = (r, (q, name, x, princ))
    print("# overall worst ratio:", overall)
    print("# worst non-principal:", worst_nonprinc)
    # large-x behaviour: sup of ratio over x in [XMAX/10, XMAX] for each q
    print("# tail sup over x in [XMAX/10, XMAX] (integers):")
    n = np.arange(XMAX + 1)
    for q in QS:
        chars = characters(q)
        tail = 0.0
        tn = None
        for name, chi, princ in chars:
            w = lam * chi[n % q]
            A = np.cumsum(w)
            B = np.cumsum(w * n)
            xs = n[XMAX // 10:].astype(float)
            val = A[XMAX // 10:] - B[XMAX // 10:] / xs - (xs / 2 if princ else 0)
            r = np.abs(val) / (np.sqrt(xs) * math.log(2 * q))
            if r.max() > tail:
                tail, tn = float(r.max()), (name, princ)
        print(f"  q={q:6d}  tail sup = {tail:.6f}  {tn}")


if __name__ == "__main__":
    main()
