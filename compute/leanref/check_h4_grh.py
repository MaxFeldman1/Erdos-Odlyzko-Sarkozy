"""(1) H4 block system with the Lean definitions literally (numBlocks, blockPt, primesIn, roughUnits, delta, rho).
(2) GRHBounds ratio |psi(x,chi) - [chi=1]x| / (sqrt(x) log^2(qx)) on small q."""
import numpy as np, math, cmath
from math import gcd, log, ceil, sqrt
from check_inputs import minfac_table

def nceil(x): return max(0, math.ceil(x))          # Nat.ceil

def numBlocks(m, eta, lam):
    if m == 0: lm = 0.0
    else: lm = log(m)
    d = log(1 + lam) if 1 + lam > 0 else (0.0 if 1 + lam == 0 else log(-(1 + lam)))  # Real.log conventions
    return nceil((0.5 - eta) * lm / d) if d != 0 else 0

def blockPt(m, eta, lam, j):
    J = numBlocks(m, eta, lam)
    e = eta + ((0.5 - eta) * j / J if J != 0 else 0.0)
    return nceil(m ** e)

def h4(m, eta, lam):
    mf = minfac_table(m + 1)
    J = numBlocks(m, eta, lam)
    pts = [blockPt(m, eta, lam, j) for j in range(J + 1)]
    units = np.array([n for n in range(1, m) if gcd(n, m) == 1], dtype=np.int64)
    phi = len(units)
    inP = np.zeros(m, dtype=np.int64)
    for p in range(2, m + 1):
        if mf[p] == p and m % p != 0: inP[p] = 1      # p<m automatically
    rho = inP.sum() / phi
    print("m=%d eta=%g lam=%g: J=%d pts=%s (ceil(m^eta)=%d, ceil(sqrt m)=%d) rho=%.4f" %
          (m, eta, lam, J, pts, nceil(m**eta), nceil(sqrt(m)), rho))
    for j in range(J):
        M, M2 = pts[j], pts[j + 1]
        I = [p for p in range(M, M2) if mf[p] == p and m % p != 0]
        iota = len(I)
        K = [k for k in range(1, m + 1) if gcd(k, m) == 1 and k * M <= m and (k == 1 or mf[k] >= M)]
        pi = np.zeros(phi, dtype=np.int64)
        for p in I:
            pi += inP[(units * pow(p, -1, m)) % m]
        d = pi - rho * iota
        lhs = float((d ** 4).sum()); rhs = (eta / 2) ** 4 * rho ** 4 * iota ** 4 * len(K)
        print("  j=%d I=[%d,%d) iota=%d |K|=%d sum delta=%.2e  var/(phi*mu)=%.3f  sum d^4=%.4g  RHS=%.4g  ratio=%s  Poisson-pred ratio=%.3g"
              % (j, M, M2, iota, len(K), d.sum(), (d**2).sum() / (phi * rho * iota) if iota else float('nan'), lhs, rhs,
                 ("%.3g" % (lhs / rhs)) if rhs > 0 else ("0/0 (holds, 0<=0)" if lhs == 0 else "inf"),
                 (phi * (3 * (rho*iota)**2 + rho*iota) / rhs) if rhs > 0 else float('nan')))

def grh(qs, X=200000):
    mf = minfac_table(X)
    lam = np.zeros(X + 1)
    for n in range(2, X + 1):
        p = mf[n]; k = n
        while k % p == 0: k //= p
        if k == 1: lam[n] = log(p)
    xs = np.arange(X + 1, dtype=float)
    worst = (0, None)
    for q in qs:
        units = [a for a in range(1, q + 1) if gcd(a, q) == 1]
        # all characters of (Z/q)^*: build via brute-force group characters as products over cyclic generators
        # simple approach: decompose by trying characters as homomorphisms determined on a generating set
        chars = all_chars(q, units)
        res = np.arange(X + 1) % q
        for ci, chi in enumerate(chars):
            vals = np.array([chi.get(r, 0) for r in range(q)], dtype=complex)
            psi = np.cumsum(lam * vals[res])
            principal = all(abs(chi[u % q] - 1) < 1e-9 for u in units)
            for lo in (0.0, 1.0):   # x = n (lo=0) and x -> (n+1)^- (lo=1): sup over [n, n+1)
                x = xs[2:] + lo * (1 - 1e-12)
                dev = np.abs(psi[2:] - (x if principal else 0))
                r = dev / (np.sqrt(x) * np.log(q * x) ** 2)
                i = int(np.argmax(r))
                if r[i] > worst[0]: worst = (float(r[i]), (q, ci, principal, float(x[i])))
    print("GRHBounds: sup ratio over q in %s, x in [2,%d]: %.4f at (q, char#, principal, x)=%s" % (qs, X, worst[0], worst[1]))

def all_chars(q, units):
    if q == 1: return [{0: 1.0}]
    # generators by greedy
    gens = []; H = {1 % q}
    def closure(gs):
        S = {1 % q}; frontier = [1 % q]
        while frontier:
            a = frontier.pop()
            for g in gs:
                b = a * g % q
                if b not in S: S.add(b); frontier.append(b)
        return S
    for u in units:
        if u not in H:
            gens.append(u); H = closure(gens)
    def order(g):
        k = 1; a = g
        while a != 1 % q: a = a * g % q; k += 1
        return k
    ords = [order(g) for g in gens]
    chars = []
    import itertools
    for exps in itertools.product(*[range(o) for o in ords]):
        chi = {1 % q: 1.0 + 0j}; frontier = [1 % q]; ok = True
        while frontier:
            a = frontier.pop()
            for g, o, e in zip(gens, ords, exps):
                b = a * g % q; v = chi[a] * cmath.exp(2j * math.pi * e / o)
                if b in chi:
                    if abs(chi[b] - v) > 1e-6: ok = False
                else: chi[b] = v; frontier.append(b)
        if ok and not any(all(abs(chi[u % q] - c[u % q]) < 1e-6 for u in units) for c in chars): chars.append(chi)
    assert len(chars) == len(units), (q, len(chars), len(units))
    return chars

if __name__ == "__main__":
    for (e, l) in [(0.6, 1.0), (0.5, 1.0), (0.25, -0.5), (0.25, -1.0), (0.25, -3.0), (0.25, 0.0)]:
        print("degenerate numBlocks(10^6, eta=%g, lam=%g) = %d" % (e, l, numBlocks(10**6, e, l)))
    h4(100003, 0.25, 1.0); h4(100003, 0.25, 0.25); h4(30030, 0.25, 1.0); h4(99990, 0.2, 0.5); h4(65536, 0.25, 1.0)
    grh([1, 2, 3, 4, 5, 7, 8, 12, 15, 24, 30, 31, 60, 101])
