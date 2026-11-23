"""
Large-prime graph Gamma_a of the modular hyperbola and the refined kernel prediction.

Large prime = prime r with r*r > m (so every n <= m has at most one large prime factor), r not dividing m.
Each row M = n * iota_a(n) has large part (r, r') in {large primes or None}^2.
  two distinct large primes r != r'   -> edge r -- r'
  exactly one large prime             -> r is attached to the root (ROOT)
  r | n and r | iota_a(n)             -> F_2: no constraint;  Q: forces x_r = 0 (attach to ROOT)
  none                                -> 'smooth row', a relation among the small primes only
Proved (Lemma K3): every root-free component gives a kernel vector over F_2 (constant on the component, 0 elsewhere);
every root-free bipartite component gives one over Q (+1/-1 on the two sides).
Refined prediction:  corank_2 = d_a + #rootfree components,  corank_Q = #rootfree bipartite components.
This holds iff the smooth rows force x_small to be a real character with chi(a)=1 (F_2) resp. 0 (Q).
"""
import sys, random
from math import gcd, isqrt
from hyperbola_rank import spf_table, rows, rank_f2, rank_modp, char_dim, pendant_pairs

ROOT = 0

def char_small_dim(m, a, spf):
    """d'_a = dim of {real chi mod m, chi(a)=1} restricted to the small primes (p*p <= m, p not | m).
    Computed in G/G^2 = F_2^r: d'_a = dim(U + <c(a)>) - [c(a) != 0], U = span of the classes of the small primes."""
    units = [x for x in range(1, m) if gcd(x, m) == 1]
    coord = {x * x % m: 0 for x in units}
    r = 0
    for g in units:
        if g not in coord:
            for h, c in list(coord.items()):
                coord[g * h % m] = c | (1 << r)
            r += 1
    def rank(vs):
        basis = {}; k = 0
        for v in vs:
            while v:
                h = v.bit_length() - 1
                if h in basis: v ^= basis[h]
                else: basis[h] = v; k += 1; break
        return k
    small = [coord[p % m] for p in range(2, isqrt(m) + 1) if spf[p] == p and m % p]
    ca = coord[a % m]
    return rank(small + [ca]) - (1 if ca else 0)

class DSU:
    def __init__(self):
        self.p = {}; self.par = {}
    def find(self, x):
        if x not in self.p:
            self.p[x] = x; self.par[x] = 0
            return x, 0
        path = []
        while self.p[x] != x:
            path.append(x); x = self.p[x]
        # recompute parities along the path
        root = x
        for y in reversed(path):
            par_parent = self.par[self.p[y]] if self.p[y] != root else 0
            self.par[y] ^= par_parent
            self.p[y] = root
        return root, None
    def find2(self, x):
        r, _ = self.find(x)
        return r, (self.par[x] if x != r else 0)
    def union(self, x, y, d):
        """constraint parity(x) xor parity(y) = d; returns False if inconsistent (odd cycle)"""
        rx, px = self.find2(x); ry, py = self.find2(y)
        if rx == ry:
            return (px ^ py) == d
        self.p[rx] = ry; self.par[rx] = px ^ py ^ d
        return True

def large_part(n, spf, m):
    best = None
    while n > 1:
        p = spf[n]
        if p * p > m:
            best = p
        n //= p
    return best

def components(m, a, spf):
    large = [p for p in range(2, m + 1) if spf[p] == p and m % p and p * p > m]
    d2 = DSU(); dq = DSU()
    for D in (d2, dq):
        D.find(ROOT)
        for r in large: D.find(r)
    oddQ = set()
    nsmooth = 0
    sizes = {}
    for n in range(1, m):
        if gcd(n, m) != 1: continue
        N = a * pow(n, -1, m) % m
        if n > N: continue
        r, r2 = large_part(n, spf, m), large_part(N, spf, m)
        if r is None and r2 is None:
            nsmooth += 1
        elif r is None or r2 is None:
            x = r if r2 is None else r2
            d2.union(x, ROOT, 0); dq.union(x, ROOT, 0)
        elif r == r2:
            dq.union(r, ROOT, 0)
        else:
            d2.union(r, r2, 0)
            if not dq.union(r, r2, 1):
                oddQ.add(dq.find2(r)[0])
    def count(D, odd=()):
        rootc = D.find2(ROOT)[0]
        oddroots = set(D.find2(x)[0] for x in odd)
        comps = {}
        for r in large:
            c = D.find2(r)[0]
            comps.setdefault(c, []).append(r)
        free = [v for c, v in comps.items() if c != rootc and c not in oddroots]
        return free
    f2 = count(d2); fq = count(dq, oddQ)
    return f2, fq, nsmooth, len(large)

def analyse(m, a, spf, doQ=True):
    primes = [p for p in range(2, m + 1) if spf[p] == p and m % p]
    col = {p: i for i, p in enumerate(primes)}
    rws = rows(m, a, spf)
    f2, fq, nsmooth, nlarge = components(m, a, spf)
    cor2 = len(primes) - rank_f2(rws, col)
    da = char_small_dim(m, a, spf)
    pd, ps = pendant_pairs(m, a, spf)
    out = dict(m=m, a=a, ncol=len(primes), nsmall=len(primes) - nlarge, nsmooth=nsmooth, cor2=cor2, da=da,
               comp2=len(f2), big2=sum(1 for c in f2 if len(c) > 2), pd=pd, ps=ps, exc2=cor2 - da - len(f2))
    if doQ:
        corQ = len(primes) - rank_modp(rws, col)
        out.update(corQ=corQ, compQ=len(fq), excQ=corQ - len(fq))
    return out

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'all':
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        spf = spf_table(hi + 1)
        tot = b2 = bq = 0; last2 = lastq = None; neg = 0
        nozero2 = []   # (m,a) with cor2 == d_a : no non-character symmetry at all
        for m in range(lo, hi + 1):
            e2 = eq = 0
            for a in range(1, m):
                if gcd(a, m) != 1: continue
                r = analyse(m, a, spf); tot += 1
                if r['exc2'] < 0 or r['excQ'] < 0: neg += 1; print('VIOLATION', r)
                if r['exc2']: e2 += 1; b2 += 1; last2 = (m, a, r['exc2'])
                if r['excQ']: eq += 1; bq += 1; lastq = (m, a, r['excQ'])
                if r['cor2'] == r['da']: nozero2.append((m, a))
            if (e2 or eq) and m > hi - 40:
                print(f'm={m:5d}: classes with F2 excess {e2}, with Q excess {eq}')
        print(f'range [{lo},{hi}]: (m,a) pairs {tot}; F2 excess in {b2} (last {last2}); Q excess in {bq} (last {lastq}); violations {neg}')
        print('number of (m,a) with corank_2 = d_a (no non-character symmetry):', len(nozero2), 'largest:', nozero2[-5:])
    else:
        random.seed(2)
        k = int(sys.argv[2]); ms = [int(x) for x in sys.argv[3:]]
        spf = spf_table(max(ms) + 1)
        print('     m      a  ncol nsmall nsmooth  cor2 d_a comp2 (size>2) pairs r!=r\' r=r\'  exc2  corQ compQ excQ')
        for m in ms:
            cand = [1, m - 1, 2 % m] + [random.randrange(2, m) for _ in range(6 * k)]
            cand = [a for a in dict.fromkeys(cand) if gcd(a, m) == 1][:k]
            for a in cand:
                r = analyse(m, a, spf, doQ=(m <= 5000))
                print(f"{m:6d} {a:6d} {r['ncol']:5d} {r['nsmall']:6d} {r['nsmooth']:7d} {r['cor2']:5d} {r['da']:3d} {r['comp2']:5d} {r['big2']:7d} "
                      f"{r['pd']:11d} {r['ps']:4d} {r['exc2']:5d} {str(r.get('corQ','-')):>5} {str(r.get('compQ','-')):>5} {str(r.get('excQ','-')):>4}", flush=True)
