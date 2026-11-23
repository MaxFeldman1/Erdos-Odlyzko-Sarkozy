"""
Relation matrix of the modular hyperbola  n * iota_a(n) = a0 + k m,  iota_a(n) = [a n^{-1}]_m.

Rows   : unordered pairs {n, iota_a(n)}, 1 <= n <= m, gcd(n,m)=1
Columns: primes p <= m, p not dividing m
Entry  : v_p(n * iota_a(n))

x in ker over F_2  <=>  completely multiplicative f: -> {+-1} with f(n) = f(iota_a(n)) for all n <= m.
x in ker over Q    <=>  completely additive g with g(n) + g(iota_a(n)) = 0 for all n <= m.

Proved lower bounds for the kernels (notes/brainstorm/r1-combinatorial.md, Lemma K1/K2):
  F_2: real characters chi mod m with chi(a)=1  (dimension d_a)
       + one vector per unordered pair {r, iota_a(r)} of primes > m/2  (r = iota_a(r) allowed)
  Q  : one vector e_r - e_r' per unordered pair r != r' of primes > m/2 with r r' = a (mod m)
The script computes the true coranks and prints the excess over these lower bounds.
"""
import sys, random
from math import gcd
import numpy as np

def spf_table(N):
    spf = list(range(N + 1))
    i = 2
    while i * i <= N:
        if spf[i] == i:
            for j in range(i * i, N + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf

def factor(n, spf):
    f = {}
    while n > 1:
        p = spf[n]
        f[p] = f.get(p, 0) + 1
        n //= p
    return f

def rows(m, a, spf):
    """list of dicts prime->exponent, one per unordered pair {n, iota(n)}"""
    out = []
    for n in range(1, m):
        if gcd(n, m) != 1:
            continue
        N = a * pow(n, -1, m) % m
        if n <= N:
            f = factor(n, spf)
            for p, e in factor(N, spf).items():
                f[p] = f.get(p, 0) + e
            out.append((n, N, f))
    return out

def rank_f2(rws, col):
    basis = {}
    rk = 0
    for (_, _, f) in rws:
        v = 0
        for p, e in f.items():
            if e & 1:
                v |= 1 << col[p]
        while v:
            h = v.bit_length() - 1
            b = basis.get(h)
            if b is None:
                basis[h] = v
                rk += 1
                break
            v ^= b
    return rk

def rank_modp(rws, col, P=2147483629):
    ncol = len(col)
    A = np.zeros((len(rws), ncol), dtype=np.int64)
    for i, (_, _, f) in enumerate(rws):
        for p, e in f.items():
            A[i, col[p]] = e
    rk = 0
    r = 0
    for c in range(ncol):
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        piv = r + nz[0]
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), -1, P)
        A[r] = (A[r] * inv) % P
        fac = A[r + 1:, c].copy()
        idx = np.nonzero(fac)[0]
        if len(idx):
            A[r + 1 + idx] = (A[r + 1 + idx] - np.outer(fac[idx], A[r]) % P) % P
        r += 1
        rk += 1
        if r == len(rws):
            break
    return rk

def char_dim(m, a):
    """dimension over F_2 of {real characters chi mod m : chi(a) = 1}"""
    units = [x for x in range(1, m) if gcd(x, m) == 1]
    nsq = sum(1 for x in units if x * x % m == 1)      # = 2^r = number of real characters
    r = nsq.bit_length() - 1
    squares = set(x * x % m for x in units)
    return r if (a % m) in squares else r - 1

def pendant_pairs(m, a, spf):
    """unordered pairs {r, iota_a(r)} of primes > m/2; returns (#with r != r', #with r == r')"""
    d = s = 0
    for r in range(m // 2 + 1, m):
        if spf[r] != r or gcd(r, m) != 1:
            continue
        N = a * pow(r, -1, m) % m
        if N > m // 2 and N > 1 and spf[N] == N:
            if N == r:
                s += 1
            elif r < N:
                d += 1
    return d, s

def analyse(m, a, spf, doQ=True):
    primes = [p for p in range(2, m + 1) if spf[p] == p and m % p]
    col = {p: i for i, p in enumerate(primes)}
    rws = rows(m, a, spf)
    r2 = rank_f2(rws, col)
    d, s = pendant_pairs(m, a, spf)
    da = char_dim(m, a)
    cor2 = len(primes) - r2
    res = dict(m=m, a=a, ncol=len(primes), nrow=len(rws), cor2=cor2, da=da, pd=d, ps=s,
               exc2=cor2 - da - d - s)
    if doQ:
        rq = rank_modp(rws, col)
        res['corQ'] = len(primes) - rq
        res['excQ'] = res['corQ'] - d
    return res

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'all':            # every (m, a) with m in [lo, hi]
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        spf = spf_table(hi + 1)
        tot = bad2 = badQ = 0
        last2 = lastQ = None
        for m in range(lo, hi + 1):
            e2 = eq = 0
            na = 0
            for a in range(1, m):
                if gcd(a, m) != 1:
                    continue
                r = analyse(m, a, spf)
                na += 1; tot += 1
                if r['exc2']:
                    e2 += 1; bad2 += 1; last2 = (m, a, r['exc2'])
                if r['excQ']:
                    eq += 1; badQ += 1; lastQ = (m, a, r['excQ'])
                if r['exc2'] < 0 or r['excQ'] < 0:
                    print('VIOLATION of proved lower bound', r)
            if e2 or eq:
                print(f'm={m:5d} classes={na:5d}  classes with F2-excess: {e2:4d}   with Q-excess: {eq:4d}')
        print(f'total (m,a)={tot}, with F2 excess={bad2} (last {last2}), with Q excess={badQ} (last {lastQ})')
    elif mode == 'sample':       # sample of a for listed m
        random.seed(1)
        ms = [int(x) for x in sys.argv[3:]]
        k = int(sys.argv[2])
        spf = spf_table(max(ms) + 1)
        print('     m      a   ncol   nrow  cor2  d_a  pairs(r!=r\') pairs(r=r\')  exc2  corQ  excQ')
        for m in ms:
            cand = [1, m - 1, 2 % m] + [random.randrange(2, m) for _ in range(4 * k)]
            cand = [a for a in dict.fromkeys(cand) if gcd(a, m) == 1][:k]
            for a in cand:
                r = analyse(m, a, spf, doQ=(m <= 6000))
                print(f"{m:6d} {a:6d} {r['ncol']:6d} {r['nrow']:6d} {r['cor2']:5d} {r['da']:4d} {r['pd']:8d} {r['ps']:10d} "
                      f"{r['exc2']:8d} {r.get('corQ','-'):>5} {r.get('excQ','-'):>5}", flush=True)
