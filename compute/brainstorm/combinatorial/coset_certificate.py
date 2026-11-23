"""
Route M experiment.  Proved inequality (prime m, H <= G subgroup, any a):
    N(aH) := sum_{h in H} N(ah)  >=  2|H| lam - T(H),   T(H) := sum_{h in H} N^-(h) = sum over cosets c of |P cap cH|^2,
lam = pi^2/phi.  So the symmetric (|S|^2) data certify 'aH meets P.P' for EVERY a as soon as T(H) < 2|H| lam.
For each subgroup H of G = (Z/m)^* (m prime) print |H|, T(H)/(|H| lam), and whether the certificate holds.
Heuristic threshold: T(H) ~ pi + (|H|-1) lam  =>  certificate iff |H| > phi/pi ~ log m.
"""
import sys
import numpy as np

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

def primitive_root(p):
    f = []; n = p - 1; d = 2
    while d * d <= n:
        if n % d == 0:
            f.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: f.append(n)
    g = 2
    while any(pow(g, (p - 1) // q, p) == 1 for q in f): g += 1
    return g

def main():
    for m in [int(x) for x in sys.argv[1:]]:
        phi = m - 1
        g = primitive_root(m)
        dlog = np.zeros(m, dtype=np.int64); x = 1
        for k in range(phi):
            dlog[x] = k; x = x * g % m
        P = primes_upto(m - 1)
        pi = len(P); lam = pi * pi / phi
        ind = np.zeros(phi); ind[dlog[P]] = 1
        F = np.fft.rfft(ind)
        Nminus = np.rint(np.fft.irfft(np.abs(F) ** 2, n=phi)).astype(np.int64)   # N^-(g^k) = #{p = g^k q}
        assert Nminus[0] == pi
        print(f'm={m}  pi={pi}  lam={lam:.2f}  phi/pi={phi/pi:.2f}  log m={np.log(m):.2f}')
        print('   |H|   index   T(H)/(|H| lam)   mean_{h!=1} N^-(h)/lam   certificate(T < 2|H|lam)   contains -1')
        divs = [d for d in range(1, phi + 1) if phi % d == 0]
        for d in divs:                       # H = <g^d>, |H| = phi/d
            h = phi // d
            if h > 400 * np.log(m): continue
            T = int(Nminus[::d].sum())
            mean_off = (T - pi) / ((h - 1) * lam) if h > 1 else float('nan')
            print(f'{h:7d} {d:7d} {T/(h*lam):12.3f} {mean_off:18.3f} {str(T < 2*h*lam):>18} {str(h % 2 == 0):>18}')

if __name__ == '__main__':
    main()
