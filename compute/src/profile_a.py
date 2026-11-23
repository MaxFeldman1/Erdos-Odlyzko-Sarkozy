"""Mean of N(a)/lambda as a function of the position a/m (deciles), averaged over many moduli m."""
import numpy as np, math
LIM = 60000
s = np.ones(LIM, bool); s[:2] = False
for i in range(2, int(LIM ** .5) + 1):
    if s[i]: s[i * i::i] = False
primes = np.nonzero(s)[0]
def prof(m):
    P = np.array([p for p in primes[primes <= m] if m % p], dtype=np.int64)
    N = np.bincount((np.outer(P, P) % m).ravel(), minlength=m).astype(float)
    U = np.array([math.gcd(a, m) == 1 for a in range(m)])
    lam = len(P) ** 2 / U.sum()
    a = np.arange(m)[U]
    d = np.minimum((a * 10) // m, 9)
    return np.array([N[a[d == k]].mean() / lam for k in range(10)]), np.array([N[a[d == k]].std() / lam for k in range(10)])
for label, ms in [("primes near 3e4", [p for p in primes if 30000 <= p < 30600][:40]),
                  ("all m in [30000,30040)", list(range(30000, 30040)))]:
    pr = np.array([prof(m)[0] for m in ms])
    print(label, "mean N/lambda by decile of a/m:", np.round(pr.mean(0), 4).tolist(), " (se ~ %.4f)" % (pr.std(0).mean() / np.sqrt(len(ms))))
for label, ms in [("primes near 3e4", [p for p in primes if 30000 <= p < 30600][:40]),
                  ("all m in [30000,30040)", list(range(30000, 30040)))]:
    sd = np.array([prof(m)[1] for m in ms])
    print(label, "sd of N/lambda by decile of a/m:", np.round(sd.mean(0), 4).tolist())
