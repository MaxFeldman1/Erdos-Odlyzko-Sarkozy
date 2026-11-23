"""For each listed m: over all a (or a random sample of size cap), count classes with
 exc2 = dim(W_a) - d'_a > 0  (W_a = projection of ker_F2 onto the small primes)  and with excQ > 0,
and record the statistics of comp2 (root-free components) and of the pendant pairs."""
import sys, random
from math import gcd
from hyperbola_rank import spf_table
from hyperbola_graph import analyse
random.seed(7)
cap = int(sys.argv[1]); doQ = sys.argv[2] == 'Q'
ms = [int(x) for x in sys.argv[3:]]
spf = spf_table(max(ms) + 1)
print('     m  classes  exc2>0  max_exc2  excQ>0  min(comp2) mean(comp2) mean(pairs) comps_not_pairs(mean)  min(cor2-d)')
for m in ms:
    A = [a for a in range(1, m) if gcd(a, m) == 1]
    if len(A) > cap: A = random.sample(A, cap)
    e2 = eq = 0; mx = 0; c2 = []; pp = []; mn = 10**9
    for a in A:
        r = analyse(m, a, spf, doQ=doQ)
        if r['exc2'] > 0: e2 += 1; mx = max(mx, r['exc2'])
        if doQ and r['excQ'] > 0: eq += 1
        c2.append(r['comp2']); pp.append(r['pd'] + r['ps']); mn = min(mn, r['cor2'] - r['da'])
    n = len(A)
    print(f"{m:6d} {n:7d} {e2:7d} {mx:8d} {eq if doQ else '-':>7} {min(c2):10d} {sum(c2)/n:11.2f} {sum(pp)/n:11.2f} {(sum(c2)-sum(pp))/n:14.2f} {mn:12d}", flush=True)
