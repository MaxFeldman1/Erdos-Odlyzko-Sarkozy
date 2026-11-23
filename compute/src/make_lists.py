"""Generate modulus lists for eos_full (composite/type samples) and eos_char (prime samples)."""
import math, random
random.seed(1)
def sieve(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i * i::i] = bytearray(len(s[i * i::i]))
    return s
LIM = 10 ** 8
isp = sieve(LIM)
def nextprime(n):
    while not isp[n]: n += 1
    return n
def prevprime(n):
    while not isp[n]: n -= 1
    return n

# primes for eos_char: all primes in [5, 20000], plus ~12 primes per factor of sqrt(10) up to 1e8
pr = [p for p in range(5, 20001) if isp[p]]
big = set()
x = 20000.0
while x < LIM * 0.99:
    for t in range(6):
        big.add(nextprime(int(x * (1 + 0.013 * t))))
    x *= 10 ** 0.125
# safe primes (m-1 = 2q, few characters of small order) and primes with smooth m-1
for p in list(big):
    pass
with open("data/list_primes_char.txt", "w") as f:
    f.write("\n".join(map(str, sorted(set(pr) | big))) + "\n")

# composite / typed sample for eos_full, 2e4 < m <= 1e6 (direct pi^2/2 counting)
S = set()
for k in range(15, 21): S.add(2 ** k)
for k in range(10, 13): S.add(3 ** k)
prim = [2 * 3 * 5 * 7 * 11 * 13, 2 * 3 * 5 * 7 * 11 * 13 * 17]
for P0 in [2310, 30030, 510510]:
    for c in range(1, 1000):
        if 20000 < P0 * c <= 10 ** 6 and (c < 8 or random.random() < 0.15): S.add(P0 * c)
# random m in geometric bins
x = 20000.0
while x <= 10 ** 6:
    for _ in range(10): S.add(random.randint(int(x), int(x * 1.15)))
    # prime, 2*prime, prime^2-ish
    S.add(nextprime(int(x))); S.add(2 * nextprime(int(x / 2))); 
    r = int(math.isqrt(int(x))); S.add(nextprime(r) ** 2)
    x *= 1.15
S = sorted(m for m in S if m <= 10 ** 6)
with open("data/list_full_sample.txt", "w") as f:
    f.write("\n".join(map(str, S)) + "\n")
print(len(set(pr) | big), "char primes;", len(S), "full-sample moduli")
