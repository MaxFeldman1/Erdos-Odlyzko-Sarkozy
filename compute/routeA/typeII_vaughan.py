#!/usr/bin/env python3
"""Route A numerics (see notes/routes/A-typeII.md).

For a prime modulus m and units a:
  A_a = {a * pbar mod m : p <= m prime},  F = indicator of A_a on [1, m-1].
  Vaughan (U, V):  Psi = sum_{n<=U} Lambda F + I1 - I2 + II   (exact identity, checked)
  II = sum_n c_II(n) F(n),  c_II = Lambda_{>U} * b,  b_k = sum_{d|k, d>V} mu(d).
Reports: identity check, centred II/(rho m), dyadic blocks G(M), Parseval bounds,
and the same for the barrier sequence A* (random, no primes > D, same Type I data).
Usage: python3 typeII_vaughan.py [m_lower_bound] [n_a] [eta]   (U = V = m^eta)
"""
import sys, math
import numpy as np

def sieve(N):
    isp = np.ones(N + 1, dtype=bool); isp[:2] = False
    for i in range(2, int(N**0.5) + 1):
        if isp[i]: isp[i*i::i] = False
    return isp

def mobius(N, isp):
    mu = np.ones(N + 1, dtype=np.int64)
    for p in np.nonzero(isp)[0]:
        mu[p::p] *= -1
        if p * p <= N: mu[p*p::p*p] = 0
    return mu

def main():
    lo = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**6
    n_a = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    eta = float(sys.argv[3]) if len(sys.argv) > 3 else 1/6
    isp = sieve(lo + 1000)
    m = int(np.nonzero(isp[lo:])[0][0]) + lo
    isp = isp[:m + 1].copy(); isp[m] = False     # primes p <= m, p != m
    mu = mobius(m, isp)
    primes = np.nonzero(isp)[0]
    nP = len(primes); phi = m - 1; rho = nP / phi
    U = V = int(round(m**eta)); D = U * V
    rng = np.random.default_rng(1)
    print(f"m={m} |P|={nP} rho={rho:.5f} U=V={U} D=UV={D} sqrt(m)={m**0.5:.1f} log m={math.log(m):.2f}")

    # Lambda
    Lam = np.zeros(m + 1)
    for p in primes:
        q = int(p); lp = math.log(q)
        while q <= m:
            Lam[q] = lp; q *= int(p)
    # b_k = [k=1] - sum_{d|k, d<=V} mu(d)
    b = np.zeros(m + 1); b[1] = 1.0
    for d in range(1, V + 1):
        if mu[d]: b[d::d] -= mu[d]
    assert abs(b[1:V + 1]).max() == 0
    # c_II and dyadic blocks c_M
    us = np.nonzero(Lam[: m // V + 1] > 0)[0]; us = us[us > U]
    nblk = int(math.log2(m / V / U)) + 1
    cM = np.zeros((nblk, m + 1))
    for u in us:
        u = int(u); j = min(int(math.log2(u / U)), nblk - 1); K = m // u
        cM[j, u:u*K + 1:u] += Lam[u] * b[1:K + 1]
    cII = cM.sum(axis=0)
    cI2 = np.zeros(D + 1)            # c_e = sum_{dc=e, d<=V, c<=U} mu(d) Lambda(c)
    for d in range(1, V + 1):
        for c in range(2, U + 1):
            if mu[d] and Lam[c] > 0: cI2[d*c] += mu[d] * Lam[c]
    logn = np.log(np.maximum(np.arange(m + 1), 1))

    def vaughan(F):
        Psi = float((Lam * F).sum())
        small = float((Lam[:U + 1] * F[:U + 1]).sum())
        I1 = sum(mu[d] * float((F[d::d] * (logn[d::d] - math.log(d))).sum()) for d in range(1, V + 1))
        I2 = sum(cI2[e] * float(F[e::e].sum()) for e in range(1, D + 1) if cI2[e])
        II = float((cII * F).sum())
        return Psi, small, I1, I2, II

    # integer model (F = 1 on units): centring constants
    ones = np.ones(m + 1); ones[0] = 0; ones[m] = 0
    Psi0, small0, I10, I20, II0 = vaughan(ones)
    sumcM = cM[:, 1:m].sum(axis=1)
    l2cM = (cM[:, 1:m]**2).sum(axis=1)
    print(f"integers: Psi/m={Psi0/m:.4f} (I1-I2)/m={(I10-I20)/m:.4f} II/m={II0/m:.4f}  "
          f"sum|c_II|/(m log m)={abs(cII).sum()/m/math.log(m):.3f}  sum c_II^2/(m log^2 m)={(cII**2).sum()/m/math.log(m)**2:.3f}")
    print("blocks: sum c_M^2/(m log m) =", np.round(l2cM / m / math.log(m), 3))

    # inverses mod m
    inv = np.zeros(m, dtype=np.int64); inv[1] = 1
    for i in range(2, m): inv[i] = (-(m // i) * inv[m % i]) % m
    # discrete log for character sums
    def prim_root():
        fac = [int(p) for p in primes if (m - 1) % p == 0]
        g = 2
        while any(pow(g, (m - 1)//p, m) == 1 for p in fac): g += 1
        return g
    g = prim_root(); dlog = np.zeros(m, dtype=np.int64); x = 1
    for k in range(m - 1):
        dlog[x] = k; x = x * g % m
    def maxchar(ind):   # max over nonprincipal chi of |sum_n ind(n) chi(n)|
        v = np.zeros(m - 1); v[dlog[1:m]] = ind[1:m]
        f = np.abs(np.fft.rfft(v)); return float(f[1:].max()), float(np.sqrt((f[1:]**2).mean()))
    mxP, rmsP = maxchar(isp.astype(float))
    print(f"primes: max|S(chi)|/sqrt(m)={mxP/m**0.5:.3f}  rms/sqrt(m)={rmsP/m**0.5:.3f}")

    # rough composites (all prime factors > D), for the barrier sequence
    rough = np.ones(m + 1, dtype=bool); rough[:2] = False; rough[m] = False
    for p in primes[primes <= D]: rough[p::p] = False
    RC = rough & ~isp
    bigP = isp.copy(); bigP[:D + 1] = False
    kappa = bigP.sum() / RC.sum()
    print(f"rough composites: {RC.sum()}  kappa={kappa:.3f}  inclusion prob on RC = {rho*(1+kappa):.3f}")

    def typeI_disc(F):   # max_{d<=D} |#A_d - rho*#{n<m: d|n}|, and sum
        r = np.array([F[d::d].sum() - rho * ((m - 1)//d) for d in range(1, D + 1)])
        return abs(r).max(), abs(r).sum(), r[0]

    rows = []
    for t in range(n_a):
        a = int(rng.integers(2, m - 1))
        F = np.zeros(m + 1); F[1:m] = isp[(a * inv[1:m]) % m]
        Psi, small, I1, I2, II = vaughan(F)
        assert abs(Psi - (small + I1 - I2 + II)) < 1e-5 * m, "Vaughan identity failed"
        GM = (cM[:, 1:m] * F[1:m]).sum(axis=1) - rho * sumcM
        # redacted: remove primes from A (A' = A \ P): Type II unchanged exactly
        Fr = F * (~isp); IIr = float((cII * Fr).sum())
        # barrier A*: random, prob rho off big primes, rho(1+kappa) on rough composites, 0 on primes > D
        prob = np.full(m + 1, rho); prob[RC] = rho * (1 + kappa); prob[bigP] = 0; prob[0] = prob[m] = 0
        Fs = (rng.random(m + 1) < prob).astype(float)
        Ps, ss, I1s, I2s, IIs = vaughan(Fs)
        GMs = (cM[:, 1:m] * Fs[1:m]).sum(axis=1) - rho * sumcM
        mxS, rmsS = maxchar(Fs)
        dA = typeI_disc(F); dS = typeI_disc(Fs)
        rows.append((a, Psi/(rho*m), (I1-I2)/(rho*m), (II - rho*II0)/(rho*m), abs(IIr-II),
                     Ps/(rho*m), (I1s-I2s)/(rho*m), (IIs - rho*II0)/(rho*m), mxS/m**0.5, dA[0], dS[0], dA[2], dS[2]))
        if t == 0:
            par = np.sqrt(nP * l2cM)
            print("a=%d dyadic blocks (u in (U 2^j, U 2^{j+1}]):" % a)
            print("  G_c(M)/(rho m)      A :", np.round(GM/(rho*m), 4))
            print("  G_c(M)/(rho m)      A*:", np.round(GMs/(rho*m), 4))
            print("  Parseval bd/(rho m)   :", np.round(par/(rho*m), 2))
            print("  target (1/log m)      : %.4f" % (1/math.log(m)))
    print("\n a | A: Psi/(rho m)  (I1-I2)/(rho m)  II_c/(rho m)  |II(A\\P)-II(A)| | A*: Psi  (I1-I2)  II_c  max|S*|/sqrt m | TypeI max disc A, A* | r_1 A, A*")
    for r in rows:
        print("%8d | %.4f %.4f %+.4f %.1e | %.4f %.4f %+.4f %.3f | %.1f %.1f | %.1f %.1f" % r)
    arr = np.array(rows)
    print("\nmean over a:  A: Psi=%.4f II_c=%+.4f (sd %.4f) ;  A*: Psi=%.4f II_c=%+.4f ; max|S*|/sqrt m=%.3f (primes %.3f)" %
          (arr[:,1].mean(), arr[:,3].mean(), arr[:,3].std(), arr[:,5].mean(), arr[:,7].mean(), arr[:,8].max(), mxP/m**0.5))

if __name__ == "__main__":
    main()
