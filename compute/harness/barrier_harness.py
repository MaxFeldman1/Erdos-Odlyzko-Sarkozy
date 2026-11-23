#!/usr/bin/env python3
"""Barrier harness for the Buchstab/H4 route (notes/routes/E-buchstab-H4.md, section 7).

Evaluates the block statistics of H4(eta), LD(eta) and the block inequality BI(eta) with a set X of
units mod m in the role of P, for the six barrier objects

  P        primes <= m not dividing m
  Pinv     {p^{-1}}                       (conjugate / quotient problem, Theorem G)
  P-R_a    P minus the primes occurring in a representation a = p q   (deletion)
  A*_a     X = a (A*)^{-1}, A* = random set with density rho, no primes >= z, z-rough composites
           boosted by 1+kappa  (route A, Theorem B, simplified version of typeII_vaughan.py)
  Ravoid   random set of density rho with X cap a X^{-1} empty
  RS_a     deterministic antisymmetric signing f(a/x) = -f(x) built from the Rudin-Shapiro sequence in
           discrete-log coordinates, X = {f = +1}, density 1/2, |hat f(chi)| <= C sqrt(phi).
           (Stand-in for the Spencer signing of route C Prop. L, which is an existence statement.)

Blocks: z = m^eta, M_j = z (1+lam_m)^j, j = 0..J, M_J = sqrt(m) exactly (lam_m <= lam), I_j = primes
in [M_j, M_{j+1}) not dividing m, iota_j = #I_j, K_j = {k <= m/M_j, (k,m)=1, k=1 or lpf(k) >= M_j}.
For X of density rho_X = |X|/phi:
  pi_j(c)  = #{p1 in I_j : c/p1 in X},   delta_j(c) = pi_j(c) - rho_X iota_j        (c in G)
  var      = mean delta^2 / (rho_X (1-rho_X) iota_j)        (Bernoulli model = 1)
  kurt     = mean delta^4 / (mean delta^2)^2
  H4       = sum_c delta^4 / ((eta/2)^4 rho_X^4 iota_j^4 |K_j|)      (H4(eta) asks <= 1)
  LD       = max_{i>=0} E(2^i T_j) / (|K_j| 4^{-i} / 4), T_j = eta rho_X iota_j / 4,
             E(T) = #{c : delta_j(c) > T}                    (LD(eta) asks <= 1); also E(T_j)/|K_j|
  arc(a)   = sum_{k in K_j} delta_j(a/k) / (rho_X iota_j |K_j|)      (BI(eta) asks <= eta/2 for all a)
Works for moduli with cyclic unit group (m prime, m = r^2 with r an odd prime, ...), by FFT over
discrete logarithms.

Usage: python3 barrier_harness.py m [eta] [lam] [seed]
"""
import sys, math
import numpy as np


def lpf_sieve(N):
    lpf = np.zeros(N + 1, dtype=np.int32)
    for i in range(2, N + 1):
        if lpf[i] == 0:
            sl = lpf[i::i]
            sl[sl == 0] = i
    return lpf


def factor(n):
    f, d = [], 2
    while d * d <= n:
        if n % d == 0:
            f.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        f.append(n)
    return f


def rudin_shapiro(n):
    """r(k) = (-1)^{number of occurrences of 11 in the binary expansion of k}, k < n."""
    k = np.arange(n, dtype=np.int64)
    x = k & (k >> 1)
    par = np.zeros(n, dtype=np.int64)
    while x.any():
        par ^= (x & 1)
        x >>= 1
    return 1 - 2 * par


def main():
    m = int(float(sys.argv[1])) if len(sys.argv) > 1 else 1000003
    eta = float(sys.argv[2]) if len(sys.argv) > 2 else 0.25
    lam = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    rng = np.random.default_rng(seed)
    L = math.log(m)
    lpf = lpf_sieve(m)
    n = np.arange(m + 1)
    unit = np.gcd(n, m) == 1
    unit[0] = False
    phi = int(unit[:m].sum())
    isp = (lpf == n) & (n >= 2)
    isP = isp & unit                       # P
    isP[m:] = False
    P = np.nonzero(isP)[0]
    nP = len(P)
    rho = nP / phi
    mu = nP * nP / phi
    # generator and discrete logs
    fac = factor(phi)
    g = 2
    while math.gcd(g, m) != 1 or any(pow(g, phi // q, m) == 1 for q in fac):
        g += 1
    dl = np.full(m, -1, dtype=np.int64)
    x = 1
    for t in range(phi):
        dl[x] = t
        x = x * g % m
    assert x == 1 and (dl[np.nonzero(unit[:m])[0]] >= 0).all(), "unit group not cyclic / bad generator"
    U = np.nonzero(unit[:m])[0]

    def tolog(ind):                         # indicator on residues -> vector on Z/phi
        v = np.zeros(phi)
        v[dl[U]] = ind[U]
        return v

    def conv(u, v):                         # (u*v)[t] = sum_s u[s] v[t-s]
        return np.fft.irfft(np.fft.rfft(u) * np.fft.rfft(v), phi)

    def inv_log(v):                         # X -> X^{-1}
        w = np.empty_like(v)
        w[0] = v[0]
        w[1:] = v[:0:-1]
        return w

    def shift(v, alpha):                    # X -> g^alpha X
        return np.roll(v, alpha)

    Plog = tolog(isP[:m].astype(float))
    # N(a) for all a, and the two test classes
    Nall = np.rint(conv(Plog, Plog)).astype(np.int64)
    al_min = int(Nall.argmin())
    a_min = pow(g, al_min, m)
    print(f"m={m} phi={phi} |P|={nP} rho={rho:.5f} mu={mu:.1f} log m={L:.3f} generator={g}")
    print(f"N(a)/mu: min={Nall.min()/mu:.4f} (a={a_min}) max={Nall.max()/mu:.4f}; eta={eta} lam={lam} seed={seed}")

    # blocks tiling [z, sqrt m)
    z = m ** eta
    J = max(1, math.ceil((0.5 - eta) * L / math.log(1 + lam)))
    q = math.exp((0.5 - eta) * L / J)
    Ms = [z * q ** j for j in range(J)] + [math.sqrt(m)]
    blocks = []
    for j in range(J):
        Ij = P[(P >= Ms[j]) & (P < Ms[j + 1])]
        kk = np.arange(1, int(m // Ms[j]) + 1)
        kk = kk[unit[kk] & ((kk == 1) | (lpf[kk] >= Ms[j]))]
        indI = np.zeros(m); indI[Ij] = 1
        indK = np.zeros(m); indK[kk] = 1
        blocks.append((Ms[j], Ms[j + 1], len(Ij), len(kk), tolog(indI), tolog(indK)))
    # Lemma 2.2 check: sum_j iota_j |K_j| against B0 = #{n < m unit : z <= lpf(n) < sqrt m}
    nn = np.arange(2, m)
    B0 = int((unit[nn] & (lpf[nn] >= z) & (lpf[nn] < math.sqrt(m))).sum())
    maj = sum(b[2] * b[3] for b in blocks)
    Phi = 1 + int((unit[nn] & (lpf[nn] >= z)).sum())
    bigP = isP.copy(); bigP[: int(math.ceil(z))] = False
    RC = unit.copy(); RC[m:] = False; RC[:2] = False
    RC &= (lpf >= z) & ~isp                 # z-rough composite units
    kappa = bigP.sum() / RC.sum()
    print(f"z={z:.2f} J={J} lam_m={q-1:.4f}  Phi_m(m,z)={Phi} B0={B0}  sum_j iota_j|K_j|={maj}  ratio={maj/B0:.4f}"
          f"  theta0=#primes>=z/#rough composites={kappa:.4f}")

    # ---- objects (in log coordinates), each with the class a it is built for (or None) ----
    objs = []
    objs.append(("P", Plog, None))
    objs.append(("Pinv", inv_log(Plog), None))
    for tag, al in (("min", al_min), ("typ", int(rng.integers(1, phi)))):
        a = pow(g, al, m)
        # deletion: R_a = {p in P : a/p in P}
        Ra = Plog * shift(inv_log(Plog), al)          # 1_P(t) 1_P(al - t)
        objs.append((f"P-R_a[{tag}]", Plog - Ra, al))
        # A*: random, prob rho, 0 on primes >= z, rho(1+kappa) on z-rough composites
        prob = np.where(unit[:m], rho, 0.0)
        prob[RC[:m]] = rho * (1 + kappa)
        prob[bigP[:m]] = 0.0
        Astar = (rng.random(m) < prob).astype(float)
        objs.append((f"A*_a[{tag}]", shift(inv_log(tolog(Astar)), al), al))   # X = a (A*)^{-1}
        # random pairing-avoiding set of density rho
        t = np.arange(phi); tp = (al - t) % phi
        u = rng.random(phi)
        R = np.zeros(phi)
        rep = t < tp
        R[t[rep & (u < rho)]] = 1
        R[tp[rep & (u >= rho) & (u < 2 * rho)]] = 1
        assert (R * shift(inv_log(R), al)).sum() == 0
        objs.append((f"Ravoid[{tag}]", R, al))
        # Rudin-Shapiro antisymmetric signing about the involution t -> al - t
        h = phi // 2
        rs = rudin_shapiro(h)
        f = np.zeros(phi)
        if al % 2 == 0:                    # s = t - al/2, pairs s <-> -s, fixed points s = 0, h
            s = np.arange(1, h)
            f[(al // 2 + s) % phi] = rs[s]
            f[(al // 2 - s) % phi] = -rs[s]
        else:                              # t = (al+1)/2 + s, pairs s <-> -1-s
            s = np.arange(0, h)
            f[((al + 1) // 2 + s) % phi] = rs[s]
            f[((al + 1) // 2 - 1 - s) % phi] = -rs[s]
        S = (f > 0).astype(float)
        assert (S * shift(inv_log(S), al)).sum() == 0
        fh = np.abs(np.fft.rfft(f))
        print(f"RS_a[{tag}]: a={a} |X|/phi={S.sum()/phi:.4f} max|hat f|/sqrt(phi)={fh.max()/math.sqrt(phi):.3f}"
              f"   (P: max|S(chi)|/sqrt(phi)={np.abs(np.fft.rfft(Plog))[1:].max()/math.sqrt(phi):.3f})")
        objs.append((f"RS_a[{tag}]", S, al))

    print("\nPer block and object.  H4 and LD ask for a value <= 1;  BI asks arc <= eta/2 = %.4f for every a." % (eta / 2))
    print("%-13s %-17s %5s %6s | %6s %6s %6s | %10s %9s %8s | %8s %8s %8s"
          % ("object", "block [M,M')", "iota", "|K|", "rho_X", "var", "kurt", "H4", "LD", "E(Tj)/|K|",
             "arc max", "arc sd", "arc(a)"))
    tot = {}
    for name, X, al in objs:
        nX = X.sum(); rX = nX / phi
        num = np.zeros(phi); den = 0.0
        for (M0, M1, iota, nK, Ilog, Klog) in blocks:
            if iota == 0:
                continue
            pi = np.rint(conv(X, Ilog))                    # pi(c) = sum_{p1} 1_X(c/p1)
            d = pi - rX * iota
            m2 = (d ** 2).mean(); m4 = (d ** 4).mean()
            var = m2 / (rX * (1 - rX) * iota); kurt = m4 / m2 ** 2
            H4 = (d ** 4).sum() / ((eta / 2) ** 4 * rX ** 4 * iota ** 4 * nK)
            Tj = eta * rX * iota / 4
            LD, i = 0.0, 0
            while 2 ** i * Tj < iota:
                E = float((d > 2 ** i * Tj).sum())
                LD = max(LD, E / (nK * 4.0 ** (-i) / 4))
                i += 1
            E0 = float((d > Tj).sum()) / nK
            arc = conv(d, Klog)                            # arc(a) = sum_k delta(a/k)
            arcn = arc / (rX * iota * nK)
            num += arc; den += rX * iota * nK
            at = "%8.4f" % arcn[al] if al is not None else "       -"
            print("%-13s [%7.1f,%7.1f) %5d %6d | %6.4f %6.3f %6.3f | %10.3e %9.3e %8.3f | %8.4f %8.4f %s"
                  % (name, M0, M1, iota, nK, rX, var, kurt, H4, LD, E0, arcn.max(), arcn.std(), at))
        tn = num / den
        tot[name] = (tn.max(), tn.std(), tn[al] if al is not None else float("nan"))
    print("\nAll blocks together: T(a) = sum_j sum_{k in K_j} delta_j(a/k) / (rho_X sum_j iota_j |K_j|).")
    print("BI(eta) for all blocks gives T(a) <= eta/2 = %.4f;  Lemma C' certifies N(a) > 0 when (S(A_a,z) = rho Phi_m assumed)"
          "  T(a) < (Phi_m - 1/rho - maj)/maj = %.4f" % (eta / 2, (Phi - 1 / rho - maj) / maj))
    print("%-13s %9s %9s %9s" % ("object", "max_a T", "sd_a T", "T(a)"))
    for name, _, _ in objs:
        print("%-13s %9.4f %9.4f %9.4f" % ((name,) + tot[name]))


if __name__ == "__main__":
    main()
