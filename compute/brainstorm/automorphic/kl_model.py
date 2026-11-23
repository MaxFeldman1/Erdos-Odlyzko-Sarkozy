#!/usr/bin/env python3
"""
Major-arc ("Kloosterman singular series") model for Pi(c) and for E(a), prime m.

Model:  Phat(h) ~ Phat#(h) := mu(r)/phi(r) * I(j/r)   when r h = j + b m, r <= R squarefree, (b,r)=1, |j| <= J r,
        I(beta) := sum_{p<=m} e(beta p/m)   (computed exactly; ~ (m/L)(e(beta)-1)/(2 pi i beta)).
Then    Pi#(c) = sum_{hl=c} Phat#(h) Phat#(l),   E##(a) = m^{-2} sum_c Pi#(c) K(ac) - mean.
Reports: how well Phat# matches Phat on the major arcs; variance of E explained by E## (R-dependence);
         the split of Var E into ##, #b, bb parts;  statistics of the residual.
Usage: python3 kl_model.py m R1,R2,...
"""
import sys, math
import numpy as np
from kl_dual import primes_upto, primitive_root, ratrec

def mobius_phi(R):
    mu = np.ones(R + 1, dtype=int); ph = np.arange(R + 1)
    for p in range(2, R + 1):
        if ph[p] == p:
            ph[p::p] -= ph[p::p] // p
            mu[p::p] *= -1
            mu[p*p::p*p] = 0
    return mu, ph

def main():
    m = int(sys.argv[1]); Rs = [int(x) for x in sys.argv[2].split(",")]; J = 3
    L = math.log(m); pr = primes_upto(m); pr = pr[pr < m]; nP = len(pr); n = m - 1
    ind = np.zeros(m, dtype=np.int64); exp = np.zeros(n, dtype=np.int64)
    g = primitive_root(m); x = 1
    for k in range(n):
        exp[k] = x; ind[x] = k; x = x * g % m
    one = np.zeros(m); one[pr] = 1.0
    mell = lambda f: np.fft.fft(f[exp])
    def imell(F):
        out = np.zeros(m, dtype=complex); out[exp] = np.fft.ifft(F); return out
    Sx = mell(one); N = imell(Sx * Sx).real; lam = nP * nP / n; E = N[1:] - lam
    Ph = np.conj(np.fft.fft(one)); Ph0 = Ph.copy(); Ph0[0] = 0
    FP = mell(Ph0); Pi = imell(FP**2).real
    xs = np.arange(1, m); inv = np.zeros(m, dtype=np.int64); inv[exp] = exp[(-np.arange(n)) % n]
    f = np.zeros(m, dtype=complex); f[xs] = np.exp(2j * np.pi * inv[xs] / m)
    K = np.conj(np.fft.fft(np.conj(f))).real
    FK = np.fft.fft(K[exp])
    def kl_transform(Q):   # T(a) = m^{-2} sum_c Q(c) K(ac)
        T = np.zeros(m); T[exp] = np.fft.ifft(np.conj(np.fft.fft(Q[exp])) * FK).real; return T / m**2
    varE = E.var()
    print(f"m={m} |P|={nP} L={L:.3f} lambda={lam:.2f} Var E={varE:.2f} (Var E/lambda={varE/lam:.3f})")
    mu, ph = mobius_phi(max(Rs))
    prf = pr.astype(np.float64)
    for R in Rs:
        model = np.zeros(m, dtype=complex); rr = np.zeros(m, dtype=np.int64)
        for r in range(1, R + 1):
            if mu[r] == 0: continue
            for b in range(0, r):
                if math.gcd(b, r) != 1: continue
                h0 = (b * m + r // 2) // r
                for t in range(-J, J + 1):
                    h = (h0 + t) % m
                    if h == 0 or rr[h]: continue
                    j = r * (h0 + t) - b * m
                    I = np.exp(2j * np.pi * (j / (r * m)) * prf).sum()
                    model[h] = mu[r] / ph[r] * I; rr[h] = r
        sel = rr > 0
        num = np.vdot(model[sel], Ph[sel]); 
        fit = abs(num) / math.sqrt((np.abs(model[sel])**2).sum() * (np.abs(Ph[sel])**2).sum())
        tot = (np.abs(Ph0)**2).sum()
        th_model = (np.abs(model)**2).sum() / tot
        resid = Ph0 - model
        th_res = (np.abs(resid)**2).sum() / tot
        FM = mell(model); FR = mell(resid)
        Pss = imell(FM**2).real; Psb = 2 * imell(FM * FR).real; Pbb = imell(FR**2).real
        Ess = kl_transform(Pss)[1:]; Esb = kl_transform(Psb)[1:]; Ebb = kl_transform(Pbb)[1:]
        Ess -= Ess.mean(); Esb -= Esb.mean(); Ebb -= Ebb.mean()
        chk = np.abs((Ess + Esb + Ebb) - (E - E.mean())).max()
        c_ss = np.corrcoef(E, Ess)[0, 1]
        kurt = lambda v: ((v - v.mean())**4).mean() / v.var()**2
        print(f" R={R:4d}: #major h={sel.sum():6d}  cos(model,Phat on major)={fit:.4f}  ||Phat#||^2 share={th_model:.4f}  residual share={th_res:.4f}  (log R/log m={math.log(R)/L:.4f})")
        print(f"         Var shares: ##={Ess.var()/varE:.4f}  #b={Esb.var()/varE:.4f}  bb={Ebb.var()/varE:.4f}   corr(E,E##)={c_ss:.4f}  recon err={chk:.2e}")
        print(f"         min over a:  E/lam={E.min()/lam:+.4f}  E##/lam={Ess.min()/lam:+.4f}  Ebb/lam={Ebb.min()/lam:+.4f}   kurt E##={kurt(Ess):.2f} kurt Ebb={kurt(Ebb):.2f}")
        print(f"         Parseval bounds on sup|.|/lam:  ##: {(np.abs(model)**2).sum()/m/lam:.3f}   bb: {(np.abs(resid)**2).sum()/m/lam:.3f}   (full: {nP/lam:.3f})")
        if R == Rs[-1]:
            rmsPi = math.sqrt(((Pi[1:] - Pi[1:].mean())**2).mean())
            print("         peaks: u/v   Pi/(m/L)^2   Pi#/(m/L)^2")
            for (u, v) in [(-1,6),(1,6),(-1,30),(-1,12),(1,4),(-1,4),(1,3),(1,1),(-1,1),(1,2),(2,1),(6,1),(-6,1),(1,5)]:
                c = u * pow(v, -1, m) % m
                print(f"           {u:3d}/{v:<3d} {Pi[c]/(m/L)**2:+.4f}  {Pss[c]/(m/L)**2:+.4f}")

if __name__ == "__main__":
    main()
