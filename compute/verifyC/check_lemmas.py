#!/usr/bin/env python3
"""Referee sanity checks for section 1 of notes/routes/C-log-exponent.md.
(1) constants in (F3),(F4) and Lemma 1.1;  (2) Re digamma(z) <= log|z| on Re z >= 1 (grid);
(3) the ratio (1+u)^2/((1/4+u)(9/4+u)) <= 16/9 (and whether it is monotone);
(4) the Cesaro explicit formula for zeta, including the poles at s=0,-1 and trivial zeros that the
    notes avoid by stopping at Re s = 1/4, checked against direct summation;
(5) Lemma 1.1 for zeta and for the primitive characters mod 3, 4, 5 via identity (1.1) at s = 3/2
    (the zero sum equals the right side of (1.1) unconditionally if Re 1/(3/2-rho) is used; under GRH
    it is sum 1/(1+gamma^2)).
"""
import mpmath as mp
mp.mp.dps = 30
z = mp.zeta
def zlog(s): return mp.zeta(s, derivative=1)/mp.zeta(s)
print("(F3) -zeta'/zeta(3/2) =", -zlog(1.5), "  -zeta'/zeta(2) =", -zlog(2))
print("(F4) psi(3/4) =", mp.digamma(0.75), " psi(5/4) =", mp.digamma(1.25))
c = -zlog(1.5) - mp.log(mp.pi)/2 + max(mp.digamma(0.75), mp.digamma(1.25))/2
print("Lemma 1.1 constant: 1.5053 - log(pi)/2 + max(psi)/2 =", c, " ; (4/3)*c =", 4*c/3)
# (2)
worst = -mp.inf
for a in [1, 1.01, 1.1, 1.25, 1.5, 2, 3, 5, 10]:
    for t in [0, .1, .3, .5, 1, 2, 3, 5, 10, 30, 100, 1000, 1e5]:
        zz = mp.mpc(a, t)
        worst = max(worst, mp.re(mp.digamma(zz)) - mp.log(abs(zz)))
print("max of Re psi(z) - log|z| on grid (should be <= 0):", worst)
# (3)
f = lambda u: (1+u)**2/((mp.mpf(1)/4+u)*(mp.mpf(9)/4+u))
us = [mp.mpf(k)/100 for k in range(0, 100000)]
vals = [f(u) for u in us]
print("ratio at 0:", vals[0], " max:", max(vals), " min:", min(vals), "at u=", us[vals.index(min(vals))],
      " monotone decreasing on [0,1000):", all(vals[i] >= vals[i+1] for i in range(len(vals)-1)))
# (4) explicit formula for zeta, Cesaro weight
import sympy
def psiC(x):
    s = mp.mpf(0)
    for n in range(2, int(mp.floor(x))+1):
        fac = sympy.factorint(n)
        if len(fac) == 1:
            p = list(fac)[0]
            s += mp.log(p)*(1 - mp.mpf(n)/x)
    return s
NZ = 400
zeros = [mp.zetazero(k) for k in range(1, NZ+1)]
S1 = sum(1/abs(r*(r+1)) for r in zeros)*2
print(f"sum over first {2*NZ} zeta zeros of 1/|rho(rho+1)| =", S1, "(Lemma 1.1 claims an absolute constant)")
print("sum 1/(1+gamma^2) partial:", 2*sum(1/(1+mp.im(r)**2) for r in zeros),
      " ; exact via (1.1) with q=1 modifications: ", None)
for x in [mp.mpf(1), mp.mpf('1.5'), mp.mpf(2), mp.mpf('10.5'), mp.mpf(100), mp.mpf('1000.3')]:
    zs = -2*sum(mp.re(x**r/(r*(r+1))) for r in zeros)
    triv = -sum(x**(-2*k)/(2*k*(2*k-1)) for k in range(1, 200))
    rhs = x/2 + zs - zlog(0) + zlog(-1)/x + triv
    print(f"x={mp.nstr(x,8)}: psiC={mp.nstr(psiC(x),12)}  explicit(400 zero pairs)={mp.nstr(rhs,12)}"
          f"  |psiC-x/2|/sqrt(x)={mp.nstr(abs(psiC(x)-x/2)/mp.sqrt(x),6)}")
# (5) identity (1.1) at s=3/2 for small primitive characters
def Lchar(chi, q):
    return lambda s: mp.dirichlet(s, chi)
for q, chi, kappa, name in [(3, [0,1,-1], 1, "mod 3"), (4, [0,1,0,-1], 1, "mod 4"),
                            (5, [0,1,-1,-1,1], 0, "mod 5 real"), (5, [0,1,1j,-1j,-1], 1, "mod 5 complex"),
                            (8, [0,1,0,-1,0,-1,0,1], 0, "mod 8 even"), (8, [0,1,0,1,0,-1,0,-1], 1, "mod 8 odd"),
                            (12, [0,1,0,0,0,-1,0,-1,0,0,0,1], 0, "mod 12")]:
    L = lambda s: mp.dirichlet(s, chi)
    s0 = mp.mpf(3)/2
    LL = mp.diff(L, s0)/L(s0)
    val = mp.re(LL) + mp.log(q/mp.pi)/2 + mp.re(mp.digamma((s0+kappa)/2))/2
    print(f"{name}: sum_rho 1/(1+gamma^2) [GRH, via (1.1)] = {mp.nstr(val,10)}  vs bound 0.5 log q + 0.82 = {mp.nstr(mp.log(q)/2+0.82,8)}")
