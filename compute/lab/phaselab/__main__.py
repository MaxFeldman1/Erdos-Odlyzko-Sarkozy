"""Command line interface. Run from compute/lab:   python3 -m phaselab <command> [options]

  info      m                         group structure, |P|, main term, Parseval mass, min N
  decompose m --by G [--object O] [--a A] [--X X] [--weight W]
                                      partial sums of E(a) by grouping G (order | conductor | parity |
                                      quantile:q | coset:pow:d | coset:mod:m1 | coset:gens:a,b), with
                                      within/across cancellation and random-phase surrogates
  phases    m [--object O] [--a A]    phase harmonics / histogram / Kuiper test at a
  psi       m [--object O] [--dmax d] phase correlation of T(chi) and T(chi psi), psi of order <= d
  blocks    m [--object O] [--M M]    route A / H4 block statistics delta_I(c)
  compare   m [--a A]                 all objects x all diagnostics, markdown separation table (no figures)
  report    m [--a A]                 compare + dynamics + X-range + figures -> data/report_m.json, fig/m_*.png
  scan      m1 m2 ...                 scaling table over several moduli (P tails, barrier spike, toy shape)

Objects (--object): P P_worst conj redacted redacted_half pairing random astar toy (default P).
"""
from __future__ import annotations

import argparse
import math
import sys

import numpy as np

from . import blocks, decomp, phases, report, sets
from .core import Problem
from .group import UnitGroup
from .objects import catalogue


def _obj(args, G):
    cat = catalogue(args.m, a=args.a, X=getattr(args, "X", None), weight=getattr(args, "weight", "1"),
                    which=[args.object], G=G)
    return cat[args.object]


def main(argv=None):
    ap = argparse.ArgumentParser(prog="phaselab", description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    def add(name):
        p = sub.add_parser(name)
        p.add_argument("m", type=int)
        p.add_argument("--a", type=int, default=None)
        p.add_argument("--object", default="P")
        p.add_argument("--X", type=float, default=None)
        p.add_argument("--weight", default="1")
        return p

    add("info")
    p = add("decompose")
    p.add_argument("--by", default="order")
    p.add_argument("--top", type=int, default=15, help="print the groups with largest |T_g|")
    add("phases")
    p = add("psi")
    p.add_argument("--dmax", type=int, default=12)
    p = add("blocks")
    p.add_argument("--M", type=float, nargs="*", default=None)
    add("compare")
    p = add("report")
    p.add_argument("--no-dynamics", action="store_true")
    p = sub.add_parser("scan")
    p.add_argument("ms", type=int, nargs="+")
    args = ap.parse_args(argv)
    if args.cmd == "scan":
        import json, os
        rows = report.scan(args.ms)
        out = os.path.join(report.HERE, "data", f"scan_{args.ms[0]}_{args.ms[-1]}.json")
        with open(out, "w") as f:
            json.dump(report._clean(rows), f, indent=1)
        fig = os.path.join(report.HERE, "fig", f"scan_{args.ms[0]}_{args.ms[-1]}.png")
        report.scan_figure(rows, fig)
        print("wrote", out, fig)
        return
    m = args.m
    G = UnitGroup(m)

    if args.cmd == "info":
        w = sets.prime_weights(m, args.X, args.weight)
        pr = Problem(G, [w, w])
        s = pr.summary()
        print(f"{G}  factors={G.factors}  exponent L={G.L}  generators={G.generators()}")
        print(f"|P| weight sum={w.sum():.1f}  main mu={s['main']:.2f}  Parseval mass A={s['parseval_mass']:.2f} "
              f"(A/mu={s['parseval_mass'] / s['main']:.2f})  rms E={s['rms_E']:.2f}")
        print(f"min N/mu={s['minN_over_main']:.4f} at a={s['argmin']}  skew={s['skew']:.3f} kurt={s['kurt']:.3f}")
        return

    o = _obj(args, G)
    pr, a = o.prob, o.a
    if args.cmd == "decompose":
        lab = decomp.make_labels(pr, args.by)
        d = decomp.decompose(pr, lab, a)
        print(f"{args.object} a={a}: E={d['E']:.3f} (E/main={d['E'] / pr.main:+.4f}, E/sd={d['E'] / d['sdE']:+.2f})"
              f"  A={d['A']:.2f}  W={d['W']:.2f}  groups={d['ngroups']}")
        print(f"log-cancellation: within={d['within']:.3f} (random {d['within_surr']:.3f})  across={d['across']:.3f} "
              f"(random {d['across_surr']:.3f})  total={d['total']:.3f}")
        print(f"W/W_cond={d['W_over_Wcond']:.3f}  chi2/dof={d['chi2_dof']:.3f}  corr(T_g, V_g)={d['corr_T_V']:.3f}")
        g = d["groups"]
        idx = np.argsort(-np.abs(g["T"]))[:args.top]
        print(" key          size        A_g          V_g         T_g      z_g    T_g/E   V_g/V")
        for i in idx:
            print(f" {g['key'][i]:<10d} {g['size'][i]:6d} {g['A'][i]:12.3f} {g['V'][i]:12.3f} {g['T'][i]:11.3f} "
                  f"{g['z'][i]:8.2f} {g['T'][i] / d['E']:8.4f} {g['V'][i] / g['V'].sum():7.4f}")
    elif args.cmd == "phases":
        ps = phases.phase_stats(pr, a)
        np.set_printoptions(precision=4, suppress=True, linewidth=150)
        print(f"{args.object} a={a}: E/A = c_w[1] = {ps['c_w'][0]:+.5f}")
        print("weighted harmonics c_k   :", ps["c_w"], "\n  z:", ps["z_w"])
        print("unweighted harmonics c_k :", ps["c_u"], "\n  z:", ps["z_u"])
        print(f"Kuiper (unweighted vs uniform): lambda={ps['kuiper']:.3f} p={ps['kuiper_p']:.3g}")
        print("weighted <cos> by |T| decile:", ps["bias_by_quantile"])
        print("share of E by |T| decile    :", ps["share_by_quantile"])
    elif args.cmd == "psi":
        pc = phases.psi_correlation(pr, args.dmax)
        print(f"null sd of C_u ~ {pc['sd_null_u']:.2e}, of |C_w| ~ 1/sqrt(n) = {1 / math.sqrt(pc['n']):.2e}")
        for s, od, cw, cu in pc["rows"][:60]:
            print(f" psi={s:<10d} order={od:<4d} |C_w|*sqrt(n)={abs(cw) * math.sqrt(pc['n']):6.2f}  "
                  f"C_u/sd={cu / pc['sd_null_u']:+6.2f}")
    elif args.cmd == "blocks":
        Ms = args.M or [m ** 0.3, m ** 0.4, m ** 0.5]
        for M in Ms:
            b = blocks.block_moments(G, pr.weights[-1], M, a=a)
            print(" ".join(f"{k}={v:.4g}" if isinstance(v, float) else f"{k}={v}" for k, v in b.items()))
    elif args.cmd == "compare":
        res = report.run(m, a=args.a, figs=False, dyn=False)
        print(report.table(res))
    elif args.cmd == "report":
        res = report.run(m, a=args.a, figs=True, dyn=not args.no_dynamics)
        print(report.table(res))


if __name__ == "__main__":
    sys.exit(main())
