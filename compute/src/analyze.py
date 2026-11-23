"""Analysis and plots for the EOS computations. Reads data/*.csv, writes fig/*.png and data/summary_*.txt."""
import numpy as np, pandas as pd, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import sys, os
os.chdir(os.path.join(os.path.dirname(__file__), ".."))
out = open("data/summary.txt", "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); out.write(s + "\n")

cov = pd.read_csv(sys.argv[1] if len(sys.argv) > 1 else "data/cover_1e6.csv")
fails = pd.read_csv(sys.argv[2] if len(sys.argv) > 2 else "data/fails_1e6.csv")
full = pd.read_csv("data/full_range.csv")
samp = pd.read_csv("data/full_sample.csv")
ch = pd.read_csv("data/char_primes.csv")

# ---------------- Task 1 ----------------
say("=== Task 1: coverage, m in [2, %d] ===" % cov.m.max())
fa = fails[fails.variant == "all"]; fd = fails[fails.variant == "distinct_only"]
bad_m = sorted(fa.m.unique())
say("failing m (p,q <= m):", len(bad_m), "values; largest", max(bad_m))
say("  list:", " ".join(map(str, bad_m)))
dist_bad = sorted(set(cov.m[cov.nfail_distinct > 0]))
say("failing m for distinct p != q variant:", len(dist_bad), "largest", max(dist_bad))
say("  m failing distinct but not base:", " ".join(str(m) for m in dist_bad if m not in set(bad_m)))
for m in bad_m[-12:]:
    say("  m=%d bad a: %s" % (m, " ".join(map(str, fa[fa.m == m].a))))
for m in dist_bad[-6:]:
    say("  distinct-variant m=%d bad a (base-OK ones): %s" % (m, " ".join(map(str, fd[fd.m == m].a))))
pr_fail = [m for m in bad_m if cov.set_index("m").loc[m, "pi_m"] == m - 1]
say("of failing m, primes:", len(pr_fail))

# ---------------- Task 3b: theta / z ----------------
c = cov[cov.m >= 1000].copy()
c["L"] = np.log(c.m)
say("\n=== Task 3: one small prime (p <= z, q <= m) ===")
for lo, hi in [(1e3, 1e4), (1e4, 1e5), (1e5, 1e6 + 1)]:
    s = c[(c.m >= lo) & (c.m < hi)]
    i = s.z.idxmax()
    say("m in [%g,%g): max z=%d at m=%d (a=%d), max theta=%.4f, mean theta=%.4f, max z/log^2 m=%.3f, mean z/log^2 m=%.3f"
        % (lo, hi, s.z.max(), s.m[i], s.z_a[i], s.theta.max(), s.theta.mean(), (s.z / s.L ** 2).max(), (s.z / s.L ** 2).mean()))
# theta record holders above 1000
rec = []; best = 1
for m, th in zip(cov.m, cov.theta):
    if m >= 500 and th > 0 and (not rec or th > rec[-1][1] - 1e-12 and False): pass
s = cov[cov.m > 1000]
say("largest theta for m>1000: %.4f at m=%d; for m>1e5: %.4f at m=%d" % (s.theta.max(), s.m[s.theta.idxmax()],
    s[s.m > 1e5].theta.max(), s[s.m > 1e5].m[s[s.m > 1e5].theta.idxmax()]))
# z vs log^2: fit z ~ C (log m)^b using block maxima
blocks = np.logspace(3, 6, 13)
bm = []
for lo, hi in zip(blocks[:-1], blocks[1:]):
    s = cov[(cov.m >= lo) & (cov.m < hi)]
    bm.append((np.sqrt(lo * hi), s.z.max(), s.z.median()))
bm = np.array(bm)
b, a = np.polyfit(np.log(np.log(bm[:, 0])), np.log(bm[:, 1]), 1)
b2, a2 = np.polyfit(np.log(np.log(bm[:, 0])), np.log(bm[:, 2]), 1)
say("fit block-max z ~ %.3f (log m)^%.2f ; block-median z ~ %.3f (log m)^%.2f" % (np.exp(a), b, np.exp(a2), b2))

# ---------------- Task 2 ----------------
say("\n=== Task 2: R(m) ===")
for d in (full, samp):
    d["delta"] = d.pi_m / d.phi
    d["Rr2"] = 1 - 2 * (1 - d.delta) * np.sqrt(np.log(d.phi) / d["lambda"])
    d["zs2"] = (d["lambda"] - d.minN) / (np.sqrt(2 * d["lambda"]) * (1 - d.delta)) / np.sqrt(2 * np.log(d.phi))
ch["delta"] = ch.pi / (ch.m - 1)
ch["lambda"] = ch.pi ** 2 / (ch.m - 1)
ch["Rr2"] = 1 - 2 * (1 - ch.delta) * np.sqrt(np.log(ch.m - 1) / ch["lambda"])
ch["zs2"] = (ch["lambda"] - ch.minN) / (np.sqrt(2 * ch["lambda"]) * (1 - ch.delta)) / np.sqrt(2 * np.log(ch.m - 1))
f = full[full.m >= 100]
say("first m with R>0 forever (in full range):", int(full.m[full.R == 0].max()) + 1 if (full.R == 0).any() else 3)
for lo, hi in [(500, 1000), (1000, 2000), (2000, 5000), (5000, 1e4), (1e4, 2e4), (2e4, 5e4), (5e4, 1e5 + 1)]:
    s = full[(full.m >= lo) & (full.m < hi)]
    if len(s) == 0: continue
    i = s.R.idxmin()
    say("m in [%g,%g): min R=%.4f at m=%d (prime=%d, phi/m=%.3f, a=%d), median R=%.4f, median R_rand=%.4f, median zscore/sqrt(2 log phi)=%.3f"
        % (lo, hi, s.R.min(), s.m[i], s.is_prime[i], s.phi_over_m[i], s.argmin_a[i], s.R.median(), s.Rr2.median(), s.zs2.median()))
say("prime m via FFT:")
for lo, hi in [(1e4, 2e4), (1e5, 2e5), (1e6, 2e6), (1e7, 2e7), (5e7, 1.01e8)]:
    s = ch[(ch.m >= lo) & (ch.m < hi)]
    if len(s) == 0: continue
    say("  m in [%g,%g): n=%d, min R=%.4f, median R=%.4f, median R_rand=%.4f, median zs=%.3f, max zs=%.3f"
        % (lo, hi, len(s), s.R.min(), s.R.median(), s.Rr2.median(), s.zs2.median(), s.zs2.max()))
# worst types: compare R within the same range by type
s = full[full.m >= 5000].copy()
s["type"] = np.where(s.is_prime == 1, "prime", np.where(s.phi_over_m < 0.3, "phi/m<0.3", np.where(s.omega == 1, "prime power", "other")))
s["resid"] = s.R - s.Rr2
say("type comparison (m in [5000, max]), residual R - R_rand mean / zscore ratio mean:")
for t, g in s.groupby("type"):
    say("  %-12s n=%6d  mean R=%.4f  mean R_rand=%.4f  mean(R-R_rand)=%+.4f  mean zs=%.3f" % (t, len(g), g.R.mean(), g.Rr2.mean(), g.resid.mean(), g.zs2.mean()))
# class types
say("argmin class types (m >= 5000):")
say("  fraction argmin is a square: %.3f (fraction of squares in G averaged: %.3f)" % (s.argmin_is_square.mean(), (s.nsquares / s.phi).mean()))
say("  fraction argmin = 1: %.4f, = -1: %.4f, <= 100: %.4f" % ((s.argmin_a == 1).mean(), (s.argmin_a == s.m - 1).mean(), (s.argmin_a <= 100).mean()))
say("  mean N(1)/lambda=%.4f, N(-1)/lambda=%.4f, mean over squares=%.4f, nonsquares=%.4f, min over a<=100 =%.4f"
    % (s.N1_norm.mean(), s.Nminus1_norm.mean(), s.mean_sq_norm.mean(), s.mean_nonsq_norm.mean(), s.min_small_norm.mean()))
say("  mean min over squares=%.4f, min over nonsquares=%.4f" % (s.min_sq_norm.mean(), s.min_nonsq_norm.mean()))
# parity split for m: odd vs even
for par, g in s.groupby(s.m % 2):
    say("  m %s: mean N(1)/lam=%.4f N(-1)/lam=%.4f mean sq=%.4f nonsq=%.4f" % ("even" if par == 0 else "odd", g.N1_norm.mean(), g.Nminus1_norm.mean(), g.mean_sq_norm.mean(), g.mean_nonsq_norm.mean()))
say("  prime m (FFT, m>=1e4): mean N(1)/lam=%.4f  N(-1)/lam=%.4f  frac argmin square=%.3f  frac argmin<=100=%.4f"
    % (ch[ch.m >= 1e4].N1_norm.mean(), ch[ch.m >= 1e4].Nminus1_norm.mean(), ch[ch.m >= 1e4].argmin_is_square.mean(), (ch[ch.m >= 1e4].argmin_a <= 100).mean()))

# fits for 1 - R
allR = pd.concat([full[full.m >= 1000][["m", "R", "lambda", "phi"]], samp[["m", "R", "lambda", "phi"]],
                  ch[ch.m > 1e5][["m", "R", "lambda"]].assign(phi=ch.m - 1)])
lm = np.log(allR.m); y1 = np.log(1 - allR.R)
bb, aa = np.polyfit(lm, y1, 1)
say("fit 1-R ~ %.3f m^%.3f (all m >= 1000)" % (np.exp(aa), bb))
w = (1 - allR.R) * np.sqrt(allR["lambda"])
bb2, aa2 = np.polyfit(np.log(np.log(allR.m)), np.log(w), 1)
say("fit (1-R) sqrt(lambda) ~ %.3f (log m)^%.3f   [random model: 2(1-delta) sqrt(log phi), i.e. exponent 0.5]" % (np.exp(aa2), bb2))

# ---------------- Task 3a: y(m) ----------------
say("\n=== Task 3: y(m) ===")
fy = full[full.y > 0].copy()
fy["L"] = np.log(fy.m)
for lo, hi in [(1e3, 1e4), (1e4, 2e4), (2e4, 5e4), (5e4, 1e5 + 1)]:
    s = fy[(fy.m >= lo) & (fy.m < hi)]
    if len(s) == 0: continue
    say("m in [%g,%g): max y/m=%.4f (m=%d), median y/m=%.4f, median y/sqrt(m)=%.2f, median y/(sqrt(m) log m)=%.3f, max y/(sqrt m log m)=%.3f"
        % (lo, hi, s.y_over_m.max(), s.m[s.y_over_m.idxmax()], s.y_over_m.median(), s.y_over_sqrtm.median(),
           (s.y_over_sqrtm / s.L).median(), (s.y_over_sqrtm / s.L).max()))
sy = samp[samp.y > 0]
say("sample to 1e6: median y/m=%.4f for m>5e5; max y/m=%.4f" % (sy[sy.m > 5e5].y_over_m.median(), sy[sy.m > 5e5].y_over_m.max()))
yy = pd.concat([fy[fy.m >= 1000][["m", "y"]], sy[["m", "y"]]])
b3, a3 = np.polyfit(np.log(yy.m), np.log(yy.y), 1)
say("fit y ~ %.3f m^%.3f" % (np.exp(a3), b3))
X = np.c_[np.ones(len(yy)), 0.5 * np.log(yy.m), np.log(np.log(yy.m))]
coef = np.linalg.lstsq(X, np.log(yy.y) - 0.5 * np.log(yy.m), rcond=None)[0]
say("fit y ~ %.3f sqrt(m) (log m)^%.2f  [with m^(1/2) fixed: coefficient c, extra sqrt-exponent %.3f]" % (np.exp(coef[0]), coef[2], coef[1]))
cnt = full[(full.m > 100) & (full.y_over_m > 0.5)]
say("m > 100 with y/m > 0.5: %d; largest such m: %s" % (len(cnt), cnt.m.max() if len(cnt) else None))
for t in [0.9, 0.75, 0.5, 0.25]:
    s = full[(full.y_over_m > t)]
    say("  largest m with y(m)/m > %.2f: %d" % (t, s.m.max()))

# ---------------- Task 4 ----------------
say("\n=== Task 4: energy and character sums ===")
for d, name in ((full, "full range"), (samp, "sample")):
    d["Xn"] = d.X_excess / (1 - d.delta) ** 2
for lo, hi in [(1e3, 5e3), (5e3, 2e4), (2e4, 1e5 + 1)]:
    s = full[(full.m >= lo) & (full.m < hi)]
    if len(s) == 0: continue
    for t, g in s.groupby(s.is_prime):
        say("m in [%g,%g) %-9s: E/(pi^4/phi+2pi^2) mean=%.5f;  X=(E-pi^4/phi)/(2pi^2) mean=%.4f [min %.4f, max %.4f];  X/(1-delta)^2 mean=%.4f"
            % (lo, hi, "prime" if t else "composite", g.E_ratio.mean(), g.X_excess.mean(), g.X_excess.min(), g.X_excess.max(), g.Xn.mean()))
ch["Xn"] = ch.X_excess / (1 - ch.delta) ** 2
for lo, hi in [(5, 1e3), (1e3, 2e4), (2e4, 2e5), (2e5, 2e6), (2e6, 2e7), (2e7, 1.01e8)]:
    s = ch[(ch.m >= lo) & (ch.m < hi)]
    if len(s) == 0: continue
    say("primes [%g,%g) n=%d: X mean=%.4f, X/(1-delta)^2 mean=%.4f; max|S|/sqrt(pi): median %.3f max %.3f; max|S|^2/(pi log phi): median %.3f; "
        "max|S|/(sqrt(m)log m): max %.4f; #|S|^2>10pi total %d; max is quadratic chi: %.2f"
        % (lo, hi, len(s), s.X_excess.mean(), s.Xn.mean(), s.maxS_over_sqrtpi.median(), s.maxS_over_sqrtpi.max(),
           s.maxS2_over_pi_logphi.median(), s.maxS_over_sqrtm_logm.max(), s.count_S2_gt_10pi.sum(), (s.order_of_max_chi == 2).mean()))
say("mean |S(quadratic)|/sqrt(pi), primes>1e4: %.3f; mean signed S_quad/sqrt(pi): %.3f"
    % (ch[ch.m > 1e4].abs_S_quad_over_sqrtpi.mean(), ch[ch.m > 1e4].S_quad_over_sqrtpi.mean()))
say("FFT rounding: max err %.2e, any sumN mismatch: %s" % (ch.max_round_err.max(), (ch.sumN_minus_pi2 != 0).any()))
out.close()

# ---------------- plots ----------------
fig, ax = plt.subplots(2, 2, figsize=(13, 9.5))
a = ax[0, 0]
fr = full[full.m >= 50]
comp = fr[fr.is_prime == 0]; prm = fr[fr.is_prime == 1]
a.scatter(comp.m, comp.R, s=0.3, c="#7f8c8d", alpha=0.35, label="composite m (all m<=%d)" % full.m.max(), rasterized=True)
a.scatter(prm.m, prm.R, s=0.5, c="#2a6fdb", alpha=0.5, label="prime m", rasterized=True)
sm = samp[samp.m > full.m.max()]
a.scatter(sm.m, sm.R, s=6, c="#555555", marker="x", label="composite sample")
cb = ch[ch.m > full.m.max()]
a.scatter(cb.m, cb.R, s=5, c="#2a6fdb", label="prime m (FFT)")
mm = np.logspace(np.log10(50), 8, 300)
lam = (mm / np.log(mm)) ** 2 / mm; dl = 1 / np.log(mm)
a.plot(mm, 1 - 2 * (1 - dl) * np.sqrt(np.log(mm) / lam), "r-", lw=1.5, label="random model, prime m")
a.set_xscale("log"); a.set_ylim(-0.02, 1.02); a.set_xlabel("m"); a.set_ylabel("R(m) = min_a N(a) / (pi_m^2/phi)")
a.set_title("Normalised minimum R(m)"); a.legend(fontsize=7, loc="lower right", markerscale=3)
a = ax[0, 1]
for d, col, lab in ((fr[fr.m >= 1000], "#7f8c8d", "m <= %d (all)" % full.m.max()), (sm, "#333333", "sample"), (cb, "#2a6fdb", "prime m (FFT)")):
    a.scatter(d.m, d.zs2, s=0.6 if len(d) > 5000 else 6, c=col, alpha=0.4 if len(d) > 5000 else 0.9, label=lab, rasterized=True)
a.axhline(1, color="r", lw=1)
a.set_xscale("log"); a.set_xlabel("m"); a.set_ylabel("(lambda - min N) / (sd * sqrt(2 log phi))")
a.set_title("Depth of the minimum vs Gaussian extreme value (1 = random)"); a.legend(fontsize=7, markerscale=3)
a = ax[1, 0]
fy2 = full[(full.y > 0) & (full.m >= 30)]
a.scatter(fy2.m, fy2.y_over_m, s=0.3, c="#7f8c8d", alpha=0.4, label="y(m)/m", rasterized=True)
a.scatter(sy.m, sy.y_over_m, s=5, c="k", marker="x", label="y(m)/m sample")
mm2 = np.logspace(1.5, 6, 200)
a.plot(mm2, np.exp(coef[0]) * np.sqrt(mm2) * np.log(mm2) ** coef[2] / mm2, "r-", lw=1, label="fit %.2f sqrt(m)(log m)^%.2f / m" % (np.exp(coef[0]), coef[2]))
a.set_xscale("log"); a.set_yscale("log"); a.set_xlabel("m"); a.set_ylabel("y(m)/m")
a.set_title("Smallest symmetric cutoff y(m) (p, q <= y covers all classes)"); a.legend(fontsize=7, markerscale=3)
a = ax[1, 1]
cc = cov[cov.m >= 30]
a.scatter(cc.m[::3], cc.theta[::3], s=0.2, c="#2a6fdb", alpha=0.3, rasterized=True, label="theta(m) = log z / log m (every 3rd m)")
a.plot(bm[:, 0], np.log(bm[:, 1]) / np.log(bm[:, 0]), "ko-", ms=3, label="block max theta")
a.set_xscale("log"); a.set_xlabel("m"); a.set_ylabel("theta"); a.set_ylim(0, 1.0)
a.set_title("One small prime: p <= m^theta, q <= m covers all classes"); a.legend(fontsize=7, markerscale=5)
plt.tight_layout(); plt.savefig("fig/eos_trends.png", dpi=130)

fig, ax = plt.subplots(1, 2, figsize=(13, 4.8))
a = ax[0]
fe = full[full.m >= 200]
a.scatter(fe.m[fe.is_prime == 0], fe.X_excess[fe.is_prime == 0], s=0.3, c="#7f8c8d", alpha=0.3, label="composite", rasterized=True)
a.scatter(fe.m[fe.is_prime == 1], fe.X_excess[fe.is_prime == 1], s=0.5, c="#2a6fdb", alpha=0.5, label="prime", rasterized=True)
a.scatter(cb.m, cb.X_excess, s=5, c="#2a6fdb")
a.scatter(sm.m, sm.X_excess, s=6, c="k", marker="x")
mm = np.logspace(2.3, 8, 200)
a.plot(mm, (1 - 1 / np.log(mm)) ** 2, "r-", label="random subset of size pi, prime m: (1-delta)^2")
a.axhline(1, color="r", ls=":", lw=1, label="naive random model pi^4/phi + 2pi^2")
a.set_xscale("log"); a.set_xlabel("m"); a.set_ylabel("(E - pi^4/phi) / (2 pi^2)"); a.set_title("Excess multiplicative energy")
a.legend(fontsize=7, markerscale=4)
a = ax[1]
a.scatter(ch.m, ch.maxS_over_sqrtpi, s=1.5, c="#2a6fdb", label="max_{chi != chi0} |S(chi)| / sqrt(pi_m)")
a.plot(mm, np.sqrt(np.log(mm)), "r-", label="sqrt(log m)  (Gaussian max)")
a.set_xscale("log"); a.set_xlabel("prime m"); a.set_title("Largest nontrivial character sum over primes"); a.legend(fontsize=7)
plt.tight_layout(); plt.savefig("fig/eos_energy_chars.png", dpi=130)
print("plots written")
