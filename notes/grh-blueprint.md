# Blueprint: from literal GRH to `GRHSmoothBound`

Written 2026-11-23. Status tags: **proved** = checked in Lean (or proved on paper where stated);
**sketched** = paper argument given, details routine; **heuristic** = an estimate or a judgement;
**[UNVERIFIED]** = not checked.

The paper proof is notes/routes/C-log-exponent.md §1, refereed in notes/routes/C-referee.md §1.
This blueprint keeps its design (Cesàro kernel x^s/(s(s+1)), contour moved only to Re s = 1/4)
but replaces the **global Hadamard partial-fraction formula (F2)** by **Landau's local
partial-fraction lemma** (Borel–Carathéodory + Jensen). That removes the functional equation,
the Γ-factor, digamma bounds and Hadamard factorization from the critical path.

---

## 0. Status of `EOS/EOS/GRH.lean` (proved, Lean, no `sorry`, standard axioms only)

```lean
def GRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → LFunction χ s = 0 → s.re = 1 / 2

theorem GRH.riemannHypothesis (h : GRH) : RiemannHypothesis
theorem GRH_iff_forall : GRH ↔ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    ∀ s : ℂ, 0 < s.re → s.re < 1 → LFunction χ s = 0 → s.re = 1 / 2
-- helpers: one_sub_mul_cpow_ne_zero, LFunction_eq_zero_iff_primitiveCharacter
```

`#print axioms` for both theorems: `propext, Classical.choice, Quot.sound`
(script: EOS/scratch_grh/Axioms.lean). Built with `lake build EOS.GRH`. `EOS.lean` was not edited, so
the orchestrator must add `import EOS.GRH`.

Design decisions:

- **Pole and junk values.** `LFunction 1` (mod 1, i.e. ζ) has a pole at s = 1 with a junk value
  there. The strict inequality `s.re < 1` excludes s = 1, so the junk value never enters.
- **Strip only.** For primitive χ there are no zeros with Re s ≥ 1
  (`LFunction_ne_zero_of_one_le_re`), and the zeros with Re s ≤ 0 are exactly the zeros of the Γ-factor
  (`LFunction_eq_zero_iff_of_re_nonpos`). So the strip loses nothing. `GRH.riemannHypothesis` uses
  both facts (in the ζ forms `riemannZeta_ne_zero_of_one_le_re`, `riemannZeta_eq_zero_iff_of_re_nonpos`).
- **Primitive χ only.** This is the standard statement. `GRH_iff_forall` shows it is equivalent to
  the statement for all χ: by `LFunction_changeLevel`,
  L(s, χ) = L(s, χ\*) ∏_{p | q} (1 − χ\*(p) p^{−s}), and an Euler factor cannot vanish when Re s > 0.
  For imprimitive χ the factors do vanish on Re s = 0, which is why the statement is restricted to the
  open strip.
- **Do primitive characters suffice downstream?** Yes. Paper §1 uses primitive χ only. The route
  below is simpler still: it applies the analytic argument to **every nonprincipal χ** directly
  (allowed by `GRH_iff_forall`), and needs a comparison lemma (E1) only for the principal character.

---

## 1. Inventory (pinned Mathlib `v4.36.0-rc2`, commit 9d581dff)

| Ingredient | In Mathlib? | Exact names / notes |
|---|---|---|
| L-series = LFunction for Re s > 1 | yes | `DirichletCharacter.LFunction_eq_LSeries`, `deriv_LFunction_eq_deriv_LSeries`, `LFunction_modOne_eq` (= `riemannZeta`), `LFunction_changeLevel`, `LFunctionTrivChar_eq_mul_riemannZeta` |
| Twisted von Mangoldt series = −L′/L | for `LSeries` only | `DirichletCharacter.LSeries_twist_vonMangoldt_eq : L (↗χ * ↗Λ) s = -deriv (L ↗χ) s / L ↗χ s` (Re s > 1), `LSeriesSummable_twist_vonMangoldt`, `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`. Transfer to `LFunction` is about 30 lines (A1) |
| Analyticity | yes | `differentiableAt_LFunction`, `differentiable_LFunction` (χ ≠ 1), `differentiable_completedLFunction` |
| Nonvanishing, Re s ≥ 1 | yes | `LFunction_ne_zero_of_one_le_re`, `LFunction_ne_zero_of_re_eq_one`, `riemannZeta_ne_zero_of_one_le_re`, `LSeries_ne_zero_of_one_lt_re` |
| Trivial zeros | yes | `LFunction_eq_zero_iff_of_re_nonpos` (primitive), `riemannZeta_eq_zero_iff_of_re_nonpos` |
| Functional equation, completed L | yes | `completedLFunction`, `gammaFactor`, `rootNumber`, `IsPrimitive.completedLFunction_one_sub`, `LFunction_eq_completed_div_gammaFactor`, `norm_rootNumber`; `logDeriv_riemannZeta_one_sub` (ζ only). **Not needed on the recommended route.** |
| Discreteness of zeros | ζ only | `isDiscrete_riemannZetaZeros`, `IsCompact.inter_riemannZetaZeros_finite`. For L, use the general analytic isolated-zeros API. |
| Growth bounds in vertical strips | **no** | Only `LFunction_isBigO_horizontal` near Re s = 1, and `isBigO_riemannZeta_sub_one_div` near s = 1. No polynomial bound for L or ζ in 0 < Re s < 1. |
| Digamma, Γ | partial | `Complex.digamma`, `digamma_apply_add_one`, `digamma_one_sub`, `Stirling` (real). No complex Stirling and no bounds for Re ψ(z). **Not needed on the recommended route.** |
| Mellin inversion | yes | `mellinInv_mellin_eq` (Mathlib/Analysis/MellinInversion.lean) |
| Perron formula | **no** | Mathlib PR #46011 ("perron's summation formula") was closed unmerged on 2026-11-14. |
| Rectangle Cauchy–Goursat | yes | `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, `..._of_differentiable_on_off_countable`, `integral_boundary_unbounded_rect_eq_zero_of_differentiable_on_off_countable[_of_integrable_on]` |
| Residue theorem | **no** | Only `AnalyticAt.tendsto_mul_logDeriv_simple_zero` and circle Cauchy formulas (`DiffContOnCl.circleIntegral_sub_inv_smul`). PRs #39232 (rectangles, open, LLM-generated) and #29588 (open). |
| Meromorphic / divisor API | yes | `MeromorphicOn.divisor`, `MeromorphicOn.extract_zeros_poles`, `MeromorphicOn.exists_canonicalDecomp` (Blaschke), `MeromorphicOn.logDeriv_mul_eventuallyEq`, `meromorphicOrderAt` |
| Jensen's formula and zero counting | yes | `MeromorphicOn.circleAverage_log_norm` (Jensen), `AnalyticOnNhd.sum_divisor_le` (zero count ≤ log(M/‖f c‖)/log(R/r)) |
| Borel–Carathéodory | yes | `Complex.borelCaratheodory`, `Complex.borelCaratheodory_zero` (Mathlib/Analysis/Complex/BorelCaratheodory.lean). No derivative version. |
| Cauchy derivative estimates | yes | `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, `norm_deriv_le_div_of_mapsTo_ball` |
| Phragmén–Lindelöf, three lines | yes | `PhragmenLindelof.vertical_strip`, `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`. Not needed. |
| Hadamard factorization | **no** | `Mathlib/Analysis/Complex/Hadamard.lean` is the three-lines theorem, not factorization. Mathlib PR #40540 (Riemann ξ, open). |
| Local partial fractions for f′/f (Landau) | **no** | absent from Mathlib |
| Abel summation | yes | `Mathlib/NumberTheory/AbelSummation.lean`, `LSeries_eq_mul_integral` (needs convergence at s, so Re s > 1 for χ), `LSeriesSummable_of_sum_norm_bigO` |

### External: PrimeNumberTheoremAnd (PNT+)

- Repo: github.com/AlexKontorovich/PrimeNumberTheoremAnd, commit `a4fb6989b07e9c76b511807ae93e33e25b820e9b`
  (2026-11-15). **Licence Apache-2.0**, the same as Mathlib. Lean `v4.35.0`, Mathlib `v4.35.0`
  (manifest commit 56a00585). Extra dependencies: LeanArchitect (the `@[blueprint]` attribute),
  checkdecls, leancert, PrimeCert. The lakefile sets `warn.sorry = false`. Outside `IEANTN/`, `sorry`
  occurs only in `Wiener.lean` and `IwaniecKowalskiCh1.lean`.
- **Coverage is ζ only.** Dirichlet L-functions appear only in `Wiener.lean`. The complex-analysis
  tools are generic.
- Relevant files, all sorry-free:
  - `Rectangle.lean` (286 lines), `ResidueCalcOnRectangles.lean` (1262): `RectangleIntegral'`,
    `ResidueTheoremOnRectangleWithSimplePole`, **`RectangleIntegral'_eq_sumResiduesIn`** (residue
    theorem on a rectangle for finitely many simple poles), `HasSimplePolesOn`, `residue`, `sumResiduesIn`.
  - `RectangleArgumentPrinciple.lean` (370) + `Mathlib/Analysis/Meromorphic/DivisorSupport.lean` (137):
    `logDeriv_residue_eq_meromorphicOrderAt`, `logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top`,
    `rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt`.
  - `PerronFormula.lean` (1180): **exactly our kernel**: `Perron.formulaGtOne : 1 < x → 0 < σ →
    VerticalIntegral' (fun s ↦ x^s/(s*(s+1))) σ = 1 - 1/x`, `Perron.formulaLtOne` (= 0 for x < 1).
  - `StrongPNT.lean` lines 1–1231 (Math Inc's "Gauss" autoformalisation, merged into PNT+):
    `borelCaratheodory'`, `BorelCaratheodoryDeriv`, `LogOfAnalyticFunction`, Blaschke-product lemmas,
    **`ZerosBound`** (Jensen-type count) and **`FinalBound`** (Landau's lemma):
    for f analytic on the closed unit disc with f 0 = 1 and ‖f‖ ≤ B on ‖z‖ ≤ R,
    ‖f′/f(z) − Σ_{‖ρ‖≤r} m_ρ/(z−ρ)‖ ≤ (16r²/(r−r′)³ + 1/((R²/R′−R′) log(R/R′))) · log B for ‖z‖ ≤ r′, z not a zero.
    Lines 1518–1730 contain the affine-change-of-variables lemmas and `LogDerivZetaFinalBound`, the ζ
    template for our B3.
  - `ZetaBounds.lean` (3689): `ResidueMult` (residue of f·g), `logDerivResidue`, ζ bounds for |t| ≥ 3.
  - `Mathlib/NumberTheory/LSeries/RiemannZetaAbel{Continuation,Kernel}.lean` (427):
    ζ(s) = 1 + 1/(s−1) − s∫₁^∞ {u}u^{−s−1}du for Re s > 1/10, with a norm bound. This is the q = 1 case of B1.
  - Route H only: `Mathlib/Analysis/Complex/HadamardFactorization{,/Growth,/Order,/Summability}.lean`,
    `WeierstrassFactor.lean`, `CanonicalProduct.lean` (about 2700 lines; `hadamard_factorization_of_order`
    for entire functions of finite order), `NumberTheory/LSeries/{ZetaFiniteOrder,RiemannZetaHadamard}.lean`
    (ζ only), `SpecialFunctions/Gamma/{StripBounds,DigammaSeries}.lean`, `IEANTN/HadamardLogDerivative.lean`.
- Math Inc's original `strongpnt` repository has been superseded by its merge into PNT+.
- **Vendoring test (proved, Lean).** I stripped the `@[blueprint …]` attributes and `blueprint_comment`
  commands, dropped `module`/`public`, renamed the namespace prefix to `PNTV`, and compiled against **our**
  Mathlib pin, cache only. Files are in EOS/scratch_grh/vendor_test/ (stripper: `tools/strip.py`).
  Seven files, 3857 lines in total: Rectangle, ResidueCalcOnRectangles, RectangleArgumentPrinciple,
  DivisorSupport, the two Asymptotics helpers, PerronFormula (with its unused `import …Wiener` removed),
  and Landau (StrongPNT lines 1–1231). They needed **7 one-line patches** for version drift: `smul_add; abel`
  twice, `smul_sub/smul_add; abel` once, a `dist_zero_right` simp-set change, and one binder annotation.
  `#print axioms` gives `propext, Classical.choice, Quot.sound` for `RectangleIntegral'_eq_sumResiduesIn`,
  `ResidueTheoremOnRectangleWithSimplePole`, `FinalBound`, `ZerosBound`, `Perron.formulaGtOne`,
  `Perron.formulaLtOne` and `rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt`.
- **Lake dependency instead of vendoring: not viable without moving our Mathlib pin.** PNT+ pins
  Mathlib v4.35.0 and we pin v4.36.0-rc2. Lake resolves a single Mathlib, so one of the two pins would have to
  move, invalidating the cache. It would also bring in four extra packages, one of them `leancert`.

---

## 2. Recommended route L (Landau local, no Hadamard, no functional equation)

Notation: K_x(s) = x^s/(s(s+1)), x ≥ 1. 𝓛 is L(s, χ) for χ ≠ 1 (any modulus, primitive or not),
or F(s) = (s−1)ζ(s) for q = 1. "Window at t" means the disc D_t = {|s − (2+it)| ≤ ρ₀}, ρ₀ = 1.88, so that
D_t ⊂ {Re s > 1/10} and 1/4 + it lies at distance 1.75 = 0.931ρ₀ from the centre. FinalBound is used with
(r′, r, R′, R) = (0.931, 0.94, 0.95, 0.96).

Sizes are in Lean lines, excluding vendored code. Difficulty: E easy, M medium, H hard.

### V. Vendoring (critical path, step 0)

| id | Content | Source | Size | Diff |
|---|---|---|---|---|
| V1 | Rectangle, ResidueCalcOnRectangles, RectangleArgumentPrinciple, DivisorSupport | PNT+ (tested) | 1900 vendored | E |
| V2 | PerronFormula + Asymptotics helpers | PNT+ (tested) | 1100 vendored | E |
| V3 | Landau: StrongPNT 1–1231 (BC, BC-deriv, ZerosBound, FinalBound) | PNT+ (tested) | 800 vendored | E |
| V4 | Affine transfer lemmas: StrongPNT 1518–1730 (`analyticOrderNatAt_fun_comp_add_*`, `_fun_div_const`); `ResidueMult` from ZetaBounds | PNT+ (untested) | ~250 vendored | E |
| V5 | ζ Abel continuation and bound (RiemannZetaAbelContinuation/Kernel/PartialSum) | PNT+ (untested) | ~600 vendored | E–M |

### A. Dirichlet-series side

| id | Statement | Source | Size | Diff |
|---|---|---|---|---|
| A1 | Re s > 1 ⇒ Σ Λ(n)χ(n)n^{−s} = −(LFunction χ)′(s)/LFunction χ s | Mathlib `LSeries_twist_vonMangoldt_eq` + `LFunction_eq_LSeries` + `deriv_LFunction_eq_deriv_LSeries` | 30 | E |
| A2 | For y > 0, σ > 0: (1/2πi)∫_{(σ)} y^s/(s(s+1)) ds = max(0, 1 − 1/y), **including y = 1** | V2 (`formulaGtOne`/`formulaLtOne`); y = 1 by a separate shift-right argument | 80 | E–M |
| A3 | ψ̃(x,χ) = (1/2πi)∫_{(2)} −𝓛′/𝓛(s) K_x(s) ds (for q = 1, with −ζ′/ζ) | A1, A2, swap of tsum and integral (dominated by Σ Λ(n)n^{−2} · ∫\|K\|) | 250 | M |
| A4 | Tail bound: \|∫_{(2), \|t\|>T}\| ≤ C x²/T | elementary | 60 | E |

### B. Unconditional L-function bounds

| id | Statement | Source | Size | Diff |
|---|---|---|---|---|
| B1 | χ ≠ 1 mod q, Re s ≥ 1/10: L(s,χ) = s∫₁^∞ S_χ(u)u^{−s−1}du, so \|L(s,χ)\| ≤ 10q\|s\|. q = 1: \|(s−1)ζ(s)\| ≤ C(\|s\|+2)². | New. Abel summation for Re s > 1 (`LSeries_eq_mul_integral`); analyticity of the parametric integral; identity theorem. ζ from V5. | 400 | M |
| B2 | Re s ≥ 2 ⇒ \|L(s,χ)\| ≥ 2 − ζ(2) > 0.35; \|(s−1)ζ(s)\| ≥ 0.35 at 2 + it | New, elementary (`hasSum_zeta_two`, `norm_le_one`) | 60 | E |
| B3 | **Landau for 𝓛.** ∃C, ∀q, χ, t, ∀s ∈ D_t at distance ≤ 1.75 from 2+it, s not a zero: \|𝓛′/𝓛(s) − Σ_{ρ ∈ D_t′} m_ρ/(s−ρ)\| ≤ C log(q(\|t\|+3)); and Σ_{ρ∈D_t′} m_ρ ≤ C log(q(\|t\|+3)). Here D_t′ is the radius-0.94ρ₀ disc. | V3, V4, B1, B2 (B = sup\|f\| ≤ Cq(\|t\|+3)²), finiteness of zeros in a disc (isolated zeros); template `LogDerivZetaFinalBound` | 450 | M–H |

### C. GRH consequences

| id | Statement | Source | Size | Diff |
|---|---|---|---|---|
| C0 | GRH ⇒ for all q, χ, every zero s of L(·,χ) with Re s > 0 (s ≠ 1 if χ = 1) has Re s = 1/2 | `GRH_iff_forall` (**proved**) + `LFunction_ne_zero_of_one_le_re` | 30 | E |
| C1 | GRH ⇒ \|𝓛′/𝓛(1/4+it)\| ≤ C log(q(\|t\|+3)) | B3 + C0 (\|s − ρ\| ≥ 1/4) | 80 | E–M |
| C2 | GRH ⇒ ∀T₀ ≥ 2 ∃T⁺, T⁻ ∈ [T₀, T₀+1] with no zeros on the segments [1/4, 2] ± iT^± and \|𝓛′/𝓛\| ≤ C log²(q(T₀+3)) there. Use independent T⁺, T⁻ (referee R2). | B3 count + pigeonhole over N+1 subintervals | 250 | M |
| C3 | GRH ⇒ Σ_{ρ: 1/4<Re ρ<2, \|γ\|≤T} m_ρ/\|ρ(ρ+1)\| ≤ C log(2q), uniformly in T | B3 count on unit windows, Σ_k log(q(k+3))/(1/4+k²) | 250 | M |

### D. Contour shift and assembly

| id | Statement | Source | Size | Diff |
|---|---|---|---|---|
| D1 | For heights from C2: ∫ over the rectangle boundary [1/4, 2] × [−T⁻, T⁺] of −𝓛′/𝓛·K_x equals 2πi Σ_{ρ inside} (−m_ρ K_x(ρ)), plus x/2 at s = 1 when q = 1 | V1 (`RectangleIntegral'_eq_sumResiduesIn`, `logDeriv_residue_eq_meromorphicOrderAt`, `logDeriv_hasSimplePolesOn_…`), V4 `ResidueMult`; finiteness of zeros in the rectangle; no poles on the boundary (C0, C2) | 400 | M–H |
| D2 | GRH ⇒ \|ψ̃(x,χ)\| ≤ C√x log(2q) for χ ≠ 1 (any q), and \|ψ̃(x,1_{mod 1}) − x/2\| ≤ C√x | A3, A4, C1 (vertical side ≤ x^{1/4}·C log 2q), C3 (residues ≤ √x·C log 2q), C2 (horizontal sides → 0 as T₀ → ∞) | 300 | M |

### E. Reductions and final theorems

| id | Statement | Source | Size | Diff |
|---|---|---|---|---|
| E1 | \|ψ̃(x,χ₀ mod q) − ψ̃(x,1_{mod 1})\| ≤ 1.1√x log q (ω(q) log x ≤ (log q/log 2)(2/e)√x) | New, elementary; paper Theorem 1 | 150 | E–M |
| E2 | `theorem GRH.grhSmoothBound : GRH → GRHSmoothBound` | D2, E1 | 60 | E |
| E3 | GRH versions of `coveredBy_log_sq`, `coveredByAsym_m_log_cube`, `coveredBy_three_primes` (compose with E2); `coveredBy_of_grhBounds`'s conclusion (log⁴) from `coveredBy_log_sq` by monotonicity of `CoveredBy` in Y once log m ≥ 1 | existing theorems | 60 | E |

E3 note (sketched, routine): `CoveredBy m Y` is monotone in Y, and K m log² m ≤ K m log⁴ m for m ≥ 3. So the
log⁴ theorem needs **no** `GRHBounds`. Deriving `GRHBounds` itself (sharp cutoff, (log qx)²) from GRH is
a separate job of about 1500 extra lines (heuristic): a truncated sharp Perron formula with error x^c/(T|log y|),
plus the same zero-counting. Not recommended unless the user wants `GRHBounds` as a theorem in its own right.

### Dependency graph

```
GRH ─(proved)─ GRH_iff_forall ── C0 ──┬── C1 ──────────────┐
                                      ├── C2 ──────────────┤
V3,V4 ─┐                              └── C3 ──────────────┤
B1(V5) ┼── B3 ────────────── (into C1, C2, C3)             ├── D2 ── E2 ── E3
B2 ────┘                                                   │
V1,V4 ─────────────────────────────────── D1 ──────────────┤
V2 ── A2 ─┐                                                │
A1 ───────┴── A3 ── A4 ────────────────────────────────────┘
E1 (elementary, independent) ──────────────────────────────── E2
```

**Critical path:** V3/V4 → B1 → B3 → C2 → D1 → D2 → E2. B3 and D1 are the two hard nodes.
A1–A4, E1 and C3 can run in parallel with B1–B3.

### Milestones

1. **M0 (done):** `GRH`, `GRH.riemannHypothesis`, `GRH_iff_forall`.
2. **M1 vendoring (≈1 day, heuristic):** bring V1–V5 into e.g. `EOS/EOS/Vendor/PNT/…`, keep the Apache
   headers, add attribution (upstream commit `a4fb698`) and a NOTICE. No lakefile change. Gate: every file
   builds with cache only, with standard axioms.
3. **M2 Dirichlet side:** A1–A4. Gate: `psiCesaro_eq_verticalIntegral` with no sorry.
4. **M3 unconditional bounds:** B1, B2, B3. Gate: Landau for 𝓛 with explicit dependence log(q(|t|+3)).
5. **M4 GRH bounds:** C0–C3.
6. **M5 contour:** D1, D2.
7. **M6 wrap-up:** E1–E3: `GRH → GRHSmoothBound` and the four headline theorems from `GRH`.

**Effort estimate (heuristic).** About 3000 new lines, with 2500–3000 more vendored, edited only lightly.
In this project's agent workflow I would plan 2–4 weeks of focused work. B3 and D1 carry most of the risk:
meromorphic and residue bookkeeping, and moving analytic orders across the affine change of variables.
For an expert human working alone it would be closer to 2–3 months. A3, B1 and E1 are routine but long.

---

## 3. Alternative routes

- **Route H (paper §1 as written: Hadamard).** Needs: completed L(s,χ) entire of order 1
  (Mathlib has no growth bounds for the completed Hurwitz functions; about 1000–1500 lines, adapting PNT+
  `ZetaFiniteOrder`); Hadamard factorization (PNT+ general theorem, about 2700 vendored lines); Davenport's
  Re B(χ) = −Σ Re 1/ρ (functional equation + `rootNumber`, about 400 lines); Re ψ(z) ≤ log|z| and ψ′ bounds
  (PNT+ `DigammaSeries`/`StripBounds`, or new); then the same contour work D1–D2. Estimated at about twice
  route L (heuristic). Its one advantage is explicit constants, which we do not need.
- **Selberg/Weil explicit formula with a compactly supported test function.** It needs the functional equation,
  Γ-factor asymptotics and either Hadamard or a contour to Re s → −∞ (trivial zeros, and Euler-factor zeros
  for imprimitive χ). Strictly more work than route H. Not recommended.
- **Contour only to Re s = 1/2 + 1/log x, without crossing zeros.** It loses a factor log x:
  ∫ log(q|t|)/δ |K| dt ≈ log q · log x. That is too weak for `GRHSmoothBound` (heuristic, standard).

---

## 4. Decisions for the user

1. **Vendor PNT+ files** (Apache-2.0, with attribution) into the repo: recommended. The alternative, a
   Lake dependency, would require moving our Mathlib pin, because PNT+ is on v4.35.0. It would add four
   packages and invalidate the cache.
2. **`GRHBounds`:** accept that the log⁴ theorem follows from the log² theorem (E3), so `GRHBounds` leaves
   the literal-GRH chain. Or require `GRH → GRHBounds` too (+≈1500 lines).
3. **Interface:** keep `GRHSmoothBound` as the named intermediate and prove `GRH → GRHSmoothBound`, so no
   existing file changes. This is recommended. CLAUDE.md's "deriving these from a literal GRH statement is
   deferred" clause would then need updating.
