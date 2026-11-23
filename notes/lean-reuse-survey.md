# Survey: existing Lean developments that could shorten `GRH → GRHSmoothBound`

Written 2026-11-23. This note is a companion to notes/grh-blueprint.md (route L, about 3,000 new lines).

Status tags:
- **checked statically**: read from the source files, with grep or ripgrep.
- **sketched**: a paper argument is given and the details are routine.
- **heuristic**: an estimate or a judgement.
- **[UNVERIFIED]**: taken from web pages or search snippets and not checked.

Nothing below was compiled. No `lake`, `lean` or build script from any downloaded archive was run. Every
downloaded file is in the session scratchpad, under
`/private/tmp/claude-501/-Users-maxfeldman-Desktop-maths-research/9e4c9912-0c7a-4fa9-a228-3de7c709a385/scratchpad/survey/`
(subfolders `alpo/`, `tauceti/`, `aintlib/`). That folder is temporary and may be cleared.

Our pin: Lean `v4.36.0-rc2`, Mathlib `9d581dff` (committed 2026-10-27).

---

## Summary and ranking

| Rank | Candidate | Licence | Lean / Mathlib | What it gives us | Savings on the ~3,000 new lines (heuristic) | Verdict |
|---|---|---|---|---|---|---|
| 1 (largest, blocked) | alpo.ge RH/GRH archive, `GlobalInterpolation` cluster (about 4,350 lines, Mathlib-only) | **none** (no LICENSE file, no headers) | v4.33.1 / `0df444a3` (2026-08-21) | Truncated explicit formula for primitive Dirichlet L-functions, including the Perron contour shift, Landau's lemma for L and ζ, good heights, L-function growth to Re s ≥ −7/4 and window zero counts | ~1,800–2,100 (route R below) | **Reference only** until the author grants a licence. Then vendor after a port. |
| 2 (best actionable) | TauCeti, selected files | Apache-2.0 | v4.37.0-rc1 / `31ce06ea` (2026-11-19); **newer** than ours | Cesàro-kernel Perron integral (A2, y = 1 included), B1 (L and ζ growth on Re s > 0), Landau's lemma at a general centre (B3 without the affine-transfer step V4), A1, E1 helper | ~500–800 new, plus ~850 vendored lines (V4, V5) no longer needed | **Vendor selected declarations** (needs a CLAUDE.md change), with a backport |
| 3 | PrimeNumberTheoremAnd (PNT+) | Apache-2.0 | v4.35.0 / v4.35.0 | Already the blueprint's V1–V5 | (baseline, already counted) | Vendor (in progress) |
| 4 | AINTLIB `DedekindResidue` (Birkbeck) | Apache-2.0 | **v4.36.0-rc2** / `805bbc49` (2026-11-05) | A GRH-conditional explicit formula for Dedekind ζ (Belabas–Friedman): rectangle Cauchy formula, zero capture, GRH zero sums | ~0–150 (templates for C3 / D1) | Reference only |
| 5 | Mathlib PRs #44967, #39232, #29588, #40540, #46011, #46100 | Apache-2.0 | master | Borel–Carathéodory derivative bound, rectangle residue theorem, Riemann ξ, Perron (closed), de la Vallée Poussin (closed) | ~0 beyond PNT+/TauCeti | Reference only |
| — | OpenAI `openai/math` (DirichletL, quasi-RH 7/8) | Apache-2.0 | v4.34.1 / `d13f23b7` | Sieve/automorphic route to a zero-free half-plane; no Perron, explicit formula or contour tooling found by file name | 0 | Irrelevant |
| — | Math Inc Gauss / `strongpnt` | Apache-2.0 | — | Merged into PNT+ (blueprint §1). No newer Dirichlet-L release found | 0 | Already covered by PNT+ |
| — | ANTEDB (Tao–Trudgian–Yang) | — | — | Python database; the Lean folder is a placeholder [UNVERIFIED] | 0 | Irrelevant |
| — | DeepMind formal-conjectures | Apache-2.0 | v4.33.1 | Statements only (e.g. `FormalConjectures/Millennium/RiemannHypothesis.lean`) | 0 | Irrelevant |
| — | Carleson, FLT, Harmonic Aristotle | — | — | Harmonic analysis or algebra; no L-function or contour material found | 0 | Irrelevant (not inspected in depth; heuristic) |

If a licence for the alpo.ge code cannot be obtained (heuristic): stay on route L. Take V1–V3 from PNT+, as
planned. Take A2, B1 and Landau-at-a-general-centre from TauCeti; this removes V4, V5 and most of B1. Use
the alpo.ge cluster only as a design reference. New lines drop from ~3,000 to about 2,200–2,500.

---

## 1. TauCeti

**What it is (checked statically and from the web).** Tau Ceti is an AI-written Lean 4 library that sits
downstream of Mathlib. Humans write the roadmaps (repository TauCetiRoadmap) and the review rubrics
(TauCetiReview). AI contributors write the code, and AI reviewers check it adversarially. The Lean FRO
and the Mathlib Initiative incubate it. The launch was presented at a National Academy of Sciences panel
on 2026-07-20 [UNVERIFIED].
- Repository: https://github.com/TauCetiProject/TauCeti. Surveyed at commit `547786e7` (2026-11-23).
- **Licence: Apache-2.0.** Each file carries a "The Tau Ceti contributors" header.
- Toolchain `leanprover/lean4:v4.37.0-rc1`; Mathlib `master`, pinned in the manifest to `31ce06ea`
  (2026-11-19, "bump toolchain to v4.37.0-rc1").
- Size: 38,921 `.lean` files, about 9.2M lines.
- CI enforces no `sorry` and runs an axiom audit. A grep finds `sorry`, `axiom` and `admit` only in prose
  and docstrings. There are 0 `native_decide` (checked statically).
- Files use the module system (`module`, `public import`, `@[expose] public section`).

**Relevant declarations (checked statically; names exact):**

| Blueprint node | TauCeti file | Declarations | Notes |
|---|---|---|---|
| A2 (kernel, **y = 1 included**) | `TauCeti/Analysis/MellinInversion.lean`, `TauCeti/Analysis/MellinTransform.lean` | `TauCeti.integral_cpow_div_mul_add_one : 0 < c → 0 < x → ∫ t, x^(c+it)/((c+it)(c+it+1)) = 2π · max(1 − x⁻¹, 0)`; `TauCeti.mellinInv_inv_mul_add_one`; `TauCeti.hasMellin_max_one_sub_zero` | The proof is Mellin inversion (Mathlib `mellinInv_mellin_eq`) applied to `max(1−t,0)`, not a contour shift, so the y = 1 case needs no separate argument. The declaration is short, but the file's import closure is 294 modules (83k lines), because it imports the residue machinery. **Re-derive it locally (~60 lines)** rather than vendor the file. |
| A1 | `TauCeti/NumberTheory/DirichletCharacter/LFunction/LogDeriv/Basic.lean` | `DirichletCharacter.logDeriv_LFunction_eq_neg_LSeries` (1 < Re s), plus prime/higher-power splitting lemmas | Closure: 6 modules, 1.4k lines. Saves ~30 lines. |
| B1 (χ ≠ 1) | `TauCeti/NumberTheory/DirichletCharacter/LFunction/Bounds.lean` | `DirichletCharacter.LFunction_eq_mul_integral` (L(s,χ) = s∫₁^∞ S_χ(t)t^{−s−1}dt on Re s > 0); **`DirichletCharacter.norm_LFunction_le_level_mul_norm_div_re : χ ≠ 1 → 0 < s.re → ‖L(s,χ)‖ ≤ N‖s‖/Re s`**; `DirichletCharacter.norm_LFunction_le` (every χ, s ≠ 1); `norm_LFunction_one_le_one_add_log` | This is B1 almost verbatim: on Re s ≥ 1/10 it gives ‖L‖ ≤ 10N‖s‖. Import closure 54 modules (15k lines); a rough token-based declaration-level closure is ~600 lines (heuristic). |
| B1 (q = 1), V5 | `TauCeti/NumberTheory/LSeries/RiemannZeta/Bounds.lean` | **`TauCeti.norm_riemannZeta_le_of_re_pos : 0 < s.re → ‖ζ s‖ ≤ ‖s−1‖⁻¹ + 1 + ‖s‖/Re s`**; `TauCeti.riemannZeta_eq_div_sub_mul_integral`; `TauCeti.norm_riemannZeta₀_le_one_add_norm_div_re` | Gives ‖(s−1)ζ(s)‖ ≤ 1 + ‖s−1‖(1 + 10‖s‖) on Re s ≥ 1/10. **Replaces V5** (~600 vendored lines of the PNT+ ζ Abel continuation). |
| B3 (Landau) | `TauCeti/Analysis/Complex/LocalLogDeriv.lean` | **`AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le`** (centre z₀, radii r < R, hypothesis ‖f w‖ ≤ M‖f z₀‖ on the sphere; bound (4(r+d)/(r−d)² + r/((R²−rd)log(R/r)))·log M); `AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le_of_two_mul_le`; `…_half_le` | Works at a **general centre and radius**, with multiplicities as Mathlib `divisor` values. **Avoids V4**, the PNT+ affine-transfer lemmas (~250 vendored lines plus their analytic-order bookkeeping), which exist only because PNT+ `FinalBound` is stated on the unit disc with f 0 = 1. Closure: 13 modules, 2.7k lines, Mathlib only. |
| B3 (count) | `TauCeti/Analysis/Complex/JensenFormula.lean` | `AnalyticOnNhd.sum_divisor_le_log_div_log`, `AnalyticOnNhd.sum_divisor_half_le`, `AnalyticOnNhd.sum_divisor_le_analyticOrderNatAt_add` | Mathlib already has `AnalyticOnNhd.sum_divisor_le`; these are more convenient variants. |
| Borel–Carathéodory derivative | `TauCeti/Analysis/Complex/BorelCaratheodory.lean` | `Complex.norm_deriv_le_of_forall_mem_ball_re_le`, `Complex.norm_logDeriv_le_of_forall_mem_ball_norm_le_mul` | Used inside the Landau lemma. |
| D1 (residues) | `TauCeti/Analysis/Contour/Residue/{Basic,Rectangle,LogDeriv,VerticalLineShift}.lean`, `TauCeti/Analysis/MellinTransform/LineShift.lean` | `TauCeti.Contour.residue`; `TauCeti.Contour.classicalResidueTheorem_rectBoundary`; **`TauCeti.Contour.integral_boundary_rect_eq_two_pi_I_mul_sum_residue`** (four-edge form, meromorphic points of any order); `TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt`; `TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue`; `TauCeti.mellinInv_eq_sum_residue_add` | More general than PNT+ (not limited to simple poles), but the closure is 277 modules (76k lines). **Do not vendor**: PNT+ V1 already covers D1. |
| E1 helper | `TauCeti/NumberTheory/Chebyshev/ResidueClass.lean` | `Chebyshev.psiAP`, `Chebyshev.sum_psiAP_not_isUnit_le`, `Chebyshev.sum_psiAP_not_isUnit_le_card_mul_log` (Σ over non-unit classes ≤ ω(q) log x), `Chebyshev.psiAP_zero_le_log`, `Chebyshev.norm_sum_vonMangoldt_smul_sub_sum_psiAP_smul_le` | Closure: 7 modules, 1.7k lines. Saves ~50 of E1's 150 lines. |
| Route H only | `TauCeti/NumberTheory/LFunctions/Zeros/Completion/Dirichlet/{Hadamard,Growth,LogDeriv,Zeros,Basic}.lean` | `dirichletData_entireCompletion_hadamard`, `dirichletData_isFiniteOrder`, `re_logDeriv_LFunction_add_eq_tsum`, `re_one_div_sub_le_re_logDeriv_LFunction_add`, `logDeriv_dirichletData_entireCompletion_eq_digamma`, … | Hadamard factorization and Re(L′/L) as a sum over zeros, for primitive χ. Closure 140 modules (32k lines). Not needed on route L. |
| GRH statements | `TauCeti/NumberTheory/LFunctions/Zeros/RiemannHypotheses.lean` | `DedekindERH`, `HeckeGRH`, `heckeGRH_one_iff_dedekindERH` | Hecke and Dedekind forms, not comparable with our `EOS.GRH`. |

**Absent from TauCeti (checked statically):** Perron's formula for sums (only the Mellin-kernel identities above),
any explicit formula for ψ, Siegel–Walfisz, Bombieri–Vinogradov, zero-density estimates, ψ(x,χ) bounds
and GRH-conditional bounds for ψ. Zero-counting exists only as the abstract
`zeroCountingFunction` (`…/Zeros/Counting/Basic.lean`); there is no N(T, χ) asymptotic.

**Compatibility (heuristic).** TauCeti's Mathlib is about 3 weeks **ahead** of ours and on the next
release candidate. A backport can hit lemmas that do not exist yet in our pin. Each file also needs the
`module`/`public` syntax removed, as was done for PNT+, and must comply with Apache-2.0 attribution.
CLAUDE.md currently allows vendored code only from PNT+, so vendoring TauCeti needs a user decision. A
cheaper option is to re-prove the four short results (A2 kernel, B1 for χ ≠ 1, B1 for ζ, Landau at a
general centre) locally, using the TauCeti proofs as templates.

---

## 2. The alpo.ge Lean development (RH/GRH announcement)

**Source (checked statically).** https://alpo.ge/remark.pdf (4 pages). In it Levent Alpöge says he and
Claude found a proof of RH and GRH and formalized it. Footnote 1 links `lean.tar.gz.part01…part14`.
- HEAD responses carry no Content-Length. A full GET showed 13 × 18,000,000 bytes plus 5,275,554 bytes,
  about 239 MB compressed. The archive has 175,190 entries and about 1.03 GB uncompressed, all regular
  files, with no symlinks or absolute or `..` paths.
- The archive was extracted to `…/scratchpad/survey/alpo/x/lean/`.
- **This code is untrusted and unreviewed. I describe it; I do not vouch for it.** A web search found
  mirrors and a visualizer, but no independent confirmation that it builds or that the mathematics is
  correct [UNVERIFIED].

**Versions and structure (checked statically).**
- `lean-toolchain`: `leanprover/lean4:v4.33.1`.
- `lakefile.toml`: package `tree`, Mathlib rev `0df444a360eaa60ab8c11dca51a86af692955474` (2026-08-21,
  "bump toolchain to v4.33.1"). Global options `maxHeartbeats = 4000000` and `--tstack=400000`.
- 175,187 `.lean` files, **about 17.4M lines**. Libraries:

  | Library | Files | Lines |
  |---|---|---|
  | `Development` | 141,928 | 12.2M |
  | `Formalism` | 18,254 | 3.2M |
  | `GroundTheory` | 8,507 | 1.1M |
  | `ReciprocityTheory` | 3,845 | 0.56M |
  | `CompanionTheory` | 2,027 | 0.19M |
  | `PositivityTheory` | 449 | 0.06M |
  | `Lemmata` | 167 | 9k |
  | `Supplements`, `BuildAid` | — | tiny |

- Directory and declaration names are **semantically scrambled**. For example, the analytic number theory
  lives under `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/`, and von Mangoldt is aliased
  as `Formalism.MainNotions.GlobalTheoryTheory.abelian₂`.
- **No LICENSE file and no copyright headers.**
- Main theorems in `src/Main.lean`, using statements from `src/Statements.lean`:
  - `riemannHypothesis : RiemannHypothesis`
  - `riemannZeta_eq_zero_re : RiemannZetaZerosOnLine`
  - `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`
  - `LFunction_eq_zero_re : DirichletLZerosOnLine` (all χ)
  - **`LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine`**
- `PrimitiveDirichletLZerosOnLine` is
  `∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2`.
  This is **character-for-character our `EOS.GRH`**; only the bound variable is `N` instead of `q`.
  `DirichletLZerosOnLine` is our `GRH_iff_forall` right-hand side.
- The remark describes an automorphic method: Stepanov-style multiplicity through iterated theta lifts.
  The archive's RH machinery is not classical analytic number theory.

**Soundness greps over all 175,187 files (checked statically; matches anywhere, including comments):**

| Pattern | Count |
|---|---|
| `sorry` | 0 |
| `axiom` | 0 |
| `admit` | 0 |
| `native_decide` | 0 |
| `implemented_by` / `extern` / `unsafe` / `opaque` / `debug.skipKernelTC` | 0 |
| `decide := true` | 26 lines |
| `set_option maxRecDepth` | 34 |

Metaprogramming:
- 5 `run_cmd`, all in `BuildAid/D*.lean`. Each only adds a namespace to the
  `LibrarySuggestions.nameDenyListExt` deny list.
- A few custom elaborators: `kcopy`, `kexactB`, and `cpt_copy_thms`, which copies theorems via `addDecl`.
  All of them go through the kernel. `#print axioms` could not be run (no build).

**Reusable infrastructure (checked statically; Lean statements read, not compiled).** One self-contained
cluster is classical Davenport-style analytic number theory for primitive Dirichlet L-functions. It is
about **4,350 lines in 23 files** and depends logically only on Mathlib. A few spurious imports pull in
unrelated libraries; the `psi0` definition sits in
`Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/FiltrationCocycleLiftCriterion.lean`.
Paths below are relative to `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/` (abbreviated `GI/`).

| Content | File (lines) | Declaration (exact) |
|---|---|---|
| **Truncated explicit formula**, primitive χ mod N (N = 1 allowed), 2 ≤ T ≤ u: ‖ψ₀(χ,u) + Σ_{0<β<1, \|γ\|≤T} m_ρ u^ρ/ρ‖ ≤ C(u log²(NuT)/T + log(Nu) + Σ_{\|γ\|<1} m_ρ/\|ρ\|), where ψ₀ = Σ_{n≤u}Λ(n)χ(n) − [N=1]u | `GI/ExplicitFormulaClosed.lean` (92), `GI/TruncatedExplicitFormula.lean` (73) | `GlobalTheory.ExplicitFormulaClosed.explicit_formula_closed`, `GlobalTheory.ExplicitFormula.truncated_explicit_formula` |
| Same for **all** χ (reduced to the primitive character), with a weaker error √u·q³·log² | `GI/ExplicitFormulaDirichletZerosRightHalf.lean` (265) | `explicit_formula_right`, `GlobalTheory.T.norm_psi0_add_zsum_le` (not traced in detail) |
| Truncated Perron for ψ(u,χ) at c = 1 + 1/log u | `GI/TruncatedPerronPsi.lean` (608), `GI/TruncatedPerronKernel.lean` (404) | `GlobalTheory.PerronPsi.truncated_perron_psi`, `truncated_perron_kernel` |
| Contour shift to Re s = −1/2 with residues at the zeros, s = 0 and s = 1 | `GI/PerronIntegralShiftPrimitiveLFunction.lean` (337), `GI/AnalyticAtDslope.lean` (298), `GI/BdIntEqZeroOfPrimitive.lean` (217) | `GlobalTheory.PerronShift.perron_shift`, `GlobalTheory.T.perron_integral_shift_primitive_LFunction`, `GlobalTheory.ExplicitRect.residue_identity`, `residue_rectangle` (rectangle residue theorem for poles of order ≤ 2) |
| **Landau's lemma, generic** (unit disc, then any disc): finitely many zeros in radius R·a, Σ m ≤ C(1 + log(M/‖F c‖)), and a‖F′/F − Σ m/(s−w)‖ ≤ C(1 + log(M/‖F c‖)) | `GI/NormOneSubConjMul.lean` (243), `GI/LogDerivLFunctionStrip.lean` (134), `GI/ImportsMore.lean` (177) | `GlobalTheory.LogDerivZeros.main`, `GlobalTheory.LWide.disc`, `GlobalTheory.ZetaWide.scaled` |
| **Landau's lemma for L (blueprint B3)**: for χ ≠ 1 of any modulus, and −1 ≤ Re s ≤ 2, L(s) ≠ 0: zeros in the disc ‖w − (2+it)‖ ≤ 7/2 number ≤ C log(q(\|t\|+2)), and ‖L′/L(s) − Σ m/(s−w)‖ ≤ C log(q(\|t\|+2)) | `GI/LogDerivLFunctionStrip.lean` | **`GlobalTheory.LWide.logDeriv_LFunction_strip`** |
| Same for ζ, with the 1/(s−1) term | `GI/ImportsMore.lean` | **`GlobalTheory.ZetaWide.main`** |
| L growth to the left of 0 by **three-fold Abel summation** (no functional equation): ‖L(s,χ)‖ ≤ C q⁴(‖s‖+2)⁴ on Re s ≥ −7/4; ‖(s−1)ζ(s)‖ ≤ C(‖s‖+2)⁵ | `GI/SummableNinePowMulInvSqSucc.lean` (322), `GI/NormSubOneMulRiemannZetaLe.lean` (217) | `norm_LFunction_le_poly_left`, `abel_three`, `LFunction_eq`; `GlobalTheory.ZetaLeft.norm_sub_one_mul_riemannZeta_le` |
| Lower bound at Re s = 2 (blueprint B2) | `GI/TsumOneDivRpowLe.lean` (92) | `norm_LFunction_ge`, `norm_LSeries_le` |
| **Good heights (C2)**: for every T ≥ 2 there is T′ ∈ [T, T+1] with L ≠ 0 and ‖L′/L‖ ≤ C log²(NT) on \|Im s\| = T′, −1/2 ≤ Re s ≤ 3 | `GI/ExistsBoundRight.lean` (359) | `GlobalTheory.GoodHeight.exists_height`, `exists_far` (pigeonhole), `local_formula` |
| L′/L on Re s = −1/2 ≪ log(N(\|t\|+2)); trivial zeros | `GI/PerronIntegralShiftPrimitiveLFunction.lean`, `GI/CompletedLFunctionNeZeroOfReNonpos.lean` (148) | private `exists_norm_logDeriv_LFunction_neg_half_le_log_conductor`; `GlobalTheory.LFunction_zero_of_re_nonpos` |
| Zeros in windows are finite and have order ≥ 1; band sums | `IwasawaDecomposition/DirichletLZerosInWindowFiniteAndPosOrder.lean` (82), `GI/FiniteBox.lean` (125) | `GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult`, `GlobalTheory.ZeroBand.zeros_band` |

Elsewhere in the archive, not needed here (checked statically, by name only):
- `Formalism/LandauZeroFreeBounds/` (58 files, 6.6k lines): Siegel–Walfisz (`SiegelWalfiszAP.lean`,
  `FinalSiegel.lean`), `LandauLemmaLfunctionZeros.lean`, `RectShiftChi.lean`, `PsiChiBoundOf.lean`.
- `Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNT*.lean` (~10k lines):
  `ExplicitS` / `smoothed_explicit_formula`, using the kernel y^w/(w(w−1)), which is close to ours. Its
  error term contains (MT)^C·y^{−κ/2}, which is polynomial in the modulus, so it cannot give log(2q).
- `Formalism/PeriodIntegrals/ExplicitFormula.lean` (`PI.ExplicitFormula`, `explicitFormula_of_perron_shift`).

**What this would buy: route R (sketched).** `explicit_formula_closed` makes our Cesàro contour unnecessary.
1. ψ̃(x,χ) = (1/x)∫₂^x ψ(u,χ)du exactly.
2. For primitive χ mod N, apply the formula with T = u for each u ∈ [2,x]. The error is
   ≤ C(log²(Nu) + Z₁). Under GRH, Z₁ = Σ_{\|γ\|<1} m/\|ρ\| ≤ 2·#{zeros} ≤ C log 2N, by the window count
   from `LWide.logDeriv_LFunction_strip` or `ZetaWide.main`.
3. Swap the finite zero sum and the integral:
   ∫₂^x Σ_{\|γ\|≤u} m u^ρ/ρ du = Σ_{\|γ\|≤x} m (x^{ρ+1} − a_ρ^{ρ+1})/(ρ(ρ+1)), with a_ρ = max(2, \|γ\|).
4. Under GRH this is ≤ x^{3/2}·Σ m/\|ρ(ρ+1)\| + Σ m a_ρ^{3/2}/\|ρ\|² ≤ C x^{3/2} log 2N + C√x log(Nx),
   using window counts ≪ log(N(\|t\|+2)).
5. Hence \|ψ̃ − [N=1]x/2\| ≤ C(√x log 2N + log²(Nx)). Split into cases:
   - if √x ≥ log 2N, then log²(Nx) ≤ C√x log 2N;
   - otherwise the trivial bound ψ̃ ≤ Cx ≤ C√x log 2N applies.
6. Imprimitive χ: \|ψ̃(x,χ) − ψ̃(x,χ*)\| ≤ ω(q) log x ≤ C√x log 2q (E1, generalized).
7. The range 1 ≤ x < 2 is trivial.

New code needed (heuristic):

| Step | Lines |
|---|---|
| Integration and swap (step 3, with the indicator rewrite for measurability) | ~300 |
| GRH zero sums | ~250 |
| Reduction to primitive and principal characters | ~200 |
| Assembly | ~150 |
| **Total** | **≈ 900–1,200** |

That replaces ~3,000 new lines: A2–A4, B1–B3, C1–C3, D1 and D2 disappear. V1–V5 also become
unnecessary, except that PNT+ is not needed at all on this route. The ~4,350-line cluster must instead be
ported from Lean v4.33.1 (Mathlib, Aug 2026) to v4.36.0-rc2. For comparison, PNT+ needed 7 one-line
patches over 3.9k lines across one minor version; three minor versions of drift on AI-written,
`nlinarith`-heavy code might need tens of fixes (heuristic). The spurious imports must also be replaced
by `import Mathlib` plus a local `psi0`.

**Blockers.**
- **No licence.** By default all rights are reserved, so we cannot vendor or adapt the code without the
  author's permission.
- Our CLAUDE.md allows vendored code only from PNT+.
- The code is unreviewed. After a port, however, our kernel would re-check every lemma, and the cluster
  uses no `sorry` or axioms, so the correctness risk becomes a porting cost, not a trust issue.
- **Verdict: reference only.** If the user wants route R, ask Alpöge for an explicit licence
  (e.g. Apache-2.0) for these files.
- Even as a reference, it settles two design questions for route L:
  1. Landau discs centred at 2+it with radius 7/2, using a three-fold Abel continuation to Re s > −2,
     work without the functional equation.
  2. The good-heights lemma is a pigeonhole over a finite zero set (`exists_far`).

---

## 3. Other candidates

### PrimeNumberTheoremAnd (PNT+)
Already analysed in notes/grh-blueprint.md §1, which also records the vendoring test at commit `a4fb6989`
(2026-11-15). No commits after that date (checked via the GitHub API). Coverage is still ζ only. Math Inc's
`strongpnt` (Gauss) lives inside PNT+ as `StrongPNT.lean`. No newer Math Inc Dirichlet-L release was found
[UNVERIFIED; one web search].

### AINTLIB (Chris Birkbeck)
https://github.com/CBirkbeck/AINTLIB, commit `c3bc9bfa` (2026-11-05).
- **Apache-2.0.** **Lean v4.36.0-rc2** (our toolchain). Mathlib `805bbc49` (2026-11-04), 8 days after our
  pin, so it is the most compatible candidate.
- Project `projects/DedekindResidue/` (~32k lines): the Belabas–Friedman GRH-conditional bound for the
  residue of ζ_K, via a Weil explicit formula with a compactly supported test function.
- `DedekindResidue.GeneralizedRiemannHypothesis K` is stated for completed Dedekind zeta, not for
  Dirichlet L.
- Possible templates:
  - `ExplicitFormula/RectangleContour.lean`: `rectangleIntegral_cauchy`, `rectangleIntegral_inv_sub`.
  - `ExplicitFormula/ZeroCapture.lean`: `exists_H_rectangle_factorization`,
    `rectangleIntegral_mul_logDeriv_H`.
  - `ExplicitFormula/GRHZeros.lean`: `exists_slab_zetaZeroDivisor_sum_le`, `summable_zetaZeros_inv_sq`,
    `ZetaZeros_re_eq_half`.
- `sorry` appears only in prose (checked statically).
- Verdict: **reference only** (wrong L-function; Hadamard and completed-function route). Possible savings
  ~0–150 lines as templates for C3.

### Mathlib PRs (checked via `gh`, 2026-11-23)
| PR | Status | Content |
|---|---|---|
| #44967 (ajirving) | open, +229 | Generalised Borel–Carathéodory and a derivative bound |
| #39232 (jerwaynejones) | open, +644 | Residue theorem for rectangles |
| #29588 | open | Residue theory at isolated singularities |
| #40540 (edwardfalk) | open, +640 | Riemann ξ |
| #46011 (startigerjln) | closed 2026-11-14, +252 | Perron summation formula |
| #46100 (Qamarbajwa) | closed 2026-11-19, +327 | de la Vallée Poussin zero-free region for ζ |

No PR by Loeffler, Stoll or Birkbeck on Dirichlet L′/L bounds, zero counting or explicit formulas was
found. Verdict: reference only. PNT+ and TauCeti already contain stronger versions of the open PRs.

### OpenAI `openai/math`
https://github.com/openai/math.
- **Apache-2.0.** Lean v4.34.1, Mathlib `d13f23b7`.
- `lean/OAI/NumberTheory/DirichletL/` has 2,926 files (~25 MB), supporting the "quasi-RH 7/8" zero-free
  half-plane released on 2026-10-06 [UNVERIFIED for the mathematics].
- Challenge statement: `lean/ComparatorChallenges/DirichletSevenEighths.lean`,
  `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` (the challenge file is a `sorry` stub
  by design).
- File names point to sieve, theta and Eisenstein machinery (`RowCompletion/…`, `Reflection/…`). None
  suggests Perron, explicit formula, Landau or L′/L tooling (checked by file name only; not downloaded).
- The lakefile depends on `strongpnt`, `AINTLIB` and `carleson`.
- Verdict: **irrelevant**.

### Others
- **ANTEDB** (https://github.com/teorth/expdb): Python, with a placeholder Lean folder [UNVERIFIED].
  Irrelevant.
- **DeepMind formal-conjectures**: Apache-2.0, v4.33.1. Statements only. Irrelevant.
- **Carleson project**: harmonic analysis (Hilbert transform, Fourier series), no contour integration.
  Irrelevant (heuristic; scope only).
- **FLT project**: algebraic. Irrelevant (heuristic).
- **Harmonic / Aristotle**: no L-function release found [UNVERIFIED].
- **Siegel–Walfisz, Bombieri–Vinogradov, explicit formula** elsewhere: only the alpo.ge archive (above)
  and AINTLIB (Dedekind ζ) were found.

---

## 4. Recommendation (heuristic)

1. **Now, with no licence question:** keep route L.
   - Take V1–V3 from PNT+ (residue theorem on rectangles, Perron kernel, Landau's lemma as already vendored).
   - Prefer TauCeti's general-centre Landau lemma `AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le`,
     which removes V4. Re-prove it locally or vendor it (13 modules, 2.7k lines).
   - Prefer TauCeti's B1 (`DirichletCharacter.norm_LFunction_le_level_mul_norm_div_re`,
     `TauCeti.norm_riemannZeta_le_of_re_pos`), which removes most of B1 and all of V5.
   - Prefer TauCeti's A2 proof idea (Mellin inversion of `max(1−t,0)`, `TauCeti.integral_cpow_div_mul_add_one`).
   - Expected new lines: ~2,200–2,500 instead of ~3,000.
2. **If the user wants the shortest path:** ask Levent Alpöge for a licence on the 23-file
   `GlobalInterpolation` cluster. Then port it and follow route R (~1,000 new lines plus a port of
   ~4,350 lines).
3. Either way, `Statements.PrimitiveDirichletLZerosOnLine` in the alpo.ge archive is literally `EOS.GRH`.
   If that archive's main theorem were ever verified and licensed, `GRH` would become a theorem. That is
   orthogonal to the `GRH → GRHSmoothBound` task, and nothing here relies on it.

Sources:
- [TauCeti repository](https://github.com/TauCetiProject/TauCeti)
- [Lean FRO: Tau Ceti use case](https://lean-lang.org/use-cases/tau-ceti)
- [Reservoir: TauCeti](https://reservoir.lean-lang.org/@TauCetiProject/TauCeti)
- [NAS panel, 2026-07-20](https://web.mit.edu/~ywang02/www/blog/nas-formalization/posts/05-panel-structures-to-understand-knowledge.html)
- [alpo.ge remark](https://alpo.ge/remark.pdf)
- [JGalego/riemann mirror](https://github.com/JGalego/riemann)
- [treemap visualizer](https://pengowray.github.io/riemann-zeta-proof-visualizer/)
- [AINTLIB](https://github.com/CBirkbeck/AINTLIB)
- [openai/math](https://github.com/openai/math)
- [Liu, arXiv:2610.12234](https://arxiv.org/html/2610.12234v1)
- [ANTEDB](https://github.com/teorth/expdb)
- [Math Inc sphere-packing note](https://gwern.net/doc/math/2026-03-mathinc-completingtheformalproofofhigherdimensionalspherepacking.html)
- [Loeffler–Stoll, Formalizing zeta and L-functions in Lean](https://arxiv.org/abs/2503.00959)
