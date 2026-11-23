# Lean referee report: do the hypotheses and conclusions mean what the notes say?

Written 2026-11-23 by an adversarial referee. No existing file was edited; git was not run; Mathlib was not built.
Files I created: `EOS/scratch_referee/Axioms.lean`, `EOS/scratch_referee/Degenerate.lean`,
`compute/leanref/check_inputs.py`, `compute/leanref/check_h4_grh.py`.

Verdict tags: FAITHFUL / FAITHFUL WITH CAVEAT / DEFECT.
Evidence tags: *Lean* = typechecked this session; *computed* = script in `compute/leanref/`; *re-derived* = argument redone
by hand; *read* = I read the source text this session; [RECALLED] = from memory, source not opened.

## 0. Bottom line

- **No DEFECT found.** Every named hypothesis is a faithful statement of what its docstring says, and every conclusion
  says what the notes claim.
- **`eos_of_H4` does not prove EOS from nothing.** The theorem restricts to `0 < η ≤ η₀ ≤ 1/4` and `0 < λ ≤ κη ≤ 1`,
  and in that range `numBlocks ≥ 1`, the blocks tile `[⌈m^η⌉, ⌈√m⌉)` exactly, and every block has length `≥ m^{η/2} ≥ 2`
  (`numBlocks_facts`, `blockPt_zero`, `blockPt_top`, `block_facts`). H4 is used once, for each block of that system.
- The caveats are: (1) `H4` as a bare definition is trivially true outside `0 < η < 1/2`, `λ > 0`; (2) the cited inputs
  rest on sources of which I could read only one; (3) nothing asymptotic can be tested numerically, and at `m ≈ 10⁵`
  both `H4` and `TypeISifted` (at `ε = 1/100`) fail, as expected; (4) two stale docstrings in Buchstab.lean.

## 1. Mechanical checks (*Lean*)

| Check | Result |
|---|---|
| `lake env lean EOS/<F>.lean` for Statement, LogFour, LogSquare, Buchstab, ThreePrimes, GapH4 | exit 0 for all six. Only output: `Statement.lean:38:8: warning: declaration uses sorry` |
| `#print axioms` for `coveredBy_of_grhBounds`, `coveredBy_log_sq`, `coveredByAsym_m_log_cube`, `coveredBy_three_primes`, `eos_of_H4`, `buchstab_identity`, `lemmaC'`, `lemmaC'_of_H4Block`, `lemma22_comb`, `defect_le` | `[propext, Classical.choice, Quot.sound]` for all ten |
| `#print axioms EOS.eos_of_grhBounds` | additionally `sorryAx`. This is the intended statement of the open problem |
| grep `sorry` | one hit, Statement.lean:39 (above) |
| grep `native_decide`, `implemented_by`, `opaque`, `axiom`, `unsafe`, `extern`, `ofReduceBool` | no hits |
| grep `set_option` | two `linter.unusedSectionVars false` in GapH4.lean; harmless |

So the claim "every theorem in EOS/EOS/*.lean is proved with no sorry" is true with the one deliberate exception
`eos_of_grhBounds`. No other theorem depends on it.

## 2. GRH-consequence hypotheses

### `GRHBounds` (Statement.lean) — FAITHFUL (*re-derived*, *computed*)

`∃ C > 0, ∀ q [NeZero q] χ x, 2 ≤ x → ‖ψ(x,χ) − [χ = 1]·x‖ ≤ C √x (log(q x))²`.

- `χ = 1` is the principal character mod `q` (zero on non-units), as the previous referee verified in Lean.
- `Λ(0) = 0`, so summing over `Iic ⌊x⌋₊` is harmless. `q x ≥ 2`, so `log(q x) ≥ log 2 > 0`; `q = 1` is not degenerate.
- Truth under GRH: for primitive χ this is Davenport ch. 20 [RECALLED]. Imprimitive χ and principal χ mod `q > 1` differ
  from the inducing character by at most `Σ_{p∣q} log p · ⌊log x / log p⌋ ≤ ω(q) log x ≤ (log q)(log x)/log 2`, which is
  `≤ 2.1 √x (log(qx))²`. Large `q` relative to `x` is covered because the GRH bound is uniform in `q`.
- Computed: over `q ∈ {1,2,3,4,5,7,8,12,15,24,30,31,60,101}`, all characters, `2 ≤ x ≤ 2·10⁵` (both ends of each
  interval `[n, n+1)`), the sup of the ratio is 1.9234, at `q = 1`, `x = 2`. So `C ≥ 1.93` is necessary and nothing grows.

### `GRHSmoothBound` (LogSquare.lean) — FAITHFUL (*re-derived*; earlier referee's checks stand)

`∃ C > 0, ∀ q [NeZero q] χ x, 1 ≤ x → ‖ψ̃(x,χ) − [χ = 1]·x/2‖ ≤ C √x log(2q)`.

I reread the Lean text against `notes/routes/C-referee.md` §1.1 and agree with each row of its table:
`1 ≤ x < 2` gives an empty sum and the claim `x/2 ≤ C √x log 2`; `log(2q) ≥ log 2`; the weight `1 − n/x` is `≥ 0` on
`n ≤ ⌊x⌋`; the casts `(n : ℂ)/(x : ℂ)` and `((x/2 : ℝ) : ℂ)` are the intended ones; imprimitive characters cost
`ω(q) log x ≤ 1.07 √x log q`. The constant terms of the Cesàro explicit formula (`L′/L(0,χ)`, and `log x` for even χ) are
`O(log 2q)` and `O(√x)`. `GRHSmoothBound.bounds` is the only consumer and uses the definition correctly.

## 3. Unconditional inputs of the gap theorem

### `siftedR`, `Phi`, `PhiCop`, `Aset`, `rho`, `primesP` — FAITHFUL (*computed*)

- `Nat.minFac 1 = 1`, so the clause `n = 1 ∨ y ≤ minFac n` is needed and is present everywhere.
- `Aset m a` is the image of `q ↦ (a·q̄).val` on primes `q ≤ m`, `q ∤ m`. For `m ≥ 2` it lies in `[1, m)`, has `|P|`
  elements, and consists of units (`mem_Aset`).
- **`ρ·PhiCop` is the exact mean of `S(A_a, y)` over units `a`**, not only the expected size: summing over `a`, each
  prime `q` contributes the number of rough units. Computed for `m ∈ {3, 4, 6, 30, 210, 2310, 10007, 30030, 99990, 100003}`:
  mean `S(A_a)` equals `ρ·PhiCop` to all printed digits (e.g. `m = 100003`, `η = 0.2`: 2192.4955 both).
  So `TypeISifted` asserts that the minimum over `a` is close to the mean, which is the right shape.

### `TypeISifted` — FAITHFUL WITH CAVEAT (*re-derived*, source partly *read*)

- Quantifiers `∀ε ∃η₁ ∀η ≤ η₁ ∃m₁ ∀m ≥ m₁ ∀a`: this is what Lemma 2.1 of `E-buchstab-H4.md` gives and is not stronger.
  `C₆ e^{−1/(17η)} ≤ εη` for all `η ≤ η₁(ε)`; `m^{1−1/300} ≤ ε ρ π(m)` for `m ≥ m₁(ε)`; uniformity in `a` comes from the
  Type I bound. The Lean form is a weakening of Lemma 2.1, as the docstring says.
- Source check (*read*): I extracted the text of Shparlinski, arXiv:1705.06087v1. Lemma 5.4 states, for arbitrary `m`,
  `m ≥ x ≥ m^{1/2}`, `m ≥ y ≥ 1`, `gcd(a, m) = 1`: `Δ₁(a; x, y) ≤ (x^{15/16} + m^{1/4} x^{2/3}) m^{o(1)}`, with main term
  `π(x) y / m`. §7 states that `#A(d) = 0` if `gcd(d, m) > 1` and otherwise `|#A(d) − π(x) y/(d m)| ≤ Δ₁`. At `x = y = m`
  this is IN-T1 of the note. Equation (5.1) quotes Fouvry–Shparlinski Thm 3.1 for `x ≤ m^{4/3}`, `gcd(a, m) = 1`.
- Caveats. (a) The proof of the `Δ₁` bound is delegated to "[14, Lemma 2]" (Shparlinski 2013), which I did not read; that
  is where frequencies `h` with `gcd(h, m) > 1` in the Erdős–Turán step must be handled. (b) The text extraction dropped
  overlines, so I infer from the section title ("sums with reciprocals of primes") that the sums are over `p̄`.
  (c) The fundamental lemma is [RECALLED] in the note and by me. (d) Remainder arithmetic re-derived:
  `1/17 + 15/16 = 271/272 < 1 − 1/300`.
- Computed: at `ε = 1/100` the inequality fails for 37% of units at `m = 100003`, `η = 0.2` (std of `S(A_a)` is 43.4,
  the slack is 13.6), and for 6% at `m = 99990`, `η = 0.25`. This is consistent with the statement, which only claims
  `m ≥ m₁`, and the slack `≍ m/log² m` overtakes the fluctuation `≍ √m` eventually. It cannot be confirmed numerically.

### `SieveUpperBound` — FAITHFUL (*re-derived*, *computed*)

`∃ C > 0, ∀ a H : ℕ, ∀ y : ℝ, 2 ≤ y ≤ H → #{a < n ≤ a + H : n = 1 ∨ y ≤ minFac n} ≤ C H / log y`.

- `n > a ≥ 0`, so `minFac 0 = 2` never enters. `log y ≥ log 2 > 0`. `H < 2` is vacuous.
- The docstring's derivation is right: `Q = min(y, √H) ≥ √y`, `H + Q² ≤ 2H`, `Σ_{q ≤ Q} μ²(q)/φ(q) ≥ log Q`, giving
  `4H/log y`; the element `n = 1` is not removed by the sieve.
- Computed: for `2 ≤ H ≤ 300`, `0 ≤ a ≤ 40000`, `y` at every prime `≤ H` and at `H`, the sup of `count · log y / H` is
  1.0595 (at `a = 22480`, `H = 33`, `y = 33`, count 10). No growth with `a`.

### `RoughMertens` — FAITHFUL (*re-derived*, *computed*)

`∀ε ∃η₁ ∀η ≤ η₁ ∃m₁ ∀m ≥ m₁: η Φ(m, m^η) ≤ (e^{−γ} + ε) π(m)`.

- From `Φ(x, x^{1/u}) ∼ u ω(u) x/log x` and PNT, `η Φ(m, m^η)/π(m) → ω(1/η)`, and `ω(u) → e^{−γ}`. The quantifier
  order is the literature's: `η₁` depends on ε, `m₁` on η and ε. [RECALLED for the Buchstab–de Bruijn theorem numbers.]
- Computed ratio `η Φ(m, m^η)/π(m)` at `m = 10⁷`: 0.500 (η = 0.5), 0.513, 0.519, 0.512, 0.492, 0.469, 0.401, 0.376
  (η = 0.05); all below `e^{−γ} = 0.5615`. At `m = 10⁶`, `η = 0.05` the ratio is 0.637 because `m^η < 2`; this is the
  reason `m₁` must depend on η, and the statement allows that.
- `RoughCounts` omits the note's D-RNL (lower bound for rough numbers). The Lean proof does not need it, so this is a
  weaker hypothesis set than the note's, not a gap.

## 4. The gap hypothesis

### `numBlocks`, `blockPt` — FAITHFUL WITH CAVEAT (*Lean*, *computed*)

- In the range used by `eos_of_H4` (`0 < η ≤ 1/4`, `0 < λ ≤ 1`, `m` large): `J ≥ 1`, `blockPt 0 = ⌈m^η⌉`,
  `blockPt J = ⌈√m⌉`, monotone, each block has integer length `≥ m^{(η + jδ)/2} ≥ 2`. Computed examples agree
  (`m = 100003`, `η = 1/4`, `λ = 1`: points 18, 32, 57, 101, 178, 317).
- Caveat: outside that range the definitions degenerate. `λ = 0` gives division by `log 1 = 0`, so `J = 0`;
  `−1 ≤ λ < 0` gives `J = 0`; `η ≥ 1/2` gives `J = 0`; `λ < −2` gives `J > 0` again because `Real.log` is even.

### `H4Block`, `roughUnits`, `delta`, `blockCount`, `primesIn` — FAITHFUL (*computed*)

- `Σ_{c unit} δ_j(c) = 0` to rounding (≤ 2·10⁻¹¹) in every computed block, so `ρ·ι_j` is the exact mean of `π_j`.
- `a` does not occur. An empty block (`ι_j = 0`) gives `0 ≤ 0`, which holds; it does not make H4 false.
- `roughUnits m ⌈M_j⌉` uses `k·⌈M_j⌉ ≤ m` where the note has `k ≤ m/M_j`. The Lean set is a subset, so the Lean H4 is a
  slightly stronger hypothesis per block than the note's, and the Lean theorem is correspondingly slightly weaker.
  GapH4.lean says this in its "Rounding" section.

### `H4` — FAITHFUL WITH CAVEAT

- **Trivially true outside the intended range** (*Lean*, `scratch_referee/Degenerate.lean`): `H4 η 0` and `H4 (1/2) λ`
  are provable in two lines, because `numBlocks = 0`. `eos_of_H4` excludes these by `0 < η ≤ η₀ ≤ 1/4` and `0 < λ`, so
  no false theorem results. Proposed fix (cosmetic): add `0 < η ∧ η < 1/2 ∧ 0 < lam ∧` to the definition of `H4`, or say
  in the docstring that the definition is meaningful only in that range.
- **Not vacuously false for a structural reason I could find** (*heuristic*). The conjugate obstruction of Prop Q′
  (many `c` with `π_j(c) = 0` forced) has no analogue here: for fixed `c` and `p ∈ I_j`, `c p̄ mod m` is a unit with no
  forced compositeness, and the mean is exactly `ρ ι_j`. On the Gaussian model the fourth moment is `≈ 3φ(ρι_j)²`, and
  H4 then needs `λ² M_j ≳ (log m)⁵/η⁴`, true for large `m` in every block including the top one.
- **Fails at every computable `m`** (*computed*, agrees with the note §7.1): ratios `Σδ⁴ / RHS` are 2.7·10⁶–1.1·10⁷ at
  `m = 100003`, `η = 1/4`, `λ = 1`; 4·10³–10⁴ at `m = 30030`; 10⁵–3·10⁵ at `m = 99990`, `η = 0.2`, `λ = 0.5`. With the
  theorem's `η ≤ η₀` and `λ ≤ η/(10000 C²)` the threshold `m₀` is astronomically large. H4 is an asymptotic statement
  with no numerical support in either direction.
- `∃ m₀` is a natural number and `[NeZero m]` is bound after `m₀ ≤ m`; both are fine.

### How `eos_of_H4` uses H4 (*read the proof*)

`η₀ = min(η_T, η_R, 1/4)`, `κ = 1/(10000 C²)`, `C = max(C₀, 1)`. For `m ≥ N`: `lemmaC'_of_H4Block` is applied with
`M = blockPt m η λ`, `J = numBlocks m η λ`, `z = ⌈m^η⌉`, with side conditions `M 0 ≤ z`, `m ≤ (M J)²`, `z² ≤ m`, and H4
supplies `H4Block` for every `j < J`. The certificate is then bounded below by `ρ·0.48·π(m) − 1 > 0` using
`TypeISifted` at `ε = 1/100`, `lemma22_comb`, `defect_le` (sieve bound only), `RoughMertens` at `ε = 1/100`,
`buchstab_identity`, and Chebyshev from Mathlib. If `J` were 0 the side condition `m ≤ (M J)²` would read
`m ≤ ⌈m^η⌉²`, which is false; so the proof cannot go through with no blocks, as it should not.

The statement is existential in `η₀` and `κ`. That is honest, but it means the theorem does not name a specific pair
`(η, λ)` for which H4 suffices.

## 5. Conclusions

| Definition / theorem | Verdict | Remarks |
|---|---|---|
| `CoveredBy m Y` | FAITHFUL | Both factors must be `Nat.Prime`; `p = q = 1` is not allowed (`¬ CoveredBy 1 1` proved in scratch). The product is cast from ℕ to `ZMod m`. |
| `Conjecture` | FAITHFUL | `∃ m₀ : ℕ, ∀ m ≥ m₀, CoveredBy m m`. `p ≤ m` is equivalent to `p < m` for `m ≥ 2`: a factor `p = m` gives the residue 0, not a unit (proved in scratch). Primes dividing `m` are excluded automatically for the same reason. |
| `CoveredByAsym m Y₁ Y₂` | FAITHFUL | Same with separate bounds. |
| `coveredBy_of_grhBounds` | FAITHFUL | `∃ K m₀ : ℝ, 0 < K ∧ ∀ m : ℕ, m ≥ m₀ → CoveredBy m (K m log⁴ m)`. |
| `coveredBy_log_sq` | FAITHFUL | Same with `log² m`; `m₀ ≥ 2⁸⁰` in the proof. |
| `coveredByAsym_m_log_cube` | FAITHFUL | `p ≤ m`, `q ≤ K m log³ m`. |
| `coveredBy_three_primes` | FAITHFUL | `p, q, s` all prime, `p, q ≤ m` in ℕ, `s ≤ K (log m)² (log log m)²` in ℝ, product `p q s ≡ a`. `m₀` is at least `exp(exp 61)`, so `log log m` is positive where it is used. |
| `eos_of_H4` | FAITHFUL | Signature `TypeISifted → RoughCounts → ∃ η₀ > 0, ∃ κ > 0, ∀ η ∈ (0, η₀], ∀ λ ∈ (0, κη], H4 η λ → Conjecture`. No GRH. This differs from the shape in CLAUDE.md (`(hH : H4 η λ) : Conjecture`) in the way the note §6 recommends. |

`K` and `m₀` are existential in all four GRH-conditional theorems. The proofs give explicit values in terms of the GRH
constant `C`, but the statements do not expose them.

## 6. Minor documentation issues (no mathematical effect)

1. Buchstab.lean, docstring of `H4Block`: "the full hypothesis `H4 η` also fixes the block system (`λ = η/(4C₁)`, blocks
   in `[m^η, (1+λ)√m]`)". The actual `H4 η λ` has two parameters and blocks tiling `[m^η, √m)`. Stale.
2. Buchstab.lean, docstring of `lemmaC'_of_H4Block`: "The remaining steps of Cor H4 … are asymptotic and not
   formalized." They are now formalized in GapH4.lean. Stale.
3. `notes/routes/E-buchstab-H4.md` §6 gives `TypeISifted` in the `C₆ e^{−1/(17η)}` form and `RoughCounts` with three
   parts; the Lean versions are the ε-form and two parts. Both Lean versions are weaker, so nothing is lost, but §6
   should point to the Lean text.
4. `EOS/README.md` is the unedited project template.

## 7. Not checked

- Fouvry–Shparlinski Thm 3.1 itself and Shparlinski 2013 Lemma 2 (the proof behind Lemma 5.4 of 1705.06087).
- The fundamental lemma and Buchstab–de Bruijn statements against the books (all [RECALLED]).
- Any asymptotic statement at the sizes where it is claimed to hold.
- The internal lemmas of LogFour, LogSquare, ThreePrimes beyond their statements; Lean has checked them.
