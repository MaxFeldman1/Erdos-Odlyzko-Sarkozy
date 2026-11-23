import EOS.Buchstab

/-!
# The gap theorem: `TypeISifted + RoughCounts + H4 ⇒ EOS`

This file proves `EOS.eos_of_H4` (Theorem E and Corollary H4 of `notes/routes/E-buchstab-H4.md`):

  `TypeISifted → RoughCounts →`
  `  ∃ η₀ > 0, ∃ κ > 0, ∀ η ∈ (0, η₀], ∀ λ ∈ (0, κη], H4 η λ → Conjecture`.

There is **no `sorry`** in this file, and **GRH is not a hypothesis**.

* `TypeISifted` and `RoughCounts` (= `SieveUpperBound ∧ RoughMertens`) are named `Prop`s for
  **unconditional, published** theorems; each docstring gives the citation and the reason the
  Lean statement follows from it. Chebyshev's lower bound `π(n) ≥ n log 2 / log n`
  (`Chebyshev.pi_ge_of_four_le`) and `γ > 1/2` (`Real.one_half_lt_eulerMascheroniConstant`) are
  taken from Mathlib, not assumed. The prime number theorem is not used.
* `H4 η λ` is the single hypothesis beyond the known theorems. **H4 is stronger than EOS, it is
  not known to follow from GRH, and GRH is not a hypothesis of `eos_of_H4`.** The theorem
  isolates the gap; it does not close it.

## Proof outline
1. `lemmaC'_of_H4Block` (Buchstab.lean, exact): under H4 it suffices that
   `S(A_a, z) − 1 − (1 + η/2) ρ Σ_j ι_j |𝒦_j| > 0`, `z = ⌈m^η⌉`.
2. `GapH4.lemma22_comb` (exact): `Σ_j ι_j |𝒦_j| ≤ B₀ + Σ_j ι_j (X_j + Y_j)`, where
   `B₀ = bilinear m z {units ≤ m}` and, by `buchstab_identity`, `B₀ = Φ_m(m, z) − 1 − P_≥`.
3. `GapH4.defect_le` (from `SieveUpperBound` only):
   `Σ_j ι_j (X_j + Y_j) ≤ (m / log m) (32 C²/(η² log m) + 96 C² λ/η)`.
4. `TypeISifted` bounds `S(A_a, z)` below by `ρ((1 − η/100) Φ_m − π(m)/100)`, `RoughMertens`
   bounds `η Φ_m ≤ (e^{−γ} + 1/100) π(m) ≤ 0.677 π(m)`, and `P_≥ ≥ π(m) − √m − 2`; the
   certificate is then `≥ ρ · 0.48 π(m) − 1 > 0` (`π(m)² ≥ 3m`).

## Deviation from the paper proof of Lemma 2.2
Step 3 replaces the multiplicative bound `(1 + C₁λ) B₀ + C₅ log(2/λ) m/L²` of the note by an
additive one of the same size (`B₀ ≍ m/(η L)`), with the cut-off defect
`X_j = #{m/M_{j+1} < k ≤ m/M_j : P⁻(k) ≥ M_j}` bounded by the sieve on an interval of length
`max(m/M_j − m/M_{j+1}, M_j)` and the roughness defect
`Y_j = #{k ≤ m/M_j : M_j ≤ P⁻(k) < M_{j+1}}` bounded by counting multiples. This needs no
lower bound for rough numbers (D-RNL), no bulk/top split, and no PNT.

## Rounding
The paper's real block points `M_j = m^{η + j(1/2−η)/J}` are rounded up: `blockPt m η λ j = ⌈M_j⌉`.
Since primes are integers, `I_j = [⌈M_j⌉, ⌈M_{j+1}⌉)` is exactly the paper's block. The paper's
`𝒦_j = {k ≤ m/M_j}` becomes `roughUnits m ⌈M_j⌉ = {k · ⌈M_j⌉ ≤ m}` (a subset, smaller by
`O(|𝒦_j|/M_j)`), so `H4` here is the paper's H4 up to this negligible change in `|𝒦_j|`.
-/

open scoped BigOperators
open Finset Real

namespace EOS

open EOS.Buchstab

/-- `S(A, y) = #{n ∈ A : n = 1 or P⁻(n) ≥ y}` for a real threshold `y`, with
`P⁻(n) = Nat.minFac n` (so `P⁻(1) = ∞` is encoded by the clause `n = 1`). -/
noncomputable def siftedR (y : ℝ) (A : Finset ℕ) : ℕ :=
  #{n ∈ A | n = 1 ∨ y ≤ (n.minFac : ℝ)}

/-- `Φ(x, y) = #{1 ≤ n ≤ x : n = 1 or P⁻(n) ≥ y}` (the count of `y`-rough numbers, `1` included). -/
noncomputable def Phi (x : ℕ) (y : ℝ) : ℕ := siftedR y (Icc 1 x)

/-- `Φ_m(x, y) = #{1 ≤ n ≤ x : (n, m) = 1, n = 1 or P⁻(n) ≥ y}`. -/
noncomputable def PhiCop (m x : ℕ) (y : ℝ) : ℕ :=
  siftedR y ((Icc 1 x).filter (fun n => n.Coprime m))

/-- **Unconditional input: Type I information for `A_a` plus the fundamental lemma**
(Lemma 2.1 of `notes/routes/E-buchstab-H4.md`, there called `TypeISifted`).

Statement: for every `ε > 0` there is `η₁ > 0` such that for every `η ∈ (0, η₁]` there is `m₁`
such that for all `m ≥ m₁` and every unit `a` mod `m`,
  `S(A_a, m^η) ≥ ρ · ((1 − εη) · Φ_m(m, m^η) − ε · π(m))`,
where `A_a = {a p̄ mod m : p ≤ m prime, p ∤ m}` (`Aset m a`), `ρ = |P|/φ(m)` (`rho m`).

Sources. (i) Type I bound, uniform in `a`: for `1 ≤ d ≤ m`, `(d, m) = 1`,
`|#{n ∈ A_a : d ∣ n} − |P|/d| ≤ m^{15/16+ε}` for `m ≥ m(ε)`. Counting `n ∈ A_a` with `d ∣ n` is
counting primes `p ≤ m` with `(a d̄) p̄ mod m` in an interval of length `m/d`, which is controlled
by the Kloosterman-type sums over primes `Σ_{p ≤ x} e_m(b p̄)` of Fouvry–Shparlinski, *On a ternary
quadratic form over primes*, Acta Arith. 150 (2011), Thm 3.1 (arbitrary modulus); the interval
version is Shparlinski, arXiv:1705.06087, Lemma 5.4 and §7. (ii) The fundamental lemma of the
sieve in dimension 1 (Friedlander–Iwaniec, *Opera de Cribro*, Cor. 6.10; Iwaniec–Kowalski,
*Analytic Number Theory*, Lemma 6.3; Halberstam–Richert, *Sieve Methods*, Thm 2.5; theorem
numbers recalled, not re-read). Applying (ii) at level `D = m^{1/17}` to `A_a` (remainders from
(i)) and to `{n ≤ m : (n, m) = 1}` and eliminating `Π_{p < z, p ∤ m}(1 − 1/p)` gives Lemma 2.1:
`S(A_a, m^η) ≥ ρ Φ_m(m, m^η)(1 − C₆ e^{−1/(17η)}) − m^{1 − 1/300}` for `η ≤ η₁`, `m ≥ m₃(η)`.

Why the Lean statement follows: `C₆ e^{−1/(17η)} ≤ εη` once `η` is small, and
`m^{1−1/300} ≤ ε ρ π(m)` once `m` is large, because `ρ π(m) ≥ (π(m) − log₂ m) π(m)/m ≫ m/log² m`.
So this is a weakening of Lemma 2.1. The proof of `eos_of_H4` uses it only with `ε = 1/100`. -/
def TypeISifted : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ → ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
    ∀ a : ZMod m, IsUnit a →
      rho m * ((1 - ε * η) * (PhiCop m m ((m : ℝ) ^ η) : ℝ) - ε * (Nat.primeCounting m : ℝ)) ≤
        (siftedR ((m : ℝ) ^ η) (Aset m a) : ℝ)

/-- **Unconditional input: the sieve upper bound for rough numbers in intervals** (D-BT of
`notes/routes/E-buchstab-H4.md`).

Statement: there is an absolute `C > 0` such that for all integers `a, H ≥ 0` and real
`2 ≤ y ≤ H`, `#{a < n ≤ a + H : n = 1 or P⁻(n) ≥ y} ≤ C H / log y`.

Sources: any upper-bound sieve of dimension 1 (Brun, Selberg, or the large sieve). E.g.
Montgomery's large sieve inequality (Montgomery, *Topics in Multiplicative Number Theory*,
LNM 227 (1971); Montgomery–Vaughan, *Multiplicative Number Theory I*, §3 (Selberg sieve, whose
Thm 3.3 is the Brun–Titchmarsh case); Halberstam–Richert, *Sieve Methods*, Ch. 3; numbering
recalled, not re-read).

Why the Lean statement follows: sift `(a, a + H]` by the primes `p < Q`, `Q = min(y, √H) ≥ √y`.
The large sieve gives the bound `(H + Q²)/Σ_{q ≤ Q} μ²(q)/φ(q) ≤ 2H/log Q ≤ 4H/log y` (the
sifted set contains every `n` with `n = 1` or `P⁻(n) ≥ y`); for `y` below an absolute constant
the trivial bound `H` suffices. -/
def SieveUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (a H : ℕ) (y : ℝ), 2 ≤ y → y ≤ (H : ℝ) →
    (#{n ∈ Ioc a (a + H) | n = 1 ∨ y ≤ (n.minFac : ℝ)} : ℝ) ≤ C * H / Real.log y

/-- **Unconditional input: rough numbers up to `m` with the Mertens constant** (D-RNA′ of
`notes/routes/E-buchstab-H4.md` §6).

Statement: for every `ε > 0` there is `η₁ > 0` such that for every `η ∈ (0, η₁]` there is `m₁`
with `η · Φ(m, m^η) ≤ (e^{−γ} + ε) · π(m)` for all `m ≥ m₁` (`γ` = Euler's constant).

Sources: Buchstab (1937) and de Bruijn (1950): for fixed `u > 1`,
`Φ(x, x^{1/u}) = (u ω(u) + o(1)) x / log x`, where `ω` is Buchstab's function, and
`ω(u) → e^{−γ}` as `u → ∞` (Tenenbaum, *Introduction to Analytic and Probabilistic Number
Theory*, III.6, Thm 6.4 and §6.4 [numbering recalled]); together with the prime number theorem
`π(x) ∼ x/log x` (Montgomery–Vaughan Thm 6.9). Alternatively (D-RNA of the note): the
fundamental lemma at level `√m` with Mertens' formula `Π_{p<z}(1 − 1/p) ∼ e^{−γ}/log z`
(Mertens 1874; Montgomery–Vaughan Thm 2.7), plus the PNT.

Why the Lean statement follows: `η Φ(m, m^η) = (ω(1/η) + o(1)) m/log m = (ω(1/η) + o(1)) π(m)`
as `m → ∞`, and `ω(1/η) ≤ e^{−γ} + ε/2` for `η` small. The proof of `eos_of_H4` uses it only with
`ε = 1/100`, and only through `e^{−γ} + 1/100 < 0.68` (from Mathlib's `γ > 1/2`). -/
def RoughMertens : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ → ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
    η * (Phi m ((m : ℝ) ^ η) : ℝ) ≤
      (Real.exp (-Real.eulerMascheroniConstant) + ε) * (Nat.primeCounting m : ℝ)

/-- **Unconditional input: rough-number counts.** The conjunction of `SieveUpperBound` (the
sieve upper bound in intervals) and `RoughMertens` (Buchstab–de Bruijn with `e^{−γ}`, plus the
PNT). Both are published, unconditional theorems; see their docstrings for citations. -/
def RoughCounts : Prop := SieveUpperBound ∧ RoughMertens

/-- The number of blocks of `𝔅(m, η, λ)`: `J = ⌈(1/2 − η) log m / log(1 + λ)⌉`. -/
noncomputable def numBlocks (m : ℕ) (η lam : ℝ) : ℕ :=
  ⌈(1 / 2 - η) * Real.log m / Real.log (1 + lam)⌉₊

/-- The block points of `𝔅(m, η, λ)`, rounded up: `blockPt m η λ j = ⌈m^{η + j(1/2 − η)/J}⌉`
`= ⌈z (1 + λ_m)^j⌉` with `z = m^η`, `1 + λ_m = exp((1/2 − η) log m / J) ≤ 1 + λ`. So
`blockPt 0 = ⌈m^η⌉` and `blockPt J = ⌈√m⌉`; the blocks `[blockPt j, blockPt (j+1))`, `j < J`,
tile `[m^η, √m)` exactly. -/
noncomputable def blockPt (m : ℕ) (η lam : ℝ) (j : ℕ) : ℕ :=
  ⌈(m : ℝ) ^ (η + (1 / 2 - η) * j / numBlocks m η lam)⌉₊

/-- **The gap hypothesis H4(η, λ). This is NOT a known theorem.**

Statement: there is `m₀` such that for every `m ≥ m₀` and every block `j < J` of the block
system `𝔅(m, η, λ)` of `notes/routes/E-buchstab-H4.md` §1 (blocks `I_j = [M_j, M_{j+1})` tiling
`[m^η, √m)`, see `numBlocks`, `blockPt`), the fourth-moment bound `H4Block` holds:
  `Σ_{c ∈ (ℤ/mℤ)ˣ} δ_j(c)⁴ ≤ (η/2)⁴ ρ⁴ ι_j⁴ |𝒦_j|`,
where `ι_j = #{p ∈ I_j prime, p ∤ m}`, `π_j(c) = #{p ∈ I_j prime, p ∤ m : c p̄ ∈ P}`,
`δ_j(c) = π_j(c) − ρ ι_j`, and `𝒦_j = roughUnits m M_j`.

**H4 is stronger than EOS**: together with the unconditional inputs it implies the conjecture
(`eos_of_H4`; the paper proof even gives `N(a) ≥ 0.4 μ` for every unit `a`). **H4 is not known
to follow from GRH**, and **GRH is not a hypothesis** of `eos_of_H4`. H4 isolates the gap of the
Buchstab route; it does not close it. It must be stated for this specific block system: for
blocks containing only a few primes it is false. Its analogue for `P⁻¹` in place of `P` fails for
every large `m` (Proposition Q′ of the note).

*Degenerate parameters.* Outside `0 < η < 1/2`, `0 < λ`, the block system is empty (`numBlocks = 0`) and
`H4 η λ` holds trivially (e.g. `H4 η 0`, `H4 (1/2) λ`). This is harmless: `eos_of_H4` only uses H4 for
`0 < η ≤ η₀ ≤ 1/4` and `0 < λ ≤ κη`, where `numBlocks ≥ 1` and the blocks tile `[⌈m^η⌉, ⌈√m⌉)`
(see `notes/lean-referee.md`, caveat 1). -/
def H4 (η lam : ℝ) : Prop :=
  ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ [NeZero m], ∀ j < numBlocks m η lam,
    H4Block m (Ico (blockPt m η lam j) (blockPt m η lam (j + 1))) (blockPt m η lam j) η

namespace GapH4

/-! ### Part 1: the combinatorial form of Lemma 2.2 -/

/-- The units `1 ≤ n ≤ m`, `(n, m) = 1` (for `m ≥ 2` these lie in `[1, m)`). -/
def unitsLe (m : ℕ) : Finset ℕ := (Icc 1 m).filter (fun n => n.Coprime m)

/-- The summand of `bilinear m z (unitsLe m)` at the prime `p`. -/
def bilTerm (m p : ℕ) : ℕ := #{n ∈ unitsLe m | p ∣ n ∧ (n / p = 1 ∨ p ≤ (n / p).minFac)}

/-- `X = #{m/M' < k ≤ m/M : k = 1 ∨ P⁻(k) ≥ M}` (the cut-off defect of a block). -/
def Xcount (m M M' : ℕ) : ℕ := #{k ∈ Ioc (m / M') (m / M) | k = 1 ∨ M ≤ k.minFac}

/-- `Y = #{1 ≤ k ≤ m/M : k ≠ 1, M ≤ P⁻(k) < M'}` (the roughness defect of a block). -/
def Ycount (m M M' : ℕ) : ℕ := #{k ∈ Ioc 0 (m / M) | k ≠ 1 ∧ M ≤ k.minFac ∧ k.minFac < M'}

lemma roughUnits_card_le {m M M' p : ℕ} (hM : 0 < M) (hMp : M ≤ p) (hpM' : p < M')
    (hp : p.Prime) (hpm : ¬ p ∣ m) :
    #(roughUnits m M) ≤ bilTerm m p + Xcount m M M' + Ycount m M M' := by
  classical
  set A := (roughUnits m M).filter (fun k => k * p < m ∧ (k = 1 ∨ p ≤ k.minFac)) with hAdef
  have hsub : roughUnits m M ⊆ A ∪ (Ioc (m / M') (m / M)).filter (fun k => k = 1 ∨ M ≤ k.minFac)
      ∪ (Ioc 0 (m / M)).filter (fun k => k ≠ 1 ∧ M ≤ k.minFac ∧ k.minFac < M') := by
    intro k hk
    have hk' := hk
    simp only [roughUnits, mem_filter, mem_range] at hk'
    obtain ⟨-, hk0, -, hkM, hkr⟩ := hk'
    simp only [mem_union, mem_filter, mem_Ioc, hAdef]
    by_cases h1 : k * p < m
    · by_cases h2 : k = 1 ∨ p ≤ k.minFac
      · exact Or.inl (Or.inl ⟨hk, h1, h2⟩)
      · right
        push Not at h2
        have hkr' : M ≤ k.minFac := hkr.resolve_left h2.1
        exact ⟨⟨hk0, (Nat.le_div_iff_mul_le hM).2 hkM⟩, h2.1, hkr', by omega⟩
    · left; right
      refine ⟨⟨?_, (Nat.le_div_iff_mul_le hM).2 hkM⟩, hkr⟩
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      push Not at h1
      nlinarith
  have hA : #A ≤ bilTerm m p := by
    unfold bilTerm
    refine card_le_card_of_injOn (fun k => k * p) ?_ ?_
    · intro k hk
      simp only [Finset.mem_coe, hAdef, roughUnits, mem_filter, mem_range] at hk
      obtain ⟨⟨-, hk0, hkc, -, -⟩, h1, h2⟩ := hk
      simp only [Finset.mem_coe, unitsLe, mem_filter, mem_Icc]
      refine ⟨⟨⟨?_, h1.le⟩,
        Nat.coprime_mul_iff_left.2 ⟨hkc, (Nat.Prime.coprime_iff_not_dvd hp).2 hpm⟩⟩,
        dvd_mul_left _ _, ?_⟩
      · nlinarith [hp.pos]
      · rw [Nat.mul_div_cancel _ hp.pos]; exact h2
    · intro k₁ _ k₂ _ h
      exact Nat.eq_of_mul_eq_mul_right hp.pos h
  calc #(roughUnits m M) ≤ #(A ∪ (Ioc (m / M') (m / M)).filter (fun k => k = 1 ∨ M ≤ k.minFac)
      ∪ (Ioc 0 (m / M)).filter (fun k => k ≠ 1 ∧ M ≤ k.minFac ∧ k.minFac < M')) :=
        card_le_card hsub
    _ ≤ #(A ∪ (Ioc (m / M') (m / M)).filter (fun k => k = 1 ∨ M ≤ k.minFac))
      + #((Ioc 0 (m / M)).filter (fun k => k ≠ 1 ∧ M ≤ k.minFac ∧ k.minFac < M')) :=
        card_union_le _ _
    _ ≤ #A + #((Ioc (m / M') (m / M)).filter (fun k => k = 1 ∨ M ≤ k.minFac))
      + #((Ioc 0 (m / M)).filter (fun k => k ≠ 1 ∧ M ≤ k.minFac ∧ k.minFac < M')) := by
        gcongr; exact card_union_le _ _
    _ ≤ _ := by unfold Xcount Ycount; gcongr

lemma sum_blocks_eq (M : ℕ → ℕ) (hM : Monotone M) (g : ℕ → ℕ) (J : ℕ) :
    ∑ j ∈ range J, ∑ p ∈ Ico (M j) (M (j + 1)), g p = ∑ p ∈ Ico (M 0) (M J), g p := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, ih, sum_Ico_consecutive _ (hM (Nat.zero_le _)) (hM (Nat.le_succ _))]

/-- **Lemma 2.2, combinatorial part (exact, no asymptotics).** For monotone boundaries with
`M 0 = z > 0` whose top `M J` satisfies `p < M J ⇒ p² < m`:
`Σ_j ι_j |𝒦_j| ≤ B₀ + Σ_j ι_j (X_j + Y_j)`, where `B₀ = bilinear m z (unitsLe m)`. -/
theorem lemma22_comb {m z J : ℕ} (M : ℕ → ℕ) (hM : Monotone M) (hM0 : M 0 = z) (hpos : 0 < M 0)
    (htop : ∀ p, p < M J → p * p < m) :
    ∑ j ∈ range J, primesIn m (Ico (M j) (M (j + 1))) * #(roughUnits m (M j)) ≤
      bilinear m z (unitsLe m) + ∑ j ∈ range J, primesIn m (Ico (M j) (M (j + 1))) *
        (Xcount m (M j) (M (j + 1)) + Ycount m (M j) (M (j + 1))) := by
  classical
  have hblock : ∀ j, primesIn m (Ico (M j) (M (j + 1))) * #(roughUnits m (M j)) ≤
      ∑ p ∈ Ico (M j) (M (j + 1)), (if p.Prime ∧ ¬ p ∣ m then bilTerm m p else 0) +
        primesIn m (Ico (M j) (M (j + 1))) *
          (Xcount m (M j) (M (j + 1)) + Ycount m (M j) (M (j + 1))) := by
    intro j
    rw [← sum_filter, primesIn, ← smul_eq_mul, ← sum_const, ← smul_eq_mul, ← sum_const,
      ← sum_add_distrib]
    refine sum_le_sum fun p hp => ?_
    simp only [mem_filter, mem_Ico] at hp
    have hMj : 0 < M j := lt_of_lt_of_le hpos (hM (Nat.zero_le _))
    have := roughUnits_card_le (m := m) hMj hp.1.1 hp.1.2 hp.2.1 hp.2.2
    omega
  calc _ ≤ ∑ j ∈ range J, (∑ p ∈ Ico (M j) (M (j + 1)),
        (if p.Prime ∧ ¬ p ∣ m then bilTerm m p else 0) +
        primesIn m (Ico (M j) (M (j + 1))) *
          (Xcount m (M j) (M (j + 1)) + Ycount m (M j) (M (j + 1)))) :=
        sum_le_sum fun j _ => hblock j
    _ = ∑ p ∈ Ico (M 0) (M J), (if p.Prime ∧ ¬ p ∣ m then bilTerm m p else 0) +
        ∑ j ∈ range J, primesIn m (Ico (M j) (M (j + 1))) *
          (Xcount m (M j) (M (j + 1)) + Ycount m (M j) (M (j + 1))) := by
        rw [sum_add_distrib, sum_blocks_eq M hM]
    _ ≤ _ := by
        gcongr
        rw [← sum_filter]
        unfold bilinear
        refine sum_le_sum_of_subset fun p hp => ?_
        simp only [mem_filter, mem_Ico, mem_range] at hp ⊢
        have h2 := htop p hp.1.2
        refine ⟨?_, hp.2.1, hM0 ▸ hp.1.1, h2⟩
        nlinarith [hp.2.1.two_le]

/-! ### Part 2: consequences of the sieve upper bound -/

section Sieve

variable {C : ℝ} (hC : ∀ (a H : ℕ) (y : ℝ), 2 ≤ y → y ≤ (H : ℝ) →
    (#{n ∈ Ioc a (a + H) | n = 1 ∨ y ≤ (n.minFac : ℝ)} : ℝ) ≤ C * H / Real.log y)
include hC

lemma sieve_mono (a b H : ℕ) (y : ℝ) (hy : 2 ≤ y) (hyH : y ≤ H) (hb : b ≤ a + H) :
    (#{n ∈ Ioc a b | n = 1 ∨ y ≤ (n.minFac : ℝ)} : ℝ) ≤ C * H / Real.log y :=
  le_trans (by exact_mod_cast card_le_card (filter_subset_filter _ (Ioc_subset_Ioc_right hb)))
    (hC a H y hy hyH)

lemma primes_Ico_le (M M' : ℕ) (hM : 1 ≤ M) (hMM : M ≤ M') (y : ℝ) (hy : 2 ≤ y)
    (hyM : y ≤ M) (hyH : y ≤ ((M' - M : ℕ) : ℝ)) :
    (#{p ∈ Ico M M' | p.Prime} : ℝ) ≤ C * ((M' - M : ℕ) : ℝ) / Real.log y := by
  refine le_trans ?_ (sieve_mono hC (M - 1) (M' - 1) (M' - M) y hy hyH (by omega))
  exact_mod_cast card_le_card (fun p hp => by
    simp only [mem_filter, mem_Ico, mem_Ioc] at hp ⊢
    refine ⟨⟨by omega, by omega⟩, Or.inr ?_⟩
    rw [hp.2.minFac_eq]; exact hyM.trans (by exact_mod_cast hp.1.1))

lemma Xcount_le (m M M' : ℕ) (hM : 2 ≤ M) :
    (Xcount m M M' : ℝ) ≤ C * (((m / M - m / M' : ℕ) : ℝ) + M) / Real.log M := by
  have hH := sieve_mono hC (m / M') (m / M) (max (m / M - m / M') M) (M : ℝ)
    (by exact_mod_cast hM) (by exact_mod_cast le_max_right _ _) (by omega)
  have hX : Xcount m M M' = #{n ∈ Ioc (m / M') (m / M) | n = 1 ∨ (M : ℝ) ≤ (n.minFac : ℝ)} := by
    unfold Xcount
    congr 1
    refine filter_congr fun n _ => ?_
    rw [Nat.cast_le]
  rw [hX]
  refine hH.trans ?_
  have hlog : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hC0 : 0 ≤ C := by
    have := hC 0 2 2 le_rfl (by norm_num)
    have h0 : (0 : ℝ) ≤ #{n ∈ Ioc 0 (0 + 2) | n = 1 ∨ (2 : ℝ) ≤ (n.minFac : ℝ)} := Nat.cast_nonneg _
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    by_contra hneg
    push Not at hneg
    have : C * ((2 : ℕ) : ℝ) / Real.log 2 < 0 := by
      apply div_neg_of_neg_of_pos _ hl; push_cast; linarith
    have h1 : (1 : ℝ) ≤ #{n ∈ Ioc 0 (0 + 2) | n = 1 ∨ (2 : ℝ) ≤ (n.minFac : ℝ)} := by
      have : 1 ∈ (Ioc 0 (0 + 2)).filter (fun n => n = 1 ∨ (2 : ℝ) ≤ (n.minFac : ℝ)) := by simp
      exact_mod_cast card_pos.2 ⟨1, this⟩
    linarith
  gcongr
  have := max_le_add_of_nonneg (Nat.zero_le (m / M - m / M')) (Nat.zero_le M)
  exact_mod_cast this

end Sieve

lemma Ycount_le (m M M' : ℕ) (hM : 1 ≤ M) :
    Ycount m M M' ≤ #{p ∈ Ico M M' | p.Prime} * (m / M / M) := by
  classical
  unfold Ycount
  calc _ ≤ #(((Ico M M').filter Nat.Prime).biUnion
          (fun p => (Ioc 0 (m / M)).filter (fun k => p ∣ k))) := card_le_card ?_
    _ ≤ ∑ p ∈ (Ico M M').filter Nat.Prime, #((Ioc 0 (m / M)).filter (fun k => p ∣ k)) :=
        card_biUnion_le
    _ ≤ ∑ p ∈ (Ico M M').filter Nat.Prime, (m / M / M) := sum_le_sum fun p hp => by
        rw [Nat.Ioc_filter_dvd_card_eq_div]
        exact Nat.div_le_div_left (mem_Ico.1 (mem_filter.1 hp).1).1 (by omega)
    _ = _ := by rw [sum_const, smul_eq_mul]
  intro k hk
  simp only [mem_filter, mem_Ioc] at hk
  simp only [mem_biUnion, mem_filter, mem_Ico, mem_Ioc]
  exact ⟨k.minFac, ⟨⟨hk.2.2.1, hk.2.2.2⟩, Nat.minFac_prime hk.2.1⟩, hk.1, Nat.minFac_dvd k⟩

/-! ### Part 3: two telescoping sums -/

lemma sum_inv_sq_le (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) (J : ℕ) :
    ∑ j ∈ range J, 1 / (η + j * δ) ^ 2 ≤ 1 / η ^ 2 + 1 / (δ * η) := by
  have key : ∀ J : ℕ, ∑ j ∈ range (J + 1), 1 / (η + j * δ) ^ 2 + 1 / (δ * (η + J * δ)) ≤
      1 / η ^ 2 + 1 / (δ * η) := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [sum_range_succ]
      have ha : 0 < η + J * δ := by positivity
      have hb : 0 < η + ((J + 1 : ℕ) : ℝ) * δ := by positivity
      have hab : η + ((J + 1 : ℕ) : ℝ) * δ = (η + J * δ) + δ := by push_cast; ring
      have : 1 / (η + ((J + 1 : ℕ) : ℝ) * δ) ^ 2 + 1 / (δ * (η + ((J + 1 : ℕ) : ℝ) * δ)) ≤
          1 / (δ * (η + J * δ)) := by
        rw [hab]
        set a := η + J * δ
        rw [div_add_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg hδ.le ha.le) (sq_nonneg δ),
          mul_pos hδ ha, mul_pos (mul_pos hδ ha) hδ]
      linarith
  rcases J with _ | J
  · simp only [range_zero, sum_empty]; positivity
  · have := key J
    have : 0 ≤ 1 / (δ * (η + J * δ)) := by positivity
    linarith

lemma sum_diff_mul_le (M : ℕ → ℝ) (J : ℕ) :
    ∑ j ∈ range J, (M (j + 1) - M j) * M j ≤ (M J) ^ 2 / 2 := by
  have h : ∀ j, (M (j + 1) - M j) * M j ≤ (M (j + 1)) ^ 2 / 2 - (M j) ^ 2 / 2 := fun j => by
    nlinarith [sq_nonneg (M (j + 1) - M j)]
  calc _ ≤ ∑ j ∈ range J, ((M (j + 1)) ^ 2 / 2 - (M j) ^ 2 / 2) := sum_le_sum fun j _ => h j
    _ = (M J) ^ 2 / 2 - (M 0) ^ 2 / 2 := sum_range_sub (fun j => (M j) ^ 2 / 2) J
    _ ≤ _ := by linarith [sq_nonneg (M 0)]


/-! ### Part 4: the per-block estimate and the block system -/

lemma block_term_le {C lam ℓ m ι ι' X Y M M' : ℝ} (hC : 0 ≤ C) (hℓ : 0 < ℓ) (hm : 0 ≤ m)
    (hM : 1 ≤ M) (hMM : M ≤ M') (hι : 0 ≤ ι) (hιι : ι ≤ ι')
    (hι' : ι' ≤ 2 * C * (M' - M) / ℓ)
    (hX0 : 0 ≤ X) (hX : X ≤ C * (m * (M' - M) / M ^ 2 + 1 + M) / ℓ)
    (hY0 : 0 ≤ Y) (hY : Y ≤ ι' * (m / M ^ 2)) (hΔ : M' - M ≤ 2 * lam * M) :
    ι * (X + Y) ≤ (24 * C ^ 2 * lam ^ 2 * m + 4 * C ^ 2 * (M' - M) * M) / ℓ ^ 2 := by
  set Δ := M' - M with hΔdef
  have hΔ0 : 0 ≤ Δ := by linarith
  have hι'0 : 0 ≤ ι' := hι.trans hιι
  have hM0 : 0 < M := by linarith
  have hlam : 0 ≤ lam := by
    by_contra h
    push Not at h
    nlinarith
  have hq : Δ ^ 2 ≤ 4 * lam ^ 2 * M ^ 2 := by nlinarith
  have hb0 : 0 ≤ 2 * C * Δ / ℓ := by positivity
  have h1 : ι * (X + Y) ≤ ι' * X + ι' * (ι' * (m / M ^ 2)) := by
    have := mul_le_mul_of_nonneg_right hιι (add_nonneg hX0 hY0)
    have h' := mul_le_mul_of_nonneg_left hY hι'0
    nlinarith
  have h2 : ι' * X ≤ (2 * C * Δ / ℓ) * (C * (m * Δ / M ^ 2 + 1 + M) / ℓ) :=
    mul_le_mul hι' hX hX0 hb0
  have h3 : ι' * (ι' * (m / M ^ 2)) ≤ (2 * C * Δ / ℓ) * ((2 * C * Δ / ℓ) * (m / M ^ 2)) := by
    have hmM : 0 ≤ m / M ^ 2 := by positivity
    exact mul_le_mul hι' (mul_le_mul_of_nonneg_right hι' hmM) (by positivity) hb0
  have hA : m * Δ / M ^ 2 * Δ ≤ 4 * lam ^ 2 * m := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hq hm]
  have h4 : (2 * C * Δ / ℓ) * (C * (m * Δ / M ^ 2 + 1 + M) / ℓ) +
      (2 * C * Δ / ℓ) * ((2 * C * Δ / ℓ) * (m / M ^ 2)) =
      (2 * C ^ 2 * (m * Δ / M ^ 2 * Δ) + 2 * C ^ 2 * Δ * (1 + M) +
        4 * C ^ 2 * (m * Δ / M ^ 2 * Δ)) / ℓ ^ 2 := by
    field_simp
    ring
  have h5 : 2 * C ^ 2 * (m * Δ / M ^ 2 * Δ) + 2 * C ^ 2 * Δ * (1 + M) +
      4 * C ^ 2 * (m * Δ / M ^ 2 * Δ) ≤ 24 * C ^ 2 * lam ^ 2 * m + 4 * C ^ 2 * Δ * M := by
    have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
    have e1 := mul_le_mul_of_nonneg_left hA hC2
    have e2 : C ^ 2 * (Δ * (1 + M)) ≤ C ^ 2 * (2 * Δ * M) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hC2
    nlinarith
  have h6 : (2 * C ^ 2 * (m * Δ / M ^ 2 * Δ) + 2 * C ^ 2 * Δ * (1 + M) +
      4 * C ^ 2 * (m * Δ / M ^ 2 * Δ)) / ℓ ^ 2 ≤
      (24 * C ^ 2 * lam ^ 2 * m + 4 * C ^ 2 * Δ * M) / ℓ ^ 2 :=
    div_le_div_of_nonneg_right h5 (by positivity)
  linarith

section Blocks

set_option linter.unusedSectionVars false

variable {m : ℕ} {η lam : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
  (hm : 2 ≤ m) (hx : 1 ≤ (1 / 2 - η) * Real.log m / Real.log (1 + lam))

/-- `δ = (1/2 − η)/J`, the step of the exponents `θ_j = η + j δ`. -/
noncomputable def step (m : ℕ) (η lam : ℝ) : ℝ := (1 / 2 - η) / numBlocks m η lam

include hlam hlam1 in
lemma log_one_add_ge : lam / 2 ≤ Real.log (1 + lam) := by
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + lam by linarith)
  have h2 : 1 - (1 + lam)⁻¹ = lam / (1 + lam) := by field_simp; ring
  have h3 : lam / 2 ≤ lam / (1 + lam) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  linarith

include hη hη4 hlam hlam1 hm hx

lemma numBlocks_facts :
    1 ≤ numBlocks m η lam ∧ 0 < step m η lam ∧ step m η lam * Real.log m ≤ Real.log (1 + lam) ∧
      lam / 4 ≤ step m η lam * Real.log m := by
  have hl : 0 < Real.log (1 + lam) := Real.log_pos (by linarith)
  have hl2 := log_one_add_ge hlam hlam1
  set x := (1 / 2 - η) * Real.log m / Real.log (1 + lam) with hxdef
  have hJx : x ≤ numBlocks m η lam := Nat.le_ceil x
  have hJx2 : (numBlocks m η lam : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hJ1 : (1 : ℝ) ≤ numBlocks m η lam := hx.trans hJx
  have hJpos : (0 : ℝ) < numBlocks m η lam := by linarith
  have hxl : x * Real.log (1 + lam) = (1 / 2 - η) * Real.log m := by
    rw [hxdef]; field_simp
  refine ⟨by exact_mod_cast hJ1, by unfold step; apply div_pos (by linarith) hJpos, ?_, ?_⟩
  · unfold step
    rw [div_mul_eq_mul_div, div_le_iff₀ hJpos]
    nlinarith
  · unfold step
    rw [div_mul_eq_mul_div, le_div_iff₀ hJpos]
    nlinarith

lemma blockPt_eq (j : ℕ) :
    blockPt m η lam j = ⌈(m : ℝ) ^ (η + j * step m η lam)⌉₊ := by
  unfold blockPt step
  congr 2
  ring

lemma step_pow_le : (m : ℝ) ^ step m η lam ≤ 1 + lam := by
  obtain ⟨-, -, h1, -⟩ := numBlocks_facts hη hη4 hlam hlam1 hm hx
  rw [Real.rpow_def_of_pos (by positivity)]
  calc Real.exp (Real.log m * step m η lam) ≤ Real.exp (Real.log (1 + lam)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = 1 + lam := Real.exp_log (by linarith)

lemma step_pow_ge : 1 + lam / 4 ≤ (m : ℝ) ^ step m η lam := by
  obtain ⟨-, -, -, h2⟩ := numBlocks_facts hη hη4 hlam hlam1 hm hx
  rw [Real.rpow_def_of_pos (by positivity)]
  have := Real.add_one_le_exp (Real.log m * step m η lam)
  linarith

lemma blockPt_mono : Monotone (blockPt m η lam) := by
  obtain ⟨-, hδ, -, -⟩ := numBlocks_facts hη hη4 hlam hlam1 hm hx
  intro j k hjk
  rw [blockPt_eq hη hη4 hlam hlam1 hm hx, blockPt_eq hη hη4 hlam hlam1 hm hx]
  apply Nat.ceil_mono
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ m))
  have : (j : ℝ) ≤ k := by exact_mod_cast hjk
  nlinarith

lemma blockPt_zero : blockPt m η lam 0 = ⌈(m : ℝ) ^ η⌉₊ := by
  rw [blockPt_eq hη hη4 hlam hlam1 hm hx]; simp

lemma blockPt_top : blockPt m η lam (numBlocks m η lam) = ⌈Real.sqrt m⌉₊ := by
  obtain ⟨hJ, -, -, -⟩ := numBlocks_facts hη hη4 hlam hlam1 hm hx
  rw [blockPt_eq hη hη4 hlam hlam1 hm hx, Real.sqrt_eq_rpow]
  congr 2
  unfold step
  have : (numBlocks m η lam : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ numBlocks m η lam := by exact_mod_cast hJ
    linarith
  field_simp
  ring

lemma top_sq_lt (p : ℕ) (hp : p < blockPt m η lam (numBlocks m η lam)) : p * p < m := by
  rw [blockPt_top hη hη4 hlam hlam1 hm hx, Nat.lt_ceil] at hp
  have h := (Real.lt_sqrt (Nat.cast_nonneg p)).1 hp
  exact_mod_cast (by nlinarith : (p : ℝ) * p < m)

lemma top_sq_ge :
    m ≤ blockPt m η lam (numBlocks m η lam) * blockPt m η lam (numBlocks m η lam) := by
  rw [blockPt_top hη hη4 hlam hlam1 hm hx]
  have h1 : Real.sqrt m ≤ ⌈Real.sqrt m⌉₊ := Nat.le_ceil _
  have h2 : (Real.sqrt m) ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg m)
  have h3 : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
  exact_mod_cast (by nlinarith : (m : ℝ) ≤ (⌈Real.sqrt m⌉₊ : ℝ) * ⌈Real.sqrt m⌉₊)

lemma top_sq_le : ((blockPt m η lam (numBlocks m η lam) : ℕ) : ℝ) ^ 2 ≤ 4 * m := by
  rw [blockPt_top hη hη4 hlam hlam1 hm hx]
  have h1 : (⌈Real.sqrt m⌉₊ : ℝ) < Real.sqrt m + 1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have h2 : (Real.sqrt m) ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg m)
  have h3 : (1 : ℝ) ≤ Real.sqrt m := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]; norm_num
    exact_mod_cast (by omega : 1 ≤ m)
  have h4 : (0 : ℝ) ≤ ⌈Real.sqrt m⌉₊ := Nat.cast_nonneg _
  nlinarith

variable (hs2 : 2 ≤ (m : ℝ) ^ (η / 2)) (hs8 : 8 / lam ≤ (m : ℝ) ^ (η / 2))
include hs2 hs8

/-- Per-block facts. With `θ = η + j δ`, `s = m^{θ/2}`, `M = M_j`, `M' = M_{j+1}`:
`2 ≤ s ≤ M`, `s ≤ M' − M ≤ 2 λ M`, `θ log m ≤ log M`, `log s = θ log m / 2`, `2 ≤ M`. -/
lemma block_facts (j : ℕ) :
    let θ := η + j * step m η lam
    let s := (m : ℝ) ^ (θ / 2)
    let M := blockPt m η lam j
    let M' := blockPt m η lam (j + 1)
    2 ≤ s ∧ s ≤ (M : ℝ) ∧ s ≤ ((M' - M : ℕ) : ℝ) ∧ ((M' : ℝ) - M ≤ 2 * lam * M) ∧
      θ * Real.log m ≤ Real.log M ∧ Real.log s = θ / 2 * Real.log m ∧ 2 ≤ M ∧ M ≤ M' := by
  intro θ s M M'
  obtain ⟨-, hδ, -, -⟩ := numBlocks_facts hη hη4 hlam hlam1 hm hx
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hm0 : (0 : ℝ) < m := by linarith
  have hθ : η ≤ θ := by
    have : (0 : ℝ) ≤ j * step m η lam := by positivity
    simp only [θ]; linarith
  set R := (m : ℝ) ^ θ with hR
  have hs_ge : (m : ℝ) ^ (η / 2) ≤ s :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hs2' : 2 ≤ s := hs2.trans hs_ge
  have hs8' : 8 / lam ≤ s := hs8.trans hs_ge
  have hls : 8 ≤ lam * s := by
    have := (div_le_iff₀ hlam).1 hs8'
    linarith
  have hRs : R = s ^ 2 := by
    simp only [hR, s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
    norm_num
  have hM : M = ⌈R⌉₊ := blockPt_eq hη hη4 hlam hlam1 hm hx j
  have hM' : M' = ⌈R * (m : ℝ) ^ step m η lam⌉₊ := by
    rw [show M' = blockPt m η lam (j + 1) from rfl, blockPt_eq hη hη4 hlam hlam1 hm hx, hR,
      ← Real.rpow_add hm0]
    congr 2
    push_cast
    ring
  have hR0 : 0 ≤ R := by positivity
  have hMR : R ≤ M := hM ▸ Nat.le_ceil R
  have hMR' : (M : ℝ) < R + 1 := hM ▸ Nat.ceil_lt_add_one hR0
  have hpow1 := step_pow_le hη hη4 hlam hlam1 hm hx
  have hpow2 := step_pow_ge hη hη4 hlam hlam1 hm hx
  have hRR : R * (m : ℝ) ^ step m η lam ≥ 0 := by positivity
  have hM'R : R * (m : ℝ) ^ step m η lam ≤ M' := hM' ▸ Nat.le_ceil _
  have hM'R' : (M' : ℝ) < R * (m : ℝ) ^ step m η lam + 1 := hM' ▸ Nat.ceil_lt_add_one hRR
  have hMM' : M ≤ M' := blockPt_mono hη hη4 hlam hlam1 hm hx (Nat.le_succ j)
  have hcast : ((M' - M : ℕ) : ℝ) = (M' : ℝ) - M := Nat.cast_sub hMM'
  have hs_le_R : s ≤ R := by rw [hRs]; nlinarith
  have hlogR : Real.log R = θ * Real.log m := Real.log_rpow hm0 θ
  refine ⟨hs2', hs_le_R.trans hMR, ?_, ?_, ?_, ?_, ?_, hMM'⟩
  · rw [hcast]
    have : R * (1 + lam / 4) ≤ R * (m : ℝ) ^ step m η lam := mul_le_mul_of_nonneg_left hpow2 hR0
    rw [hRs] at this hMR'
    nlinarith
  · have : R * (m : ℝ) ^ step m η lam ≤ R * (1 + lam) := mul_le_mul_of_nonneg_left hpow1 hR0
    have hlR : 1 ≤ lam * R := by rw [hRs]; nlinarith
    nlinarith
  · rw [← hlogR]
    exact Real.log_le_log (by rw [hRs]; positivity) hMR
  · simp only [s]
    rw [Real.log_rpow hm0]
  · have : (2 : ℝ) ≤ M := by rw [hRs] at hMR; nlinarith
    exact_mod_cast this

end Blocks


/-! ### Part 5: Lemma 2.2, analytic part: the defect sum is `O(λ m/(η log m)) + O_η(m/log² m)` -/

lemma natDiv_sub_le (m M M' : ℕ) (hM : 0 < M) (hMM : M ≤ M') :
    (((m / M - m / M' : ℕ) : ℕ) : ℝ) ≤ m * ((M' : ℝ) - M) / (M : ℝ) ^ 2 + 1 := by
  have hle : m / M' ≤ m / M := Nat.div_le_div_left hMM hM
  rw [Nat.cast_sub hle]
  have h1 : ((m / M : ℕ) : ℝ) ≤ (m : ℝ) / M := Nat.cast_div_le
  have h2 : (m : ℝ) / M' < ((m / M' : ℕ) : ℝ) + 1 := by
    rw [← Nat.floor_div_eq_div (K := ℝ)]; exact Nat.lt_floor_add_one _
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hM'0 : (0 : ℝ) < M' := by exact_mod_cast (lt_of_lt_of_le hM hMM)
  have hMM' : (M : ℝ) ≤ M' := by exact_mod_cast hMM
  have h3 : (m : ℝ) / M - m / M' ≤ m * ((M' : ℝ) - M) / (M : ℝ) ^ 2 := by
    rw [div_sub_div _ _ hM0.ne' hM'0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : 0 ≤ (m : ℝ) * ((M' : ℝ) - M) := mul_nonneg hm0 (by linarith)
    nlinarith [mul_nonneg this (mul_nonneg hM0.le (by linarith : (0:ℝ) ≤ M' - M))]
  linarith

lemma natDiv_div_le (m M : ℕ) : (((m / M / M : ℕ)) : ℝ) ≤ (m : ℝ) / (M : ℝ) ^ 2 := by
  calc (((m / M / M : ℕ)) : ℝ) ≤ ((m / M : ℕ) : ℝ) / M := Nat.cast_div_le
    _ ≤ ((m : ℝ) / M) / M := by gcongr; exact Nat.cast_div_le
    _ = (m : ℝ) / (M : ℝ) ^ 2 := by rw [div_div, sq]

set_option linter.unusedSectionVars false in
/-- **Lemma 2.2, analytic part.** For the block system `𝔅(m, η, λ)` (once `m` is large in the
explicit sense of the hypotheses), with `C` the constant of the sieve upper bound:
`Σ_j ι_j (X_j + Y_j) ≤ (m / log m) (32 C²/(η² log m) + 96 C² λ/η)`. -/
theorem defect_le {C : ℝ} (hC0 : 0 < C) (hC : ∀ (a H : ℕ) (y : ℝ), 2 ≤ y → y ≤ (H : ℝ) →
      (#{n ∈ Ioc a (a + H) | n = 1 ∨ y ≤ (n.minFac : ℝ)} : ℝ) ≤ C * H / Real.log y)
    {m : ℕ} {η lam : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hm : 2 ≤ m) (hx : 1 ≤ (1 / 2 - η) * Real.log m / Real.log (1 + lam))
    (hs2 : 2 ≤ (m : ℝ) ^ (η / 2)) (hs8 : 8 / lam ≤ (m : ℝ) ^ (η / 2)) :
    ∑ j ∈ range (numBlocks m η lam),
      (primesIn m (Ico (blockPt m η lam j) (blockPt m η lam (j + 1))) : ℝ) *
        ((Xcount m (blockPt m η lam j) (blockPt m η lam (j + 1)) : ℝ) +
          (Ycount m (blockPt m η lam j) (blockPt m η lam (j + 1)) : ℝ)) ≤
      (m / Real.log m) * (32 * C ^ 2 / (η ^ 2 * Real.log m) + 96 * C ^ 2 * lam / η) := by
  classical
  obtain ⟨hJ, hδ, -, hδ2⟩ := numBlocks_facts hη hη4 hlam hlam1 hm hx
  set J := numBlocks m η lam
  set δ := step m η lam
  set M := blockPt m η lam with hMdef
  set L := Real.log m with hL
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hL0 : 0 < L := Real.log_pos hm1
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- per-block bound
  have hblock : ∀ j, (primesIn m (Ico (M j) (M (j + 1))) : ℝ) *
      ((Xcount m (M j) (M (j + 1)) : ℝ) + (Ycount m (M j) (M (j + 1)) : ℝ)) ≤
      (24 * C ^ 2 * lam ^ 2 * m + 4 * C ^ 2 * ((M (j + 1) : ℝ) - M j) * M j) /
        ((η + j * δ) * L) ^ 2 := by
    intro j
    obtain ⟨hs2', hsM, hsΔ, hΔ, hlogM, hlogs, hM2, hMM'⟩ :=
      block_facts hη hη4 hlam hlam1 hm hx hs2 hs8 j
    have e1 : step m η lam = δ := rfl
    have e2 : Real.log (m : ℝ) = L := rfl
    rw [e1] at hs2' hsM hsΔ hlogM hlogs
    rw [e2] at hlogM hlogs
    have hθ : η ≤ η + j * δ := by have : (0:ℝ) ≤ j * δ := by positivity
                                  linarith
    have hℓ : 0 < (η + j * δ) * L := by positivity
    have hM2r : (2 : ℝ) ≤ M j := by exact_mod_cast hM2
    have hMr : (1 : ℝ) ≤ M j := by linarith
    have hMMr : (M j : ℝ) ≤ M (j + 1) := by exact_mod_cast hMM'
    have hcast : ((M (j + 1) - M j : ℕ) : ℝ) = (M (j + 1) : ℝ) - M j := Nat.cast_sub hMM'
    have hM1 : 1 ≤ M j := by exact_mod_cast hMr
    refine block_term_le (ι' := (#{p ∈ Ico (M j) (M (j + 1)) | p.Prime} : ℝ)) hC0.le hℓ hm0 hMr
      hMMr (Nat.cast_nonneg _) ?_ ?_ (Nat.cast_nonneg _) ?_ (Nat.cast_nonneg _) ?_ hΔ
    · unfold primesIn
      exact_mod_cast card_le_card (fun p hp => by
        simp only [mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩)
    · have h := primes_Ico_le hC (M j) (M (j + 1)) hM1 hMM' _ hs2' hsM hsΔ
      rw [hcast, hlogs] at h
      refine h.trans (le_of_eq ?_)
      field_simp
    · have h := Xcount_le hC m (M j) (M (j + 1)) hM2
      have hns := natDiv_sub_le m (M j) (M (j + 1)) (by omega) hMM'
      have hlogM0 : 0 ≤ Real.log (M j) := hℓ.le.trans hlogM
      calc (Xcount m (M j) (M (j + 1)) : ℝ)
          ≤ C * (((M j : ℕ) : ℝ) * 0 + ((m / M j - m / M (j + 1) : ℕ) : ℝ) + M j) /
              Real.log (M j) := by simpa using h
        _ ≤ C * (m * ((M (j + 1) : ℝ) - M j) / (M j : ℝ) ^ 2 + 1 + M j) / Real.log (M j) := by
            apply div_le_div_of_nonneg_right _ hlogM0
            apply mul_le_mul_of_nonneg_left _ hC0.le
            linarith
        _ ≤ C * (m * ((M (j + 1) : ℝ) - M j) / (M j : ℝ) ^ 2 + 1 + M j) / ((η + j * δ) * L) := by
            apply div_le_div_of_nonneg_left _ hℓ hlogM
            have : 0 ≤ m * ((M (j + 1) : ℝ) - M j) / (M j : ℝ) ^ 2 := by
              apply div_nonneg (mul_nonneg hm0 (by linarith)) (by positivity)
            positivity
    · have h := Ycount_le m (M j) (M (j + 1)) hM1
      have h' : (Ycount m (M j) (M (j + 1)) : ℝ) ≤
          (#{p ∈ Ico (M j) (M (j + 1)) | p.Prime} : ℝ) * ((m / M j / M j : ℕ) : ℝ) := by
        exact_mod_cast h
      refine h'.trans (mul_le_mul_of_nonneg_left (natDiv_div_le m (M j)) (Nat.cast_nonneg _))
  have h1δ : 1 / (δ * η) ≤ 4 * L / (lam * η) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have htop := top_sq_le hη hη4 hlam hlam1 hm hx
  have hsum2 : ∑ j ∈ range J, ((M (j + 1) : ℝ) - M j) * M j ≤ ((M J : ℕ) : ℝ) ^ 2 / 2 :=
    sum_diff_mul_le (fun j => (M j : ℝ)) J
  calc _ ≤ ∑ j ∈ range J, (24 * C ^ 2 * lam ^ 2 * m + 4 * C ^ 2 * ((M (j + 1) : ℝ) - M j) * M j) /
        ((η + j * δ) * L) ^ 2 := sum_le_sum fun j _ => hblock j
    _ = (24 * C ^ 2 * lam ^ 2 * m / L ^ 2) * ∑ j ∈ range J, 1 / (η + j * δ) ^ 2 +
        ∑ j ∈ range J, 4 * C ^ 2 * (((M (j + 1) : ℝ) - M j) * M j) / ((η + j * δ) * L) ^ 2 := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun j _ => ?_
        have : 0 < η + j * δ := by positivity
        field_simp
    _ ≤ (24 * C ^ 2 * lam ^ 2 * m / L ^ 2) * (1 / η ^ 2 + 1 / (δ * η)) +
        ∑ j ∈ range J, 4 * C ^ 2 * (((M (j + 1) : ℝ) - M j) * M j) / (η * L) ^ 2 := by
        gcongr with j hj
        · exact sum_inv_sq_le η δ hη hδ J
        · have hMM' := blockPt_mono hη hη4 hlam hlam1 hm hx (Nat.le_succ j)
          have : (M j : ℝ) ≤ M (j + 1) := by exact_mod_cast hMM'
          have : 0 ≤ ((M (j + 1) : ℝ) - M j) * M j := mul_nonneg (by linarith) (Nat.cast_nonneg _)
          positivity
        · have : (0 : ℝ) ≤ j * δ := by positivity
          linarith
    _ = (24 * C ^ 2 * lam ^ 2 * m / L ^ 2) * (1 / η ^ 2 + 1 / (δ * η)) +
        4 * C ^ 2 / (η * L) ^ 2 * ∑ j ∈ range J, ((M (j + 1) : ℝ) - M j) * M j := by
        rw [mul_sum]
        refine congrArg _ (sum_congr rfl fun j _ => ?_)
        ring
    _ ≤ (24 * C ^ 2 * lam ^ 2 * m / L ^ 2) * (1 / η ^ 2 + 4 * L / (lam * η)) +
        4 * C ^ 2 / (η * L) ^ 2 * (4 * m / 2) := by
        gcongr
        exact hsum2.trans (by linarith)
    _ ≤ _ := by
        have key : (m / L) * (32 * C ^ 2 / (η ^ 2 * L) + 96 * C ^ 2 * lam / η) -
            ((24 * C ^ 2 * lam ^ 2 * m / L ^ 2) * (1 / η ^ 2 + 4 * L / (lam * η)) +
              4 * C ^ 2 / (η * L) ^ 2 * (4 * m / 2)) =
            24 * C ^ 2 * (1 - lam ^ 2) * m / (η ^ 2 * L ^ 2) := by
          field_simp
          ring
        have : 0 ≤ 24 * C ^ 2 * (1 - lam ^ 2) * m / (η ^ 2 * L ^ 2) := by
          have : 0 ≤ 1 - lam ^ 2 := by nlinarith
          positivity
        linarith


/-! ### Part 6: elementary facts -/

lemma siftedR_eq_sifted (y : ℝ) (A : Finset ℕ) : siftedR y A = sifted ⌈y⌉₊ A := by
  unfold siftedR sifted
  congr 1
  refine filter_congr fun n _ => ?_
  rw [Nat.ceil_le]

lemma PhiCop_le_Phi (m x : ℕ) (y : ℝ) : PhiCop m x y ≤ Phi x y := by
  unfold PhiCop Phi siftedR
  exact card_le_card (filter_subset_filter _ (filter_subset _ _))

lemma unitsLe_bounds {m : ℕ} (hm : 2 ≤ m) : ∀ n ∈ unitsLe m, 0 < n ∧ n < m := by
  intro n hn
  simp only [unitsLe, mem_filter, mem_Icc] at hn
  refine ⟨by omega, lt_of_le_of_ne hn.1.2 ?_⟩
  rintro rfl
  rw [Nat.coprime_self] at hn
  omega

lemma one_mem_unitsLe {m : ℕ} (hm : 1 ≤ m) : 1 ∈ unitsLe m := by
  simp [unitsLe, hm]

lemma primeCount_le_primesP (m : ℕ) : primeCount m (unitsLe m) ≤ #(primesP m) := by
  unfold primeCount
  refine card_le_card fun n hn => ?_
  simp only [unitsLe, mem_filter, mem_Icc] at hn
  rw [mem_primesP]
  refine ⟨hn.1.1.2, hn.2.1, fun hd => ?_⟩
  have := Nat.Coprime.coprime_dvd_right hd hn.1.2
  rw [Nat.coprime_self] at this
  exact hn.2.1.one_lt.ne' this

/-- `π(m) ≤ P_≥ + ⌊√m⌋ + 2`, where `P_≥ = #{p < m prime, p ∤ m, p² ≥ m}`. -/
lemma primeCounting_le (m : ℕ) (hm : 1 ≤ m) :
    Nat.primeCounting m ≤ primeCount m (unitsLe m) + (Nat.sqrt m + 1) + 1 := by
  classical
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE, Nat.primesBelow_eq_filter_range]
  set S := (range (m + 1)).filter Nat.Prime
  have hsub : S ⊆ (unitsLe m).filter (fun n => n.Prime ∧ m ≤ n * n) ∪ range (Nat.sqrt m + 1) ∪
      S.filter (fun p => p ∣ m ∧ m ≤ p * p) := by
    intro p hp
    have hp' := hp
    simp only [S, mem_filter, mem_range] at hp'
    simp only [mem_union, mem_filter, mem_range, unitsLe, mem_Icc]
    by_cases h1 : p * p < m
    · left; right
      exact Nat.lt_succ_of_le (Nat.le_sqrt.2 h1.le)
    · push Not at h1
      by_cases hd : p ∣ m
      · right; exact ⟨hp, hd, h1⟩
      · left; left
        exact ⟨⟨⟨hp'.2.one_lt.le, by omega⟩, (Nat.Prime.coprime_iff_not_dvd hp'.2).2 hd⟩, hp'.2, h1⟩
  have hone : #(S.filter (fun p => p ∣ m ∧ m ≤ p * p)) ≤ 1 := by
    refine card_le_one.2 fun a ha b hb => ?_
    simp only [S, mem_filter, mem_range] at ha hb
    by_contra hne
    have hab : a * b ∣ m :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes ha.1.2 hb.1.2).2 hne) ha.2.1 hb.2.1
    have hle : a * b ≤ m := Nat.le_of_dvd (by omega) hab
    have h1 : b ≤ a := Nat.le_of_mul_le_mul_left (by linarith [ha.2.2]) ha.1.2.pos
    have h2 : a ≤ b := Nat.le_of_mul_le_mul_right (by linarith [hb.2.2]) hb.1.2.pos
    exact hne (le_antisymm h2 h1)
  calc #S ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := add_le_add ((card_union_le _ _).trans (by unfold primeCount; rw [card_range])) hone

lemma rho_ge (m : ℕ) (hm : 1 ≤ m) :
    (primeCount m (unitsLe m) : ℝ) / m ≤ rho m := by
  unfold rho
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hφm : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hP : (primeCount m (unitsLe m) : ℝ) ≤ #(primesP m) := by
    exact_mod_cast primeCount_le_primesP m
  calc (primeCount m (unitsLe m) : ℝ) / m ≤ (primeCount m (unitsLe m) : ℝ) / m.totient :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hφ hφm
    _ ≤ _ := div_le_div_of_nonneg_right hP hφ.le

lemma rho_nonneg (m : ℕ) : 0 ≤ rho m := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma exp_neg_gamma_le : Real.exp (-Real.eulerMascheroniConstant) ≤ 2 / 3 := by
  have h1 := Real.one_half_lt_eulerMascheroniConstant
  have h2 : Real.exp (-Real.eulerMascheroniConstant) ≤ Real.exp (-(1 / 2)) :=
    Real.exp_le_exp.2 (by linarith)
  have h3 : (1 / 2 : ℝ) + 1 ≤ Real.exp (1 / 2) := Real.add_one_le_exp _
  have h4 : Real.exp (-(1 / 2)) = (Real.exp (1 / 2))⁻¹ := Real.exp_neg _
  have h5 : (Real.exp (1 / 2))⁻¹ ≤ 2 / 3 := by
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
  linarith

/-- Large-`m` facts used at the end (`t = m^{1/4} ≥ 400`). -/
lemma large_facts (m : ℕ) (hm : 4 ≤ m) (η : ℝ) (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (ht : 400 ≤ (m : ℝ) ^ ((1 : ℝ) / 4)) :
    Real.sqrt m + 2 ≤ (Nat.primeCounting m : ℝ) / 10 ∧ 3 * (m : ℝ) ≤ (Nat.primeCounting m : ℝ) ^ 2 ∧
      (m : ℝ) / Real.log m ≤ (Nat.primeCounting m : ℝ) / (693 / 1000) ∧
      ⌈(m : ℝ) ^ η⌉₊ * ⌈(m : ℝ) ^ η⌉₊ ≤ m := by
  set t := (m : ℝ) ^ ((1 : ℝ) / 4) with htdef
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hL : 0 < Real.log m := Real.log_pos hm1
  have ht4 : (m : ℝ) = t ^ 4 := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hm0]; norm_num
  have hsqrt : Real.sqrt m = t ^ 2 := by
    rw [ht4, show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hlog : Real.log m ≤ 4 * t := by
    have := Real.log_le_rpow_div hm0 (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [← htdef] at this; linarith
  have hpi := Chebyshev.pi_ge_of_four_le hm
  have hlog2 : (693 / 1000 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hmL : (m : ℝ) / Real.log m ≤ (Nat.primeCounting m : ℝ) / (693 / 1000) := by
    rw [le_div_iff₀ (by norm_num)]
    have : (m : ℝ) / Real.log m * (693 / 1000) ≤ m * Real.log 2 / Real.log m := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left hlog2.le (div_nonneg hm0 hL.le)
    linarith
  have hpi2 : (693 / 1000) * t ^ 3 / 4 ≤ (Nat.primeCounting m : ℝ) := by
    have h1 : (m : ℝ) / Real.log m ≥ t ^ 3 / 4 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hL]
      have : 0 ≤ t ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hlog this]
    have h2 := hmL
    rw [le_div_iff₀ (by norm_num)] at h2
    nlinarith
  refine ⟨?_, ?_, hmL, ?_⟩
  · rw [hsqrt]
    have : 0 ≤ t ^ 2 := by positivity
    nlinarith
  · rw [ht4]
    have h0 : 0 ≤ (693 / 1000) * t ^ 3 / 4 := by positivity
    have := mul_le_mul hpi2 hpi2 h0 (h0.trans hpi2)
    have h100 : 100 * t ^ 4 ≤ t ^ 6 := by
      have := mul_le_mul_of_nonneg_left (show 100 ≤ t ^ 2 by nlinarith)
        (show 0 ≤ t ^ 4 by positivity)
      nlinarith
    nlinarith
  · have hz : (m : ℝ) ^ η ≤ t :=
      Real.rpow_le_rpow_of_exponent_le hm1.le hη4
    have hc : (⌈(m : ℝ) ^ η⌉₊ : ℝ) < (m : ℝ) ^ η + 1 := Nat.ceil_lt_add_one (by positivity)
    have hc0 : (0 : ℝ) ≤ ⌈(m : ℝ) ^ η⌉₊ := Nat.cast_nonneg _
    have : (⌈(m : ℝ) ^ η⌉₊ : ℝ) * ⌈(m : ℝ) ^ η⌉₊ ≤ m := by
      have h1 : (⌈(m : ℝ) ^ η⌉₊ : ℝ) ≤ t + 1 := by linarith
      have h2 := mul_le_mul h1 h1 hc0 (by linarith)
      have h3a : (t + 1) * (t + 1) ≤ 2 * t ^ 2 := by nlinarith
      have h3b : 2 * t ^ 2 ≤ t ^ 4 := by
        nlinarith [mul_le_mul_of_nonneg_left (show 2 ≤ t ^ 2 by nlinarith) (sq_nonneg t)]
      have h3 : (t + 1) * (t + 1) ≤ t ^ 4 := h3a.trans h3b
      linarith
    exact_mod_cast this

lemma eventually_large (η lam C : ℝ) (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hlam : 0 < lam)
    (N₀ : ℕ) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → N₀ ≤ m ∧ 1 ≤ (1 / 2 - η) * Real.log m / Real.log (1 + lam) ∧
      2 ≤ (m : ℝ) ^ (η / 2) ∧ 8 / lam ≤ (m : ℝ) ^ (η / 2) ∧ 2000 * C ^ 2 / η ^ 2 ≤ Real.log m ∧
      400 ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := by
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog := Real.tendsto_log_atTop.comp hcast
  have hpow := (tendsto_rpow_atTop (show 0 < η / 2 by positivity)).comp hcast
  have hpow4 := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).comp hcast
  have hl : 0 < Real.log (1 + lam) := Real.log_pos (by linarith)
  have e1 := hlog.eventually_ge_atTop (Real.log (1 + lam) / (1 / 2 - η))
  have e2 := hpow.eventually_ge_atTop (max 2 (8 / lam))
  have e3 := hlog.eventually_ge_atTop (2000 * C ^ 2 / η ^ 2)
  have e4 := hpow4.eventually_ge_atTop 400
  have e0 := Filter.eventually_ge_atTop N₀
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (e0.and (e1.and (e2.and (e3.and e4))))
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨h0, h1, h2, h3, h4⟩ := hN m hm
  simp only [Function.comp] at h1 h2 h3 h4
  refine ⟨h0, ?_, le_of_max_le_left h2, le_of_max_le_right h2, h3, h4⟩
  rw [le_div_iff₀ hl, one_mul]
  rw [div_le_iff₀ (by linarith)] at h1
  linarith

end GapH4

/-- **The gap theorem (Theorem E and Corollary H4 of `notes/routes/E-buchstab-H4.md`).**
Assume the unconditional inputs `TypeISifted` (Type I + fundamental lemma) and `RoughCounts`
(sieve upper bound; Buchstab–de Bruijn with `e^{−γ}`). Then there are `η₀ > 0` and `κ > 0` such
that for every `η ∈ (0, η₀]` and every `λ ∈ (0, κη]`, the hypothesis `H4 η λ` implies the
Erdős–Odlyzko–Sárközy conjecture.

GRH is not a hypothesis. **H4 is stronger than EOS and is not known to follow from GRH**; this
theorem isolates the gap, it does not close it. (`κ = 1/(10000 C²)` with `C ≥ 1` the sieve constant;
`η₀ = min(η_T, η_R, 1/4)` with `η_T`, `η_R` the thresholds of `TypeISifted`, `RoughMertens` at
`ε = 1/100`.) -/
theorem eos_of_H4 (hT : TypeISifted) (hR : RoughCounts) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ lam : ℝ, 0 < lam → lam ≤ κ * η → H4 η lam → Conjecture := by
  classical
  obtain ⟨⟨C₀, -, hC₀'⟩, hRM⟩ := hR
  set C := max C₀ 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by linarith
  have hC : ∀ (a H : ℕ) (y : ℝ), 2 ≤ y → y ≤ (H : ℝ) →
      (#{n ∈ Ioc a (a + H) | n = 1 ∨ y ≤ (n.minFac : ℝ)} : ℝ) ≤ C * H / Real.log y := by
    intro a H y hy hyH
    refine (hC₀' a H y hy hyH).trans ?_
    have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    apply div_le_div_of_nonneg_right _ hl
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
  obtain ⟨ηT, hηT, hTη⟩ := hT (1 / 100) (by norm_num)
  obtain ⟨ηR, hηR, hRη⟩ := hRM (1 / 100) (by norm_num)
  refine ⟨min (min ηT ηR) (1 / 4), by positivity, 1 / (10000 * C ^ 2), by positivity, ?_⟩
  intro η hη hηle lam hlam hlamle hH
  have hη4 : η ≤ 1 / 4 := hηle.trans (min_le_right _ _)
  have hηT' : η ≤ ηT := hηle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hηR' : η ≤ ηR := hηle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hlamC : 10000 * C ^ 2 * lam ≤ η := by
    have h := hlamle
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h
    linarith
  have hlam1 : lam ≤ 1 := by nlinarith
  obtain ⟨mT, hmT⟩ := hTη η hη hηT'
  obtain ⟨mR, hmR⟩ := hRη η hη hηR'
  obtain ⟨mH, hmH⟩ := hH
  obtain ⟨N, hN⟩ := GapH4.eventually_large η lam C hη hη4 hlam (max mT (max mR (max mH 16)))
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨hmN, hx, hs2, hs8, hLC, ht⟩ := hN m hm
  have hmT' : mT ≤ m := le_trans (le_max_left _ _) hmN
  have hmR' : mR ≤ m := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hmN
  have hmH' : mH ≤ m :=
    le_trans (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hmN
  have hm16 : 16 ≤ m :=
    le_trans (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hmN
  have : NeZero m := ⟨by omega⟩
  have hm2 : 2 ≤ m := by omega
  obtain ⟨hsq, hpi2, hmL, hz⟩ := GapH4.large_facts m (by omega) η hη hη4 ht
  set z := ⌈(m : ℝ) ^ η⌉₊ with hzdef
  have hM0 := GapH4.blockPt_zero hη hη4 hlam hlam1 hm2 hx
  apply coveredBy_of_certificate
  intro a ha
  refine lemmaC'_of_H4Block hm2 ha hz (blockPt m η lam) (numBlocks m η lam) (le_of_eq hM0)
    (GapH4.top_sq_ge hη hη4 hlam hlam1 hm2 hx) hη.le (fun j hj => hmH m hmH' j hj) ?_
  -- the inputs at this `m`
  have hS := hmT m hmT' a ha
  rw [GapH4.siftedR_eq_sifted] at hS
  have hΦ := hmR m hmR'
  have hPhiCop : PhiCop m m ((m : ℝ) ^ η) = sifted z (GapH4.unitsLe m) := by
    unfold PhiCop; rw [GapH4.siftedR_eq_sifted]; rfl
  have hΦle : (PhiCop m m ((m : ℝ) ^ η) : ℝ) ≤ Phi m ((m : ℝ) ^ η) := by
    exact_mod_cast GapH4.PhiCop_le_Phi m m _
  have hid := buchstab_identity m z (GapH4.unitsLe m) (GapH4.unitsLe_bounds hm2) hz
  have h1U := GapH4.one_mem_unitsLe (m := m) (by omega)
  simp only [h1U, ↓reduceIte] at hid
  have hidR : (primeCount m (GapH4.unitsLe m) : ℝ) + bilinear m z (GapH4.unitsLe m) + 1 =
      sifted z (GapH4.unitsLe m) := by exact_mod_cast hid
  have hpos : 0 < blockPt m η lam 0 := by
    rw [hM0]; exact Nat.ceil_pos.2 (by positivity)
  have hcomb := GapH4.lemma22_comb (m := m) (z := z) (J := numBlocks m η lam) (blockPt m η lam)
    (GapH4.blockPt_mono hη hη4 hlam hlam1 hm2 hx) hM0 hpos
    (GapH4.top_sq_lt hη hη4 hlam hlam1 hm2 hx)
  have hcombR := (Nat.cast_le (α := ℝ)).2 hcomb
  push_cast at hcombR
  have hE := GapH4.defect_le hC0 hC hη hη4 hlam hlam1 hm2 hx hs2 hs8
  set E := ∑ j ∈ range (numBlocks m η lam),
    (primesIn m (Ico (blockPt m η lam j) (blockPt m η lam (j + 1))) : ℝ) *
      ((GapH4.Xcount m (blockPt m η lam j) (blockPt m η lam (j + 1)) : ℝ) +
        (GapH4.Ycount m (blockPt m η lam j) (blockPt m η lam (j + 1)) : ℝ)) with hEdef
  set Sig := ∑ j ∈ range (numBlocks m η lam),
    (primesIn m (Ico (blockPt m η lam j) (blockPt m η lam (j + 1))) : ℝ) *
      (#(roughUnits m (blockPt m η lam j)) : ℝ) with hSigdef
  have hE0 : 0 ≤ E := sum_nonneg fun j _ => by positivity
  set L := Real.log m with hL
  set πm := (Nat.primeCounting m : ℝ) with hπm
  have hL0 : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hEpi : E ≤ πm / 20 := by
    have h1 : 32 * C ^ 2 / (η ^ 2 * L) ≤ 16 / 1000 := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hLC
      nlinarith
    have h2 : 96 * C ^ 2 * lam / η ≤ 96 / 10000 := by
      rw [div_le_iff₀ hη]; nlinarith
    have h3 : 0 ≤ (m : ℝ) / L := by positivity
    have h4 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) h3
    have h5 : (m : ℝ) / L * (16 / 1000 + 96 / 10000) ≤
        πm / (693 / 1000) * (16 / 1000 + 96 / 10000) :=
      mul_le_mul_of_nonneg_right hmL (by norm_num)
    have hπ0 : 0 ≤ πm := Nat.cast_nonneg _
    linarith
  -- prime counts
  have hPge := GapH4.primeCounting_le m (by omega)
  have hPgeR : πm ≤ (primeCount m (GapH4.unitsLe m) : ℝ) + ((Nat.sqrt m : ℕ) : ℝ) + 2 := by
    have := (Nat.cast_le (α := ℝ)).2 hPge
    push_cast at this
    linarith
  have hsqrtle : ((Nat.sqrt m : ℕ) : ℝ) ≤ Real.sqrt m := Real.nat_sqrt_le_real_sqrt
  set P := (primeCount m (GapH4.unitsLe m) : ℝ) with hPdef
  have hP9 : 9 / 10 * πm ≤ P := by linarith
  have hρ := GapH4.rho_ge m (by omega)
  have hρ0 := GapH4.rho_nonneg m
  have hγ := GapH4.exp_neg_gamma_le
  set Φm := (sifted z (GapH4.unitsLe m) : ℝ) with hΦmdef
  set B := (bilinear m z (GapH4.unitsLe m) : ℝ) with hBdef
  set S := (sifted z (Aset m a) : ℝ) with hSdef
  set ρ := rho m with hρdef
  rw [hPhiCop] at hS hΦle
  have hηΦ : η * Φm ≤ (2 / 3 + 1 / 100) * πm := by
    have hπ0 : 0 ≤ πm := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hΦle hη.le
    have h2 := mul_le_mul_of_nonneg_right (add_le_add_right hγ (1 / 100)) hπ0
    linarith
  have hB : B = Φm - P - 1 := by linarith
  have hSig : Sig ≤ B + E := hcombR
  set W := (1 + η / 2) * (P + 1 - E) - (η / 2 + η / 100) * Φm - πm / 100 with hWdef
  have hW : 48 / 100 * πm ≤ W := by
    have ha : 0 ≤ η * (P + 1) := mul_nonneg hη.le (by positivity)
    have hb : η * E ≤ 1 / 4 * E := mul_le_mul_of_nonneg_right hη4 hE0
    have hπ0 : 0 ≤ πm := Nat.cast_nonneg _
    have hexp : W = P + 1 - E + η / 2 * (P + 1) - η / 2 * E - 51 / 100 * (η * Φm) - πm / 100 := by
      rw [hWdef]; ring
    rw [hexp]
    linarith only [ha, hb, hηΦ, hP9, hEpi, hπ0]
  have hρW : ρ * W = ρ * ((1 - 1 / 100 * η) * Φm - 1 / 100 * πm) - (1 + η / 2) * ρ * (B + E) := by
    rw [hWdef, hB]; ring
  have hSig : (1 + η / 2) * ρ * Sig ≤ (1 + η / 2) * ρ * (B + E) :=
    mul_le_mul_of_nonneg_left hSig (by positivity)
  have hπ0 : 0 ≤ πm := Nat.cast_nonneg _
  have h1 : ρ * (48 / 100 * πm) ≤ ρ * W := mul_le_mul_of_nonneg_left hW hρ0
  have h2 : 9 / 10 * πm / m ≤ ρ := (div_le_div_of_nonneg_right hP9 hm0.le).trans hρ
  have h3 : 9 / 10 * πm / m * (48 / 100 * πm) ≤ ρ * (48 / 100 * πm) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have h4 : 1 < 9 / 10 * πm / m * (48 / 100 * πm) := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hm0]
    linarith only [hpi2, hm0]
  linarith only [hS, hSig, hρW, h1, h3, h4]

end EOS
