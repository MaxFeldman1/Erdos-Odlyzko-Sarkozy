import EOS.LogFour

/-!
# EOS with `p, q ≪ m log² m` and with `p ≤ m`, `q ≪ m log³ m`, conditional on `GRHSmoothBound`

Route C of the project notes (`notes/routes/C-log-exponent.md`, §1–§3). The analytic input is the
Cesàro-smoothed GRH bound `GRHSmoothBound` (notes §1, Theorem 1), which has `log (2q)` in place
of the `(log (q x))²` of `GRHBounds`.

Write `S(x, χ) = ψ̃(x, χ) = Σ_{n ≤ x} Λ(n) χ(n) (1 - n/x)` and
`R(a) = Σ_{n₁ ≤ x₁, n₂ ≤ x₂, n₁ n₂ ≡ a} Λ(n₁)(1 - n₁/x₁) Λ(n₂)(1 - n₂/x₂)`.

* `totient_mul_wpair` (D1): `φ(m) R(a) = Σ_χ χ(a⁻¹) S(x₁, χ) S(x₂, χ)`.
* `sum_norm_sq_wsum_le` (D4(a), Parseval): for `N < m`, `Σ_χ |Σ_{n ≤ N} c(n) χ(n)|² ≤ φ(m) Σ c(n)²`.
* `wpair_le_of_not_exists`: the weights lie in `[0, Λ]`, so if no prime pair `p ≤ x₁, q ≤ x₂` has
  `pq ≡ a`, only pairs involving a prime power `p^k`, `k ≥ 2`, contribute, and `R(a)` is small.
  (This replaces D0: we work with `Λ` throughout and never pass to the prime-supported `ϑ̃`.)
* `exists_of_criterion` (D7): principal term minus non-principal terms beats the prime-power bound.
* `coveredBy_log_sq` (Theorem S): sup bound on every non-principal character, `x = K m log² m`.
* `coveredByAsym_m_log_cube` (Corollary A1): `x₂ = m - 1`, `x₁ = K m log³ m`; the non-principal
  terms are bounded by `sup_χ |S(x₁, χ)| · Σ_χ |S(x₂, χ)|` and Cauchy–Schwarz plus Parseval (D5).

We use `φ(m) ≤ m` throughout, so the ranges are `K m log² m` and `K m log³ m`, not the sharper
`K φ log² m` and `K φ² log³ m / m` of the notes.
-/

open scoped BigOperators
open Finset ArithmeticFunction

namespace EOS

-- `psiCesaro` and `GRHSmoothBound` are copied verbatim from notes/routes/C-log-exponent.md §1.5.
-- A referee is checking that H follows from GRH (notes §1); if the notes are corrected, change
-- them here and in the proof of `GRHSmoothBound.bounds` only.

/-- Cesàro-smoothed twisted Chebyshev sum `ψ̃(x, χ) = Σ_{n ≤ x} Λ(n) χ(n) (1 - n/x)`. -/
noncomputable def psiCesaro {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Iic ⌊x⌋₊,
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ n * (1 - (n : ℂ) / (x : ℂ))

/-- **Analytic input H (consequence of GRH).** Absolute `C` with
`|ψ̃(x, χ) - [χ = 1] x/2| ≤ C √x log (2q)` for all `q ≥ 1`, all `χ` mod `q`, all `x ≥ 1`.
Proof from GRH: notes/routes/C-log-exponent.md §1. Literature: Banks–Shparlinski,
arXiv:2610.19597, Lemma 2.5; Montgomery–Vaughan, Multiplicative Number Theory I, §13.2. -/
def GRHSmoothBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ), 1 ≤ x →
    ‖psiCesaro χ x - (if χ = 1 then ((x / 2 : ℝ) : ℂ) else 0)‖
      ≤ C * Real.sqrt x * Real.log (2 * q)

/-- The only two consequences of `GRHSmoothBound` used below (at modulus `q = m`): a lower bound
for the principal character and an upper bound for the others. All later lemmas use this
lemma, never the definition, so a corrected `GRHSmoothBound` only affects this proof. -/
lemma GRHSmoothBound.bounds (h : GRHSmoothBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m] (x : ℝ), 1 ≤ x →
      x / 2 - C * Real.sqrt x * Real.log (2 * m) ≤
          ‖psiCesaro (1 : DirichletCharacter ℂ m) x‖ ∧
        ∀ χ : DirichletCharacter ℂ m, χ ≠ 1 →
          ‖psiCesaro χ x‖ ≤ C * Real.sqrt x * Real.log (2 * m) := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun m _ x hx ↦ ⟨?_, fun χ hχ ↦ ?_⟩⟩
  · have hb := hC m 1 x hx
    rw [ite_eq_left rfl] at hb
    have h1 := norm_sub_norm_le ((x / 2 : ℝ) : ℂ) (psiCesaro (1 : DirichletCharacter ℂ m) x)
    rw [norm_sub_rev, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h1
    linarith
  · have hb := hC m χ x hx
    rwa [ite_eq_right hχ, sub_zero] at hb

/-- Asymmetric covering: every unit mod `m` is `p * q` with primes `p ≤ Y₁`, `q ≤ Y₂`. -/
def CoveredByAsym (m : ℕ) (Y₁ Y₂ : ℝ) : Prop :=
  ∀ a : ZMod m, IsUnit a →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (p : ℝ) ≤ Y₁ ∧ (q : ℝ) ≤ Y₂ ∧ ((p * q : ℕ) : ZMod m) = a

/-- Weighted twisted sum `Σ_{n ≤ N} c(n) χ(n)`. -/
noncomputable def wsum {m : ℕ} (c : ℕ → ℝ) (N : ℕ) (χ : DirichletCharacter ℂ m) : ℂ :=
  ∑ n ∈ Iic N, (c n : ℂ) * χ n

/-- The Cesàro weight `Λ(n) (1 - n/x)`. -/
noncomputable def cw (x : ℝ) (n : ℕ) : ℝ := Λ n * (1 - n / x)

lemma psiCesaro_eq_wsum {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    psiCesaro χ x = wsum (cw x) ⌊x⌋₊ χ := by
  unfold psiCesaro wsum cw
  refine sum_congr rfl fun n _ ↦ ?_
  push_cast; ring

/-- Weighted pair count `Σ_{n₁ ≤ N₁, n₂ ≤ N₂, n₁ n₂ ≡ a} c₁(n₁) c₂(n₂)`. -/
noncomputable def wpair (m : ℕ) (a : ZMod m) (c₁ c₂ : ℕ → ℝ) (N₁ N₂ : ℕ) : ℝ :=
  ∑ n₁ ∈ Iic N₁, ∑ n₂ ∈ Iic N₂,
    if ((n₁ : ZMod m) * (n₂ : ZMod m) = a) then c₁ n₁ * c₂ n₂ else 0

/-- Orthogonality (D1): `φ(m) R(a) = Σ_χ χ(a⁻¹) S₁(χ) S₂(χ)`. -/
lemma totient_mul_wpair (m : ℕ) [NeZero m] {a : ZMod m} (ha : IsUnit a) (c₁ c₂ : ℕ → ℝ)
    (N₁ N₂ : ℕ) :
    (m.totient : ℂ) * (wpair m a c₁ c₂ N₁ N₂ : ℂ) =
      ∑ χ : DirichletCharacter ℂ m, χ a⁻¹ * (wsum c₁ N₁ χ * wsum c₂ N₂ χ) := by
  have h : ∀ χ : DirichletCharacter ℂ m, wsum c₁ N₁ χ * wsum c₂ N₂ χ =
      ∑ n₁ ∈ Iic N₁, ∑ n₂ ∈ Iic N₂,
        ((c₁ n₁ : ℂ) * c₂ n₂) * χ ((n₁ : ZMod m) * (n₂ : ZMod m)) := by
    intro χ
    rw [wsum, wsum, sum_mul_sum]
    refine sum_congr rfl fun n₁ _ ↦ sum_congr rfl fun n₂ _ ↦ ?_
    rw [map_mul]; ring
  simp_rw [h, mul_sum]
  rw [sum_comm, wpair]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun n₁ _ ↦ ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun n₂ _ ↦ ?_
  have : ∀ χ : DirichletCharacter ℂ m,
      χ a⁻¹ * ((c₁ n₁ : ℂ) * c₂ n₂ * χ ((n₁ : ZMod m) * (n₂ : ZMod m))) =
        ((c₁ n₁ : ℂ) * c₂ n₂) * (χ a⁻¹ * χ ((n₁ : ZMod m) * (n₂ : ZMod m))) := fun χ ↦ by ring
  simp_rw [this, ← mul_sum, DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
  split_ifs with h1 h2 h2
  · push_cast; ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

/-- Orthogonality in the form `Σ_χ χ(b) conj(χ(b')) = φ(m) [b' unit, b = b']`. -/
lemma sum_char_mul_star (m : ℕ) [NeZero m] (b b' : ZMod m) :
    ∑ χ : DirichletCharacter ℂ m, χ b * star (χ b') =
      if IsUnit b' ∧ b' = b then (m.totient : ℂ) else 0 := by
  by_cases hu : IsUnit b'
  · have hk : ∀ χ : DirichletCharacter ℂ m, star (χ b') = χ b'⁻¹ := by
      intro χ
      rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
      symm
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← map_mul, (ZMod.inv_mul_eq_one_of_isUnit hu b').mpr rfl, map_one]
    have hc : ∀ χ : DirichletCharacter ℂ m, χ b * χ b'⁻¹ = χ b'⁻¹ * χ b := fun χ ↦ mul_comm _ _
    simp_rw [hk, hc, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu]
    simp [hu]
  · simp [MulChar.map_nonunit _ hu, hu]

/-- Parseval for short sums (D4(a)): if `N < m`, distinct `n ≤ N` are distinct residues, so
`Σ_χ |Σ_{n ≤ N} c(n) χ(n)|² ≤ φ(m) Σ_{n ≤ N} c(n)²`. -/
lemma sum_norm_sq_wsum_le (m : ℕ) [NeZero m] (c : ℕ → ℝ) (N : ℕ) (hN : N < m) :
    ∑ χ : DirichletCharacter ℂ m, ‖wsum c N χ‖ ^ 2 ≤ m.totient * ∑ n ∈ Iic N, c n ^ 2 := by
  have key : ((∑ χ : DirichletCharacter ℂ m, ‖wsum c N χ‖ ^ 2 : ℝ) : ℂ) =
      ((m.totient * ∑ n ∈ Iic N, (if IsUnit (n : ZMod m) then c n ^ 2 else 0) : ℝ) : ℂ) := by
    push_cast
    simp_rw [← Complex.mul_conj']
    have h1 : ∀ χ : DirichletCharacter ℂ m,
        wsum c N χ * (starRingEnd ℂ) (wsum c N χ) =
          ∑ n ∈ Iic N, ∑ n' ∈ Iic N, ((c n : ℂ) * c n') * (χ n * star (χ n')) := by
      intro χ
      rw [wsum, map_sum, sum_mul_sum]
      refine sum_congr rfl fun n _ ↦ sum_congr rfl fun n' _ ↦ ?_
      rw [map_mul, Complex.conj_ofReal]
      simp only [RCLike.star_def]
      ring
    simp_rw [h1]
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun n hn ↦ ?_
    rw [sum_comm]
    simp_rw [← mul_sum, sum_char_mul_star]
    rw [sum_eq_single n]
    · split_ifs with h2 h3 h3
      · push_cast; ring
      · exact absurd h2.1 h3
      · exact absurd ⟨h3, rfl⟩ h2
      · simp
    · intro n' hn' hne
      have : ¬ (IsUnit (n' : ZMod m) ∧ (n' : ZMod m) = n) := by
        rintro ⟨-, h⟩
        rw [ZMod.natCast_eq_natCast_iff'] at h
        rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (mem_Iic.mp hn') hN),
          Nat.mod_eq_of_lt (lt_of_le_of_lt (mem_Iic.mp hn) hN)] at h
        exact hne h
      simp [this]
    · intro h; exact absurd hn h
  have key' := Complex.ofReal_injective key
  rw [key']
  gcongr with n _
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

/-! ### Existence from a positive weighted count -/

lemma sum_badPart_le' (m : ℕ) [NeZero m] {a : ZMod m} (ha : IsUnit a) {x₁ x₂ : ℝ}
    (hx₁ : 1 ≤ x₁) (hx₂ : 1 ≤ x₂) :
    ∑ n₁ ∈ Iic ⌊x₁⌋₊, ∑ n₂ ∈ Iic ⌊x₂⌋₊, badPart m a n₁ n₂
      ≤ (2 * Real.sqrt x₁ * Real.log x₁) * ((x₂ / m + 1) * Real.log x₂) := by
  have hB : 0 ≤ (x₂ / m + 1) * Real.log x₂ := by
    have : 0 ≤ Real.log x₂ := Real.log_nonneg hx₂
    positivity
  calc ∑ n₁ ∈ Iic ⌊x₁⌋₊, ∑ n₂ ∈ Iic ⌊x₂⌋₊, badPart m a n₁ n₂
      ≤ ∑ n₁ ∈ Iic ⌊x₁⌋₊, (if ¬ n₁.Prime then Λ n₁ * ((x₂ / m + 1) * Real.log x₂) else 0) := by
        refine sum_le_sum fun n₁ _ ↦ ?_
        by_cases hp : n₁.Prime
        · simp [badPart, hp]
        · simp only [badPart, hp, not_false_eq_true, ite_true]
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (inner_le m ha n₁ hx₂) vonMangoldt_nonneg
    _ = (∑ n ∈ (Iic ⌊x₁⌋₊).filter (fun n ↦ ¬ n.Prime), Λ n) * ((x₂ / m + 1) * Real.log x₂) := by
        rw [sum_filter, sum_mul]
        refine sum_congr rfl fun n _ ↦ ?_
        split_ifs <;> simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_nonprime_le hx₁) hB

/-- If no pair of primes `p ≤ x₁`, `q ≤ x₂` has `pq ≡ a`, then a weighted pair count with
weights `0 ≤ cᵢ ≤ Λ` is small: only pairs involving a prime power `p^k`, `k ≥ 2`, contribute. -/
lemma wpair_le_of_not_exists (m : ℕ) [NeZero m] {a : ZMod m} (ha : IsUnit a) {c₁ c₂ : ℕ → ℝ}
    {x₁ x₂ : ℝ} (hx₁ : 1 ≤ x₁) (hx₂ : 1 ≤ x₂)
    (hc₁ : ∀ n ∈ Iic ⌊x₁⌋₊, 0 ≤ c₁ n ∧ c₁ n ≤ Λ n)
    (hc₂ : ∀ n ∈ Iic ⌊x₂⌋₊, 0 ≤ c₂ n ∧ c₂ n ≤ Λ n)
    (hno : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (p : ℝ) ≤ x₁ ∧ (q : ℝ) ≤ x₂ ∧
      ((p * q : ℕ) : ZMod m) = a) :
    wpair m a c₁ c₂ ⌊x₁⌋₊ ⌊x₂⌋₊ ≤
      (2 * Real.sqrt x₁ * Real.log x₁) * ((x₂ / m + 1) * Real.log x₂)
        + (2 * Real.sqrt x₂ * Real.log x₂) * ((x₁ / m + 1) * Real.log x₁) := by
  have hle₁ : ∀ n ∈ Iic ⌊x₁⌋₊, (n : ℝ) ≤ x₁ := fun n hn ↦
    (Nat.cast_le.mpr (mem_Iic.mp hn)).trans (Nat.floor_le (by linarith))
  have hle₂ : ∀ n ∈ Iic ⌊x₂⌋₊, (n : ℝ) ≤ x₂ := fun n hn ↦
    (Nat.cast_le.mpr (mem_Iic.mp hn)).trans (Nat.floor_le (by linarith))
  have hpt : ∀ n₁ ∈ Iic ⌊x₁⌋₊, ∀ n₂ ∈ Iic ⌊x₂⌋₊,
      (if ((n₁ : ZMod m) * (n₂ : ZMod m) = a) then c₁ n₁ * c₂ n₂ else 0)
        ≤ badPart m a n₁ n₂ + badPart m a n₂ n₁ := by
    intro n₁ hn₁ n₂ hn₂
    have h1 := badPart_nonneg m a n₁ n₂
    have h2 := badPart_nonneg m a n₂ n₁
    obtain ⟨c10, c11⟩ := hc₁ n₁ hn₁
    obtain ⟨c20, c21⟩ := hc₂ n₂ hn₂
    have hcc : c₁ n₁ * c₂ n₂ ≤ Λ n₁ * Λ n₂ := mul_le_mul c11 c21 c20 vonMangoldt_nonneg
    split_ifs with hc
    · by_cases hp₁ : n₁.Prime
      · by_cases hp₂ : n₂.Prime
        · exact absurd ⟨n₁, n₂, hp₁, hp₂, hle₁ n₁ hn₁, hle₂ n₂ hn₂, by push_cast; exact hc⟩ hno
        · have : badPart m a n₂ n₁ = Λ n₁ * Λ n₂ := by
            unfold badPart
            rw [mul_comm (n₂ : ZMod m)]
            simp [hp₂, hc, mul_comm]
          linarith
      · have : badPart m a n₁ n₂ = Λ n₁ * Λ n₂ := by
          unfold badPart
          simp [hp₁, hc]
        linarith
    · linarith
  calc wpair m a c₁ c₂ ⌊x₁⌋₊ ⌊x₂⌋₊
      ≤ ∑ n₁ ∈ Iic ⌊x₁⌋₊, ∑ n₂ ∈ Iic ⌊x₂⌋₊, (badPart m a n₁ n₂ + badPart m a n₂ n₁) :=
        sum_le_sum fun n₁ hn₁ ↦ sum_le_sum fun n₂ hn₂ ↦ hpt n₁ hn₁ n₂ hn₂
    _ = ∑ n₁ ∈ Iic ⌊x₁⌋₊, ∑ n₂ ∈ Iic ⌊x₂⌋₊, badPart m a n₁ n₂
        + ∑ n₂ ∈ Iic ⌊x₂⌋₊, ∑ n₁ ∈ Iic ⌊x₁⌋₊, badPart m a n₂ n₁ := by
        simp_rw [sum_add_distrib]
        congr 1
        exact sum_comm
    _ ≤ _ := add_le_add (sum_badPart_le' m ha hx₁ hx₂) (sum_badPart_le' m ha hx₂ hx₁)

lemma wpair_nonneg (m : ℕ) (a : ZMod m) {c₁ c₂ : ℕ → ℝ} {N₁ N₂ : ℕ}
    (hc₁ : ∀ n ∈ Iic N₁, 0 ≤ c₁ n) (hc₂ : ∀ n ∈ Iic N₂, 0 ≤ c₂ n) :
    0 ≤ wpair m a c₁ c₂ N₁ N₂ := by
  unfold wpair
  refine sum_nonneg fun n₁ hn₁ ↦ sum_nonneg fun n₂ hn₂ ↦ ?_
  split_ifs
  · exact mul_nonneg (hc₁ n₁ hn₁) (hc₂ n₂ hn₂)
  · exact le_rfl

lemma cw_bounds {x : ℝ} (hx : 0 < x) : ∀ n ∈ Iic ⌊x⌋₊, 0 ≤ cw x n ∧ cw x n ≤ Λ n := by
  intro n hn
  have hnx : (n : ℝ) ≤ x := (Nat.cast_le.mpr (mem_Iic.mp hn)).trans (Nat.floor_le hx.le)
  have h0 : 0 ≤ 1 - (n : ℝ) / x := by
    rw [sub_nonneg, div_le_one hx]; exact hnx
  have h1 : 1 - (n : ℝ) / x ≤ 1 := by
    have : 0 ≤ (n : ℝ) / x := by positivity
    linarith
  refine ⟨mul_nonneg vonMangoldt_nonneg h0, ?_⟩
  calc cw x n = Λ n * (1 - n / x) := rfl
    _ ≤ Λ n * 1 := mul_le_mul_of_nonneg_left h1 vonMangoldt_nonneg
    _ = Λ n := mul_one _

/-! ### The lower bound from the principal character -/

lemma card_chars (m : ℕ) [NeZero m] :
    (univ : Finset (DirichletCharacter ℂ m)).card = m.totient := by
  rw [card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

lemma norm_sum_char_ge (m : ℕ) [NeZero m] {a : ZMod m} (ha : IsUnit a)
    (F : DirichletCharacter ℂ m → ℂ) :
    ‖F 1‖ - ∑ χ ∈ univ.erase 1, ‖F χ‖ ≤ ‖∑ χ : DirichletCharacter ℂ m, χ a⁻¹ * F χ‖ := by
  have hainv : IsUnit a⁻¹ :=
    IsUnit.of_mul_eq_one a ((ZMod.inv_mul_eq_one_of_isUnit ha a).mpr rfl)
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (DirichletCharacter ℂ m))
    (fun χ ↦ χ a⁻¹ * F χ) (Finset.mem_univ 1)
  simp only [MulChar.one_apply hainv, one_mul] at hsplit
  rw [← hsplit]
  have hrest : ‖∑ χ ∈ univ.erase 1, χ a⁻¹ * F χ‖ ≤ ∑ χ ∈ univ.erase 1, ‖F χ‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun χ _ ↦ ?_)
    rw [norm_mul]
    calc ‖χ a⁻¹‖ * ‖F χ‖ ≤ 1 * ‖F χ‖ := by
          gcongr; exact DirichletCharacter.norm_le_one χ _
      _ = ‖F χ‖ := one_mul _
  have := norm_sub_norm_le (F 1) (-(∑ χ ∈ univ.erase 1, χ a⁻¹ * F χ))
  rw [norm_neg, sub_neg_eq_add] at this
  linarith

/-- **Covering criterion (D7).** With `S_i(χ) = ψ̃(xᵢ, χ)`: if the principal term `A` beats the
non-principal terms `B` plus `m` times the prime-power bound, then every unit `a` is `pq` with
primes `p ≤ x₁`, `q ≤ x₂`. -/
lemma exists_of_criterion (m : ℕ) [NeZero m] {a : ZMod m} (ha : IsUnit a) {x₁ x₂ A B : ℝ}
    (hx₁ : 1 ≤ x₁) (hx₂ : 1 ≤ x₂)
    (hA : A ≤ ‖psiCesaro (1 : DirichletCharacter ℂ m) x₁ *
      psiCesaro (1 : DirichletCharacter ℂ m) x₂‖)
    (hB : ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ m),
        ‖psiCesaro χ x₁ * psiCesaro χ x₂‖ ≤ B)
    (hineq : B + m * ((2 * Real.sqrt x₁ * Real.log x₁) * ((x₂ / m + 1) * Real.log x₂)
        + (2 * Real.sqrt x₂ * Real.log x₂) * ((x₁ / m + 1) * Real.log x₁)) < A) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (p : ℝ) ≤ x₁ ∧ (q : ℝ) ≤ x₂ ∧
      ((p * q : ℕ) : ZMod m) = a := by
  by_contra hno
  set U := (2 * Real.sqrt x₁ * Real.log x₁) * ((x₂ / m + 1) * Real.log x₂)
        + (2 * Real.sqrt x₂ * Real.log x₂) * ((x₁ / m + 1) * Real.log x₁) with hU
  have hc₁ := cw_bounds (x := x₁) (by linarith)
  have hc₂ := cw_bounds (x := x₂) (by linarith)
  have hW := wpair_le_of_not_exists m ha hx₁ hx₂ hc₁ hc₂ hno
  rw [← hU] at hW
  have hW0 := wpair_nonneg m a (fun n hn ↦ (hc₁ n hn).1) (fun n hn ↦ (hc₂ n hn).1)
  set W := wpair m a (cw x₁) (cw x₂) ⌊x₁⌋₊ ⌊x₂⌋₊ with hWdef
  have hlow := norm_sum_char_ge m ha (fun χ ↦ psiCesaro χ x₁ * psiCesaro χ x₂)
  simp_rw [psiCesaro_eq_wsum] at hlow
  rw [← totient_mul_wpair m ha] at hlow
  simp_rw [← psiCesaro_eq_wsum] at hlow
  have hnorm : ‖(m.totient : ℂ) * (W : ℂ)‖ = m.totient * W := by
    rw [norm_mul, Complex.norm_real, Complex.norm_natCast, Real.norm_of_nonneg hW0]
  rw [hnorm] at hlow
  have hU0 : 0 ≤ U := hW0.trans hW
  have hφ : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have h1 : (m.totient : ℝ) * W ≤ m.totient * U :=
    mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg _)
  have h2 : (m.totient : ℝ) * U ≤ m * U := mul_le_mul_of_nonneg_right hφ hU0
  linarith

/-! ### Real-variable estimates -/

lemma log_pow_eight_le {y : ℝ} (hy : 1 ≤ y) : Real.log y ^ 8 ≤ 8 ^ 8 * y := by
  have hy0 : 0 ≤ y := by linarith
  have h := Real.log_le_rpow_div hy0 (by norm_num : (0 : ℝ) < 1 / 8)
  have hr : (y ^ (1 / 8 : ℝ)) ^ 8 = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
  have h8 : Real.log y ≤ 8 * y ^ (1 / 8 : ℝ) := by
    have : y ^ (1 / 8 : ℝ) / (1 / 8) = 8 * y ^ (1 / 8 : ℝ) := by ring
    linarith
  calc Real.log y ^ 8 ≤ (8 * y ^ (1 / 8 : ℝ)) ^ 8 := pow_le_pow_left₀ (Real.log_nonneg hy) h8 8
    _ = 8 ^ 8 * y := by rw [mul_pow, hr]

lemma log_large {y : ℝ} (hy : (2 : ℝ) ^ 80 ≤ y) :
    1 ≤ Real.log y ∧ 2 ^ 28 * Real.log y ^ 4 ≤ y ∧ Real.log 2 ≤ Real.log y := by
  have hy1 : (1 : ℝ) ≤ y := le_trans (by norm_num) hy
  have hy0 : 0 < y := by linarith
  have hL1 : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]
    have := Real.exp_one_lt_d9
    have : (2.7182818286 : ℝ) ≤ 2 ^ 80 := by norm_num
    linarith
  refine ⟨hL1, ?_, ?_⟩
  · have h8 := log_pow_eight_le hy1
    have hsq : (2 ^ 28 * Real.log y ^ 4) ^ 2 ≤ y ^ 2 := by
      calc (2 ^ 28 * Real.log y ^ 4) ^ 2 = 2 ^ 56 * Real.log y ^ 8 := by ring
        _ ≤ 2 ^ 56 * (8 ^ 8 * y) := by gcongr
        _ = 2 ^ 80 * y := by norm_num; ring
        _ ≤ y * y := by gcongr
        _ = y ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) hy0.le two_ne_zero).mp hsq
  · exact Real.log_le_log (by norm_num) (le_trans (by norm_num) hy)

lemma log_two_mul_le {y : ℝ} (hy : (2 : ℝ) ^ 80 ≤ y) : Real.log (2 * y) ≤ 2 * Real.log y := by
  obtain ⟨hL1, -, hL2⟩ := log_large hy
  rw [Real.log_mul (by norm_num) (by linarith)]
  linarith

/-- The real-variable estimates for Theorem S, `x = K m (log m)²`. -/
lemma analytic_S {C K : ℝ} (hC0 : 0 < C) (hK1 : 1 ≤ K) (hKC : 256 * C ^ 2 ≤ K) (m : ℕ)
    (hm : (2 : ℝ) ^ 80 ≤ m) (hmK : K ≤ m) (x : ℝ) (hx : x = K * m * Real.log m ^ 2) :
    1 ≤ x ∧ C * Real.sqrt x * Real.log (2 * m) ≤ x / 2 ∧
      m * (C * Real.sqrt x * Real.log (2 * m)) ^ 2
        + m * ((2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x)
          + (2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x))
      < (x / 2 - C * Real.sqrt x * Real.log (2 * m)) ^ 2 := by
  obtain ⟨hL1, hL4, -⟩ := log_large hm
  have hl2m := log_two_mul_le hm
  set L := Real.log m with hLdef
  have hm0 : (0 : ℝ) < m := by linarith [show (0 : ℝ) < 2 ^ 80 by norm_num]
  have hm1 : (1 : ℝ) ≤ m := by linarith [show (1 : ℝ) ≤ 2 ^ 80 by norm_num]
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hL24 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL4m : L ^ 4 ≤ m := by nlinarith
  have hxm : (m : ℝ) ≤ x := by
    rw [hx]
    calc (m : ℝ) = 1 * m * 1 := by ring
      _ ≤ K * m * L ^ 2 := by gcongr
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxm4 : x ≤ (m : ℝ) ^ 4 := by
    rw [hx]
    calc K * m * L ^ 2 ≤ m * m * m := by gcongr; linarith
      _ ≤ m * m * m * m := le_mul_of_one_le_right (by positivity) hm1
      _ = (m : ℝ) ^ 4 := by ring
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlx : Real.log x ≤ 4 * L := by
    calc Real.log x ≤ Real.log ((m : ℝ) ^ 4) := Real.log_le_log hx0 hxm4
      _ = 4 * L := by rw [Real.log_pow]; push_cast; ring
  set s := Real.sqrt x with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg x
  have hss : s ^ 2 = x := Real.sq_sqrt hx0.le
  set E := C * s * Real.log (2 * m) with hEdef
  have hl2m0 : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ E := by positivity
  have hE2 : E ≤ 2 * C * s * L := by
    rw [hEdef]
    calc C * s * Real.log (2 * m) ≤ C * s * (2 * L) := by gcongr
      _ = 2 * C * s * L := by ring
  have hmE : m * E ^ 2 ≤ x ^ 2 / 64 := by
    have h1 : E ^ 2 ≤ (2 * C * s * L) ^ 2 := pow_le_pow_left₀ hE0 hE2 2
    have h2 : (m : ℝ) * (2 * C * s * L) ^ 2 = 4 * C ^ 2 * x * (m * L ^ 2) := by
      rw [← hss]; ring
    have h3 : x ^ 2 = K * x * (m * L ^ 2) := by rw [sq]; nth_rw 2 [hx]; ring
    have h4 : 0 ≤ x * (m * L ^ 2) := by positivity
    calc m * E ^ 2 ≤ m * (2 * C * s * L) ^ 2 := by gcongr
      _ = 4 * C ^ 2 * x * (m * L ^ 2) := h2
      _ ≤ (K / 64) * x * (m * L ^ 2) := by gcongr; linarith
      _ = x ^ 2 / 64 := by rw [h3]; ring
  have hEx : E ≤ x / 8 := by
    have : E ^ 2 ≤ (x / 8) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hE0 (by positivity) two_ne_zero).mp this
  have hsL : 2048 * L ^ 2 ≤ s := by
    have : (2048 * L ^ 2) ^ 2 ≤ s ^ 2 := by
      rw [hss]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hs0 two_ne_zero).mp this
  have hU : (m : ℝ) * ((2 * s * Real.log x) * ((x / m + 1) * Real.log x)
          + (2 * s * Real.log x) * ((x / m + 1) * Real.log x)) ≤ x ^ 2 / 16 := by
    have hA : (m : ℝ) * ((2 * s * Real.log x) * ((x / m + 1) * Real.log x)
          + (2 * s * Real.log x) * ((x / m + 1) * Real.log x))
        = 4 * s * Real.log x ^ 2 * (x + m) := by
      field_simp; ring
    have hlx2 : Real.log x ^ 2 ≤ 16 * L ^ 2 := by nlinarith
    rw [hA]
    calc 4 * s * Real.log x ^ 2 * (x + m) ≤ 4 * s * (16 * L ^ 2) * (2 * x) := by
          gcongr; linarith
      _ = x * (128 * (L ^ 2 * s)) := by ring
      _ ≤ x * (128 * (s * s / 2048)) := by
          gcongr
          rw [le_div_iff₀ (by norm_num)]
          nlinarith
      _ = x ^ 2 / 16 := by rw [← hss]; ring
  refine ⟨hx1, by linarith, ?_⟩
  have h38 : 3 * x / 8 ≤ x / 2 - E := by linarith
  have h964 : (3 * x / 8) ^ 2 ≤ (x / 2 - E) ^ 2 := pow_le_pow_left₀ (by positivity) h38 2
  have hx2 : 0 < x ^ 2 := by positivity
  nlinarith

/-! ### Theorem S -/

/-- **Theorem S (notes §3), conditional on `GRHSmoothBound`.** Every unit mod `m` is a product of
two primes `p, q ≤ K m (log m)²`, for all large `m`. -/
theorem coveredBy_log_sq (h : GRHSmoothBound) :
    ∃ K m₀ : ℝ, 0 < K ∧ ∀ m : ℕ, (m : ℝ) ≥ m₀ → CoveredBy m (K * m * (Real.log m) ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := h.bounds
  refine ⟨256 * C ^ 2 + 1, max (2 ^ 80) (256 * C ^ 2 + 1), by positivity, ?_⟩
  intro m hm
  have hm1 : (2 : ℝ) ^ 80 ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : 256 * C ^ 2 + 1 ≤ (m : ℝ) := le_trans (le_max_right _ _) hm
  have hm0 : (0 : ℝ) < m := by linarith [show (0 : ℝ) < 2 ^ 80 by norm_num]
  have hmpos : 0 < m := by exact_mod_cast hm0
  have : NeZero m := ⟨hmpos.ne'⟩
  set x := (256 * C ^ 2 + 1) * m * Real.log m ^ 2 with hxdef
  obtain ⟨hx1, hEx, hineq⟩ :=
    analytic_S hC0 (by nlinarith [sq_nonneg C]) (by linarith) m hm1 hm2 x rfl
  set E := C * Real.sqrt x * Real.log (2 * m) with hE
  intro a ha
  obtain ⟨hprin, hnon⟩ := hC m x hx1
  have hA : (x / 2 - E) ^ 2 ≤ ‖psiCesaro (1 : DirichletCharacter ℂ m) x *
      psiCesaro (1 : DirichletCharacter ℂ m) x‖ := by
    rw [norm_mul, ← sq]; exact pow_le_pow_left₀ (by linarith) hprin 2
  have hB : ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ m),
      ‖psiCesaro χ x * psiCesaro χ x‖ ≤ m * E ^ 2 := by
    calc _ ≤ ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ m), E ^ 2 := by
          refine sum_le_sum fun χ hχ ↦ ?_
          rw [norm_mul, ← sq]
          exact pow_le_pow_left₀ (norm_nonneg _) (hnon χ (ne_of_mem_erase hχ)) 2
      _ = ((univ.erase (1 : DirichletCharacter ℂ m)).card : ℝ) * E ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ m * E ^ 2 := by
          gcongr
          have := (card_erase_le (s := (univ : Finset (DirichletCharacter ℂ m))) (a := 1)).trans
            ((card_chars m).le.trans (Nat.totient_le m))
          exact_mod_cast this
  exact exists_of_criterion m ha hx1 hx1 hA hB (by linarith [hineq])

/-! ### Corollary A1 -/

lemma sum_cw_sq_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Iic ⌊x⌋₊, cw x n ^ 2 ≤ (Real.log 4 + 4) * x * Real.log x := by
  have hc := cw_bounds (x := x) (by linarith)
  have hpsi : ∑ n ∈ Iic ⌊x⌋₊, Λ n = Chebyshev.psi x := by
    rw [Chebyshev.psi]
    symm
    refine sum_subset (fun n hn ↦ ?_) (fun n hn hn' ↦ ?_)
    · simp only [mem_Ioc, mem_Iic] at hn ⊢; exact hn.2
    · simp only [mem_Ioc, mem_Iic, not_and] at hn hn'
      have : n = 0 := by
        by_contra h0
        exact absurd hn (hn' (Nat.pos_of_ne_zero h0))
      simp [this]
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  calc ∑ n ∈ Iic ⌊x⌋₊, cw x n ^ 2 ≤ ∑ n ∈ Iic ⌊x⌋₊, Real.log x * Λ n := by
        refine sum_le_sum fun n hn ↦ ?_
        obtain ⟨h0, h1⟩ := hc n hn
        have hΛ := vonMangoldt_le_log_of_le hx hn
        rw [sq]
        calc cw x n * cw x n ≤ Λ n * Λ n := mul_le_mul h1 h1 h0 vonMangoldt_nonneg
          _ ≤ Real.log x * Λ n := mul_le_mul_of_nonneg_right hΛ vonMangoldt_nonneg
    _ = Real.log x * Chebyshev.psi x := by rw [← mul_sum, hpsi]
    _ ≤ Real.log x * ((Real.log 4 + 4) * x) :=
        mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self (by linarith)) hlog
    _ = (Real.log 4 + 4) * x * Real.log x := by ring

/-- The real-variable estimates for Corollary A1, `x₁ = K m (log m)³`, `x₂ = m - 1`. -/
lemma analytic_A {C K : ℝ} (hC0 : 0 < C) (hK1 : 1 ≤ K) (hKC : 7 * 65536 * C ^ 2 ≤ K) (m : ℕ)
    (hm : (2 : ℝ) ^ 80 ≤ m) (hmK : K ^ 2 ≤ m) (x₁ x₂ Y : ℝ)
    (hx₁ : x₁ = K * m * Real.log m ^ 3) (hx₂ : x₂ = m - 1) (hY0 : 0 ≤ Y)
    (hY : Y ^ 2 ≤ 7 * m ^ 3 * Real.log m) :
    1 ≤ x₁ ∧ 1 ≤ x₂ ∧ C * Real.sqrt x₁ * Real.log (2 * m) ≤ x₁ / 2 ∧
      C * Real.sqrt x₂ * Real.log (2 * m) ≤ x₂ / 2 ∧
      C * Real.sqrt x₁ * Real.log (2 * m) * Y
        + m * ((2 * Real.sqrt x₁ * Real.log x₁) * ((x₂ / m + 1) * Real.log x₂)
          + (2 * Real.sqrt x₂ * Real.log x₂) * ((x₁ / m + 1) * Real.log x₁))
      < (x₁ / 2 - C * Real.sqrt x₁ * Real.log (2 * m)) *
          (x₂ / 2 - C * Real.sqrt x₂ * Real.log (2 * m)) := by
  obtain ⟨hL1, hL4, -⟩ := log_large hm
  have hl2m := log_two_mul_le hm
  set L := Real.log m with hLdef
  have hm0 : (0 : ℝ) < m := by linarith [show (0 : ℝ) < 2 ^ 80 by norm_num]
  have hm4 : (4 : ℝ) ≤ m := by linarith [show (4 : ℝ) ≤ 2 ^ 80 by norm_num]
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hL12 : L ≤ L ^ 2 := by nlinarith
  have hL23 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL34 : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have hL4m : L ^ 4 ≤ m := by nlinarith
  have hKm : K ≤ m := by nlinarith
  -- sizes of x₁, x₂
  have hx₁m : (m : ℝ) ≤ x₁ := by
    rw [hx₁]
    calc (m : ℝ) = 1 * m * 1 := by ring
      _ ≤ K * m * L ^ 3 := by gcongr
  have hx₁0 : 0 < x₁ := by linarith
  have hx₁1 : 1 ≤ x₁ := by linarith
  have hx₁m4 : x₁ ≤ (m : ℝ) ^ 4 := by
    rw [hx₁]
    calc K * m * L ^ 3 ≤ m * m * m := by gcongr; linarith
      _ ≤ m * m * m * m := le_mul_of_one_le_right (by positivity) hm1
      _ = (m : ℝ) ^ 4 := by ring
  have hlx₁0 : 0 ≤ Real.log x₁ := Real.log_nonneg hx₁1
  have hlx₁ : Real.log x₁ ≤ 4 * L := by
    calc Real.log x₁ ≤ Real.log ((m : ℝ) ^ 4) := Real.log_le_log hx₁0 hx₁m4
      _ = 4 * L := by rw [Real.log_pow]; push_cast; ring
  have hx₂1 : 1 ≤ x₂ := by rw [hx₂]; linarith
  have hx₂0 : 0 < x₂ := by linarith
  have hx₂m : x₂ ≤ m := by rw [hx₂]; linarith
  have hlx₂0 : 0 ≤ Real.log x₂ := Real.log_nonneg hx₂1
  have hlx₂ : Real.log x₂ ≤ L := Real.log_le_log hx₂0 hx₂m
  set s₁ := Real.sqrt x₁ with hs₁
  set s₂ := Real.sqrt x₂ with hs₂
  have hs₁0 : 0 ≤ s₁ := Real.sqrt_nonneg _
  have hs₂0 : 0 ≤ s₂ := Real.sqrt_nonneg _
  have hss₁ : s₁ ^ 2 = x₁ := Real.sq_sqrt hx₁0.le
  have hss₂ : s₂ ^ 2 = x₂ := Real.sq_sqrt hx₂0.le
  have hl2m0 : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
  set E₁ := C * s₁ * Real.log (2 * m) with hE₁
  set E₂ := C * s₂ * Real.log (2 * m) with hE₂
  have hE₁0 : 0 ≤ E₁ := by positivity
  have hE₁L : E₁ ≤ 2 * C * s₁ * L := by
    calc C * s₁ * Real.log (2 * m) ≤ C * s₁ * (2 * L) := by gcongr
      _ = 2 * C * s₁ * L := by ring
  have hE₂L : E₂ ≤ 2 * C * s₂ * L := by
    calc C * s₂ * Real.log (2 * m) ≤ C * s₂ * (2 * L) := by gcongr
      _ = 2 * C * s₂ * L := by ring
  -- E₁ ≤ x₁ / 4
  have h8CL : 8 * C * L ≤ s₁ := by
    have : (8 * C * L) ^ 2 ≤ s₁ ^ 2 := by
      rw [hss₁, hx₁]
      calc (8 * C * L) ^ 2 = (64 * C ^ 2) * L ^ 2 := by ring
        _ ≤ K * (m * L ^ 3) := by
            gcongr
            · linarith
            · nlinarith
        _ = K * m * L ^ 3 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) hs₁0 two_ne_zero).mp this
  have hE₁x : E₁ ≤ x₁ / 4 := by
    calc E₁ ≤ 2 * C * s₁ * L := hE₁L
      _ = (8 * C * L) * s₁ / 4 := by ring
      _ ≤ s₁ * s₁ / 4 := by gcongr
      _ = x₁ / 4 := by rw [← hss₁]; ring
  -- E₂ ≤ m / 4
  have hKL : K * L ^ 2 ≤ m := by
    have : (K * L ^ 2) ^ 2 ≤ (m : ℝ) ^ 2 := by
      calc (K * L ^ 2) ^ 2 = K ^ 2 * L ^ 4 := by ring
        _ ≤ (m : ℝ) * m := by gcongr
        _ = (m : ℝ) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) hm0.le two_ne_zero).mp this
  have h8CsL : 8 * C * s₂ * L ≤ m := by
    have : (8 * C * s₂ * L) ^ 2 ≤ (m : ℝ) ^ 2 := by
      calc (8 * C * s₂ * L) ^ 2 = (64 * C ^ 2) * s₂ ^ 2 * L ^ 2 := by ring
        _ ≤ K * m * L ^ 2 := by
            rw [hss₂]; gcongr; linarith
        _ = m * (K * L ^ 2) := by ring
        _ ≤ (m : ℝ) * m := by gcongr
        _ = (m : ℝ) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) hm0.le two_ne_zero).mp this
  have hE₂m : E₂ ≤ m / 4 := by linarith
  -- the main term
  have hA1 : x₁ / 4 ≤ x₁ / 2 - E₁ := by linarith
  have hA2 : (m : ℝ) / 8 ≤ x₂ / 2 - E₂ := by rw [hx₂] at *; linarith
  have hA : x₁ * m / 32 ≤ (x₁ / 2 - E₁) * (x₂ / 2 - E₂) := by
    calc x₁ * m / 32 = (x₁ / 4) * (m / 8) := by ring
      _ ≤ (x₁ / 2 - E₁) * (x₂ / 2 - E₂) :=
          mul_le_mul hA1 hA2 (by positivity) (by linarith)
  -- the prime-power terms
  have h2048a : 2048 * L ^ 2 ≤ s₁ := by
    have : (2048 * L ^ 2) ^ 2 ≤ s₁ ^ 2 := by
      rw [hss₁]
      calc (2048 * L ^ 2) ^ 2 = 2 ^ 22 * L ^ 4 := by ring
        _ ≤ 2 ^ 28 * L ^ 4 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ ≤ x₁ := by linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hs₁0 two_ne_zero).mp this
  have h2048b : 2048 * s₂ * L ^ 2 ≤ m := by
    have : (2048 * s₂ * L ^ 2) ^ 2 ≤ (m : ℝ) ^ 2 := by
      calc (2048 * s₂ * L ^ 2) ^ 2 = s₂ ^ 2 * (2 ^ 22 * L ^ 4) := by ring
        _ ≤ (m : ℝ) * m := by
            rw [hss₂]
            gcongr
            calc (2 : ℝ) ^ 22 * L ^ 4 ≤ 2 ^ 28 * L ^ 4 :=
                  mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
              _ ≤ (m : ℝ) := hL4
        _ = (m : ℝ) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) hm0.le two_ne_zero).mp this
  have hU1 : (m : ℝ) * ((2 * s₁ * Real.log x₁) * ((x₂ / m + 1) * Real.log x₂))
      ≤ x₁ * m / 128 := by
    have hq : x₂ / m + 1 ≤ 2 := by
      have : x₂ / m ≤ 1 := by rw [div_le_one hm0]; exact hx₂m
      linarith
    calc (m : ℝ) * ((2 * s₁ * Real.log x₁) * ((x₂ / m + 1) * Real.log x₂))
        ≤ m * ((2 * s₁ * (4 * L)) * (2 * L)) := by gcongr
      _ = m * s₁ * (16 * L ^ 2) := by ring
      _ ≤ m * s₁ * (s₁ / 128) := by gcongr; linarith
      _ = x₁ * m / 128 := by rw [← hss₁]; ring
  have hU2 : (m : ℝ) * ((2 * s₂ * Real.log x₂) * ((x₁ / m + 1) * Real.log x₁))
      ≤ x₁ * m / 128 := by
    have hid : (m : ℝ) * ((2 * s₂ * Real.log x₂) * ((x₁ / m + 1) * Real.log x₁))
        = 2 * s₂ * Real.log x₂ * Real.log x₁ * (x₁ + m) := by
      field_simp
    rw [hid]
    calc 2 * s₂ * Real.log x₂ * Real.log x₁ * (x₁ + m)
        ≤ 2 * s₂ * L * (4 * L) * (2 * x₁) := by gcongr; linarith
      _ = x₁ * (16 * s₂ * L ^ 2) := by ring
      _ ≤ x₁ * (m / 128) := by gcongr; linarith
      _ = x₁ * m / 128 := by ring
  -- the non-principal characters
  have hBY : 256 * C * L * Y ≤ s₁ * m := by
    have : (256 * C * L * Y) ^ 2 ≤ (s₁ * m) ^ 2 := by
      calc (256 * C * L * Y) ^ 2 = 65536 * C ^ 2 * L ^ 2 * Y ^ 2 := by ring
        _ ≤ 65536 * C ^ 2 * L ^ 2 * (7 * m ^ 3 * L) := by gcongr
        _ = (7 * 65536 * C ^ 2) * (m ^ 3 * L ^ 3) := by ring
        _ ≤ K * (m ^ 3 * L ^ 3) := by gcongr
        _ = (s₁ * m) ^ 2 := by rw [mul_pow, hss₁, hx₁]; ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp this
  have hB : E₁ * Y ≤ x₁ * m / 128 := by
    calc E₁ * Y ≤ 2 * C * s₁ * L * Y := by gcongr
      _ = (s₁ / 128) * (256 * C * L * Y) := by ring
      _ ≤ (s₁ / 128) * (s₁ * m) := by gcongr
      _ = x₁ * m / 128 := by rw [← hss₁]; ring
  refine ⟨hx₁1, hx₂1, by linarith, by linarith, ?_⟩
  have hpos : 0 < x₁ * m := by positivity
  rw [mul_add]
  linarith

/-- **Corollary A1 (notes §3), conditional on `GRHSmoothBound`.** Every unit mod `m` is `pq` with
primes `p ≤ m` and `q ≤ K m (log m)³`, for all large `m`. (In fact `p ≤ m - 1`.) -/
theorem coveredByAsym_m_log_cube (h : GRHSmoothBound) :
    ∃ K m₀ : ℝ, 0 < K ∧ ∀ m : ℕ, (m : ℝ) ≥ m₀ →
      CoveredByAsym m m (K * m * (Real.log m) ^ 3) := by
  obtain ⟨C, hC0, hC⟩ := h.bounds
  refine ⟨7 * 65536 * C ^ 2 + 1, max (2 ^ 80) ((7 * 65536 * C ^ 2 + 1) ^ 2), by positivity, ?_⟩
  intro m hm
  set K := 7 * 65536 * C ^ 2 + 1 with hK
  have hm1 : (2 : ℝ) ^ 80 ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : K ^ 2 ≤ (m : ℝ) := le_trans (le_max_right _ _) hm
  have hm0 : (0 : ℝ) < m := by linarith [show (0 : ℝ) < 2 ^ 80 by norm_num]
  have hmpos : 0 < m := by exact_mod_cast hm0
  have : NeZero m := ⟨hmpos.ne'⟩
  set x₁ := K * m * Real.log m ^ 3 with hx₁
  set x₂ : ℝ := ((m - 1 : ℕ) : ℝ) with hx₂
  have hx₂' : x₂ = m - 1 := by rw [hx₂, Nat.cast_sub (by omega), Nat.cast_one]
  have hfl : ⌊x₂⌋₊ = m - 1 := Nat.floor_natCast _
  have hx₂1 : 1 ≤ x₂ := by rw [hx₂']; linarith [show (2 : ℝ) ≤ 2 ^ 80 by norm_num]
  have hpe : ∀ χ : DirichletCharacter ℂ m, psiCesaro χ x₂ = wsum (cw x₂) (m - 1) χ :=
    fun χ ↦ by rw [psiCesaro_eq_wsum, hfl]
  -- the L¹ norm of `χ ↦ ψ̃(x₂, χ)`, bounded by Cauchy–Schwarz and Parseval
  set Y := ∑ χ : DirichletCharacter ℂ m, ‖psiCesaro χ x₂‖ with hYdef
  have hY0 : 0 ≤ Y := sum_nonneg fun _ _ ↦ norm_nonneg _
  have hY : Y ^ 2 ≤ 7 * m ^ 3 * Real.log m := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (DirichletCharacter ℂ m)))
      (f := fun χ ↦ ‖psiCesaro χ x₂‖)
    rw [card_chars] at hcs
    simp_rw [hpe] at hcs hYdef
    rw [← hYdef] at hcs
    have hpar := sum_norm_sq_wsum_le m (cw x₂) (m - 1) (by omega)
    have hsq := sum_cw_sq_le hx₂1
    rw [hfl] at hsq
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
    have hx₂m : x₂ ≤ m := by rw [hx₂']; linarith
    have hlx₂ : Real.log x₂ ≤ Real.log m := Real.log_le_log (by linarith) hx₂m
    have hlx₂0 : 0 ≤ Real.log x₂ := Real.log_nonneg hx₂1
    have hc2 : ∑ n ∈ Iic (m - 1), cw x₂ n ^ 2 ≤ 7 * (m * Real.log m) := by
      calc _ ≤ (Real.log 4 + 4) * x₂ * Real.log x₂ := hsq
        _ ≤ 7 * (x₂ * Real.log x₂) := by
            rw [mul_assoc]; gcongr; linarith
        _ ≤ 7 * (m * Real.log m) := by gcongr
    have hφ : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
    have hS0 : 0 ≤ ∑ χ : DirichletCharacter ℂ m, ‖wsum (cw x₂) (m - 1) χ‖ ^ 2 :=
      sum_nonneg fun _ _ ↦ sq_nonneg _
    have hc0 : 0 ≤ ∑ n ∈ Iic (m - 1), cw x₂ n ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
    calc Y ^ 2 ≤ m.totient * ∑ χ : DirichletCharacter ℂ m, ‖wsum (cw x₂) (m - 1) χ‖ ^ 2 := hcs
      _ ≤ m * (m.totient * ∑ n ∈ Iic (m - 1), cw x₂ n ^ 2) := by gcongr
      _ ≤ m * (m * (7 * (m * Real.log m))) := by gcongr
      _ = 7 * m ^ 3 * Real.log m := by ring
  obtain ⟨hx₁1, -, hE₁, hE₂, hineq⟩ :=
    analytic_A hC0 (by nlinarith [sq_nonneg C]) (by linarith) m hm1 hm2 x₁ x₂ Y rfl hx₂' hY0 hY
  set E₁ := C * Real.sqrt x₁ * Real.log (2 * m) with hE₁def
  set E₂ := C * Real.sqrt x₂ * Real.log (2 * m) with hE₂def
  intro a ha
  obtain ⟨hprin₁, hnon₁⟩ := hC m x₁ hx₁1
  obtain ⟨hprin₂, -⟩ := hC m x₂ hx₂1
  have hA : (x₁ / 2 - E₁) * (x₂ / 2 - E₂) ≤ ‖psiCesaro (1 : DirichletCharacter ℂ m) x₁ *
      psiCesaro (1 : DirichletCharacter ℂ m) x₂‖ := by
    rw [norm_mul]
    exact mul_le_mul hprin₁ hprin₂ (by linarith) (norm_nonneg _)
  have hB : ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ m),
      ‖psiCesaro χ x₁ * psiCesaro χ x₂‖ ≤ E₁ * Y := by
    calc _ ≤ ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ m), E₁ * ‖psiCesaro χ x₂‖ := by
          refine sum_le_sum fun χ hχ ↦ ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hnon₁ χ (ne_of_mem_erase hχ)) (norm_nonneg _)
      _ = E₁ * ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ m), ‖psiCesaro χ x₂‖ := by
          rw [mul_sum]
      _ ≤ E₁ * Y := by
          have hE₁0 : 0 ≤ E₁ := by
            have := hnon₁; have h0 := norm_nonneg (psiCesaro (1 : DirichletCharacter ℂ m) x₁)
            have : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
            positivity
          refine mul_le_mul_of_nonneg_left ?_ hE₁0
          exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ ↦ norm_nonneg _
  obtain ⟨p, q, hp, hq, hpx, hqx, hpq⟩ :=
    exists_of_criterion m ha hx₁1 hx₂1 hA hB (by linarith [hineq])
  refine ⟨q, p, hq, hp, by linarith [hx₂'], hpx, ?_⟩
  rw [Nat.mul_comm]; exact hpq

end EOS
