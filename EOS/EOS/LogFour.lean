import EOS.Statement

/-!
# EOS with `p, q ≪ m log⁴ m`, conditional on `GRHBounds`

The Erdős–Odlyzko–Sárközy (1987) argument. Fix `m`, a unit `a` mod `m`, and
`x = K m (log m)⁴`. Let `T(a) = Σ_{n₁, n₂ ≤ x, n₁ n₂ ≡ a} Λ(n₁) Λ(n₂)`.

* `totient_mul_pairSum`: orthogonality, `φ(m) T(a) = Σ_χ χ(a⁻¹) ψ(x, χ)²`.
* `lower_bound`: by `GRHBounds`, `φ(m) T(a) ≥ (x - E)² - φ(m) E²` with `E = C √x log²(mx)`.
* `upper_bound`: if no pair of primes `p, q ≤ x` has `pq ≡ a`, then the pairs involving a
  non-prime contribute everything, and `T(a) ≤ 2 (2 √x log x) (x/m + 1) log x`.
* `analytic`: these bounds are incompatible for `x = K m log⁴ m`, `K, m` large.
* `coveredBy_of_grhBounds`: the main theorem.
-/

open scoped BigOperators
open Finset ArithmeticFunction

namespace EOS

/-- The weighted count `T(a) = Σ_{n₁, n₂ ≤ N, n₁ n₂ ≡ a} Λ(n₁) Λ(n₂)`. -/
noncomputable def pairSum (m : ℕ) (a : ZMod m) (N : ℕ) : ℝ :=
  ∑ n₁ ∈ Iic N, ∑ n₂ ∈ Iic N,
    if ((n₁ : ZMod m) * (n₂ : ZMod m) = a) then Λ n₁ * Λ n₂ else 0

lemma psiChi_sq {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    psiChi χ x ^ 2 = ∑ n₁ ∈ Iic ⌊x⌋₊, ∑ n₂ ∈ Iic ⌊x⌋₊,
      ((Λ n₁ : ℂ) * Λ n₂) * χ ((n₁ : ZMod q) * (n₂ : ZMod q)) := by
  rw [psiChi, sq, sum_mul_sum]
  refine sum_congr rfl fun n₁ _ ↦ sum_congr rfl fun n₂ _ ↦ ?_
  rw [map_mul]; ring

/-- Orthogonality: `φ(m) T(a) = Σ_χ χ(a⁻¹) ψ(x, χ)²`. -/
lemma totient_mul_pairSum (m : ℕ) [NeZero m] {a : ZMod m} (ha : IsUnit a) (x : ℝ) :
    ((m.totient : ℂ) * (pairSum m a ⌊x⌋₊ : ℂ)) =
      ∑ χ : DirichletCharacter ℂ m, χ a⁻¹ * psiChi χ x ^ 2 := by
  simp_rw [psiChi_sq, mul_sum]
  rw [sum_comm]
  rw [pairSum]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun n₁ _ ↦ ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun n₂ _ ↦ ?_
  have : ∀ χ : DirichletCharacter ℂ m,
      χ a⁻¹ * ((Λ n₁ : ℂ) * Λ n₂ * χ ((n₁ : ZMod m) * (n₂ : ZMod m))) =
        ((Λ n₁ : ℂ) * Λ n₂) * (χ a⁻¹ * χ ((n₁ : ZMod m) * (n₂ : ZMod m))) := fun χ ↦ by ring
  simp_rw [this, ← mul_sum, DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
  split_ifs with h1 h2 h2
  · push_cast; ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

lemma pairSum_nonneg (m : ℕ) (a : ZMod m) (N : ℕ) : 0 ≤ pairSum m a N := by
  unfold pairSum
  refine sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ ?_
  split_ifs
  · exact mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg
  · exact le_rfl

/-- The GRH input with a fixed constant `C`. -/
def GRHWith (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x →
    ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤ C * Real.sqrt x * (Real.log (q * x)) ^ 2

/-- Lower bound for `φ(m) T(a)` from GRH. -/
lemma lower_bound {C : ℝ} (hC : GRHWith C) (m : ℕ) [NeZero m] {a : ZMod m} (ha : IsUnit a)
    (x : ℝ) (hx : 2 ≤ x) (hE : C * Real.sqrt x * (Real.log (m * x)) ^ 2 ≤ x) :
    (x - C * Real.sqrt x * (Real.log (m * x)) ^ 2) ^ 2
        - m.totient * (C * Real.sqrt x * (Real.log (m * x)) ^ 2) ^ 2
      ≤ m.totient * pairSum m a ⌊x⌋₊ := by
  set E := C * Real.sqrt x * (Real.log (m * x)) ^ 2 with hEdef
  have hE0 : 0 ≤ E := by
    have := hC m 1 x hx
    exact (norm_nonneg _).trans this
  set S := ∑ χ : DirichletCharacter ℂ m, χ a⁻¹ * psiChi χ x ^ 2 with hS
  have hainv : IsUnit a⁻¹ := IsUnit.of_mul_eq_one a ((ZMod.inv_mul_eq_one_of_isUnit ha a).mpr rfl)
  -- the non-principal characters
  have hrest : ‖S - psiChi (1 : DirichletCharacter ℂ m) x ^ 2‖ ≤ m.totient * E ^ 2 := by
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (DirichletCharacter ℂ m))
      (fun χ ↦ χ a⁻¹ * psiChi χ x ^ 2) (Finset.mem_univ 1)
    rw [← hS, MulChar.one_apply hainv, one_mul] at hsplit
    rw [← hsplit, add_sub_cancel_left]
    calc ‖∑ χ ∈ univ.erase 1, χ a⁻¹ * psiChi χ x ^ 2‖
        ≤ ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ m), E ^ 2 := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun χ hχ ↦ ?_)
          have hχ1 : χ ≠ 1 := Finset.ne_of_mem_erase hχ
          have hb := hC m χ x hx
          simp only [hχ1, ite_false, sub_zero] at hb
          rw [norm_mul, norm_pow]
          calc ‖χ a⁻¹‖ * ‖psiChi χ x‖ ^ 2 ≤ 1 * E ^ 2 := by
                gcongr
                exact DirichletCharacter.norm_le_one χ _
            _ = E ^ 2 := one_mul _
      _ = ((univ.erase (1 : DirichletCharacter ℂ m)).card : ℝ) * E ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (m.totient : ℝ) * E ^ 2 := by
          gcongr
          have hcard : (univ : Finset (DirichletCharacter ℂ m)).card = m.totient := by
            rw [card_univ, ← Nat.card_eq_fintype_card,
              DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
          exact_mod_cast (Finset.card_erase_le).trans hcard.le
  -- the principal character
  have hprin : x - E ≤ ‖psiChi (1 : DirichletCharacter ℂ m) x‖ := by
    have hb := hC m 1 x hx
    simp only [ite_true] at hb
    have h1 := norm_sub_norm_le (x : ℂ) (psiChi (1 : DirichletCharacter ℂ m) x)
    rw [norm_sub_rev, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h1
    linarith
  have hprin2 : (x - E) ^ 2 ≤ ‖psiChi (1 : DirichletCharacter ℂ m) x ^ 2‖ := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (by linarith) hprin 2
  have hST : S = ((m.totient * pairSum m a ⌊x⌋₊ : ℝ) : ℂ) := by
    rw [hS, ← totient_mul_pairSum m ha x]; push_cast; rfl
  have hSnorm : ‖S‖ = m.totient * pairSum m a ⌊x⌋₊ := by
    rw [hST, Complex.norm_real, Real.norm_of_nonneg]
    exact mul_nonneg (Nat.cast_nonneg _) (pairSum_nonneg _ _ _)
  have htri : ‖psiChi (1 : DirichletCharacter ℂ m) x ^ 2‖ ≤
      ‖S‖ + ‖S - psiChi (1 : DirichletCharacter ℂ m) x ^ 2‖ := by
    have := norm_sub_le S (S - psiChi (1 : DirichletCharacter ℂ m) x ^ 2)
    rwa [sub_sub_cancel] at this
  linarith

/-- For fixed `n₁`, the `n₂ ≤ N` with `n₁ n₂ ≡ a` lie in one residue class, so there are at most
`N / m + 1` of them. -/
lemma card_filter_mul_eq_le (m : ℕ) [NeZero m] {a : ZMod m} (ha : IsUnit a) (n₁ N : ℕ) :
    ((Iic N).filter (fun n₂ : ℕ ↦ (n₁ : ZMod m) * (n₂ : ZMod m) = a)).card ≤ N / m + 1 := by
  have h := card_le_card_of_injOn
    (s := (Iic N).filter (fun n₂ : ℕ ↦ (n₁ : ZMod m) * (n₂ : ZMod m) = a))
    (t := range (N / m + 1)) (fun n : ℕ ↦ n / m) ?_ ?_
  · simpa using h
  · intro n hn
    simp only [coe_filter, mem_Iic, Set.mem_ofPred_eq] at hn
    simp only [coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1)
  · intro n hn n' hn' hnn'
    simp only [coe_filter, mem_Iic, Set.mem_ofPred_eq] at hn hn'
    have hu : IsUnit (n₁ : ZMod m) := isUnit_of_mul_isUnit_left (hn.2 ▸ ha)
    have hc : (n : ZMod m) = n' := hu.mul_left_cancel (hn.2.trans hn'.2.symm)
    rw [ZMod.natCast_eq_natCast_iff'] at hc
    simp only at hnn'
    rw [← Nat.div_add_mod n m, ← Nat.div_add_mod n' m, hnn', hc]

lemma vonMangoldt_le_log_of_le {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : n ∈ Iic ⌊x⌋₊) :
    Λ n ≤ Real.log x := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp only [ArithmeticFunction.map_zero]; exact Real.log_nonneg hx
  · refine vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hpos) ?_)
    exact (Nat.cast_le.mpr (mem_Iic.mp hn)).trans (Nat.floor_le (by linarith))

lemma inner_le (m : ℕ) [NeZero m] {a : ZMod m} (ha : IsUnit a) (n₁ : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n₂ ∈ Iic ⌊x⌋₊, (if (n₁ : ZMod m) * (n₂ : ZMod m) = a then Λ n₂ else 0)
      ≤ (x / m + 1) * Real.log x := by
  rw [← sum_filter]
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  calc _ ≤ ((Iic ⌊x⌋₊).filter (fun n₂ : ℕ ↦ (n₁ : ZMod m) * (n₂ : ZMod m) = a)).card • Real.log x :=
        sum_le_card_nsmul _ _ _ fun n hn ↦ vonMangoldt_le_log_of_le hx (mem_filter.mp hn).1
    _ ≤ ((⌊x⌋₊ / m + 1 : ℕ) : ℝ) * Real.log x := by
        rw [nsmul_eq_mul]; gcongr; exact_mod_cast card_filter_mul_eq_le m ha n₁ ⌊x⌋₊
    _ ≤ (x / m + 1) * Real.log x := by
        gcongr
        push_cast
        gcongr
        calc ((⌊x⌋₊ / m : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) / m := Nat.cast_div_le
          _ ≤ x / m := by gcongr; exact Nat.floor_le (by linarith)

/-- The sum of `Λ` over non-prime `n ≤ x` (prime powers `p^k`, `k ≥ 2`). -/
lemma sum_nonprime_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ (Iic ⌊x⌋₊).filter (fun n ↦ ¬ n.Prime), Λ n ≤ 2 * Real.sqrt x * Real.log x := by
  have h := Chebyshev.psi_sub_theta_le hx
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime] at h
  refine le_trans (le_of_eq ?_) h
  symm
  refine sum_subset (fun n hn ↦ ?_) (fun n hn hn' ↦ ?_)
  · simp only [mem_filter, mem_Ioc, mem_Iic] at hn ⊢; exact ⟨hn.1.2, hn.2⟩
  · simp only [mem_filter, mem_Ioc, mem_Iic, not_and] at hn hn'
    have : n = 0 := by
      by_contra h0
      exact hn' ⟨Nat.pos_of_ne_zero h0, hn.1⟩ hn.2
    simp [this]

/-- Contribution of pairs whose first entry is a non-prime. -/
noncomputable def badPart (m : ℕ) (a : ZMod m) (n₁ n₂ : ℕ) : ℝ :=
  if ¬ n₁.Prime then Λ n₁ * (if (n₁ : ZMod m) * (n₂ : ZMod m) = a then Λ n₂ else 0) else 0

lemma badPart_nonneg (m : ℕ) (a : ZMod m) (n₁ n₂ : ℕ) : 0 ≤ badPart m a n₁ n₂ := by
  unfold badPart
  split_ifs <;> first | exact le_rfl | exact mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg |
    simp

lemma sum_badPart_le (m : ℕ) [NeZero m] {a : ZMod m} (ha : IsUnit a) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n₁ ∈ Iic ⌊x⌋₊, ∑ n₂ ∈ Iic ⌊x⌋₊, badPart m a n₁ n₂
      ≤ (2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x) := by
  have hB : 0 ≤ (x / m + 1) * Real.log x := by
    have : 0 ≤ Real.log x := Real.log_nonneg hx
    positivity
  calc ∑ n₁ ∈ Iic ⌊x⌋₊, ∑ n₂ ∈ Iic ⌊x⌋₊, badPart m a n₁ n₂
      ≤ ∑ n₁ ∈ Iic ⌊x⌋₊, (if ¬ n₁.Prime then Λ n₁ * ((x / m + 1) * Real.log x) else 0) := by
        refine sum_le_sum fun n₁ _ ↦ ?_
        by_cases hp : n₁.Prime
        · simp [badPart, hp]
        · simp only [badPart, hp, not_false_eq_true, ite_true]
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (inner_le m ha n₁ hx) vonMangoldt_nonneg
    _ = (∑ n ∈ (Iic ⌊x⌋₊).filter (fun n ↦ ¬ n.Prime), Λ n) * ((x / m + 1) * Real.log x) := by
        rw [sum_filter, sum_mul]
        refine sum_congr rfl fun n _ ↦ ?_
        split_ifs <;> simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_nonprime_le hx) hB

/-- If no pair of primes `p, q ≤ x` has `pq ≡ a`, then `T(a)` is small. -/
lemma upper_bound (m : ℕ) [NeZero m] {a : ZMod m} (ha : IsUnit a) {x : ℝ} (hx : 1 ≤ x)
    (hno : ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (p : ℝ) ≤ x ∧ (q : ℝ) ≤ x ∧
      ((p * q : ℕ) : ZMod m) = a) :
    pairSum m a ⌊x⌋₊ ≤ 2 * ((2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x)) := by
  have hle : ∀ n ∈ Iic ⌊x⌋₊, (n : ℝ) ≤ x := fun n hn ↦
    (Nat.cast_le.mpr (mem_Iic.mp hn)).trans (Nat.floor_le (by linarith))
  have hpt : ∀ n₁ ∈ Iic ⌊x⌋₊, ∀ n₂ ∈ Iic ⌊x⌋₊,
      (if ((n₁ : ZMod m) * (n₂ : ZMod m) = a) then Λ n₁ * Λ n₂ else 0)
        ≤ badPart m a n₁ n₂ + badPart m a n₂ n₁ := by
    intro n₁ hn₁ n₂ hn₂
    have h1 := badPart_nonneg m a n₁ n₂
    have h2 := badPart_nonneg m a n₂ n₁
    split_ifs with hc
    · by_cases hp₁ : n₁.Prime
      · by_cases hp₂ : n₂.Prime
        · exact absurd ⟨n₁, n₂, hp₁, hp₂, hle n₁ hn₁, hle n₂ hn₂, by push_cast; exact hc⟩ hno
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
  have hsum := sum_badPart_le m ha hx
  calc pairSum m a ⌊x⌋₊
      ≤ ∑ n₁ ∈ Iic ⌊x⌋₊, ∑ n₂ ∈ Iic ⌊x⌋₊,
          (badPart m a n₁ n₂ + badPart m a n₂ n₁) :=
        sum_le_sum fun n₁ hn₁ ↦ sum_le_sum fun n₂ hn₂ ↦ hpt n₁ hn₁ n₂ hn₂
    _ = ∑ n₁ ∈ Iic ⌊x⌋₊, ∑ n₂ ∈ Iic ⌊x⌋₊, badPart m a n₁ n₂
        + ∑ n₁ ∈ Iic ⌊x⌋₊, ∑ n₂ ∈ Iic ⌊x⌋₊, badPart m a n₁ n₂ := by
        simp_rw [sum_add_distrib]
        congr 1
        exact sum_comm
    _ ≤ _ := by linarith

/-- The covering criterion: if the main term beats the error terms, every unit is covered. -/
lemma covered_of_ineq {C : ℝ} (hC : GRHWith C) (m : ℕ) [NeZero m] (x : ℝ) (hx : 2 ≤ x)
    (hE : C * Real.sqrt x * (Real.log (m * x)) ^ 2 ≤ x)
    (hineq : m * (2 * ((2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x)))
        + m * (C * Real.sqrt x * (Real.log (m * x)) ^ 2) ^ 2
      < (x - C * Real.sqrt x * (Real.log (m * x)) ^ 2) ^ 2) :
    CoveredBy m x := by
  intro a ha
  by_contra hno
  have hlow := lower_bound hC m ha x hx hE
  have hup := upper_bound m ha (by linarith) hno
  have hT := pairSum_nonneg m a ⌊x⌋₊
  have hφ : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have h1 : (m.totient : ℝ) * pairSum m a ⌊x⌋₊ ≤ m * pairSum m a ⌊x⌋₊ :=
    mul_le_mul_of_nonneg_right hφ hT
  have h2 : (m : ℝ) * pairSum m a ⌊x⌋₊ ≤
      m * (2 * ((2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x))) :=
    mul_le_mul_of_nonneg_left hup (Nat.cast_nonneg _)
  have h3 : (m.totient : ℝ) * (C * Real.sqrt x * (Real.log (m * x)) ^ 2) ^ 2 ≤
      m * (C * Real.sqrt x * (Real.log (m * x)) ^ 2) ^ 2 :=
    mul_le_mul_of_nonneg_right hφ (sq_nonneg _)
  linarith

lemma log_pow_four_le {y : ℝ} (hy : 1 ≤ y) : Real.log y ^ 4 ≤ 256 * y := by
  have hy0 : 0 ≤ y := by linarith
  have h := Real.log_le_rpow_div hy0 (by norm_num : (0 : ℝ) < 1 / 4)
  have hr : (y ^ (1 / 4 : ℝ)) ^ 4 = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
  have h4 : Real.log y ≤ 4 * y ^ (1 / 4 : ℝ) := by
    have : y ^ (1 / 4 : ℝ) / (1 / 4) = 4 * y ^ (1 / 4 : ℝ) := by ring
    linarith
  calc Real.log y ^ 4 ≤ (4 * y ^ (1 / 4 : ℝ)) ^ 4 := pow_le_pow_left₀ (Real.log_nonneg hy) h4 4
    _ = 256 * y := by rw [mul_pow, hr]; norm_num

/-- The elementary real-variable estimates, for `x = K m log⁴ m` with `K, m` large. -/
lemma analytic {C K : ℝ} (hC0 : 0 < C) (hK1 : 1 ≤ K) (hKC : 4096 * C ^ 2 ≤ K) (m : ℕ)
    (hm : (262144 : ℝ) ≤ m) (hmK : 256 * K ≤ m) (x : ℝ) (hx : x = K * m * Real.log m ^ 4) :
    2 ≤ x ∧ C * Real.sqrt x * (Real.log (m * x)) ^ 2 ≤ x ∧
      m * (2 * ((2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x)))
        + m * (C * Real.sqrt x * (Real.log (m * x)) ^ 2) ^ 2
      < (x - C * Real.sqrt x * (Real.log (m * x)) ^ 2) ^ 2 := by
  set L := Real.log m with hLdef
  have hm0 : (0 : ℝ) < m := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hm0]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
  have hL4m : L ^ 4 ≤ 256 * m := log_pow_four_le (by linarith)
  have hxm : (m : ℝ) ≤ x := by
    rw [hx]
    calc (m : ℝ) = 1 * m * 1 := by ring
      _ ≤ K * m * L ^ 4 := by gcongr
  have hx0 : 0 < x := by linarith
  have hx2 : 2 ≤ x := by linarith
  have hmx1 : 1 ≤ (m : ℝ) * x := by nlinarith
  have hmx : (m : ℝ) * x ≤ (m : ℝ) ^ 4 := by
    rw [hx]
    calc (m : ℝ) * (K * m * L ^ 4) = K * (m : ℝ) ^ 2 * L ^ 4 := by ring
      _ ≤ K * (m : ℝ) ^ 2 * (256 * m) := by gcongr
      _ = (256 * K) * (m : ℝ) ^ 3 := by ring
      _ ≤ (m : ℝ) * (m : ℝ) ^ 3 := by gcongr
      _ = (m : ℝ) ^ 4 := by ring
  have hlogmx : Real.log (m * x) ≤ 4 * L := by
    calc Real.log (m * x) ≤ Real.log ((m : ℝ) ^ 4) := Real.log_le_log (by linarith) hmx
      _ = 4 * L := by rw [Real.log_pow, hLdef]; norm_num
  have hlogmx0 : 0 ≤ Real.log (m * x) := Real.log_nonneg hmx1
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogx : Real.log x ≤ 4 * L := by
    refine le_trans (Real.log_le_log hx0 ?_) hlogmx
    nlinarith
  set E := C * Real.sqrt x * (Real.log (m * x)) ^ 2 with hEdef
  have hsx0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hE0 : 0 ≤ E := by positivity
  have hEsq : E ^ 2 = C ^ 2 * x * Real.log (m * x) ^ 4 := by
    rw [hEdef, mul_pow, mul_pow, Real.sq_sqrt hx0.le]; ring
  have hlog4 : Real.log (m * x) ^ 4 ≤ 256 * L ^ 4 := by
    calc Real.log (m * x) ^ 4 ≤ (4 * L) ^ 4 := pow_le_pow_left₀ hlogmx0 hlogmx 4
      _ = 256 * L ^ 4 := by ring
  have hmE : 16 * (m * E ^ 2) ≤ x ^ 2 := by
    rw [hEsq]
    calc 16 * (m * (C ^ 2 * x * Real.log (m * x) ^ 4))
        ≤ 16 * (m * (C ^ 2 * x * (256 * L ^ 4))) := by gcongr
      _ = (4096 * C ^ 2) * (x * (m * L ^ 4)) := by ring
      _ ≤ K * (x * (m * L ^ 4)) := by gcongr
      _ = x ^ 2 := by rw [hx]; ring
  have hEm : E ^ 2 ≤ m * E ^ 2 := by
    have : (1 : ℝ) ≤ m := by linarith
    nlinarith [sq_nonneg E]
  have hEx : E ≤ x / 4 := by nlinarith
  have hsqrt : 512 * L ^ 2 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by positivity) hx0.le, hx]
    calc (512 * L ^ 2) ^ 2 = 262144 * L ^ 4 := by ring
      _ ≤ m * L ^ 4 := by gcongr
      _ = 1 * m * L ^ 4 := by ring
      _ ≤ K * m * L ^ 4 := by gcongr
  have hU : m * (2 * ((2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x)))
      ≤ x ^ 2 / 4 := by
    have hA : (m : ℝ) * (2 * ((2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x)))
        = 4 * Real.sqrt x * Real.log x ^ 2 * (x + m) := by
      field_simp; ring
    have hlx2 : Real.log x ^ 2 ≤ 16 * L ^ 2 := by
      calc Real.log x ^ 2 ≤ (4 * L) ^ 2 := pow_le_pow_left₀ hlogx0 hlogx 2
        _ = 16 * L ^ 2 := by ring
    have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    rw [hA]
    calc 4 * Real.sqrt x * Real.log x ^ 2 * (x + m)
        ≤ 4 * Real.sqrt x * (16 * L ^ 2) * (2 * x) := by gcongr; linarith
      _ = x * (128 * (L ^ 2 * Real.sqrt x)) := by ring
      _ ≤ x * (128 * (Real.sqrt x * Real.sqrt x / 512)) := by
          gcongr
          rw [le_div_iff₀ (by norm_num)]
          nlinarith
      _ = x ^ 2 / 4 := by rw [hss]; ring
  refine ⟨hx2, by linarith, ?_⟩
  have h34 : 3 * x / 4 ≤ x - E := by linarith
  have h916 : (3 * x / 4) ^ 2 ≤ (x - E) ^ 2 := pow_le_pow_left₀ (by positivity) h34 2
  nlinarith

/-- **Main theorem (unconditional modulo `GRHBounds`).** Every unit mod `m` is a product of two
primes `p, q ≤ K m (log m)⁴`, for all large `m`. -/
theorem coveredBy_of_grhBounds (h : GRHBounds) :
    ∃ K m₀ : ℝ, 0 < K ∧ ∀ m : ℕ, (m : ℝ) ≥ m₀ → CoveredBy m (K * m * (Real.log m) ^ 4) := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨4096 * C ^ 2 + 1, max 262144 (256 * (4096 * C ^ 2 + 1)), by positivity, ?_⟩
  intro m hm
  have hm1 : (262144 : ℝ) ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : 256 * (4096 * C ^ 2 + 1) ≤ (m : ℝ) := le_trans (le_max_right _ _) hm
  have hmpos : 0 < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  have : NeZero m := ⟨hmpos.ne'⟩
  obtain ⟨hx2, hE, hineq⟩ := analytic hC0 (by nlinarith [sq_nonneg C]) (by linarith) m hm1 hm2
    _ rfl
  exact covered_of_ineq hC m _ hx2 hE hineq

end EOS
