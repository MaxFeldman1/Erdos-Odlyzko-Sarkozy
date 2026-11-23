import EOS.LogSquare

/-!
# Theorem W: `a = p q s` with `p, q ≤ m` and `s ≪ (log m)² (log log m)²`, conditional on GRH

The wildcard's Theorem W (notes/brainstorm/r1-wildcard.md §1.1–§1.2; r3-synthesis.md §3.1).
GRH enters only through `GRHSmoothBound` (via `GRHSmoothBound.bounds`), as in `LogSquare.lean`.

Notation: `x = m - 1`, `S(χ) = ψ̃(x, χ)`, `W` a set of primes `≤ y` not dividing `m`,
`F(χ) = Σ_{s ∈ W} χ(s)`, `R(c) = Σ_{n₁ n₂ ≡ c} cw(n₁) cw(n₂)` (`wpair`).

* `totient_mul_sum_wpair`: `φ(m) Σ_{s ∈ W} R(a s⁻¹) = Σ_χ χ(a⁻¹) S(χ)² F(χ)`.
* `tupleCount_le` (Lemma S, weak form): a product of `k` primes determines the tuple up to
  `k^k` choices (each entry is one of the primes of a fixed tuple). The notes use `k!`; `k^k`
  costs only a constant in `(k^k)^{1/2k} = √k`.
* `sum_norm_charSum_pow_le` (energy + Parseval): if all `k`-fold products from `W` are `< m`,
  then `Σ_χ |F(χ)|^{2k} ≤ φ(m) k^k |W|^k`.
* `le_add_pow_div` (Lemma M without real exponents): `t ≤ λ + t^{2k} / λ^{2k-1}`. Summed against
  `|S(χ)|²` over `χ ≠ 1` this gives `λ Σ_χ |S|² + M² λ^{1-2k} Σ_χ |F|^{2k}`, which is Hölder's
  bound after optimising `λ`.
* `exists_three_of_criterion`: if no `p q s ≡ a`, each `R(a s⁻¹)` is bounded by the prime-power
  terms (`wpair_le_of_not_exists`), and the principal term `|W| |S(1)|²` beats everything.
* `theta_sub_log_le`: `θ(y) - log m ≤ |W| log y` (unconditional; uses Mathlib's `theta_ge'`).
* `coveredBy_three_primes`: `k = ⌈log L⌉`, `y = K L² (log L)²`, `λ = |W| / (2048 L)`, `L = log m`.

Differences from the notes: we use `Λ`-weights with prime powers handled as in `LogSquare.lean`
instead of `ϑ̃`; we use `φ(m) ≤ m`, so the bound is `K L² (log L)²` rather than
`K (φ/m)² L² (log L)²`; in fact `p, q ≤ m - 1`.
-/

open scoped BigOperators
open Finset ArithmeticFunction

namespace EOS

/-- The number of `k`-tuples from `W` with product `n`. -/
noncomputable def tupleCount (W : Finset ℕ) (k : ℕ) (n : ℕ) : ℝ :=
  (((Fintype.piFinset fun _ : Fin k ↦ W).filter fun t ↦ ∏ i, t i = n).card : ℝ)

/-- Lemma S (weak form): if `W` consists of primes, at most `k ^ k` tuples have a given product. -/
lemma tupleCount_le (W : Finset ℕ) (hW : ∀ s ∈ W, s.Prime) (k n : ℕ) :
    tupleCount W k n ≤ (k : ℝ) ^ k := by
  unfold tupleCount
  set T := (Fintype.piFinset fun _ : Fin k ↦ W).filter fun t ↦ ∏ i, t i = n with hT
  rcases T.eq_empty_or_nonempty with h | ⟨t₀, ht₀⟩
  · rw [h]; simp
  have ht₀' := mem_filter.mp ht₀
  have key : ∀ t ∈ T, ∀ i : Fin k, ∃ j : Fin k, t i = t₀ j := by
    intro t ht i
    have ht' := mem_filter.mp ht
    have hp : (t i).Prime := hW _ (Fintype.mem_piFinset.mp ht'.1 i)
    have hdvd : t i ∣ ∏ j, t₀ j := by
      rw [ht₀'.2, ← ht'.2]
      exact Finset.dvd_prod_of_mem _ (mem_univ i)
    obtain ⟨j, -, hj⟩ := hp.prime.exists_mem_finset_dvd hdvd
    exact ⟨j, (Nat.prime_dvd_prime_iff_eq hp (hW _ (Fintype.mem_piFinset.mp ht₀'.1 j))).mp hj⟩
  classical
  let f : (Fin k → ℕ) → (Fin k → Fin k) := fun t i ↦
    if h : ∃ j : Fin k, t i = t₀ j then h.choose else i
  have hinj : Set.InjOn f T := by
    intro t ht t' ht' hff
    funext i
    have h1 := key t ht i
    have h2 := key t' ht' i
    have e1 : t i = t₀ (f t i) := by
      simp only [f]; rw [dite_eq_left_of_eq_true (eq_true h1)]; exact h1.choose_spec
    have e2 : t' i = t₀ (f t' i) := by
      simp only [f]; rw [dite_eq_left_of_eq_true (eq_true h2)]; exact h2.choose_spec
    rw [e1, e2, hff]
  have := card_le_card_of_injOn f (s := T) (t := (univ : Finset (Fin k → Fin k)))
    (fun _ _ ↦ by simp) hinj
  simp only [card_univ, Fintype.card_fun, Fintype.card_fin] at this
  exact_mod_cast this

/-- The character sum over `W`, `F(χ) = Σ_{s ∈ W} χ(s)`. -/
noncomputable def charSum {m : ℕ} (W : Finset ℕ) (χ : DirichletCharacter ℂ m) : ℂ :=
  ∑ s ∈ W, χ s

/-- If all products of `k` elements of `W` are `≤ N`, then `F(χ)^k = Σ_{n ≤ N} r_k(n) χ(n)`. -/
lemma charSum_pow_eq {m : ℕ} (W : Finset ℕ) (k N : ℕ)
    (hprod : ∀ t ∈ Fintype.piFinset (fun _ : Fin k ↦ W), ∏ i, t i ≤ N)
    (χ : DirichletCharacter ℂ m) :
    charSum W χ ^ k = wsum (tupleCount W k) N χ := by
  rw [charSum, ← Fin.prod_const, prod_univ_sum]
  have h1 : ∀ t ∈ Fintype.piFinset (fun _ : Fin k ↦ W), ∏ i, χ (t i) = χ ((∏ i, t i : ℕ)) := by
    intro t _
    push_cast
    rw [map_prod]
  rw [sum_congr rfl h1, wsum]
  rw [← sum_fiberwise_of_maps_to' (t := Iic N) (g := fun t : Fin k → ℕ ↦ ∏ i, t i)
    (fun t ht ↦ mem_Iic.mpr (hprod t ht)) (fun n : ℕ ↦ χ (n : ZMod m))]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [sum_const, nsmul_eq_mul, tupleCount]
  push_cast
  rfl

lemma sum_tupleCount (W : Finset ℕ) (k N : ℕ)
    (hprod : ∀ t ∈ Fintype.piFinset (fun _ : Fin k ↦ W), ∏ i, t i ≤ N) :
    ∑ n ∈ Iic N, tupleCount W k n = (W.card : ℝ) ^ k := by
  unfold tupleCount
  rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise (fun t ht ↦ mem_Iic.mpr (hprod t ht))]
  simp

/-- **Energy bound (Lemma S + Parseval).** For a set `W` of primes all of whose `k`-fold products
are `< m`, `Σ_χ |F(χ)|^{2k} ≤ φ(m) k^k |W|^k`. -/
lemma sum_norm_charSum_pow_le (m : ℕ) [NeZero m] (W : Finset ℕ) (hW : ∀ s ∈ W, s.Prime) (k : ℕ)
    (hprod : ∀ t ∈ Fintype.piFinset (fun _ : Fin k ↦ W), ∏ i, t i ≤ m - 1) :
    ∑ χ : DirichletCharacter ℂ m, ‖charSum W χ‖ ^ (2 * k) ≤
      m.totient * ((k : ℝ) ^ k * (W.card : ℝ) ^ k) := by
  have h1 : ∀ χ : DirichletCharacter ℂ m, ‖charSum W χ‖ ^ (2 * k) =
      ‖wsum (tupleCount W k) (m - 1) χ‖ ^ 2 := by
    intro χ
    rw [← charSum_pow_eq W k (m - 1) hprod, norm_pow, ← pow_mul, mul_comm]
  simp_rw [h1]
  refine (sum_norm_sq_wsum_le m _ (m - 1) (by have := NeZero.pos m; omega)).trans ?_
  gcongr
  have h0 : ∀ n, 0 ≤ tupleCount W k n := fun n ↦ by unfold tupleCount; positivity
  calc ∑ n ∈ Iic (m - 1), tupleCount W k n ^ 2
      ≤ ∑ n ∈ Iic (m - 1), (k : ℝ) ^ k * tupleCount W k n := by
        refine sum_le_sum fun n _ ↦ ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_right (tupleCount_le W hW k n) (h0 n)
    _ = (k : ℝ) ^ k * (W.card : ℝ) ^ k := by rw [← mul_sum, sum_tupleCount W k _ hprod]

/-! ### Orthogonality with a multiplier -/

lemma zmod_inv_mul_inv {m : ℕ} {a b : ZMod m} (ha : IsUnit a) (hb : IsUnit b) :
    (a * b⁻¹)⁻¹ = a⁻¹ * b := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  rw [ZMod.inv_coe_unit, ← Units.val_mul, ZMod.inv_coe_unit, ZMod.inv_coe_unit, ← Units.val_mul]
  congr 1
  rw [mul_inv_rev, inv_inv, mul_comm]

lemma isUnit_mul_inv {m : ℕ} {a b : ZMod m} (ha : IsUnit a) (hb : IsUnit b) :
    IsUnit (a * b⁻¹) :=
  ha.mul (IsUnit.of_mul_eq_one b (ZMod.inv_mul_of_unit b hb))

/-- Orthogonality with the multiplier `F(χ)`:
`φ(m) Σ_{s ∈ W} R(a s⁻¹) = Σ_χ χ(a⁻¹) S₁(χ) S₂(χ) F(χ)`. -/
lemma totient_mul_sum_wpair (m : ℕ) [NeZero m] {a : ZMod m} (ha : IsUnit a) (W : Finset ℕ)
    (hW : ∀ s ∈ W, IsUnit (s : ZMod m)) (c₁ c₂ : ℕ → ℝ) (N₁ N₂ : ℕ) :
    (m.totient : ℂ) * ((∑ s ∈ W, wpair m (a * (s : ZMod m)⁻¹) c₁ c₂ N₁ N₂ : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ m,
        χ a⁻¹ * (wsum c₁ N₁ χ * wsum c₂ N₂ χ * charSum W χ) := by
  push_cast
  rw [mul_sum]
  have h1 : ∀ s ∈ W, (m.totient : ℂ) * (wpair m (a * (s : ZMod m)⁻¹) c₁ c₂ N₁ N₂ : ℂ) =
      ∑ χ : DirichletCharacter ℂ m, χ s * (χ a⁻¹ * (wsum c₁ N₁ χ * wsum c₂ N₂ χ)) := by
    intro s hs
    rw [totient_mul_wpair m (isUnit_mul_inv ha (hW s hs)), zmod_inv_mul_inv ha (hW s hs)]
    refine sum_congr rfl fun χ _ ↦ ?_
    rw [map_mul]; ring
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun χ _ ↦ ?_
  rw [← sum_mul, charSum]
  ring

/-- The pointwise inequality behind Hölder: `t ≤ λ + t^{2k} / λ^{2k-1}`. -/
lemma le_add_pow_div {t lam : ℝ} (ht : 0 ≤ t) (hlam : 0 < lam) {k : ℕ} (hk : 1 ≤ k) :
    t ≤ lam + t ^ (2 * k) / lam ^ (2 * k - 1) := by
  have h0 : 0 ≤ t ^ (2 * k) / lam ^ (2 * k - 1) := by positivity
  rcases le_or_gt t lam with h | h
  · linarith
  · have : t ≤ t ^ (2 * k) / lam ^ (2 * k - 1) := by
      rw [le_div_iff₀ (pow_pos hlam _)]
      calc t * lam ^ (2 * k - 1) ≤ t * t ^ (2 * k - 1) := by gcongr
        _ = t ^ (2 * k) := by rw [← pow_succ']; congr 1; omega
    linarith

/-! ### The covering criterion for `p q s` -/

/-- **Covering criterion for three primes.** `S(χ) = ψ̃(m - 1, χ)`, `F(χ) = Σ_{s ∈ W} χ(s)`. If the
principal term `|W| P²` beats the non-principal terms (bounded by Hölder with exponent `2k`, the
GRH bound `E` and the energy bound) plus the prime-power terms, then `a = p q s` with `p, q ≤ m - 1`
prime and `s ∈ W`. -/
lemma exists_three_of_criterion (m : ℕ) [NeZero m] {a : ZMod m} (ha : IsUnit a) (W : Finset ℕ)
    (hWp : ∀ s ∈ W, s.Prime) (hWu : ∀ s ∈ W, IsUnit (s : ZMod m)) {k : ℕ} (hk : 1 ≤ k)
    (hprod : ∀ t ∈ Fintype.piFinset (fun _ : Fin k ↦ W), ∏ i, t i ≤ m - 1)
    {x P E V lam : ℝ} (hx : x = ((m - 1 : ℕ) : ℝ)) (hx1 : 1 ≤ x) (hlam : 0 < lam) (hP0 : 0 ≤ P)
    (hprin : P ≤ ‖psiCesaro (1 : DirichletCharacter ℂ m) x‖)
    (hnon : ∀ χ : DirichletCharacter ℂ m, χ ≠ 1 → ‖psiCesaro χ x‖ ≤ E)
    (hV : m * ∑ n ∈ Iic (m - 1), cw x n ^ 2 ≤ V)
    (hineq : lam * V + E ^ 2 * (m * ((k : ℝ) ^ k * (W.card : ℝ) ^ k)) / lam ^ (2 * k - 1)
        + m * W.card * ((2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x)
          + (2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x))
      < W.card * P ^ 2) :
    ∃ p q s : ℕ, p.Prime ∧ q.Prime ∧ s ∈ W ∧ p ≤ m - 1 ∧ q ≤ m - 1 ∧
      ((p * q * s : ℕ) : ZMod m) = a := by
  by_contra hno
  set U := (2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x)
      + (2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x) with hU
  have hfl : ⌊x⌋₊ = m - 1 := by rw [hx, Nat.floor_natCast]
  have hS : ∀ χ : DirichletCharacter ℂ m, psiCesaro χ x = wsum (cw x) (m - 1) χ := fun χ ↦ by
    rw [psiCesaro_eq_wsum, hfl]
  have hc := cw_bounds (x := x) (by linarith)
  rw [hfl] at hc
  have hφ : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- the weighted count is small for every `s`
  have hR : ∀ s ∈ W, wpair m (a * (s : ZMod m)⁻¹) (cw x) (cw x) (m - 1) (m - 1) ≤ U := by
    intro s hs
    have h := wpair_le_of_not_exists m (isUnit_mul_inv ha (hWu s hs)) hx1 hx1
      (by rw [hfl]; exact hc) (by rw [hfl]; exact hc) ?_
    · rwa [hfl] at h
    rintro ⟨p, q, hp, hq, hpx, hqx, hpq⟩
    refine hno ⟨p, q, s, hp, hq, hs, ?_, ?_, ?_⟩
    · have : (p : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := hx ▸ hpx
      exact_mod_cast this
    · have : (q : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := hx ▸ hqx
      exact_mod_cast this
    · push_cast at hpq ⊢
      rw [hpq, mul_assoc, ZMod.inv_mul_of_unit _ (hWu s hs), mul_one]
  have hR0 : ∀ s ∈ W, 0 ≤ wpair m (a * (s : ZMod m)⁻¹) (cw x) (cw x) (m - 1) (m - 1) :=
    fun s _ ↦ wpair_nonneg m _ (fun n hn ↦ (hc n hn).1) (fun n hn ↦ (hc n hn).1)
  have hU0 : 0 ≤ U := by
    rcases W.eq_empty_or_nonempty with h | ⟨s, hs⟩
    · rw [h] at hineq; simp at hineq
      have : 0 ≤ lam * V := by
        refine mul_nonneg hlam.le (le_trans ?_ hV)
        exact mul_nonneg hm0 (sum_nonneg fun _ _ ↦ sq_nonneg _)
      rcases k with _ | k
      · omega
      · simp at hineq; linarith
    · exact (hR0 s hs).trans (hR s hs)
  set Rsum := ∑ s ∈ W, wpair m (a * (s : ZMod m)⁻¹) (cw x) (cw x) (m - 1) (m - 1) with hRsum
  have hRsum0 : 0 ≤ Rsum := sum_nonneg hR0
  have hRsumU : Rsum ≤ W.card * U := by
    calc Rsum ≤ ∑ s ∈ W, U := sum_le_sum hR
      _ = W.card * U := by rw [sum_const, nsmul_eq_mul]
  -- orthogonality
  have hlow := norm_sum_char_ge m ha (fun χ ↦ psiCesaro χ x * psiCesaro χ x * charSum W χ)
  simp_rw [hS] at hlow
  rw [← totient_mul_sum_wpair m ha W hWu, ← hRsum] at hlow
  simp_rw [← hS] at hlow
  have hnorm : ‖(m.totient : ℂ) * (Rsum : ℂ)‖ = m.totient * Rsum := by
    rw [norm_mul, Complex.norm_real, Complex.norm_natCast, Real.norm_of_nonneg hRsum0]
  rw [hnorm] at hlow
  -- the principal character
  have hG1 : charSum W (1 : DirichletCharacter ℂ m) = W.card := by
    rw [charSum, sum_congr rfl fun s hs ↦ MulChar.one_apply (hWu s hs)]
    simp
  have hprin' : (W.card : ℝ) * P ^ 2 ≤ ‖psiCesaro (1 : DirichletCharacter ℂ m) x *
      psiCesaro (1 : DirichletCharacter ℂ m) x * charSum W (1 : DirichletCharacter ℂ m)‖ := by
    rw [norm_mul, norm_mul, hG1, Complex.norm_natCast, mul_comm, ← sq]
    gcongr
  -- the non-principal characters
  have hS2 : ∑ χ : DirichletCharacter ℂ m, ‖psiCesaro χ x‖ ^ 2 ≤ V := by
    simp_rw [hS]
    refine (sum_norm_sq_wsum_le m _ _ (by have := NeZero.pos m; omega)).trans (le_trans ?_ hV)
    gcongr
  have hen := sum_norm_charSum_pow_le m W hWp k hprod
  have hB : ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ m),
      ‖psiCesaro χ x * psiCesaro χ x * charSum W χ‖ ≤
      lam * V + E ^ 2 * (m * ((k : ℝ) ^ k * (W.card : ℝ) ^ k)) / lam ^ (2 * k - 1) := by
    have hlp : 0 < lam ^ (2 * k - 1) := pow_pos hlam _
    calc ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ m),
          ‖psiCesaro χ x * psiCesaro χ x * charSum W χ‖
        ≤ ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ m),
          (lam * ‖psiCesaro χ x‖ ^ 2 + E ^ 2 * ‖charSum W χ‖ ^ (2 * k) / lam ^ (2 * k - 1)) := by
          refine sum_le_sum fun χ hχ ↦ ?_
          have h1 := le_add_pow_div (norm_nonneg (charSum W χ)) hlam hk
          have h2 := hnon χ (ne_of_mem_erase hχ)
          have h3 : ‖psiCesaro χ x‖ ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
          rw [norm_mul, norm_mul, ← sq]
          calc ‖psiCesaro χ x‖ ^ 2 * ‖charSum W χ‖
              ≤ ‖psiCesaro χ x‖ ^ 2 * (lam + ‖charSum W χ‖ ^ (2 * k) / lam ^ (2 * k - 1)) := by
                gcongr
            _ = lam * ‖psiCesaro χ x‖ ^ 2
                + ‖psiCesaro χ x‖ ^ 2 * ‖charSum W χ‖ ^ (2 * k) / lam ^ (2 * k - 1) := by ring
            _ ≤ _ := by gcongr
      _ = lam * ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ m), ‖psiCesaro χ x‖ ^ 2
          + E ^ 2 * (∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ m), ‖charSum W χ‖ ^ (2 * k))
            / lam ^ (2 * k - 1) := by
          rw [sum_add_distrib, mul_sum, mul_sum, sum_div]
      _ ≤ lam * V + E ^ 2 * (m * ((k : ℝ) ^ k * (W.card : ℝ) ^ k)) / lam ^ (2 * k - 1) := by
          gcongr
          · exact (sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
              fun _ _ _ ↦ sq_nonneg _).trans hS2
          · refine (sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
              fun _ _ _ ↦ by positivity).trans (hen.trans ?_)
            gcongr
  have h1 : (m.totient : ℝ) * Rsum ≤ m * (W.card * U) :=
    mul_le_mul hφ hRsumU hRsum0 hm0
  have : (m : ℝ) * W.card * U = m * (W.card * U) := by ring
  linarith

/-! ### The set of small primes -/

/-- The primes `s ≤ y` not dividing `m`. -/
noncomputable def smallPrimes (m : ℕ) (y : ℝ) : Finset ℕ :=
  (Iic ⌊y⌋₊).filter fun s ↦ s.Prime ∧ ¬ s ∣ m

lemma smallPrimes_prime {m : ℕ} {y : ℝ} {s : ℕ} (hs : s ∈ smallPrimes m y) : s.Prime :=
  (mem_filter.mp hs).2.1

lemma smallPrimes_isUnit {m : ℕ} {y : ℝ} {s : ℕ} (hs : s ∈ smallPrimes m y) :
    IsUnit (s : ZMod m) :=
  (ZMod.isUnit_iff_coprime s m).mpr
    ((Nat.Prime.coprime_iff_not_dvd (mem_filter.mp hs).2.1).mpr (mem_filter.mp hs).2.2)

lemma smallPrimes_le {m : ℕ} {y : ℝ} (hy : 0 ≤ y) {s : ℕ} (hs : s ∈ smallPrimes m y) :
    (s : ℝ) ≤ y :=
  (Nat.cast_le.mpr (mem_Iic.mp (mem_filter.mp hs).1)).trans (Nat.floor_le hy)

/-- Counting: `θ(y) - log m ≤ |W| log y`, since the primes dividing `m` contribute at most
`log m` to `θ`. -/
lemma theta_sub_log_le (m : ℕ) (hm : m ≠ 0) {y : ℝ} (hy : 1 ≤ y) :
    Chebyshev.theta y - Real.log m ≤ (smallPrimes m y).card * Real.log y := by
  set A := (Ioc 0 ⌊y⌋₊).filter Nat.Prime with hA
  have hθ : Chebyshev.theta y = ∑ p ∈ A, Real.log p := rfl
  rw [hθ, ← sum_filter_add_sum_filter_not A (fun p ↦ p ∣ m)]
  have h1 : ∑ p ∈ A.filter (fun p ↦ p ∣ m), Real.log p ≤ Real.log m := by
    have hsub : A.filter (fun p ↦ p ∣ m) ⊆ m.primeFactors := by
      intro p hp
      simp only [hA, mem_filter] at hp
      exact Nat.mem_primeFactors.mpr ⟨hp.1.2, hp.2, hm⟩
    calc ∑ p ∈ A.filter (fun p ↦ p ∣ m), Real.log p
        ≤ ∑ p ∈ m.primeFactors, Real.log p :=
          sum_le_sum_of_subset_of_nonneg hsub fun p _ _ ↦ Real.log_natCast_nonneg p
      _ = Real.log ((∏ p ∈ m.primeFactors, p : ℕ) : ℝ) := by
          push_cast
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      _ ≤ Real.log m := by
          refine Real.log_le_log ?_ ?_
          · exact_mod_cast Nat.pos_of_ne_zero
              (Finset.prod_ne_zero_iff.mpr fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).ne_zero)
          · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)
  have h2 : ∑ p ∈ A.filter (fun p ↦ ¬ p ∣ m), Real.log p ≤
      (smallPrimes m y).card * Real.log y := by
    have hsub : A.filter (fun p ↦ ¬ p ∣ m) ⊆ smallPrimes m y := by
      intro p hp
      simp only [hA, mem_filter, mem_Ioc] at hp
      simp only [smallPrimes, mem_filter, mem_Iic]
      exact ⟨hp.1.1.2, hp.1.2, hp.2⟩
    calc ∑ p ∈ A.filter (fun p ↦ ¬ p ∣ m), Real.log p
        ≤ ∑ p ∈ smallPrimes m y, Real.log p :=
          sum_le_sum_of_subset_of_nonneg hsub fun p _ _ ↦ Real.log_natCast_nonneg p
      _ ≤ ∑ p ∈ smallPrimes m y, Real.log y := by
          refine sum_le_sum fun p hp ↦ Real.log_le_log ?_ (smallPrimes_le (by linarith) hp)
          exact_mod_cast (smallPrimes_prime hp).pos
      _ = (smallPrimes m y).card * Real.log y := by rw [sum_const, nsmul_eq_mul]
  linarith

/-! ### Real-variable estimates for Theorem W -/

/-- The Hölder term: with `λ = w / D`, `D = 2048 L` and `w ≥ B k D²`, `B = 3 (C² + 1)`,
`E² m k^k w^k / λ^{2k-1} ≤ w m² / 256`. -/
lemma holder_term_le {C L M E w : ℝ} (hC0 : 0 < C) (hL1 : 1 ≤ L) {k : ℕ}
    (hk : 1 ≤ k) (hL3 : L ≤ 3 ^ k) (hE : E ^ 2 * M ≤ 4 * C ^ 2 * L ^ 2 * M ^ 2)
    (hw : 3 * (C ^ 2 + 1) * k * (2048 * L) ^ 2 ≤ w) :
    E ^ 2 * (M * ((k : ℝ) ^ k * w ^ k)) / (w / (2048 * L)) ^ (2 * k - 1) ≤ w * M ^ 2 / 256 := by
  set D := 2048 * L with hD
  set B := 3 * (C ^ 2 + 1) with hB
  have hD0 : 0 < D := by positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hBk : L * (C ^ 2 + 1) ≤ B ^ k := by
    rw [hB, mul_pow]
    have : C ^ 2 + 1 ≤ (C ^ 2 + 1) ^ k := le_self_pow₀ (by nlinarith) (by omega)
    exact mul_le_mul hL3 this (by positivity) (by positivity)
  have hwk : B ^ k * (k : ℝ) ^ k * D ^ (2 * k) ≤ w ^ k := by
    calc B ^ k * (k : ℝ) ^ k * D ^ (2 * k) = (B * k * D ^ 2) ^ k := by
          rw [mul_pow (B * k), mul_pow B, ← pow_mul, mul_comm 2 k]
      _ ≤ w ^ k := pow_le_pow_left₀ (by positivity) hw k
  have h2k : 2 * k = (2 * k - 1) + 1 := by omega
  set Q := (k : ℝ) ^ k * w ^ k * D ^ (2 * k - 1) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  rw [div_le_iff₀ (by positivity), div_pow]
  have hlhs : E ^ 2 * (M * ((k : ℝ) ^ k * w ^ k)) * D ^ (2 * k - 1) ≤
      4 * C ^ 2 * L ^ 2 * M ^ 2 * Q := by
    rw [hQ]
    calc E ^ 2 * (M * ((k : ℝ) ^ k * w ^ k)) * D ^ (2 * k - 1)
        = (E ^ 2 * M) * ((k : ℝ) ^ k * w ^ k * D ^ (2 * k - 1)) := by ring
      _ ≤ (4 * C ^ 2 * L ^ 2 * M ^ 2) * ((k : ℝ) ^ k * w ^ k * D ^ (2 * k - 1)) := by gcongr
  have hrhs : M ^ 2 / 256 * B ^ k * D * Q ≤ w * M ^ 2 / 256 * w ^ (2 * k - 1) := by
    have hww : w * w ^ (2 * k - 1) = w ^ k * w ^ k := by
      rw [← pow_succ', ← pow_add, ← h2k, two_mul]
    have hDD : D ^ (2 * k) = D ^ (2 * k - 1) * D := by rw [← pow_succ, ← h2k]
    calc M ^ 2 / 256 * B ^ k * D * Q
        = M ^ 2 / 256 * w ^ k * (B ^ k * (k : ℝ) ^ k * D ^ (2 * k)) := by rw [hQ, hDD]; ring
      _ ≤ M ^ 2 / 256 * w ^ k * w ^ k := by gcongr
      _ = w * M ^ 2 / 256 * w ^ (2 * k - 1) := by rw [mul_assoc, ← hww]; ring
  have hcoef : 4 * C ^ 2 * L ^ 2 * M ^ 2 ≤ M ^ 2 / 256 * B ^ k * D := by
    have : 4 * C ^ 2 * L ^ 2 ≤ B ^ k * (8 * L) := by
      have h1 : 4 * C ^ 2 * L ^ 2 ≤ (L * (C ^ 2 + 1)) * (8 * L) := by nlinarith [sq_nonneg C]
      exact h1.trans (by gcongr)
    calc 4 * C ^ 2 * L ^ 2 * M ^ 2 = M ^ 2 * (4 * C ^ 2 * L ^ 2) := by ring
      _ ≤ M ^ 2 * (B ^ k * (8 * L)) := by gcongr
      _ = M ^ 2 / 256 * B ^ k * D := by rw [hD]; ring
  rw [mul_div_assoc', le_div_iff₀ (pow_pos hD0 _)]
  calc E ^ 2 * (M * ((k : ℝ) ^ k * w ^ k)) * D ^ (2 * k - 1)
      ≤ 4 * C ^ 2 * L ^ 2 * M ^ 2 * Q := hlhs
    _ ≤ M ^ 2 / 256 * B ^ k * D * Q := by gcongr
    _ ≤ w * M ^ 2 / 256 * w ^ (2 * k - 1) := hrhs

/-- The real-variable estimates for Theorem W at `x = m - 1`, `λ = w / (2048 L)`,
`V = 7 m² L`, given `w ≥ 3 (C² + 1) k (2048 L)²` and `L ≤ 3^k`. -/
lemma analytic_W {C : ℝ} (hC0 : 0 < C) (m : ℕ) (hm : (2 : ℝ) ^ 80 ≤ m)
    (hCL : 64 * C ^ 2 ≤ Real.log m) {k : ℕ} (hk : 1 ≤ k) (hL3 : Real.log m ≤ 3 ^ k) {w : ℝ}
    (hw : 3 * (C ^ 2 + 1) * k * (2048 * Real.log m) ^ 2 ≤ w) (x : ℝ) (hx : x = m - 1) :
    1 ≤ x ∧ 0 ≤ x / 2 - C * Real.sqrt x * Real.log (2 * m) ∧
      w / (2048 * Real.log m) * (7 * m ^ 2 * Real.log m)
        + (C * Real.sqrt x * Real.log (2 * m)) ^ 2 * (m * ((k : ℝ) ^ k * w ^ k))
          / (w / (2048 * Real.log m)) ^ (2 * k - 1)
        + m * w * ((2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x)
          + (2 * Real.sqrt x * Real.log x) * ((x / m + 1) * Real.log x))
      < w * (x / 2 - C * Real.sqrt x * Real.log (2 * m)) ^ 2 := by
  obtain ⟨hL1, hL4, -⟩ := log_large hm
  have hl2m := log_two_mul_le hm
  set L := Real.log m with hLdef
  have hm0 : (0 : ℝ) < m := by linarith [show (0 : ℝ) < 2 ^ 80 by norm_num]
  have hm4 : (4 : ℝ) ≤ m := by linarith [show (4 : ℝ) ≤ 2 ^ 80 by norm_num]
  have hL0 : 0 ≤ L := by linarith
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  have hx0 : 0 < x := by linarith
  have hxm : x ≤ m := by rw [hx]; linarith
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlx : Real.log x ≤ L := Real.log_le_log hx0 hxm
  set s := Real.sqrt x with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg x
  have hss : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hl2m0 : 0 ≤ Real.log (2 * m) := Real.log_nonneg (by linarith)
  set E := C * s * Real.log (2 * m) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hEL : E ≤ 2 * C * s * L := by
    calc C * s * Real.log (2 * m) ≤ C * s * (2 * L) := by gcongr
      _ = 2 * C * s * L := by ring
  have hE2 : E ^ 2 ≤ 4 * C ^ 2 * L ^ 2 * m := by
    calc E ^ 2 ≤ (2 * C * s * L) ^ 2 := pow_le_pow_left₀ hE0 hEL 2
      _ = 4 * C ^ 2 * L ^ 2 * x := by rw [← hss]; ring
      _ ≤ 4 * C ^ 2 * L ^ 2 * m := by gcongr
  have hE2m : E ^ 2 * m ≤ 4 * C ^ 2 * L ^ 2 * m ^ 2 := by
    calc E ^ 2 * m ≤ 4 * C ^ 2 * L ^ 2 * m * m := by gcongr
      _ = 4 * C ^ 2 * L ^ 2 * m ^ 2 := by ring
  have hL24 : L ^ 3 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hCL2 : 64 * C ^ 2 * L ^ 2 ≤ m := by
    calc 64 * C ^ 2 * L ^ 2 ≤ L * L ^ 2 := by gcongr
      _ = L ^ 3 := by ring
      _ ≤ L ^ 4 := hL24
      _ ≤ m := by nlinarith
  have hEm : E ≤ m / 4 := by
    have h8 : (8 * C * s * L) ^ 2 ≤ (m : ℝ) ^ 2 := by
      calc (8 * C * s * L) ^ 2 = (64 * C ^ 2 * L ^ 2) * s ^ 2 := by ring
        _ ≤ (m : ℝ) * m := by rw [hss]; gcongr
        _ = (m : ℝ) ^ 2 := by ring
    have := (pow_le_pow_iff_left₀ (by positivity) hm0.le two_ne_zero).mp h8
    linarith
  have hP : (m : ℝ) / 8 ≤ x / 2 - E := by rw [hx] at *; linarith
  have hP2 : (m : ℝ) ^ 2 / 64 ≤ (x / 2 - E) ^ 2 := by
    calc (m : ℝ) ^ 2 / 64 = (m / 8) ^ 2 := by ring
      _ ≤ (x / 2 - E) ^ 2 := pow_le_pow_left₀ (by positivity) hP 2
  -- the prime-power terms
  have hsL : 16384 * s * L ^ 2 ≤ m := by
    have : (16384 * s * L ^ 2) ^ 2 ≤ (m : ℝ) ^ 2 := by
      calc (16384 * s * L ^ 2) ^ 2 = s ^ 2 * (2 ^ 28 * L ^ 4) := by ring
        _ ≤ (m : ℝ) * m := by rw [hss]; gcongr
        _ = (m : ℝ) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) hm0.le two_ne_zero).mp this
  have hU : (m : ℝ) * ((2 * s * Real.log x) * ((x / m + 1) * Real.log x)
      + (2 * s * Real.log x) * ((x / m + 1) * Real.log x)) ≤ (m : ℝ) ^ 2 / 2048 := by
    have hq : x / m + 1 ≤ 2 := by
      have : x / m ≤ 1 := by rw [div_le_one hm0]; exact hxm
      linarith
    calc (m : ℝ) * ((2 * s * Real.log x) * ((x / m + 1) * Real.log x)
          + (2 * s * Real.log x) * ((x / m + 1) * Real.log x))
        ≤ m * ((2 * s * L) * (2 * L) + (2 * s * L) * (2 * L)) := by gcongr
      _ = m * (16384 * s * L ^ 2) / 2048 := by ring
      _ ≤ m * m / 2048 := by gcongr
      _ = (m : ℝ) ^ 2 / 2048 := by ring
  -- the Hölder term
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hH := holder_term_le hC0 hL1 hk hL3 hE2m hw
  have hlamV : w / (2048 * L) * (7 * m ^ 2 * L) = 7 * (w * m ^ 2) / 2048 := by
    field_simp
  refine ⟨hx1, by linarith, ?_⟩
  rw [hlamV]
  have hUw : (m : ℝ) * w * ((2 * s * Real.log x) * ((x / m + 1) * Real.log x)
      + (2 * s * Real.log x) * ((x / m + 1) * Real.log x)) ≤ w * ((m : ℝ) ^ 2 / 2048) := by
    rw [mul_comm (m : ℝ) w, mul_assoc]
    exact mul_le_mul_of_nonneg_left hU hw0.le
  have hmain : w * ((m : ℝ) ^ 2 / 64) ≤ w * (x / 2 - E) ^ 2 :=
    mul_le_mul_of_nonneg_left hP2 hw0.le
  have hpos : 0 < w * (m : ℝ) ^ 2 := by positivity
  linarith

/-- Sizes of `k = ⌈log L⌉` and `y = K' L² (log L)²` for `L ≥ K'` and `log L ≥ 61`. -/
lemma sizes_W {K' L ℓ y : ℝ} {k : ℕ} (hK' : 1 ≤ K') (hLK : K' ≤ L) (hℓdef : ℓ = Real.log L)
    (hℓ : 61 ≤ ℓ) (hkdef : k = ⌈ℓ⌉₊) (hy : y = K' * L ^ 2 * ℓ ^ 2) :
    1 ≤ k ∧ L ≤ 3 ^ k ∧ (k : ℝ) ≤ 2 * ℓ ∧ y ^ k ≤ Real.exp (L - 1) ∧ 1 ≤ y ∧
      Real.log y ≤ 5 * ℓ ∧ y / 4 + L ≤ Chebyshev.theta y := by
  have hL1 : 1 ≤ L := hK'.trans hLK
  have hL0 : 0 < L := by linarith
  have hexp : Real.exp ℓ = L := by rw [hℓdef, Real.exp_log hL0]
  have hℓ0 : 0 < ℓ := by linarith
  have hℓk : ℓ ≤ k := hkdef ▸ Nat.le_ceil ℓ
  have hkℓ : (k : ℝ) < ℓ + 1 := hkdef ▸ Nat.ceil_lt_add_one hℓ0.le
  have hk1 : 1 ≤ k := by rw [hkdef]; exact Nat.ceil_pos.mpr hℓ0
  -- `L ≥ ℓ³ / 6`
  have hL6 : ℓ ^ 3 / 6 ≤ L := by
    have := Real.pow_div_factorial_le_exp (x := ℓ) hℓ0.le 3
    rw [hexp] at this
    simpa [Nat.factorial] using this
  have hℓ2 : ℓ ^ 2 * 61 ≤ ℓ ^ 3 := by
    calc ℓ ^ 2 * 61 ≤ ℓ ^ 2 * ℓ := by gcongr
      _ = ℓ ^ 3 := by ring
  have hℓL : 10 * ℓ ^ 2 + 1 ≤ L - 1 := by nlinarith
  have hℓL' : ℓ ≤ L := by nlinarith
  have hy1 : 1 ≤ y := by
    rw [hy]
    calc (1 : ℝ) = 1 * 1 ^ 2 * 1 ^ 2 := by ring
      _ ≤ K' * L ^ 2 * ℓ ^ 2 := by gcongr; linarith
  have hy5 : y ≤ L ^ 5 := by
    rw [hy]
    calc K' * L ^ 2 * ℓ ^ 2 ≤ L * L ^ 2 * L ^ 2 := by gcongr
      _ = L ^ 5 := by ring
  have hly : Real.log y ≤ 5 * ℓ := by
    calc Real.log y ≤ Real.log (L ^ 5) := Real.log_le_log (by linarith) hy5
      _ = 5 * ℓ := by rw [Real.log_pow, hℓdef]; norm_num
  refine ⟨hk1, ?_, by linarith, ?_, ?_, ?_, ?_⟩
  · calc L = Real.exp ℓ := hexp.symm
      _ ≤ Real.exp k := Real.exp_le_exp.mpr hℓk
      _ = Real.exp 1 ^ k := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ 3 ^ k := by
          gcongr
          have := Real.exp_one_lt_d9
          linarith
  · calc y ^ k ≤ (L ^ 5) ^ k := pow_le_pow_left₀ (by linarith) hy5 k
      _ = Real.exp ((5 * k : ℕ) * ℓ) := by rw [Real.exp_nat_mul, hexp, ← pow_mul]
      _ ≤ Real.exp (L - 1) := by
          rw [Real.exp_le_exp]
          push_cast
          nlinarith
  · exact hy1
  · exact hly
  · have hth := Chebyshev.theta_ge' hy1
    have hlog2 := Real.log_two_gt_d9
    have hyL : 3721 * L ≤ y := by
      rw [hy]
      calc 3721 * L = 1 * L * 61 ^ 2 := by ring
        _ ≤ K' * L ^ 2 * ℓ ^ 2 := by
            gcongr
            · nlinarith
    have hy2 : 2 ≤ y := by nlinarith
    have hl1 : Real.log (y + 2) ≤ 10 * ℓ := by
      calc Real.log (y + 2) ≤ Real.log (y ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
        _ = 2 * Real.log y := by rw [Real.log_pow]; norm_num
        _ ≤ 10 * ℓ := by linarith
    have hsy : 100 * ℓ ≤ Real.sqrt y := by
      rw [Real.le_sqrt (by positivity) (by linarith), hy]
      have hL100 : (100 : ℝ) ≤ L := by nlinarith
      calc (100 * ℓ) ^ 2 = 10000 * ℓ ^ 2 := by ring
        _ ≤ 1 * L ^ 2 * ℓ ^ 2 := by gcongr; nlinarith
        _ ≤ K' * L ^ 2 * ℓ ^ 2 := by gcongr
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    have hss : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
    have hl2 : 2 * Real.sqrt y * Real.log y ≤ y / 10 := by
      have hly0 : 0 ≤ Real.log y := Real.log_nonneg hy1
      calc 2 * Real.sqrt y * Real.log y ≤ 2 * Real.sqrt y * (5 * ℓ) := by gcongr
        _ = Real.sqrt y * (100 * ℓ) / 10 := by ring
        _ ≤ Real.sqrt y * Real.sqrt y / 10 := by gcongr
        _ = y / 10 := by rw [hss]
    nlinarith

/-! ### Theorem W -/

/-- **Theorem W, conditional on `GRHSmoothBound`.** For all large `m`, every unit `a` mod `m` is
`p q s` with primes `p, q ≤ m` and a prime `s ≤ K (log m)² (log log m)²`. -/
theorem coveredBy_three_primes (h : GRHSmoothBound) :
    ∃ K m₀ : ℝ, 0 < K ∧ ∀ m : ℕ, (m : ℝ) ≥ m₀ →
      ∀ a : ZMod m, IsUnit a → ∃ p q s : ℕ, p.Prime ∧ q.Prime ∧ s.Prime ∧ p ≤ m ∧ q ≤ m ∧
        (s : ℝ) ≤ K * (Real.log m) ^ 2 * (Real.log (Real.log m)) ^ 2 ∧
        ((p * q * s : ℕ) : ZMod m) = a := by
  obtain ⟨C, hC0, hC⟩ := h.bounds
  set c := 3 * (C ^ 2 + 1) * 2048 ^ 2 with hc
  set K' := 40 * c with hK'
  have hK'1 : 1 ≤ K' := by rw [hK', hc]; nlinarith [sq_nonneg C]
  have hK'C : 64 * C ^ 2 ≤ K' := by rw [hK', hc]; nlinarith [sq_nonneg C]
  refine ⟨K', max (2 ^ 80) (Real.exp (max K' (Real.exp 61))), by linarith, ?_⟩
  intro m hm a ha
  have hm1 : (2 : ℝ) ^ 80 ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : Real.exp (max K' (Real.exp 61)) ≤ m := le_trans (le_max_right _ _) hm
  have hm0 : (0 : ℝ) < m := by linarith [show (0 : ℝ) < 2 ^ 80 by norm_num]
  have hmpos : 0 < m := by exact_mod_cast hm0
  have : NeZero m := ⟨hmpos.ne'⟩
  set L := Real.log m with hLdef
  have hLmax : max K' (Real.exp 61) ≤ L := (Real.le_log_iff_exp_le hm0).mpr hm2
  have hLK : K' ≤ L := le_trans (le_max_left _ _) hLmax
  have hLe : Real.exp 61 ≤ L := le_trans (le_max_right _ _) hLmax
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hLe
  set ℓ := Real.log L with hℓdef
  have hℓ : 61 ≤ ℓ := (Real.le_log_iff_exp_le hL0).mpr hLe
  set k := ⌈ℓ⌉₊ with hkdef
  set y := K' * L ^ 2 * ℓ ^ 2 with hy
  obtain ⟨hk1, hL3, hk2, hyk, hy1, hly, hθ⟩ := sizes_W hK'1 hLK hℓdef hℓ hkdef hy
  set W := smallPrimes m y with hW
  set w := (W.card : ℝ) with hwdef
  -- the size of `W`
  have hw : 3 * (C ^ 2 + 1) * k * (2048 * L) ^ 2 ≤ w := by
    have hcount := theta_sub_log_le m hmpos.ne' hy1
    have hw0 : 0 ≤ w := Nat.cast_nonneg _
    have hℓ0 : 0 < ℓ := by linarith
    have h1 : y / 4 ≤ w * (5 * ℓ) := by
      have : w * Real.log y ≤ w * (5 * ℓ) := mul_le_mul_of_nonneg_left hly hw0
      linarith
    have h2 : 20 * ℓ * (3 * (C ^ 2 + 1) * k * (2048 * L) ^ 2) ≤ 20 * ℓ * w := by
      calc 20 * ℓ * (3 * (C ^ 2 + 1) * k * (2048 * L) ^ 2)
          = 20 * ℓ * k * (c * L ^ 2) := by rw [hc]; ring
        _ ≤ 20 * ℓ * (2 * ℓ) * (c * L ^ 2) := by gcongr
        _ = y := by rw [hy, hK']; ring
        _ ≤ 20 * ℓ * w := by linarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  -- all products of `k` elements of `W` are `< m`
  have hprod : ∀ t ∈ Fintype.piFinset (fun _ : Fin k ↦ W), ∏ i, t i ≤ m - 1 := by
    intro t ht
    have h1 : ∏ i, t i ≤ ⌊y⌋₊ ^ k := by
      have := Finset.prod_le_pow_card (univ : Finset (Fin k)) t ⌊y⌋₊ fun i _ ↦
        mem_Iic.mp (mem_filter.mp (Fintype.mem_piFinset.mp ht i)).1
      simpa using this
    have h2 : ((⌊y⌋₊ ^ k : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
      push_cast
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      calc (⌊y⌋₊ : ℝ) ^ k ≤ y ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _)
            (Nat.floor_le (by linarith)) k
        _ ≤ Real.exp (L - 1) := hyk
        _ = m / Real.exp 1 := by rw [Real.exp_sub, hLdef, Real.exp_log hm0]
        _ ≤ m / 2 := by
            gcongr
            have := Real.exp_one_gt_d9
            linarith
        _ ≤ m - 1 := by linarith
    exact h1.trans (by exact_mod_cast h2)
  -- the analytic input at `x = m - 1`
  set x : ℝ := ((m - 1 : ℕ) : ℝ) with hx
  have hx' : x = m - 1 := by rw [hx, Nat.cast_sub (by omega), Nat.cast_one]
  have hCL : 64 * C ^ 2 ≤ L := hK'C.trans hLK
  obtain ⟨hx1, hP0, hineq⟩ := analytic_W hC0 m hm1 hCL hk1 hL3 hw x hx'
  obtain ⟨hprin, hnon⟩ := hC m x hx1
  have hfl : ⌊x⌋₊ = m - 1 := by rw [hx, Nat.floor_natCast]
  have hV : (m : ℝ) * ∑ n ∈ Iic (m - 1), cw x n ^ 2 ≤ 7 * m ^ 2 * L := by
    have hsq := sum_cw_sq_le hx1
    rw [hfl] at hsq
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
    have hxm : x ≤ m := by rw [hx']; linarith
    have hlx : Real.log x ≤ L := Real.log_le_log (by linarith) hxm
    have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hc2 : ∑ n ∈ Iic (m - 1), cw x n ^ 2 ≤ 7 * (m * L) := by
      calc _ ≤ (Real.log 4 + 4) * x * Real.log x := hsq
        _ ≤ 7 * (x * Real.log x) := by rw [mul_assoc]; gcongr; linarith
        _ ≤ 7 * (m * L) := by gcongr
    calc (m : ℝ) * ∑ n ∈ Iic (m - 1), cw x n ^ 2 ≤ m * (7 * (m * L)) := by gcongr
      _ = 7 * m ^ 2 * L := by ring
  have hlam : 0 < w / (2048 * L) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk1
    exact div_pos (lt_of_lt_of_le (by positivity) hw) (by positivity)
  obtain ⟨p, q, s, hp, hq, hs, hpm, hqm, hpqs⟩ :=
    exists_three_of_criterion m ha W (fun s hs ↦ smallPrimes_prime hs)
      (fun s hs ↦ smallPrimes_isUnit hs) hk1 hprod hx hx1 hlam hP0 hprin hnon hV hineq
  refine ⟨p, q, s, hp, hq, smallPrimes_prime hs, by omega, by omega, ?_, hpqs⟩
  exact smallPrimes_le (by linarith) hs

end EOS
