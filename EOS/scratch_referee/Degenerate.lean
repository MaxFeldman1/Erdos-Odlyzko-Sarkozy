import EOS
open EOS

/-- `H4 η 0` is trivially true (no blocks): the definition is only meaningful for `λ > 0`. -/
example (η : ℝ) : H4 η 0 := by
  refine ⟨0, fun m _ _ j hj => ?_⟩
  simp [numBlocks] at hj

/-- `H4 (1/2) λ` is trivially true (no blocks): only meaningful for `η < 1/2`. -/
example (lam : ℝ) : H4 (1 / 2) lam := by
  refine ⟨0, fun m _ _ j hj => ?_⟩
  simp [numBlocks] at hj

/-- `CoveredBy 1 1` is false: the definition does not allow `p = q = 1`. -/
example : ¬ CoveredBy 1 1 := by
  intro h
  obtain ⟨p, q, hp, -, hp1, -, -⟩ := h 0 (by simp [isUnit_iff_eq_one, eq_iff_true_of_subsingleton])
  have : p ≤ 1 := by exact_mod_cast hp1
  exact absurd hp.two_le (by omega)

/-- For `m ≥ 2`, a prime factor in a representation of a unit is automatically `< m` (so `≤ m` = `< m`). -/
example (m : ℕ) (hm : 2 ≤ m) (a : ZMod m) (ha : IsUnit a) (p q : ℕ) (hp : p ≤ m)
    (h : ((p * q : ℕ) : ZMod m) = a) : p < m := by
  rcases hp.lt_or_eq with h1 | rfl
  · exact h1
  · exfalso
    have : ((p * q : ℕ) : ZMod p) = 0 := by simp
    rw [this] at h
    rw [← h] at ha
    haveI : Fact (1 < p) := ⟨by omega⟩
    exact not_isUnit_zero ha
