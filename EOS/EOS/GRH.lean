import Mathlib

/-!
# The Generalized Riemann Hypothesis for Dirichlet L-functions, stated literally

`EOS.GRH` says: for every modulus `q ≥ 1` and every **primitive** Dirichlet character `χ` mod `q`,
every zero `s` of `DirichletCharacter.LFunction χ` in the open critical strip `0 < Re s < 1`
lies on the critical line `Re s = 1/2`.

Design notes.
* `DirichletCharacter.LFunction χ` is Mathlib's analytic continuation of `Σ χ(n) n^{-s}`. It is
  entire for `χ ≠ 1`. For the trivial character it has a simple pole at `s = 1`, where Mathlib
  stores a junk value. The strict inequality `Re s < 1` excludes `s = 1`, so the junk value never
  enters the definition.
* The strip `0 < Re s < 1` loses nothing: for primitive `χ` there are no zeros with `Re s ≥ 1`
  (`DirichletCharacter.LFunction_ne_zero_of_one_le_re`), and the zeros with `Re s ≤ 0` are the
  trivial ones (`DirichletCharacter.LFunction_eq_zero_iff_of_re_nonpos`).
* Primitive characters suffice. For imprimitive `χ` induced by `χ*`,
  `L(s, χ) = L(s, χ*) · ∏_{p ∣ q} (1 - χ*(p) p^{-s})`, and the Euler factors vanish only on
  `Re s = 0`. `GRH_iff_forall` proves that the definition is equivalent to the same statement for
  all characters. (The analytic proof of `GRHSmoothBound` uses primitive characters only; see
  notes/routes/C-log-exponent.md §1.4, Theorem 1, and notes/grh-blueprint.md.)
* `q = 1`, `χ = 1` gives `riemannZeta` (`DirichletCharacter.LFunction_modOne_eq`), so `GRH`
  contains the Riemann hypothesis: `GRH.riemannHypothesis` derives Mathlib's `RiemannHypothesis`.
-/

namespace EOS

open DirichletCharacter Complex

/-- **The Generalized Riemann Hypothesis** for Dirichlet L-functions: for every `q ≥ 1` and every
primitive Dirichlet character `χ` mod `q`, every zero of `L(s, χ)` with `0 < Re s < 1` has
`Re s = 1/2`. -/
def GRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → LFunction χ s = 0 → s.re = 1 / 2

/-- **GRH implies RH** (Mathlib's `RiemannHypothesis`). Zeros of `ζ` with `Re s ≥ 1` do not exist,
zeros with `Re s ≤ 0` are trivial, and the rest are covered by `GRH` at `q = 1`. -/
theorem GRH.riemannHypothesis (h : GRH) : RiemannHypothesis := by
  intro s hz htriv _
  rcases le_or_gt s.re 0 with hs0 | hs0
  · exact absurd ((riemannZeta_eq_zero_iff_of_re_nonpos hs0).mp hz) htriv
  rcases lt_or_ge s.re 1 with hs1 | hs1
  · refine h 1 1 isPrimitive_one_level_one s hs0 hs1 ?_
    rwa [LFunction_modOne_eq]
  · exact absurd hz (riemannZeta_ne_zero_of_one_le_re hs1)

/-- An Euler factor `1 - c p^{-s}` with `‖c‖ ≤ 1`, `p ≥ 2` and `Re s > 0` does not vanish. -/
lemma one_sub_mul_cpow_ne_zero {c : ℂ} (hc : ‖c‖ ≤ 1) {p : ℕ} (hp : 2 ≤ p) {s : ℂ}
    (hs : 0 < s.re) : 1 - c * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : c * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [norm_natCast_cpow_of_pos (by omega), neg_re]
  have hlt : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < p)) (by linarith)
  have := congrArg norm h1
  rw [norm_mul, hnorm, norm_one] at this
  have hpos : 0 ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg hp0.le _
  nlinarith [norm_nonneg c]

/-- In the open strip `0 < Re s < 1`, an L-function vanishes iff the L-function of the inducing
primitive character vanishes. -/
lemma LFunction_eq_zero_iff_primitiveCharacter {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0 := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hs : s ≠ 1 := fun h ↦ by simp [h] at hs1
  conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
  rw [LFunction_changeLevel _ _ (.inr hs), mul_eq_zero, or_iff_left_iff_imp]
  intro hprod
  obtain ⟨p, hp, hp0⟩ := Finset.prod_eq_zero_iff.mp hprod
  exact absurd hp0 (one_sub_mul_cpow_ne_zero (norm_le_one _ _)
    (Nat.prime_of_mem_primeFactors hp).two_le hs0)

/-- `GRH` is equivalent to the same statement for **all** Dirichlet characters, primitive or not:
the restriction to primitive characters loses nothing in the strip `0 < Re s < 1`. -/
theorem GRH_iff_forall : GRH ↔
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      ∀ s : ℂ, 0 < s.re → s.re < 1 → LFunction χ s = 0 → s.re = 1 / 2 := by
  refine ⟨fun h q _ χ s hs0 hs1 hz ↦ ?_, fun h q _ χ _ ↦ h q χ⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact h χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive s hs0 hs1
    ((LFunction_eq_zero_iff_primitiveCharacter χ hs0 hs1).mp hz)

end EOS
