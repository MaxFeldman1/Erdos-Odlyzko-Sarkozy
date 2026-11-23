import Mathlib

/-!
# The Erdős–Odlyzko–Sárközy conjecture: statements

The target theorem is `eos_of_grhBounds`. The analytic input is `GRHBounds`, a standard
consequence of GRH for Dirichlet L-functions. It is used as a hypothesis during the
approach phase. Deriving `GRHBounds` from a literal GRH statement is a separate, later task.
-/

open scoped BigOperators
open Finset

namespace EOS

/-- Every unit mod `m` is `p * q` with primes `p, q ≤ Y`. -/
def CoveredBy (m : ℕ) (Y : ℝ) : Prop :=
  ∀ a : ZMod m, IsUnit a →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (p : ℝ) ≤ Y ∧ (q : ℝ) ≤ Y ∧ ((p * q : ℕ) : ZMod m) = a

/-- The Erdős–Odlyzko–Sárközy conjecture (two primes, both `≤ m`, all large `m`). -/
def Conjecture : Prop := ∃ m₀ : ℕ, ∀ m ≥ m₀, CoveredBy m m

/-- Chebyshev sum twisted by a Dirichlet character: `ψ(x, χ) = Σ_{n ≤ x} Λ(n) χ(n)`. -/
noncomputable def psiChi {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Iic ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n

/-- **Analytic input (consequence of GRH).** There is an absolute constant `C` such that for
every modulus `q ≥ 1`, every Dirichlet character `χ` mod `q`, and every `x ≥ 2`,
`|ψ(x, χ) - [χ = 1] x| ≤ C √x (log (q x))²`.
(Classical, e.g. Davenport ch. 20. Explicit versions: Lamzouri–Li–Soundararajan,
Math. Comp. 2015.) -/
def GRHBounds : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x →
    ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤ C * Real.sqrt x * (Real.log (q * x)) ^ 2

/-- Target theorem. -/
theorem eos_of_grhBounds (h : GRHBounds) : Conjecture := by
  sorry

end EOS
