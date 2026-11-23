/-
Vendored from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
file `PrimeNumberTheoremAnd/ZetaBounds.lean`,
commit a4fb6989b07e9c76b511807ae93e33e25b820e9b (2026-11-15).
Licence: Apache License 2.0, see `EOS/EOS/Vendor/PNT/LICENSE`.
Copyright: the upstream file has no copyright header; copyright belongs to the
PrimeNumberTheoremAnd contributors (Apache License 2.0).
See `EOS/EOS/Vendor/PNT/NOTICE.md`.

Local modifications:
- Removed the Lean module system keywords (`module`, `public`, `@[expose] public`,
  `public import`) and the `import Architect` line.
- Removed the LeanArchitect `@[blueprint ...]` attributes; where an attribute carried a
  `statement := /-- ... -/`, that text is kept as a plain comment `/- Blueprint statement ... -/`.
- Tactic-level docstrings `/-- ... -/` inside proofs (a LeanArchitect feature) are now plain
  comments `/- ... -/`.
- `blueprint_comment /-- ... -/` commands are kept as plain comments `/- ... -/`.
- Import paths `PrimeNumberTheoremAnd.*` renamed to `EOS.Vendor.PNT.*`. Declaration names and
  namespaces unchanged.
- Trailing whitespace removed. Style linters disabled by `set_option` after the imports,
  as the upstream lakefile does (plus `linter.style.missingEnd`).
- **Excerpt only.** This file contains the import/`open` header of upstream `ZetaBounds.lean`
  (lines 1–21) and upstream lines 500–578: the theorem `ResidueMult` with its blueprint comment.
  The upstream imports are replaced by `import PrimeNumberTheoremAnd.ResidueCalcOnRectangles`
  (which provides `HolomorphicOn`); `set_option lang.lemmaCmd true` is dropped (unused).
  Everything else (ζ bounds, `logDerivResidue`, ...) is omitted.
-/

import EOS.Vendor.PNT.ResidueCalcOnRectangles

-- Local modification: style linters disabled as in the upstream lakefile.
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.openClassical false
set_option linter.style.missingEnd false

section

open Complex Topology Filter Interval Set Asymptotics

/-
Let's also record that if a function $f$ has a simple pole at $p$ with residue $A$, and $g$ is
holomorphic near $p$, then the residue of $f \cdot g$ is $A \cdot g(p)$.
-/

/- Blueprint statement (upstream `@[blueprint]` annotation):
If $f$ has a simple pole at $p$ with residue $A$, and $g$ is holomorphic near $p$, then the
  residue of $f \cdot g$ at $p$ is $A \cdot g(p)$. That is, we assume that
  $$
  f(s) = \frac{A}{s - p} + O(1)$$
  near $p$, and that $g$ is holomorphic near $p$. Then
  $$
  f(s) \cdot g(s) = \frac{A \cdot g(p)}{s - p} + O(1).$$
-/
theorem ResidueMult {f g : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (g_holc : HolomorphicOn g U) (U_in_nhds : U ∈ 𝓝 p) {A : ℂ}
    (f_near_p : (f - (fun s ↦ A * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    (f * g - (fun s ↦ A * g p * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  -- Add and subtract a term
  have : (f * g - fun s ↦ A * g p * (s - p)⁻¹)
      = (f - A • fun s ↦ (s - p)⁻¹) * g + fun s ↦ (A * (g s - g p) / (s - p)) := by
    ext; simp; ring
  -- Apply to goal
  rw[this]
  have p_in_U : p ∈ U := mem_of_mem_nhds U_in_nhds
  refine Asymptotics.IsBigO.add ?_ ?_
  · rw[← mul_one (1 : ℂ → ℂ)]
    refine Asymptotics.IsBigO.mul f_near_p ?_
    -- Show g is bounded near p
    have g_cont : ContinuousAt g p := by
      -- g is holomorphic on U, p ∈ U, so g is continuous at p
      exact (g_holc.continuousOn.continuousWithinAt p_in_U).continuousAt U_in_nhds
    -- Use continuity to get boundedness
    have := g_cont.norm.isBoundedUnder_le.isBigO_one ℂ
    exact IsBigO.mono this inf_le_left
  · -- Show that (fun s ↦ A * (g s - g p) / (s - p)) =O[𝓝[≠] p] 1

    suffices (fun s ↦ A * ((s - p)⁻¹ * (g s - g p))) =O[𝓝[≠] p] 1 by
      convert! this using 2
      rw[div_eq_mul_inv]
      ring
    apply Asymptotics.IsBigO.const_mul_left

    -- g is differentiable at p since it's holomorphic on U
    have g_diff : HasDerivAt g (deriv g p) p :=
        (DifferentiableOn.differentiableAt g_holc U_in_nhds).hasDerivAt

    rw [hasDerivAt_iff_isLittleO] at g_diff
    apply Asymptotics.IsLittleO.isBigO at g_diff
    have : (fun x' ↦ deriv g p * (x' - p)) =O[𝓝 p] fun x' ↦ x' - p := by
      apply Asymptotics.IsBigO.const_mul_left
      exact Asymptotics.isBigO_refl (fun x ↦ x - p) (𝓝 p)
    have h1 := g_diff.add this
    have h2 : (fun x ↦ g x - g p) =O[𝓝 p] fun x' ↦ x' - p := by
      convert! h1 using 2
      simp
      ring
    refine (Asymptotics.isBigO_mul_iff_isBigO_div ?_).mpr ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_compl_iff, mem_singleton_iff] at hx
      exact inv_ne_zero (sub_ne_zero.mpr hx)
    · simp only [div_inv_eq_mul]
      refine Asymptotics.IsBigO.mono ?_ inf_le_left
      simpa
