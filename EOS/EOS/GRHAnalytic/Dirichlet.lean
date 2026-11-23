import Mathlib
import EOS.LogSquare
import EOS.Vendor.PNT.PerronFormula

/-!
# Dirichlet-series side of the literal-GRH route (blueprint M2)

This file implements items A1 and A2 of `notes/grh-blueprint.md`:

* **A1** `EOS.LSeries_twist_vonMangoldt_eq_LFunction`: for `1 < re s`,
  `∑ χ(n) Λ(n) n^{-s} = -L'(s, χ) / L(s, χ)`, stated for `DirichletCharacter.LFunction`.
  This transfers Mathlib's `DirichletCharacter.LSeries_twist_vonMangoldt_eq` (stated for `LSeries`).
* **A2** `EOS.perron_cesaro_kernel`: for `y > 0` and `σ > 0`,
  `(1/2πi) ∫_{(σ)} y^s / (s(s+1)) ds = max 0 (1 - 1/y)`, **including `y = 1`**.
  The cases `y > 1` and `y < 1` are the vendored `Perron.formulaGtOne` and `Perron.formulaLtOne`;
  the case `y = 1` follows by dominated convergence as `y → 1⁺`.
* **A3** `EOS.psiCesaro_eq_verticalIntegral` (the M2 gate): for `x > 0` and `σ > 1`,
  `psiCesaro χ x = (1/2πi) ∫_{(σ)} (-L'/L)(s, χ) x^s / (s(s+1)) ds`, for every Dirichlet
  character `χ` (principal or not, any modulus `q ≥ 1`; for `q = 1` this is `-ζ'/ζ`).
  Proof: expand `-L'/L` as its Dirichlet series (A1), swap sum and integral (the sum of the
  `L¹` norms is `∑ |χ(n)Λ(n)| n^{-σ} · ∫ |x^s/(s(s+1))| dt < ∞`), and apply A2 to each term
  with `y = x/n`.
-/

open Complex Filter Topology MeasureTheory
open scoped LSeries.notation ArithmeticFunction.vonMangoldt

namespace EOS

/-! ### A1: the twisted von Mangoldt series is `-L'/L` -/

/-- **A1.** For `1 < re s`, the L-series of `n ↦ χ(n) Λ(n)` equals `-L'(s, χ) / L(s, χ)`, where
`L(·, χ) = DirichletCharacter.LFunction χ`. -/
theorem LSeries_twist_vonMangoldt_eq_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ χ n * Λ n) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs]
  exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs

/-- **A1**, logarithmic-derivative form: for `1 < re s`,
`L(Λχ, s) = -logDeriv (LFunction χ) s`. -/
theorem LSeries_twist_vonMangoldt_eq_neg_logDeriv {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ χ n * Λ n) s = -logDeriv (DirichletCharacter.LFunction χ) s := by
  rw [LSeries_twist_vonMangoldt_eq_LFunction χ hs, logDeriv_apply, neg_div]

/-- The series `∑ χ(n) Λ(n) n^{-s}` converges absolutely for `1 < re s`. -/
theorem LSeriesSummable_twist_vonMangoldt' {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (fun n ↦ χ n * Λ n) s :=
  DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs

/-! ### A2: the Perron formula for the Cesàro kernel `y^s / (s(s+1))` -/

/-- The integrand on the line `re s = σ`, as a function of `y`, tends to its value at `y = 1`
in `L¹` (dominated convergence), so the vertical integral is right-continuous at `y = 1`. -/
private lemma tendsto_verticalIntegral_kernel_one {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun y : ℝ ↦ ∫ t : ℝ, Perron.f y (σ + t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, Perron.f 1 (σ + t * I))) := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hσ1 : σ ≠ -1 := by linarith
  -- dominating function
  set bound : ℝ → ℝ := fun t ↦ 2 ^ σ * ‖Perron.f 1 (σ + t * I)‖ with hbound
  have hint1 : Integrable (fun t : ℝ ↦ Perron.f 1 (σ + t * I)) :=
    Perron.isIntegrable one_pos hσ0 hσ1
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (Perron.isIntegrable (lt_trans one_pos hy) hσ0 hσ1).aestronglyMeasurable
  · have h2 : Set.Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT one_lt_two
    filter_upwards [h2] with y hy
    refine ae_of_all _ fun t ↦ ?_
    have hy0 : 0 < y := lt_trans one_pos hy.1
    simp only [Perron.f, hbound, norm_div, norm_cpow_eq_rpow_re_of_pos hy0,
      Complex.ofReal_one, one_cpow, add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, one_div]
    rw [norm_inv, ← div_eq_mul_inv]
    gcongr
    exact hy.2.le
  · exact hint1.norm.const_mul _
  · refine ae_of_all _ fun t ↦ ?_
    simp only [Perron.f]
    refine Tendsto.div_const ?_ _
    exact ((continuousAt_ofReal_cpow_const 1 _ (Or.inr one_ne_zero)).tendsto).mono_left
      nhdsWithin_le_nhds

/-- The Perron integral of the Cesàro kernel at `y = 1` vanishes. -/
theorem perron_cesaro_kernel_one {σ : ℝ} (hσ : 0 < σ) :
    VerticalIntegral' (fun s : ℂ ↦ ((1 : ℝ) : ℂ) ^ s / (s * (s + 1))) σ = 0 := by
  -- `G y` is the normalised vertical integral; it equals `1 - 1/y` for `y > 1`.
  set G : ℝ → ℂ := fun y ↦ VerticalIntegral' (fun s : ℂ ↦ (y : ℂ) ^ s / (s * (s + 1))) σ
  have hG : Tendsto G (𝓝[>] 1) (𝓝 (G 1)) := by
    have := ((tendsto_verticalIntegral_kernel_one hσ).const_smul I).const_smul
      (1 / (2 * (Real.pi : ℂ) * I))
    exact this
  have hG' : Tendsto G (𝓝[>] 1) (𝓝 0) := by
    have heq : (fun y : ℝ ↦ (1 : ℂ) - 1 / (y : ℂ)) =ᶠ[𝓝[>] 1] G := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (Perron.formulaGtOne hy hσ).symm
    refine Tendsto.congr' heq ?_
    have hc : ContinuousAt (fun y : ℝ ↦ (1 : ℂ) - 1 / (y : ℂ)) 1 := by
      refine continuousAt_const.sub (continuousAt_const.div ?_ ?_)
      · exact Complex.continuous_ofReal.continuousAt
      · simp
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa using this
  exact tendsto_nhds_unique hG hG'

/-- **A2.** The Perron formula for the Cesàro kernel: for `y > 0` and `σ > 0`,
`(1/2πi) ∫_{(σ)} y^s / (s(s+1)) ds = max 0 (1 - 1/y)`. This includes the boundary case `y = 1`. -/
theorem perron_cesaro_kernel {y σ : ℝ} (hy : 0 < y) (hσ : 0 < σ) :
    VerticalIntegral' (fun s : ℂ ↦ (y : ℂ) ^ s / (s * (s + 1))) σ =
      ((max 0 (1 - 1 / y) : ℝ) : ℂ) := by
  rcases lt_trichotomy y 1 with h | rfl | h
  · have h1 : 1 - 1 / y ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hy, one_mul]; exact h.le
    rw [max_eq_left h1, ofReal_zero]
    change (1 / (2 * (Real.pi : ℂ) * I)) • VerticalIntegral (Perron.f y) σ = 0
    rw [Perron.formulaLtOne hy h hσ, smul_zero]
  · rw [perron_cesaro_kernel_one hσ]; simp
  · have h1 : 0 ≤ 1 - 1 / y := by
      rw [sub_nonneg, div_le_iff₀ hy, one_mul]; exact h.le
    rw [max_eq_right h1, Perron.formulaGtOne h hσ]
    push_cast; ring

/-- **A2**, in the form used for the Cesàro-weighted sums: for `0 < n`, `0 < x` and `σ > 0`,
`(1/2πi) ∫_{(σ)} (x/n)^s / (s(s+1)) ds = max 0 (1 - n/x)`. -/
theorem perron_cesaro_kernel_div {x n σ : ℝ} (hx : 0 < x) (hn : 0 < n) (hσ : 0 < σ) :
    VerticalIntegral' (fun s : ℂ ↦ ((x / n : ℝ) : ℂ) ^ s / (s * (s + 1))) σ =
      ((max 0 (1 - n / x) : ℝ) : ℂ) := by
  rw [perron_cesaro_kernel (div_pos hx hn) hσ, one_div_div]

/-! ### A3: `psiCesaro` as a vertical integral of `-L'/L` against the Cesàro kernel -/

/-- **A3** (blueprint M2 gate). For every Dirichlet character `χ` mod `q ≥ 1`, `x > 0` and
`σ > 1`:
`psiCesaro χ x = (1/2πi) ∫_{(σ)} (-L'(s, χ)/L(s, χ)) · x^s / (s(s+1)) ds`. -/
theorem psiCesaro_eq_verticalIntegral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    psiCesaro χ x = VerticalIntegral'
      (fun s : ℂ ↦ -deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s * ((x : ℂ) ^ s / (s * (s + 1)))) σ := by
  set a : ℕ → ℂ := fun n ↦ χ n * Λ n with ha
  set F : ℕ → ℝ → ℂ :=
    fun n t ↦ LSeries.term a (σ + t * I) n * Perron.f x (σ + t * I) with hF
  have hσ0 : σ ≠ 0 := by linarith
  have hσ1 : σ ≠ -1 := by linarith
  have hre : ∀ t : ℝ, ((σ : ℂ) + t * I).re = σ := fun t ↦ by simp
  -- Step 1: on the line, the integrand is `∑' n, F n t` (Dirichlet series of `-L'/L`, A1).
  have h1 : ∀ t : ℝ, -deriv (DirichletCharacter.LFunction χ) (σ + t * I) /
      DirichletCharacter.LFunction χ (σ + t * I) *
        ((x : ℂ) ^ ((σ : ℂ) + t * I) / ((σ + t * I) * (σ + t * I + 1))) = ∑' n, F n t := by
    intro t
    rw [← LSeries_twist_vonMangoldt_eq_LFunction χ (by rw [hre]; exact hσ), LSeries,
      ← tsum_mul_right]
  -- Step 2: for `n ≠ 0`, `F n` is `a n` times the Perron kernel at `y = x / n`.
  have hFn : ∀ n, n ≠ 0 → ∀ t : ℝ, F n t = a n * Perron.f (x / n) (σ + t * I) := by
    intro n hn t
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    simp only [hF, LSeries.term_of_ne_zero hn]
    rw [← Perron.f_mul_eq_f hx hn', Complex.cpow_neg, Complex.ofReal_natCast, div_eq_mul_inv]
    ring
  have hF_int : ∀ n, Integrable (F n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hF]
    · rw [show F n = fun t : ℝ ↦ a n * Perron.f (x / n) (σ + t * I) from funext (hFn n hn)]
      exact (Perron.isIntegrable (div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))
        hσ0 hσ1).const_mul _
  -- Step 3: the `L¹` norms are summable.
  have hF_norm : ∀ n, ∫ t, ‖F n t‖ =
      ‖LSeries.term a σ n‖ * ∫ t : ℝ, ‖Perron.f x (σ + t * I)‖ := by
    intro n
    rw [← integral_const_mul]
    refine congrArg (fun g : ℝ → ℝ ↦ ∫ t, g t) (funext fun t ↦ ?_)
    rw [hF, norm_mul, LSeries.norm_term_eq, LSeries.norm_term_eq, hre, ofReal_re]
  have hF_sum : Summable fun n ↦ ∫ t, ‖F n t‖ := by
    simp_rw [hF_norm]
    exact (LSeriesSummable_twist_vonMangoldt' χ (s := σ) (by simpa using hσ)).norm.mul_right _
  have key := integral_tsum_of_summable_integral_norm hF_int hF_sum
  -- Step 4: each term, by A2.
  have hterm : ∀ n, (1 / (2 * (Real.pi : ℂ) * I)) * (I * ∫ t, F n t) =
      if n = 0 then 0 else a n * ((max 0 (1 - n / x) : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hF]
    · rw [ite_eq_right hn,
        show F n = fun t : ℝ ↦ a n * Perron.f (x / n) (σ + t * I) from funext (hFn n hn),
        integral_const_mul, ← perron_cesaro_kernel_div hx
          (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) (by linarith : (0 : ℝ) < σ)]
      simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
      ring
  -- Step 5: assemble.
  have hint : VerticalIntegral'
      (fun s : ℂ ↦ -deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s * ((x : ℂ) ^ s / (s * (s + 1)))) σ =
      ∑' n, (if n = 0 then 0 else a n * ((max 0 (1 - n / x) : ℝ) : ℂ)) := by
    simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
    simp_rw [h1, ← key, ← hterm]
    rw [← tsum_mul_left, ← tsum_mul_left]
  rw [hint, tsum_eq_sum (s := Finset.Iic ⌊x⌋₊)]
  · unfold psiCesaro
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp (Finset.mem_Iic.mp hn)
      have h0 : 0 ≤ 1 - (n : ℝ) / x := by
        rw [sub_nonneg, div_le_one hx]; exact hnx
      rw [ite_eq_right hn0, max_eq_right h0, ha]
      push_cast
      ring
  · intro n hn
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have hxn : x < n := by
      rw [Finset.mem_Iic, not_le] at hn
      exact (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast hn)
    have h0 : 1 - (n : ℝ) / x ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hx, one_mul]; exact hxn.le
    rw [ite_eq_right hn0, max_eq_left h0, ofReal_zero, mul_zero]

end EOS
