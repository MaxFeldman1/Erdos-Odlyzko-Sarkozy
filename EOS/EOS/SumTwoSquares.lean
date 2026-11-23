import EOS.Buchstab
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-!
# Prime × (sum of two squares), conditional on the endpoint Type I hypothesis `TypeIHalf`

This file formalizes reduction H1 of `notes/routes/F-estermann-sumsquares.md` §2.2, **for prime moduli `m`**.

* `TypeIHalf` is an **open hypothesis**. It is a Type I bound for `A_a` at level of distribution
  exactly `1/2`, endpoint included. That is the Weil/Kloosterman barrier. It is not known, and it is
  not implied by GRH. It is not a GRH consequence and not a cited theorem.
* `sumTwoSq_of_typeIHalf` is a **conditional reduction**. Under `TypeIHalf`, for every large prime `m`
  and every unit `a`, there are a prime `p ≤ m` and an `n < m` with `n = x² + y²` and `p n ≡ a (mod m)`.

## Proof (simplified relative to the note)
Only *existence* is needed, so neither `r₂(n)` asymptotics nor the Leibniz value `π/4` are used.
1. (`sum_chi_divisors_eq_zero`, `sum_chi_small_divisors_eq_zero`) If `n ≡ 1 (mod 4)` is **not** a sum
   of two squares, then `Σ_{d ∣ n} χ₄(d) = 0`. Some prime `q ≡ 3 (mod 4)` divides `n` to an odd power,
   and `1 ∗ χ₄` is multiplicative. Also `n` is not a square, and `χ₄(n/d) = χ₄(d)`. So pairing
   `d ↔ n/d` gives `Σ_{d ∣ n, d² < n} χ₄(d) = 0`.
2. Suppose the conclusion fails for `a`. Then every `n ∈ A_a` with `n ≡ 1 (4)` is not a sum of two
   squares. Swapping sums gives `Σ_{d} χ₄(d) N_d(a) = 0`, where `N_d` is the count in `TypeIHalf`.
3. `TypeIHalf` then gives `Σ_d χ₄(d) M_d ≤ |P|/log m`, where `M_d = |P|(m − d²)/(4dm)`.
4. For prime `m`, the `d` in the sum are exactly the odd `d < √m`. Then
   `Σ_d χ₄(d) M_d = (|P|/4) Σ_{d odd, d² < m} χ₄(d) g(d)`, with `g(d) = 1/d − d/m` positive and
   decreasing. By the alternating-series bound this is `≥ (|P|/4)(g(1) − g(3)) ≥ |P|/6`. So
   `log m ≤ 6`, which is false for `m ≥ 729`.

Remark: the proof uses `TypeIHalf` only with right side `< |P|/6`. The note's `π/16` would come from the
Leibniz value. The weaker constant `2/3 < π/4` costs nothing here.

Composite odd `m` is **not** treated. There the coprimality condition `(d, m) = 1` breaks the
alternation. The note's argument then needs Möbius over `e ∣ m`, the Leibniz limit, `τ(m)/√m → 0`,
and a lower bound `κ_m ≥ φ(m)/m ≫ 1/log log m`. The crude bound `φ(m)/m ≥ 1/(1 + log₂ m)` does not
beat the hypothesis's `1/log m`.
-/

open scoped BigOperators ArithmeticFunction
open Finset

namespace EOS.SumTwoSquares

open EOS.Buchstab

/-- **`TypeIHalf` — an OPEN HYPOTHESIS, not a theorem.** (`notes/routes/F-estermann-sumsquares.md` §2.1.)

For odd `m ≥ m₀` and every unit `a`, the Type I discrepancies of `A_a ∩ {n ≡ 1 (mod 4)}` in the classes
`d ∣ n` sum to at most `|P| / log m`. Here `d` ranges over **all** `d < √m` with `(d, 2m) = 1`, and each
count is cut to `n > d²`:

`Σ_{d < √m, (d,2m)=1} |#{n ∈ A_a : n ≡ 1 (4), d ∣ n, d² < n} − |P|(m − d²)/(4dm)| ≤ |P| / log m`.

This is level of distribution **exactly 1/2, endpoint included**, uniformly in `a`. That is exactly the
Weil/Kloosterman barrier, not inside it. It asks for square-root cancellation on average over `h ≤ m^{1/2+o(1)}`
in `Σ_{p ≤ m} e_m(h b p̄)`. **It is not known**. The known range is `d ≤ m^{1/16−ε}` (Fouvry–Shparlinski).
**It is not implied by GRH**: it is not known to follow from GRH, because GRH for Dirichlet `L`-functions
gives no known control of Kloosterman sums over primes. It is not a GRH consequence and not a cited theorem.
It is consistent with the numerics of the note (§3) and with the random model.

Any theorem proved from it, in particular `sumTwoSq_of_typeIHalf`, is a **conditional reduction** only. -/
def TypeIHalf : Prop :=
  ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → Odd m → ∀ a : ZMod m, IsUnit a →
    ∑ d ∈ (Finset.range m).filter (fun d => d * d < m ∧ d.Coprime (2 * m)),
      |(#{n ∈ Aset m a | n % 4 = 1 ∧ d ∣ n ∧ d * d < n} : ℝ)
        - #(primesP m) * ((m : ℝ) - d ^ 2) / (4 * d * m)| ≤ #(primesP m) / Real.log m

/-! ### The character `χ₄` on `ℕ` -/

/-- `χ₄` on naturals, integer-valued. -/
def chiZ (d : ℕ) : ℤ := ZMod.χ₄ ((d : ℕ) : ZMod 4)

lemma chiZ_eq (d : ℕ) : chiZ d = if d % 2 = 0 then 0 else if d % 4 = 1 then 1 else -1 :=
  ZMod.χ₄_nat_eq_if_mod_four d

lemma chiZ_mul (d e : ℕ) : chiZ (d * e) = chiZ d * chiZ e := by
  simp [chiZ, Nat.cast_mul, map_mul]

lemma chiZ_pow (d k : ℕ) : chiZ (d ^ k) = chiZ d ^ k := by
  simp [chiZ, Nat.cast_pow, map_pow]

/-- `χ₄` on naturals, real-valued. -/
noncomputable def chi (d : ℕ) : ℝ := (chiZ d : ℝ)

lemma chi_eq (d : ℕ) : chi d = if d % 2 = 0 then 0 else if d % 4 = 1 then 1 else -1 := by
  unfold chi
  rw [chiZ_eq]
  split_ifs <;> simp

lemma abs_chi_le (d : ℕ) : |chi d| ≤ 1 := by
  rw [chi_eq]; split_ifs <;> simp

lemma chi_mod4_zero {d : ℕ} (h : d % 4 = 0) : chi d = 0 := by
  rw [chi_eq]; split_ifs <;> first | rfl | (exfalso; omega)
lemma chi_mod4_one {d : ℕ} (h : d % 4 = 1) : chi d = 1 := by
  rw [chi_eq]; split_ifs <;> first | rfl | (exfalso; omega)
lemma chi_mod4_two {d : ℕ} (h : d % 4 = 2) : chi d = 0 := by
  rw [chi_eq]; split_ifs <;> first | rfl | (exfalso; omega)
lemma chi_mod4_three {d : ℕ} (h : d % 4 = 3) : chi d = -1 := by
  rw [chi_eq]; split_ifs <;> first | rfl | (exfalso; omega)

/-! ### Step 1: `n` not a sum of two squares ⇒ `Σ_{d ∣ n} χ₄(d) = 0` -/

/-- `χ₄` as an arithmetic function. -/
def chiAF : ArithmeticFunction ℤ := ⟨chiZ, by simp [chiZ]⟩

lemma chiAF_apply (d : ℕ) : chiAF d = chiZ d := rfl

lemma chiAF_isMultiplicative : chiAF.IsMultiplicative := by
  refine ⟨by simp [chiAF_apply, chiZ], fun {m n} _ => ?_⟩
  simp only [chiAF_apply, chiZ_mul]

lemma sum_range_two_mul_neg_one_pow (j : ℕ) : ∑ i ∈ range (2 * j), (-1 : ℤ) ^ i = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, pow_succ,
      pow_mul]
    simp

lemma sum_range_neg_one_pow_of_odd {k : ℕ} (hk : Odd k) :
    ∑ i ∈ range (k + 1), (-1 : ℤ) ^ i = 0 := by
  obtain ⟨j, rfl⟩ := hk
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
  exact sum_range_two_mul_neg_one_pow _

/-- If `n` is not a sum of two squares then `Σ_{d ∣ n} χ₄(d) = 0`. -/
lemma sum_chi_divisors_eq_zero {n : ℕ} (hn : 0 < n) (h : ¬ ∃ x y, n = x ^ 2 + y ^ 2) :
    ∑ d ∈ n.divisors, chiZ d = 0 := by
  rw [Nat.eq_sq_add_sq_iff] at h
  push Not at h
  obtain ⟨q, hq, hq3, hodd⟩ := h
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  rw [← Nat.factorization_def n hqp, Nat.not_even_iff_odd] at hodd
  set k := n.factorization q with hk
  have hmul : (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) * chiAF).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul chiAF_isMultiplicative
  have hsplit : n = q ^ k * (n / q ^ k) := (Nat.ordProj_mul_ordCompl_eq_self n q).symm
  have hcop : (q ^ k).Coprime (n / q ^ k) :=
    (Nat.coprime_ordCompl hqp hn.ne').pow_left k
  have key : ∀ x, ∑ d ∈ x.divisors, chiZ d
      = (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) * chiAF) x := by
    intro x; rw [ArithmeticFunction.coe_zeta_mul_apply]; rfl
  have hq_val : chiZ q = -1 := by
    rw [chiZ_eq]; split_ifs <;> first | rfl | (exfalso; omega)
  have hpow : ∑ d ∈ (q ^ k).divisors, chiZ d = 0 := by
    rw [Nat.sum_divisors_prime_pow hqp]
    simp_rw [chiZ_pow, hq_val]
    exact sum_range_neg_one_pow_of_odd hodd
  rw [key, hsplit, hmul.map_mul_of_coprime hcop, ← key, hpow, zero_mul]

/-- **Divisor switching.** If `n ≡ 1 (mod 4)` is not a sum of two squares, then
`Σ_{d ∣ n, d² < n} χ₄(d) = 0`. -/
lemma sum_chi_small_divisors_eq_zero {n : ℕ} (hn4 : n % 4 = 1) (h : ¬ ∃ x y, n = x ^ 2 + y ^ 2) :
    ∑ d ∈ n.divisors.filter (fun d => d * d < n), chiZ d = 0 := by
  have hn : 0 < n := by omega
  have hr := sum_chi_divisors_eq_zero hn h
  rw [← sum_filter_add_sum_filter_not n.divisors (fun d => d * d < n)] at hr
  -- the large divisors: `d * d > n` (no `d * d = n`, since a square is a sum of two squares)
  have hχn : chiZ n = 1 := by
    rw [chiZ_eq]; split_ifs <;> first | rfl | (exfalso; omega)
  have hswap : ∑ d ∈ n.divisors.filter (fun d => ¬ d * d < n), chiZ d
      = ∑ d ∈ n.divisors.filter (fun d => d * d < n), chiZ d := by
    refine sum_nbij' (fun d => n / d) (fun d => n / d) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      obtain ⟨⟨hdn, -⟩, hdd⟩ := hd
      obtain ⟨e, rfl⟩ := hdn
      have hd0 : 0 < d := Nat.pos_of_mul_pos_right hn
      rw [Nat.mul_div_cancel_left _ hd0]
      have hne : d * d ≠ d * e := by
        intro hde
        apply h
        refine ⟨d, 0, ?_⟩
        rw [← hde]; ring
      have hlt : d * e < d * d := lt_of_le_of_ne (not_lt.1 hdd) (Ne.symm hne)
      have hed : e < d := Nat.lt_of_mul_lt_mul_left hlt
      refine ⟨⟨Dvd.intro_left _ rfl, hn.ne'⟩, ?_⟩
      calc e * e < d * e := Nat.mul_lt_mul_of_pos_right hed (Nat.pos_of_mul_pos_left hn)
        _ = _ := rfl
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      obtain ⟨⟨hdn, -⟩, hdd⟩ := hd
      obtain ⟨e, rfl⟩ := hdn
      have hd0 : 0 < d := Nat.pos_of_mul_pos_right hn
      rw [Nat.mul_div_cancel_left _ hd0]
      have hde : d < e := Nat.lt_of_mul_lt_mul_left hdd
      refine ⟨⟨Dvd.intro_left _ rfl, hn.ne'⟩, ?_⟩
      intro hlt
      have : e * e < e * d := lt_of_lt_of_le hlt (by rw [mul_comm])
      have := Nat.lt_of_mul_lt_mul_left this
      omega
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 hn.ne'
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 hn.ne'
    · intro d hd
      simp only [mem_filter, Nat.mem_divisors] at hd
      obtain ⟨e, he⟩ := hd.1.1
      have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at he; omega)
      have hne : n / d = e := by rw [he, Nat.mul_div_cancel_left _ hd0]
      rw [hne]
      have hprod : chiZ d * chiZ e = 1 := by
        rw [← chiZ_mul, ← he, hχn]
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rw [h1, h2]
  rw [hswap] at hr
  omega

/-! ### Step 2: swapping sums -/

lemma sum_mul_card_filter (A D : Finset ℕ) (Q : ℕ → ℕ → Prop) [∀ n d, Decidable (Q n d)]
    (f : ℕ → ℝ) :
    ∑ d ∈ D, f d * (#{n ∈ A | Q n d} : ℝ) = ∑ n ∈ A, ∑ d ∈ D.filter (fun d => Q n d), f d := by
  calc ∑ d ∈ D, f d * (#{n ∈ A | Q n d} : ℝ)
      = ∑ d ∈ D, ∑ n ∈ A, if Q n d then f d else 0 := by
        refine sum_congr rfl fun d _ => ?_
        rw [natCast_card_filter, mul_sum]
        refine sum_congr rfl fun n _ => ?_
        split_ifs <;> simp
    _ = ∑ n ∈ A, ∑ d ∈ D, if Q n d then f d else 0 := sum_comm
    _ = _ := by
        refine sum_congr rfl fun n _ => ?_
        rw [sum_filter]

/-! ### Step 4: the alternating-series lower bound -/

/-- Partial sums of `Σ χ₄(d) g(d)` for `g ≥ 0` decreasing (on `d ≥ 1`, step 2): at least `g 1 − g 3`
once at least four terms are present. -/
lemma alt_sum_ge (g : ℕ → ℝ) (hg0 : ∀ d, 0 ≤ g d) (hg : ∀ d, 1 ≤ d → g (d + 2) ≤ g d) :
    ∀ N, 4 ≤ N → g 1 - g 3 ≤ ∑ d ∈ range N, chi d * g d := by
  -- blocks of four
  have hblock : ∀ j, ∑ d ∈ range (4 * (j + 1)), chi d * g d
      = ∑ d ∈ range (4 * j), chi d * g d + g (4 * j + 1) - g (4 * j + 3) := by
    intro j
    rw [show 4 * (j + 1) = 4 * j + 1 + 1 + 1 + 1 by ring]
    simp only [sum_range_succ]
    rw [chi_mod4_zero (by omega), chi_mod4_one (by omega), chi_mod4_two (by omega),
      chi_mod4_three (by omega)]
    ring
  have hfour : ∀ j, g 1 - g 3 ≤ ∑ d ∈ range (4 * (j + 1)), chi d * g d := by
    intro j
    induction j with
    | zero => rw [hblock]; simp
    | succ j ih =>
      rw [hblock]
      have := hg (4 * (j + 1) + 1) (by omega)
      linarith
  intro N hN
  obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 4 ∧ N = 4 * (j + 1) + r :=
    ⟨N / 4 - 1, N % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  have h := hfour j
  have h1 := hg0 (4 * (j + 1) + 1)
  interval_cases r
  · simpa using h
  · rw [sum_range_succ, chi_mod4_zero (by omega)]; linarith
  · rw [sum_range_succ, sum_range_succ, chi_mod4_zero (by omega), chi_mod4_one (by omega)]
    linarith
  · rw [sum_range_succ, sum_range_succ, sum_range_succ, chi_mod4_zero (by omega),
      chi_mod4_one (by omega), chi_mod4_two (by omega)]
    linarith

/-- The weight `g(d) = (m − d²)/(dm) = 1/d − d/m` cut off at `d² < m`. -/
noncomputable def gW (m d : ℕ) : ℝ := if d * d < m then ((m : ℝ) - d ^ 2) / (d * m) else 0

lemma gW_nonneg (m d : ℕ) : 0 ≤ gW m d := by
  unfold gW
  split_ifs with h
  · have : ((d : ℝ)) ^ 2 < m := by rw [pow_two]; exact_mod_cast h
    exact div_nonneg (by linarith) (by positivity)
  · exact le_rfl

lemma gW_eq {m d : ℕ} (hm : 0 < m) (hd : 1 ≤ d) (h : d * d < m) :
    gW m d = 1 / (d : ℝ) - d / m := by
  unfold gW
  rw [ite_eq_left h]
  have : (0 : ℝ) < d := by exact_mod_cast hd
  have : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp

lemma gW_anti {m : ℕ} (hm : 0 < m) (d : ℕ) (hd : 1 ≤ d) : gW m (d + 2) ≤ gW m d := by
  by_cases h : (d + 2) * (d + 2) < m
  · have h' : d * d < m := lt_of_le_of_lt (Nat.mul_le_mul (by omega) (by omega)) h
    rw [gW_eq hm (by omega) h, gW_eq hm hd h']
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 : 1 / ((d + 2 : ℕ) : ℝ) ≤ 1 / (d : ℝ) :=
      one_div_le_one_div_of_le hd0 (by push_cast; linarith)
    have h2 : (d : ℝ) / m ≤ ((d + 2 : ℕ) : ℝ) / m :=
      div_le_div_of_nonneg_right (by push_cast; linarith) hm0.le
    linarith
  · unfold gW
    rw [ite_eq_right h]
    exact gW_nonneg m d

lemma gW_one_sub_three {m : ℕ} (hm : 9 < m) : 2 / 3 ≤ gW m 1 - gW m 3 := by
  rw [gW_eq (by omega) le_rfl (by omega), gW_eq (by omega) (by norm_num) (by omega)]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  push_cast
  have : 1 / (1 : ℝ) - 1 / m - (1 / 3 - 3 / m) = 2 / 3 + 2 / m := by ring
  have : 0 ≤ 2 / (m : ℝ) := by positivity
  linarith

/-! ### The reduction for prime `m` -/

/-- **Conditional reduction (H1 of `notes/routes/F-estermann-sumsquares.md`), for prime moduli.**
Assume the **open hypothesis** `TypeIHalf`. It is endpoint level `1/2`, at the Weil/Kloosterman barrier,
not known, and not implied by GRH. Then for every large prime `m` and every unit `a`, there are a prime
`p ≤ m` and an `n < m` with `n = x² + y²` and `p n ≡ a (mod m)`. This is a conditional statement only:
it says nothing unconditionally. -/
theorem sumTwoSq_of_typeIHalf (hT : TypeIHalf) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, m.Prime → ∀ a : ZMod m, IsUnit a →
      ∃ p n : ℕ, p.Prime ∧ p ≤ m ∧ n < m ∧ (∃ x y, n = x ^ 2 + y ^ 2) ∧
        ((p * n : ℕ) : ZMod m) = a := by
  obtain ⟨m₀, hT⟩ := hT
  refine ⟨max m₀ 729, fun m hm hmp a ha => ?_⟩
  have hm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hm
  have hm729 : 729 ≤ m := le_trans (le_max_right _ _) hm
  have hm2 : 2 ≤ m := by omega
  have : NeZero m := ⟨by omega⟩
  have hodd : Odd m := hmp.odd_of_ne_two (by omega)
  by_contra hcon
  -- every relevant `n ∈ A_a` fails to be a sum of two squares
  have hnot : ∀ n ∈ Aset m a, ¬ ∃ x y, n = x ^ 2 + y ^ 2 := by
    intro n hn hsq
    obtain ⟨-, hnm, -, q, hq, hqa⟩ := mem_Aset hm2 ha hn
    rw [mem_primesP] at hq
    exact hcon ⟨q, n, hq.2.1, hq.1, hnm, hsq, by rw [mul_comm]; exact hqa⟩
  set D := (Finset.range m).filter (fun d => d * d < m ∧ d.Coprime (2 * m)) with hD
  set Pc : ℝ := ((#(primesP m) : ℕ) : ℝ) with hPc
  set N : ℕ → ℝ := fun d => (#{n ∈ Aset m a | n % 4 = 1 ∧ d ∣ n ∧ d * d < n} : ℝ) with hN
  set M : ℕ → ℝ := fun d => Pc * ((m : ℝ) - d ^ 2) / (4 * d * m) with hM
  have hTm : ∑ d ∈ D, |N d - M d| ≤ Pc / Real.log m := hT m hm₀ hodd a ha
  -- Step 2: `Σ χ₄(d) N_d = 0`
  have hzero : ∑ d ∈ D, chi d * N d = 0 := by
    simp only [hN]
    rw [sum_mul_card_filter (Aset m a) D (fun n d => n % 4 = 1 ∧ d ∣ n ∧ d * d < n) chi]
    refine sum_eq_zero fun n hn => ?_
    obtain ⟨hn0, hnm, hncop, -⟩ := mem_Aset hm2 ha hn
    by_cases hn4 : n % 4 = 1
    · have hset : D.filter (fun d => n % 4 = 1 ∧ d ∣ n ∧ d * d < n)
          = n.divisors.filter (fun d => d * d < n) := by
        ext d
        simp only [hD, mem_filter, mem_range, Nat.mem_divisors]
        constructor
        · rintro ⟨-, -, hdn, hdd⟩
          exact ⟨⟨hdn, hn0.ne'⟩, hdd⟩
        · rintro ⟨⟨hdn, -⟩, hdd⟩
          have hdle : d ≤ n := Nat.le_of_dvd hn0 hdn
          have hn2 : n.Coprime 2 := Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))
          have hn2m : n.Coprime (2 * m) := Nat.Coprime.mul_right hn2 hncop
          exact ⟨⟨by omega, by omega, Nat.Coprime.coprime_dvd_left hdn hn2m⟩, hn4, hdn, hdd⟩
      rw [hset]
      have := sum_chi_small_divisors_eq_zero hn4 (hnot n hn)
      simp only [chi]
      exact_mod_cast this
    · rw [sum_eq_zero]
      intro d hd
      simp only [mem_filter] at hd
      exact absurd hd.2.1 hn4
  -- Step 3: `Σ χ₄(d) M_d ≤ |P| / log m`
  have hupper : ∑ d ∈ D, chi d * M d ≤ Pc / Real.log m := by
    have : ∑ d ∈ D, chi d * M d = ∑ d ∈ D, chi d * (M d - N d) := by
      rw [← sub_zero (∑ d ∈ D, chi d * M d), ← hzero, ← sum_sub_distrib]
      refine sum_congr rfl fun d _ => by ring
    rw [this]
    refine le_trans (sum_le_sum fun d _ => ?_) hTm
    calc chi d * (M d - N d) ≤ |chi d * (M d - N d)| := le_abs_self _
      _ = |chi d| * |N d - M d| := by rw [abs_mul, abs_sub_comm]
      _ ≤ 1 * |N d - M d| := mul_le_mul_of_nonneg_right (abs_chi_le d) (abs_nonneg _)
      _ = |N d - M d| := one_mul _
  -- Step 4: `Σ χ₄(d) M_d = (|P|/4) Σ_{d < m} χ₄(d) g(d) ≥ |P|/6`
  have hrewrite : ∑ d ∈ D, chi d * M d = Pc / 4 * ∑ d ∈ range m, chi d * gW m d := by
    rw [hD, sum_filter, mul_sum]
    refine sum_congr rfl fun d hd => ?_
    rw [mem_range] at hd
    by_cases hdd : d * d < m
    · have hgW : gW m d = ((m : ℝ) - d ^ 2) / (d * m) := by unfold gW; rw [ite_eq_left hdd]
      by_cases hc : d.Coprime (2 * m)
      · rw [ite_eq_left ⟨hdd, hc⟩, hgW, hM]
        ring
      · rw [ite_eq_right (fun h => hc h.2)]
        -- `χ₄(d) = 0`: otherwise `d` is odd, `1 ≤ d < m`, hence coprime to `2m`
        have hchi : chi d = 0 := by
          by_contra hne
          have hd2 : d % 2 = 1 := by
            by_contra h2
            exact hne (by rw [chi_eq, ite_eq_left (by omega)])
          apply hc
          have hd1 : 1 ≤ d := by omega
          have hdm : d < m := by nlinarith
          have hcm : d.Coprime m := by
            rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hmp]
            intro hmd
            exact absurd (Nat.le_of_dvd (by omega) hmd) (by omega)
          exact Nat.Coprime.mul_right (Nat.coprime_two_right.2 (Nat.odd_iff.2 hd2)) hcm
        rw [hchi]; ring
    · rw [ite_eq_right (fun h => hdd h.1)]
      unfold gW; rw [ite_eq_right hdd]; ring
  have halt := alt_sum_ge (gW m) (gW_nonneg m) (gW_anti (by omega)) m (by omega)
  have h23 := gW_one_sub_three (m := m) (by omega)
  -- `|P| > 0`: `2 ∈ P`
  have h2P : 2 ∈ primesP m := by
    rw [mem_primesP]
    exact ⟨hm2, Nat.prime_two, fun h => by
      rw [← even_iff_two_dvd] at h; exact (Nat.not_even_iff_odd.2 hodd) h⟩
  have hPpos : 0 < Pc := by
    rw [hPc]; exact_mod_cast Finset.card_pos.2 ⟨2, h2P⟩
  -- `log m > 6`
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogm : 6 < Real.log m := by
    have h729 : Real.log 729 = 6 * Real.log 3 := by
      rw [show (729 : ℝ) = 3 ^ 6 by norm_num, Real.log_pow]; norm_num
    have : Real.log 729 ≤ Real.log m :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hm729)
    linarith
  have hmain : Pc / 6 ≤ Pc / Real.log m := by
    have : Pc / 4 * (2 / 3) ≤ Pc / 4 * ∑ d ∈ range m, chi d * gW m d :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [← hrewrite] at this
    linarith
  have hlogpos : 0 < Real.log m := by linarith
  rw [div_le_div_iff₀ (by norm_num) hlogpos] at hmain
  nlinarith

end EOS.SumTwoSquares
