import EOS.GapH4

/-!
# Prime × squarefree: the Estermann analogue for EOS (Theorems F0 and F1′)

Formalization of Task 1 of `notes/routes/F-estermann-sumsquares.md` (§1.1 and §1.3).
There is **no `sorry`** in this file, and **GRH is not used anywhere**: no GRH hypothesis and no
GRH-consequence hypothesis appears in any statement.

Notation as in `Buchstab.lean`: `P = primesP m = {p ≤ m prime, p ∤ m}`, `n_p = a p̄ mod m`,
`A_a = Aset m a = {n_p : p ∈ P}`.

## Main results
* `EOS.estermann_long` (Theorem F0, **hypothesis-free**). For `m ≥ 2`, `6 ∣ K` and
  `27 m < K |P|`, every unit `a` mod `m` is `≡ p s` with `p ≤ m` prime and `s < K m` squarefree.
  Pure finite combinatorics: pairs `(p, j)`, `s = n_p + j m`, union bound over `q² ∣ s`, split at
  `q ≤ K/6`, using `Σ_{q prime} q⁻² ≤ 11/18`.
* `EOS.estermann_long_log` (F0 with Chebyshev, **hypothesis-free**). For `m ≥ 400⁴`, every unit is
  `p s` with `p ≤ m` prime and `s ≤ 56 m log m` squarefree. Chebyshev's bound
  `π(m) ≥ m log 2 / log m` comes from Mathlib (`Chebyshev.pi_ge_of_four_le`, via
  `GapH4.large_facts`); nothing is assumed.
* `EOS.estermann_of_typeISifted_rough` / `EOS.estermann_of_typeISifted` (Theorem F1′). Under
  `TypeISifted` there are `η > 0` and `m₀` such that for all `m ≥ m₀` every unit `a` is `≡ p s`
  with `p ≤ m` prime and `s < m` squarefree, all of whose prime factors are `≥ m^η`.

`TypeISifted` (defined and documented in `GapH4.lean`) is a named `Prop` for a **cited,
unconditional** theorem (Fouvry–Shparlinski Type I bound for `A_a` plus the fundamental lemma of
the sieve). It is not a GRH consequence and not an open hypothesis.

**The result F1′ is known**: K. H. Yau, *On products of primes and square-free integers in
arithmetic progressions*, arXiv:1907.06016, Theorem 3.1, gives it (with a power saving and with
`p, s ≤ m^{16/17+ε}`). F0 is an elementary remark.

## Deviations from the note
* F0's `n_p + j m` with `j < K` gives `s < K m` exactly as stated in the note.
* F1′ is proved with `ε = 1/4` in `TypeISifted` and `η = min(η₁, 1/4)`; the note's bound
  `π(m) ≤ |P| + log₂ m` is replaced by `π(m) ≤ |P| + √m + 2` (`GapH4.primeCounting_le`), and
  `Φ_m(m, y) ≥ |P| − y − 1`. The conclusion is `s < m` (the note's Lean sketch had `s ≤ m`).
* The non-squarefree rough count uses `Σ_{d ≥ ⌈y⌉} m/d² ≤ m/(⌈y⌉ − 1) ≤ 2m/y`, as in the note.
-/

open scoped BigOperators
open Finset Real

namespace EOS

open EOS.Buchstab

namespace Estermann

/-- Telescoping: `Σ_{k < d < N} 1/d² ≤ 1/k` for `k ≥ 1`. -/
lemma sum_inv_sq_Ico_le (k N : ℕ) (hk : 1 ≤ k) :
    ∑ d ∈ Ico (k + 1) N, (1 : ℝ) / ((d : ℝ) * d) ≤ 1 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have key : ∀ n : ℕ, ∑ d ∈ Ico (k + 1) (k + 1 + n), (1 : ℝ) / ((d : ℝ) * d) ≤
      1 / k - 1 / (k + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show k + 1 + (n + 1) = (k + 1 + n) + 1 by ring, sum_Ico_succ_top (by omega)]
      have ha : (0 : ℝ) < k + n := by positivity
      have hstep : (1 : ℝ) / (((k + 1 + n : ℕ) : ℝ) * ((k + 1 + n : ℕ) : ℝ)) ≤
          1 / (k + n) - 1 / (k + n + 1) := by
        push_cast
        rw [div_sub_div _ _ ha.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast at ih hstep ⊢
      have e : (k : ℝ) + (n + 1) = k + n + 1 := by ring
      rw [e]
      linarith
  rcases le_or_gt N (k + 1) with h | h
  · rw [Ico_eq_empty_of_le h, sum_empty]; positivity
  · obtain ⟨n, rfl⟩ : ∃ n, N = k + 1 + n := ⟨N - (k + 1), by omega⟩
    have := key n
    have : (0 : ℝ) ≤ 1 / (k + n) := by positivity
    linarith

/-- Integers in `(0, N)` divisible by `d²` for some `d > k`: at most `N/k` of them. -/
lemma card_sq_tail (N k : ℕ) (hk : 1 ≤ k) :
    ((#((Ioo 0 N).filter (fun n => ∃ d ∈ Ico (k + 1) N, d * d ∣ n)) : ℕ) : ℝ) ≤ N / k := by
  classical
  have hsub : (Ioo 0 N).filter (fun n => ∃ d ∈ Ico (k + 1) N, d * d ∣ n) ⊆
      (Ico (k + 1) N).biUnion (fun d => (Ioc 0 N).filter (fun n => d * d ∣ n)) := by
    intro n hn
    simp only [mem_filter, mem_Ioo] at hn
    obtain ⟨⟨h0, hN⟩, d, hd, hdvd⟩ := hn
    simp only [mem_biUnion, mem_filter, mem_Ioc]
    exact ⟨d, hd, ⟨h0, hN.le⟩, hdvd⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  simp only [Nat.Ioc_filter_dvd_card_eq_div] at h1
  have h2 : ((#((Ioo 0 N).filter (fun n => ∃ d ∈ Ico (k + 1) N, d * d ∣ n)) : ℕ) : ℝ) ≤
      ∑ d ∈ Ico (k + 1) N, ((N / (d * d) : ℕ) : ℝ) := by exact_mod_cast h1
  calc _ ≤ ∑ d ∈ Ico (k + 1) N, ((N / (d * d) : ℕ) : ℝ) := h2
    _ ≤ ∑ d ∈ Ico (k + 1) N, (N : ℝ) * (1 / ((d : ℝ) * d)) := by
        refine sum_le_sum fun d _ => ?_
        calc ((N / (d * d) : ℕ) : ℝ) ≤ (N : ℝ) / ((d * d : ℕ) : ℝ) := Nat.cast_div_le
          _ = _ := by push_cast; ring
    _ = N * ∑ d ∈ Ico (k + 1) N, (1 / ((d : ℝ) * d)) := by rw [mul_sum]
    _ ≤ N * (1 / k) := mul_le_mul_of_nonneg_left (sum_inv_sq_Ico_le k N hk) (Nat.cast_nonneg _)
    _ = N / k := by ring

/-- For a prime `q` and `(n, m) = 1`, the `j < K` with `q² ∣ n + j m` number at most `K/q² + 1`. -/
lemma card_res_le (q m n K : ℕ) (hq : q.Prime) (hn : n.Coprime m) :
    #((range K).filter (fun j => q * q ∣ n + j * m)) ≤ K / (q * q) + 1 := by
  classical
  by_cases hqm : q ∣ m
  · have : (range K).filter (fun j => q * q ∣ n + j * m) = ∅ := by
      refine filter_eq_empty_iff.2 fun j _ hj => ?_
      have h1 : q ∣ n + j * m := (Dvd.intro _ rfl).trans hj
      have h2 : q ∣ n := (Nat.dvd_add_left (dvd_mul_of_dvd_right hqm j)).1 h1
      have h3 : q ∣ Nat.gcd n m := Nat.dvd_gcd h2 hqm
      rw [hn] at h3
      exact hq.one_lt.ne' (Nat.dvd_one.1 h3)
    rw [this, card_empty]; exact Nat.zero_le _
  · have hcop : Nat.gcd (q * q) m = 1 :=
      Nat.coprime_mul_iff_left.2 ⟨(Nat.Prime.coprime_iff_not_dvd hq).2 hqm,
        (Nat.Prime.coprime_iff_not_dvd hq).2 hqm⟩
    have hinj : Set.InjOn (fun j => j / (q * q)) ↑((range K).filter (fun j => q * q ∣ n + j * m)) := by
      intro j₁ hj₁ j₂ hj₂ hj
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hj₁ hj₂
      have e1 : n + j₁ * m ≡ n + j₂ * m [MOD q * q] :=
        (Nat.modEq_zero_iff_dvd.2 hj₁.2).trans (Nat.modEq_zero_iff_dvd.2 hj₂.2).symm
      have e2 : j₁ ≡ j₂ [MOD q * q] :=
        Nat.ModEq.cancel_right_of_coprime hcop (Nat.ModEq.add_left_cancel' n e1)
      simp only at hj
      rw [← Nat.div_add_mod j₁ (q * q), ← Nat.div_add_mod j₂ (q * q), hj]
      unfold Nat.ModEq at e2
      rw [e2]
    have := card_le_card_of_injOn (fun j => j / (q * q)) (t := range (K / (q * q) + 1)) ?_ hinj
    · simpa using this
    · intro j hj
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hj
      simp only [coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hj.1.le)

/-- `Σ_{q ≤ z prime} 1/q² ≤ 1/4 + 1/9 + Σ_{d ≥ 5} 1/(d(d−1)) = 11/18`. -/
lemma sum_prime_inv_sq_le (z : ℕ) :
    ∑ q ∈ (Icc 1 z).filter Nat.Prime, (1 : ℝ) / ((q : ℝ) * q) ≤ 11 / 18 := by
  classical
  have hsub : (Icc 1 z).filter Nat.Prime ⊆ {2, 3} ∪ Ico (4 + 1) (z + 1) := by
    intro q hq
    simp only [mem_filter, mem_Icc] at hq
    simp only [mem_union, mem_insert, mem_singleton, mem_Ico]
    by_cases h4 : q = 4
    · subst h4; exact absurd hq.2 (by decide)
    · have := hq.2.two_le
      omega
  have hdisj : Disjoint ({2, 3} : Finset ℕ) (Ico (4 + 1) (z + 1)) := by
    rw [disjoint_left]
    intro q hq
    simp only [mem_insert, mem_singleton] at hq
    simp only [mem_Ico]
    omega
  calc _ ≤ ∑ q ∈ {2, 3} ∪ Ico (4 + 1) (z + 1), (1 : ℝ) / ((q : ℝ) * q) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (1 / 4 + 1 / 9) + ∑ q ∈ Ico (4 + 1) (z + 1), (1 : ℝ) / ((q : ℝ) * q) := by
        rw [sum_union hdisj]; norm_num
    _ ≤ (1 / 4 + 1 / 9) + 1 / (4 : ℕ) := by
        have := sum_inv_sq_Ico_le 4 (z + 1) (by norm_num); linarith
    _ = 11 / 18 := by norm_num

/-- The residue `n_p = a p̄ mod m` lies in `[1, m)`, is coprime to `m`, and `p n_p ≡ a`. -/
lemma resid_facts {m : ℕ} [NeZero m] (hm : 2 ≤ m) {a : ZMod m} (ha : IsUnit a) {p : ℕ}
    (hp : p ∈ primesP m) :
    0 < (a * (p : ZMod m)⁻¹).val ∧ (a * (p : ZMod m)⁻¹).val < m ∧
      (a * (p : ZMod m)⁻¹).val.Coprime m ∧ ((p * (a * (p : ZMod m)⁻¹).val : ℕ) : ZMod m) = a := by
  have hmem : (a * (p : ZMod m)⁻¹).val ∈ Aset m a := mem_image_of_mem _ hp
  obtain ⟨h0, h1, h2, -⟩ := mem_Aset hm ha hmem
  refine ⟨h0, h1, h2, ?_⟩
  have hp1 : (p : ZMod m) * (p : ZMod m)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one p (coprime_of_mem_primesP hp)
  push_cast
  rw [ZMod.natCast_zmod_val]
  calc (p : ZMod m) * (a * (p : ZMod m)⁻¹) = a * ((p : ZMod m) * (p : ZMod m)⁻¹) := by ring
    _ = a := by rw [hp1, mul_one]

/-- `p ↦ a p̄ mod m` is injective on `P`. -/
lemma resid_injOn {m : ℕ} [NeZero m] {a : ZMod m} (ha : IsUnit a) :
    Set.InjOn (fun p : ℕ => (a * (p : ZMod m)⁻¹).val) ↑(primesP m) := by
  intro p₁ hp₁ p₂ hp₂ h
  have hv : a * (p₁ : ZMod m)⁻¹ = a * (p₂ : ZMod m)⁻¹ := ZMod.val_injective m h
  have hinv : (p₁ : ZMod m)⁻¹ = (p₂ : ZMod m)⁻¹ := ha.mul_left_cancel hv
  have e1 := ZMod.coe_mul_inv_eq_one p₁ (coprime_of_mem_primesP hp₁)
  have e2 := ZMod.coe_mul_inv_eq_one p₂ (coprime_of_mem_primesP hp₂)
  have : (p₁ : ZMod m) = p₂ := by
    calc (p₁ : ZMod m) = p₁ * ((p₂ : ZMod m) * (p₂ : ZMod m)⁻¹) := by rw [e2, mul_one]
      _ = p₂ * ((p₁ : ZMod m) * (p₁ : ZMod m)⁻¹) := by rw [← hinv]; ring
      _ = p₂ := by rw [e1, mul_one]
  have := congrArg ZMod.val this
  rwa [ZMod.val_cast_of_lt (lt_of_mem_primesP hp₁),
    ZMod.val_cast_of_lt (lt_of_mem_primesP hp₂)] at this

/-- `|P| ≤ Φ_m(m, y) + y + 1`: every `p ∈ P` with `p ≥ y` is counted by `Φ_m(m, y)`. -/
lemma card_primesP_le_PhiCop (m : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    (#(primesP m) : ℝ) ≤ PhiCop m m y + (y + 1) := by
  classical
  have hsub : primesP m ⊆ ((Icc 1 m).filter (fun n => n.Coprime m)).filter
      (fun n => n = 1 ∨ y ≤ (n.minFac : ℝ)) ∪ range ⌈y⌉₊ := by
    intro p hp
    have hc := coprime_of_mem_primesP hp
    rw [mem_primesP] at hp
    simp only [mem_union, mem_filter, mem_Icc, mem_range]
    by_cases hyp : y ≤ (p : ℝ)
    · left
      exact ⟨⟨⟨hp.2.1.one_lt.le, hp.1⟩, hc⟩, Or.inr (by rw [hp.2.1.minFac_eq]; exact hyp)⟩
    · right
      exact Nat.lt_ceil.2 (lt_of_not_ge hyp)
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_range] at h1
  have h2 : (#(primesP m) : ℝ) ≤ PhiCop m m y + ⌈y⌉₊ := by
    unfold PhiCop siftedR; exact_mod_cast h1
  have h3 := Nat.ceil_lt_add_one hy
  linarith

/-- `|P| ≥ π(m) − √m − 2`. -/
lemma card_primesP_ge (m : ℕ) (hm : 1 ≤ m) :
    (Nat.primeCounting m : ℝ) - Real.sqrt m - 2 ≤ #(primesP m) := by
  have h1 := GapH4.primeCounting_le m hm
  have h2 := GapH4.primeCount_le_primesP m
  have h3 : (Nat.primeCounting m : ℝ) ≤ #(primesP m) + (Nat.sqrt m + 1) + 1 := by
    exact_mod_cast h1.trans (by omega)
  have h4 : (Nat.sqrt m : ℝ) ≤ Real.sqrt m := Real.nat_sqrt_le_real_sqrt
  linarith

/-- The finite step of F1′: if the `y`-rough part of `A_a` has more than `2m/y` elements
(`y ≥ 2`), one of them is squarefree. Non-squarefree `y`-rough `n < m` are divisible by `d²` for
some `d ≥ y`, and there are at most `m/(⌈y⌉ − 1) ≤ 2m/y` of them. -/
lemma exists_sqfree_of_sifted {m : ℕ} [NeZero m] (hm : 2 ≤ m) {a : ZMod m} (ha : IsUnit a)
    {y : ℝ} (hy : 2 ≤ y) (hbig : 2 * (m : ℝ) / y < siftedR y (Aset m a)) :
    ∃ p s : ℕ, p.Prime ∧ p ≤ m ∧ Squarefree s ∧ s < m ∧
      (∀ q : ℕ, q.Prime → q ∣ s → y ≤ q) ∧ ((p * s : ℕ) : ZMod m) = a := by
  classical
  set Y := ⌈y⌉₊ with hY
  have hyY : y ≤ Y := Nat.le_ceil y
  have hY2 : 2 ≤ Y := by
    have : ((2 : ℕ) : ℝ) ≤ Y := by push_cast; linarith
    exact_mod_cast this
  by_contra hcon
  have hsub : (Aset m a).filter (fun n => n = 1 ∨ y ≤ (n.minFac : ℝ)) ⊆
      (Ioo 0 m).filter (fun n => ∃ d ∈ Ico ((Y - 1) + 1) m, d * d ∣ n) := by
    intro n hn
    rw [mem_filter] at hn
    obtain ⟨hn0, hnm, -, q, hq, hqa⟩ := mem_Aset hm ha hn.1
    have hns : ¬ Squarefree n := by
      intro hsq
      refine hcon ⟨q, n, (mem_primesP.1 hq).2.1, (mem_primesP.1 hq).1, hsq, hnm, ?_, ?_⟩
      · intro r hr hrn
        rcases hn.2 with h1 | h1
        · subst h1; exact absurd (Nat.le_of_dvd one_pos hrn) (by have := hr.two_le; omega)
        · exact h1.trans (by exact_mod_cast Nat.minFac_le_of_dvd hr.two_le hrn)
      · rw [mul_comm]; exact hqa
    rw [Nat.squarefree_iff_prime_squarefree] at hns
    push Not at hns
    obtain ⟨r, hr, hrd⟩ := hns
    have hn1 : n ≠ 1 := by
      rintro rfl
      exact absurd (Nat.le_of_dvd one_pos hrd) (by have := hr.two_le; nlinarith)
    have hyr : y ≤ (r : ℝ) := by
      rcases hn.2 with h1 | h1
      · exact absurd h1 hn1
      · exact h1.trans (by exact_mod_cast Nat.minFac_le_of_dvd hr.two_le ((Dvd.intro _ rfl).trans hrd))
    have hYr : Y ≤ r := Nat.ceil_le.2 hyr
    have hrr : r ≤ r * r := Nat.le_mul_of_pos_right r hr.pos
    have hrn : r * r ≤ n := Nat.le_of_dvd hn0 hrd
    simp only [mem_filter, mem_Ioo, mem_Ico]
    exact ⟨⟨hn0, hnm⟩, r, ⟨by omega, by omega⟩, hrd⟩
  have h1 := card_le_card hsub
  have h2 := card_sq_tail m (Y - 1) (by omega)
  have hY1 : ((Y - 1 : ℕ) : ℝ) = (Y : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hY1] at h2
  have h3 : (siftedR y (Aset m a) : ℝ) ≤ m / ((Y : ℝ) - 1) := by
    unfold siftedR
    exact (Nat.cast_le.2 h1).trans h2
  have h4 : (m : ℝ) / ((Y : ℝ) - 1) ≤ 2 * m / y := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  linarith

/-- The numerical step of F1′: `2m/y < (0.9 π/m)(0.35 π)` from `π log m ≥ 0.693 m` and
`y ≥ 18 log² m`. -/
lemma f1_numeric {m pc y L : ℝ} (hm : 0 < m) (hy : 0 < y)
    (hpcL : 693 / 1000 * m ≤ pc * L) (hyL : 18 * L ^ 2 ≤ y) :
    2 * m / y < 9 / 10 * pc / m * (35 / 100 * pc) := by
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ hy hm]
  have hpc2 : (693 / 1000 * m) ^ 2 ≤ (pc * L) ^ 2 := pow_le_pow_left₀ (by positivity) hpcL 2
  have hpcy : pc ^ 2 * (18 * L ^ 2) ≤ pc ^ 2 * y := mul_le_mul_of_nonneg_left hyL (sq_nonneg pc)
  have k1 : 18 * (693 / 1000 * m) ^ 2 ≤ pc ^ 2 * y := by
    have : pc ^ 2 * (18 * L ^ 2) = 18 * (pc * L) ^ 2 := by ring
    linarith
  have hmm : 0 < m * m := mul_pos hm hm
  have e : 315 / 1000 * (18 * (693 / 1000 * m) ^ 2) - 2 * m * m =
      (315 / 1000 * 18 * (693 / 1000) ^ 2 - 2) * (m * m) := by ring
  have hc : (0 : ℝ) < 315 / 1000 * 18 * (693 / 1000) ^ 2 - 2 := by norm_num
  have k2 := mul_pos hc hmm
  have k3 : 9 / 10 * pc * (35 / 100 * pc) * y = 315 / 1000 * (pc ^ 2 * y) := by ring
  rw [k3]
  linarith

end Estermann

open Estermann

/-- **Theorem F0 (hypothesis-free).** Let `m ≥ 2` and `K` with `6 ∣ K` and `27 m < K |P|`,
`P = primesP m`. Then every unit `a` mod `m` is `≡ p s` with `p ≤ m` prime and `s < K m`
squarefree. No analytic input of any kind (in particular no GRH). -/
theorem estermann_long (m : ℕ) (hm : 2 ≤ m) (K : ℕ) (hK6 : 6 ∣ K)
    (hK : 27 * (m : ℝ) < K * #(primesP m)) (a : ZMod m) (ha : IsUnit a) :
    ∃ p s : ℕ, p.Prime ∧ p ≤ m ∧ Squarefree s ∧ s < K * m ∧ ((p * s : ℕ) : ZMod m) = a := by
  classical
  have : NeZero m := ⟨by omega⟩
  set P := primesP m with hPdef
  set nf : ℕ → ℕ := fun p => (a * (p : ZMod m)⁻¹).val with hnf
  set T := P ×ˢ range K with hT
  set f : ℕ × ℕ → ℕ := fun x => nf x.1 + x.2 * m with hf
  have hfT : ∀ x ∈ T, 0 < f x ∧ f x < K * m := by
    intro x hx
    simp only [hT, mem_product, mem_range] at hx
    have h0 : 0 < nf x.1 := (resid_facts hm ha hx.1).1
    have h1 : nf x.1 < m := (resid_facts hm ha hx.1).2.1
    have : x.2 * m + m ≤ K * m := by
      have := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hx.2)
      simpa [Nat.succ_mul] using this
    change 0 < nf x.1 + x.2 * m ∧ nf x.1 + x.2 * m < K * m
    omega
  by_contra hcon
  have hbad : ∀ x ∈ T, ¬ Squarefree (f x) := by
    intro x hx hsq
    have hx' := hx
    simp only [hT, mem_product, mem_range] at hx'
    obtain ⟨-, h1, -, h3⟩ := resid_facts hm ha hx'.1
    rw [mem_primesP] at hx'
    refine hcon ⟨x.1, f x, hx'.1.2.1, hx'.1.1, hsq, (hfT x hx).2, ?_⟩
    have : ((f x : ℕ) : ZMod m) = (nf x.1 : ℕ) := by
      simp only [hf]; push_cast; simp
    push_cast at h3 ⊢
    rw [this]; exact h3
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h] at hK; simp at hK; linarith
    · exact h
  set z := K / 6 with hz
  have hzK : K = 6 * z := by omega
  have hz1 : 1 ≤ z := by omega
  set Q := (Icc 1 z).filter Nat.Prime with hQ
  -- every pair is bad: split by the size of the prime `q` with `q² ∣ s`
  have hsub : T ⊆ T.filter (fun x => ∃ q ∈ Q, q * q ∣ f x) ∪
      T.filter (fun x => ∃ d ∈ Ico (z + 1) (K * m), d * d ∣ f x) := by
    intro x hx
    have := hbad x hx
    rw [Nat.squarefree_iff_prime_squarefree] at this
    push Not at this
    obtain ⟨q, hq, hqd⟩ := this
    simp only [mem_union, mem_filter]
    by_cases hqz : q ≤ z
    · left
      exact ⟨hx, q, by simp only [hQ, mem_filter, mem_Icc]; exact ⟨⟨hq.one_lt.le, hqz⟩, hq⟩, hqd⟩
    · right
      refine ⟨hx, q, ?_, hqd⟩
      have hle : q * q ≤ f x := Nat.le_of_dvd (hfT x hx).1 hqd
      have : q ≤ q * q := Nat.le_mul_of_pos_right q hq.pos
      simp only [mem_Ico]
      constructor <;> [omega; exact lt_of_le_of_lt (this.trans hle) (hfT x hx).2]
  -- small primes
  have hsmall_q : ∀ q ∈ Q, #(T.filter (fun x => q * q ∣ f x)) ≤ #P * (K / (q * q) + 1) := by
    intro q hq
    simp only [hQ, mem_filter] at hq
    rw [card_filter, hT, sum_product]
    calc ∑ p ∈ P, ∑ j ∈ range K, (if q * q ∣ f (p, j) then 1 else 0)
        = ∑ p ∈ P, #((range K).filter (fun j => q * q ∣ nf p + j * m)) := by
          refine sum_congr rfl fun p _ => ?_
          rw [card_filter]
      _ ≤ ∑ p ∈ P, (K / (q * q) + 1) := by
          refine sum_le_sum fun p hp => ?_
          exact card_res_le q m (nf p) K hq.2 (resid_facts hm ha hp).2.2.1
      _ = #P * (K / (q * q) + 1) := by rw [sum_const, smul_eq_mul]
  have hsmall : (#(T.filter (fun x => ∃ q ∈ Q, q * q ∣ f x)) : ℝ) ≤
      #P * ((11 / 18) * K + z) := by
    have h1 : T.filter (fun x => ∃ q ∈ Q, q * q ∣ f x) ⊆
        Q.biUnion (fun q => T.filter (fun x => q * q ∣ f x)) := by
      intro x hx
      simp only [mem_filter] at hx
      obtain ⟨hx, q, hq, hd⟩ := hx
      exact mem_biUnion.2 ⟨q, hq, mem_filter.2 ⟨hx, hd⟩⟩
    have h2 := ((card_le_card h1).trans card_biUnion_le).trans (sum_le_sum hsmall_q)
    have h3 : (#(T.filter (fun x => ∃ q ∈ Q, q * q ∣ f x)) : ℝ) ≤
        ∑ q ∈ Q, (#P : ℝ) * (((K / (q * q) : ℕ) : ℝ) + 1) := by exact_mod_cast h2
    have hQz : (#Q : ℝ) ≤ z := by
      have : #Q ≤ z := (card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    have hsum := sum_prime_inv_sq_le z
    calc _ ≤ ∑ q ∈ Q, (#P : ℝ) * (((K / (q * q) : ℕ) : ℝ) + 1) := h3
      _ ≤ ∑ q ∈ Q, (#P : ℝ) * ((K : ℝ) * (1 / ((q : ℝ) * q)) + 1) := by
          refine sum_le_sum fun q _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have : ((K / (q * q) : ℕ) : ℝ) ≤ (K : ℝ) / ((q * q : ℕ) : ℝ) := Nat.cast_div_le
          push_cast at this
          rw [mul_one_div]; linarith
      _ = (#P : ℝ) * ((K : ℝ) * ∑ q ∈ Q, (1 / ((q : ℝ) * q)) + #Q) := by
          rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one]
      _ ≤ #P * ((11 / 18) * K + z) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have hK' : (0 : ℝ) ≤ K := Nat.cast_nonneg _
          nlinarith
  -- large primes: injectivity of `(p, j) ↦ n_p + j m`
  have hlarge : (#(T.filter (fun x => ∃ d ∈ Ico (z + 1) (K * m), d * d ∣ f x)) : ℝ) ≤
      (K * m : ℕ) / z := by
    have hinj : Set.InjOn f ↑(T.filter (fun x => ∃ d ∈ Ico (z + 1) (K * m), d * d ∣ f x)) := by
      intro x hx y hy hxy
      simp only [coe_filter, hT, mem_product, mem_range, Set.mem_ofPred_eq] at hx hy
      have hx1 : nf x.1 < m := (resid_facts hm ha hx.1.1).2.1
      have hy1 : nf y.1 < m := (resid_facts hm ha hy.1.1).2.1
      have hxy' : nf x.1 + x.2 * m = nf y.1 + y.2 * m := hxy
      have e1 : nf x.1 = nf y.1 := by
        have := congrArg (· % m) hxy'
        simp only [Nat.add_mul_mod_self_right] at this
        rwa [Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hy1] at this
      have e2 : x.2 = y.2 := by
        have : x.2 * m = y.2 * m := by omega
        exact Nat.eq_of_mul_eq_mul_right (by omega) this
      have e3 : x.1 = y.1 := resid_injOn ha hx.1.1 hy.1.1 e1
      exact Prod.ext e3 e2
    have hmaps : Set.MapsTo f ↑(T.filter (fun x => ∃ d ∈ Ico (z + 1) (K * m), d * d ∣ f x))
        ↑((Ioo 0 (K * m)).filter (fun n => ∃ d ∈ Ico (z + 1) (K * m), d * d ∣ n)) := by
      intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨mem_Ioo.2 (hfT x hx.1), hx.2⟩
    have := card_le_card_of_injOn f hmaps hinj
    have h2 := card_sq_tail (K * m) z hz1
    calc _ ≤ ((#((Ioo 0 (K * m)).filter (fun n => ∃ d ∈ Ico (z + 1) (K * m), d * d ∣ n)) : ℕ) : ℝ) := by
          exact_mod_cast this
      _ ≤ _ := h2
  have htot : (#T : ℝ) ≤ #P * ((11 / 18) * K + z) + (K * m : ℕ) / z := by
    have := (card_le_card hsub).trans (card_union_le _ _)
    have : (#T : ℝ) ≤ (#(T.filter (fun x => ∃ q ∈ Q, q * q ∣ f x)) : ℝ) +
        #(T.filter (fun x => ∃ d ∈ Ico (z + 1) (K * m), d * d ∣ f x)) := by exact_mod_cast this
    linarith
  have hTc : (#T : ℝ) = K * #P := by
    rw [hT, card_product, card_range]; push_cast; ring
  have hzR : (K : ℝ) = 6 * z := by exact_mod_cast hzK
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz1
  rw [hTc] at htot
  have : ((K * m : ℕ) : ℝ) / z = 6 * m := by
    push_cast; rw [hzR]; field_simp
  rw [this, hzR] at htot
  rw [hzR] at hK
  nlinarith


/-- **Theorem F1′, with roughness.** Assume `TypeISifted` (a cited **unconditional** theorem:
Fouvry–Shparlinski Type I for `A_a` plus the fundamental lemma; see its docstring in
`GapH4.lean`). Then there are `η > 0` and `m₀` such that for all `m ≥ m₀` and every unit `a`
mod `m`, `a ≡ p s` with `p ≤ m` prime and `s < m` squarefree with every prime factor `≥ m^η`
(so `ω(s) < 1/η`).

**GRH is not used.** The result is **known**: K. H. Yau, arXiv:1907.06016, Theorem 3.1. -/
theorem estermann_of_typeISifted_rough (hT : TypeISifted) :
    ∃ η : ℝ, 0 < η ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ a : ZMod m, IsUnit a →
      ∃ p s : ℕ, p.Prime ∧ p ≤ m ∧ Squarefree s ∧ s < m ∧
        (∀ q : ℕ, q.Prime → q ∣ s → (m : ℝ) ^ η ≤ q) ∧ ((p * s : ℕ) : ZMod m) = a := by
  obtain ⟨η₁, hη₁, hT'⟩ := hT (1 / 4) (by norm_num)
  set η := min η₁ (1 / 4) with hηdef
  have hη0 : 0 < η := lt_min hη₁ (by norm_num)
  have hη4 : η ≤ 1 / 4 := min_le_right _ _
  obtain ⟨m₁, hm₁⟩ := hT' η hη0 (min_le_left _ _)
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hpow := (tendsto_rpow_atTop (show 0 < η / 2 by positivity)).comp hcast
  have hpow4 := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).comp hcast
  have e1 := hpow.eventually_ge_atTop (300 / η ^ 2 + 2)
  have e2 := hpow4.eventually_ge_atTop 400
  have e0 := Filter.eventually_ge_atTop (max m₁ 4)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (e0.and (e1.and e2))
  refine ⟨η, hη0, N, fun m hm a ha => ?_⟩
  obtain ⟨h0, h1, h2⟩ := hN m hm
  simp only [Function.comp] at h1 h2
  have hm4 : 4 ≤ m := (le_max_right _ _).trans h0
  have hmm₁ : m₁ ≤ m := (le_max_left _ _).trans h0
  have : NeZero m := ⟨by omega⟩
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hmpos : (0 : ℝ) < m := by linarith
  set y := (m : ℝ) ^ η with hy
  set u := (m : ℝ) ^ (η / 2) with hu
  set v := (m : ℝ) ^ (η / 4) with hv
  have hyu : y = u ^ 2 := by
    rw [hy, hu, ← Real.rpow_natCast, ← Real.rpow_mul hm0]; congr 1; push_cast; ring
  have huv : u = v ^ 2 := by
    rw [hu, hv, ← Real.rpow_natCast, ← Real.rpow_mul hm0]; congr 1; push_cast; ring
  have hη2 : 0 ≤ 300 / η ^ 2 := by positivity
  have hu1 : 1 ≤ u := by linarith
  have hy2 : 2 ≤ y := by nlinarith
  -- `log m ≤ 4 m^{η/4}/η`, hence `log² m ≤ 16 u/η²` and `y ≥ 18 log² m`
  set L := Real.log m with hLdef
  have hL : 0 < L := Real.log_pos hm1
  have hlog : L ≤ v / (η / 4) := Real.log_le_rpow_div hm0 (by positivity)
  have hL2 : L ^ 2 ≤ 16 * u / η ^ 2 := by
    have h := pow_le_pow_left₀ hL.le hlog 2
    rw [huv]
    calc L ^ 2 ≤ (v / (η / 4)) ^ 2 := h
      _ = 16 * v ^ 2 / η ^ 2 := by field_simp; ring
  have hyL : 18 * L ^ 2 ≤ y := by
    have h3 : 18 * L ^ 2 ≤ 18 * (16 * u / η ^ 2) := by linarith
    have h4 : 18 * (16 * u / η ^ 2) ≤ (300 / η ^ 2) * u := by
      rw [div_mul_eq_mul_div, mul_div_assoc']
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have h5 : (300 / η ^ 2) * u ≤ y := by
      rw [hyu]; nlinarith
    linarith
  -- Chebyshev and `|P| ≥ π(m) − √m − 2`
  obtain ⟨hA, -, hC, -⟩ := GapH4.large_facts m hm4 η hη0 hη4 h2
  set π' := (Nat.primeCounting m : ℝ) with hπ'
  have hP := card_primesP_ge m (by omega)
  have hysq : y ≤ Real.sqrt m := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hm1.le (by linarith)
  have hΦ := card_primesP_le_PhiCop m y (by linarith)
  have hρ : (#(primesP m) : ℝ) / m ≤ rho m := by
    unfold rho
    have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
    have hφm : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hφ hφm
  have hTI := hm₁ m hmm₁ a ha
  rw [← hy] at hTI
  set Φ := (PhiCop m m y : ℝ)
  set S := (siftedR y (Aset m a) : ℝ)
  set P := (#(primesP m) : ℝ)
  have hΦ0 : 0 ≤ Φ := Nat.cast_nonneg _
  have hP9 : 9 / 10 * π' ≤ P := by linarith
  have hB : 35 / 100 * π' ≤ (1 - 1 / 4 * η) * Φ - 1 / 4 * π' := by
    have : 3 / 4 * Φ ≤ (1 - 1 / 4 * η) * Φ := by nlinarith
    linarith
  have hπ0 : 0 ≤ π' := Nat.cast_nonneg _
  have hρ9 : 9 / 10 * π' / m ≤ rho m := (div_le_div_of_nonneg_right hP9 hm0).trans hρ
  have hS : 9 / 10 * π' / m * (35 / 100 * π') ≤ S :=
    (mul_le_mul hρ9 hB (by positivity) (GapH4.rho_nonneg m)).trans hTI
  have hπL : 693 / 1000 * m ≤ π' * L := by
    have := hC; rw [div_le_div_iff₀ hL (by norm_num)] at this; linarith
  have hfin : 2 * (m : ℝ) / y < S :=
    lt_of_lt_of_le (f1_numeric hmpos (by linarith) hπL hyL) hS
  obtain ⟨p, s, hp, hpm, hs, hsm, hrough, hps⟩ := exists_sqfree_of_sifted (by omega) ha hy2 hfin
  exact ⟨p, s, hp, hpm, hs, hsm, hrough, hps⟩

/-- **Theorem F1′ (Estermann analogue for EOS).** Assume `TypeISifted` (a cited
**unconditional** theorem: Fouvry–Shparlinski Type I for `A_a` plus the fundamental lemma; see
`GapH4.lean`). Then for all large `m` every unit `a` mod `m` is `≡ p s` with `p ≤ m` prime and
`s < m` squarefree.

**GRH is not used.** The result is **known**: K. H. Yau, arXiv:1907.06016, Theorem 3.1. -/
theorem estermann_of_typeISifted (hT : TypeISifted) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ a : ZMod m, IsUnit a →
      ∃ p s : ℕ, p.Prime ∧ p ≤ m ∧ Squarefree s ∧ s < m ∧ ((p * s : ℕ) : ZMod m) = a := by
  obtain ⟨η, -, m₀, h⟩ := estermann_of_typeISifted_rough hT
  refine ⟨m₀, fun m hm a ha => ?_⟩
  obtain ⟨p, s, hp, hpm, hs, hsm, -, hps⟩ := h m hm a ha
  exact ⟨p, s, hp, hpm, hs, hsm, hps⟩


/-- **F0 in explicit form (hypothesis-free).** For `m ≥ 400⁴`, every unit `a` mod `m` is
`≡ p s` with `p ≤ m` prime and `s ≤ 56 m log m` squarefree. Uses only Mathlib's Chebyshev bound
`π(m) ≥ m log 2 / log m`; no GRH. -/
theorem estermann_long_log (m : ℕ) (hm : 400 ^ 4 ≤ m) (a : ZMod m) (ha : IsUnit a) :
    ∃ p s : ℕ, p.Prime ∧ p ≤ m ∧ Squarefree s ∧ (s : ℝ) ≤ 56 * m * Real.log m ∧
      ((p * s : ℕ) : ZMod m) = a := by
  have hm4 : 4 ≤ m := le_trans (by norm_num) hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have ht : 400 ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : ((400 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) = 400 := by
      rw [show (1 : ℝ) / 4 = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hm) (by norm_num)
  obtain ⟨hA, -, hC, -⟩ := GapH4.large_facts m hm4 (1 / 4) (by norm_num) le_rfl ht
  have hP := Estermann.card_primesP_ge m (by omega)
  set L := Real.log m with hLdef
  have hL3 : 3 ≤ L := by
    have h32 : ((32 : ℕ) : ℝ) ≤ m := by exact_mod_cast le_trans (by norm_num) hm
    have := Real.log_le_log (by norm_num) h32
    have e : Real.log ((32 : ℕ) : ℝ) = 5 * Real.log 2 := by
      rw [show ((32 : ℕ) : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hL : 0 < L := by linarith
  set pc := (Nat.primeCounting m : ℝ)
  set P := (#(primesP m) : ℝ)
  have hπL : 693 / 1000 * m ≤ pc * L := by
    have := hC; rw [div_le_div_iff₀ hL (by norm_num)] at this; linarith
  have hPL : 6 / 10 * m ≤ P * L := by
    have : 9 / 10 * pc ≤ P := by linarith
    nlinarith
  set K := 6 * (⌊9 * L⌋₊ + 1) with hK
  have hKlo : 54 * L < K := by
    have := Nat.lt_floor_add_one (9 * L)
    simp only [hK]; push_cast; linarith
  have hKhi : (K : ℝ) ≤ 54 * L + 6 := by
    have := Nat.floor_le (show 0 ≤ 9 * L by linarith)
    simp only [hK]; push_cast; linarith
  have hP0 : 0 < P := by
    by_contra h; push Not at h
    have h1 : P * L ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hL.le
    have h2 : (4 : ℝ) ≤ m := by exact_mod_cast hm4
    linarith
  have hKP : 27 * (m : ℝ) < K * P := by
    have := mul_lt_mul_of_pos_right hKlo hP0
    nlinarith
  obtain ⟨p, s, hp, hpm, hs, hsK, hps⟩ :=
    estermann_long m (by omega) K (Dvd.intro _ rfl) hKP a ha
  refine ⟨p, s, hp, hpm, hs, ?_, hps⟩
  have : (s : ℝ) ≤ K * m := by exact_mod_cast hsK.le
  have h2 : (K : ℝ) * m ≤ (54 * L + 6) * m := mul_le_mul_of_nonneg_right hKhi hm0
  nlinarith

end EOS
