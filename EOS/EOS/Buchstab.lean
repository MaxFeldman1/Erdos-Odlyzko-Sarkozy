import EOS.Statement

/-!
# The finite Buchstab certificate (Lemmas C and C′ of `notes/brainstorm/r3-synthesis.md` §2.3)

Everything in this file is **unconditional** and has **no `sorry`**. GRH is not used.

Notation (`m ≥ 2`, `a` a unit mod `m`):
* `primesP m` is `P = {p ≤ m prime, p ∤ m}`.
* `Aset m a` is `A_a = {a·p̄ mod m : p ∈ P}`, as least non-negative residues (`ZMod.val`); its
  elements lie in `[1, m)` (`mem_Aset`).
* `P⁻(n)` is `Nat.minFac n`. Conditions `x < √m`, `x ≥ √m` are written `x * x < m`, `m ≤ x * x`.
* `sifted z A = S(A, z) = #{n ∈ A : n = 1 ∨ P⁻(n) ≥ z}`.
* `bilinear m z A = B = Σ_{z ≤ p₁ < √m} #{n = p₁ k ∈ A : k = 1 ∨ P⁻(k) ≥ p₁}`.
* `primeCount m A = #{n ∈ A prime : n ≥ √m}`.
* `roughUnits m M = 𝒦 = {1 ≤ k ≤ m/M : (k, m) = 1, k = 1 ∨ P⁻(k) ≥ M}`.
* `blockCount m I c = π_I(c) = #{p₁ ∈ I prime, p₁ ∤ m : c·p̄₁ ∈ P}`, `delta m I ν c = π_I(c) − ν`.
* `rho m = |P|/φ(m)`, `primesIn m I = |I|′ = #{p ∈ I prime, p ∤ m}`.

## Main results
* `buchstab_identity` (Lemma C, general): for any `A ⊆ [1, m)` and `z * z ≤ m`,
  `primeCount m A + B + [1 ∈ A] = S(A, z)`.
* `lemmaC` (Lemma C for `A_a`): `#{primes n ≥ √m in A_a} = S(A_a, z) − B(a) − [1 ∈ A_a]` in `ℤ`.
* `buchstab_certificate` (Lemma C′, general blocks, any centring constants `ν_j`, fourth moment)
  and `buchstab_certificate_two` (second-moment / Cauchy–Schwarz variant).
* `lemmaC'` (Lemma C′ exactly as in §2.3: boundaries `M₀ ≤ z`, `M_J ≥ √m`, `I_j = [M_j, M_{j+1})`,
  `ν_j = ρ|I_j|′`): if `S(A_a,z) − 1 − Σ_j (ρ|I_j|′|𝒦_j| + |𝒦_j|^{3/4} Y_j^{1/4}) > 0` with
  `Y_j ≥ Σ_{c∈G} δ_j(c)⁴`, then `a ≡ p q` with primes `p, q ≤ m`.
* `lemmaC'_of_H4Block`: under the H4(η) block inequality the certificate reads
  `S(A_a,z) − 1 − (1 + η/2) ρ Σ_j |I_j|′|𝒦_j| > 0`.
* `coveredBy_of_certificate`: certificates for all units give `CoveredBy m m`.

Remarks on §2.3 found while formalizing: the lower bound `2 ≤ z` in Lemma C is not needed
(only `z ≤ √m` is); the blocks need only cover the primes `p ∤ m` in `[z, √m)` and lie above
their `M_j` (overlaps are harmless); the decomposition `π = ν + δ` holds for any `ν_j`, so the
certificate is valid for every choice of centring, not only `ρ|I_j|′`.

## The gap theorem

The gap theorem is proved, with no `sorry`, in `EOS/GapH4.lean` as `EOS.eos_of_H4`:
`TypeISifted → RoughCounts → (∃ η₀ κ > 0, ∀ η ≤ η₀, ∀ λ ≤ κη, H4 η λ → Conjecture)`.
`TypeISifted` and `RoughCounts` are cited **unconditional** theorems (Fouvry–Shparlinski Type I plus the fundamental
lemma; sieve upper bound and Buchstab/Mertens rough-number asymptotics). `H4` is the per-block fourth-moment bound
`H4Block` over the block system tiling `[m^η, √m)`. **H4 is stronger than EOS and is not known to follow from GRH**;
GRH is not a hypothesis. See `notes/routes/E-buchstab-H4.md` for the paper proof.
-/

open scoped BigOperators
open Finset

namespace EOS.Buchstab

/-- `S(A, z) = #{n ∈ A : n = 1 or P⁻(n) ≥ z}` (with `P⁻(n) = Nat.minFac n`). -/
def sifted (z : ℕ) (A : Finset ℕ) : ℕ :=
  #{n ∈ A | n = 1 ∨ z ≤ n.minFac}

/-- `B = Σ_{z ≤ p₁ < √m, p₁ prime} #{n = p₁ k ∈ A : k = 1 or P⁻(k) ≥ p₁}`. The condition
`p₁ < √m` is written `p₁ * p₁ < m`. -/
def bilinear (m z : ℕ) (A : Finset ℕ) : ℕ :=
  ∑ p ∈ (range m).filter (fun p => p.Prime ∧ z ≤ p ∧ p * p < m),
    #{n ∈ A | p ∣ n ∧ (n / p = 1 ∨ p ≤ (n / p).minFac)}

/-- `#{primes n ≥ √m in A}`; the condition `n ≥ √m` is written `m ≤ n * n`. -/
def primeCount (m : ℕ) (A : Finset ℕ) : ℕ :=
  #{n ∈ A | n.Prime ∧ m ≤ n * n}

/-- For a prime `p` and `n > 0`: `n = p k` with `k = 1` or `P⁻(k) ≥ p` iff `n ≠ 1` and `P⁻(n) = p`. -/
lemma dvd_rough_iff {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    (p ∣ n ∧ (n / p = 1 ∨ p ≤ (n / p).minFac)) ↔ (n ≠ 1 ∧ n.minFac = p) := by
  constructor
  · rintro ⟨⟨k, rfl⟩, hk⟩
    have hp0 : 0 < p := hp.pos
    rw [Nat.mul_div_cancel_left _ hp0] at hk
    have hk0 : 0 < k := Nat.pos_of_mul_pos_left hn
    refine ⟨?_, ?_⟩
    · intro h
      exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right h)
    · apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right _ _))
      have hmf : (p * k).minFac.Prime := Nat.minFac_prime (by
        intro h; exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right h))
      rcases (Nat.Prime.dvd_mul hmf).1 (Nat.minFac_dvd (p * k)) with h | h
      · exact ((Nat.prime_dvd_prime_iff_eq hmf hp).1 h).symm.le
      · rcases hk with hk | hk
        · subst hk
          rw [Nat.dvd_one] at h
          exact absurd h hmf.one_lt.ne'
        · exact hk.trans (Nat.minFac_le_of_dvd hmf.two_le h)
  · rintro ⟨hn1, hmin⟩
    have hpd : p ∣ n := hmin ▸ Nat.minFac_dvd n
    refine ⟨hpd, ?_⟩
    by_cases hk : n / p = 1
    · exact Or.inl hk
    · right
      have hk0 : n / p ≠ 0 := by
        intro h
        rw [Nat.div_eq_zero_iff_lt hp.pos] at h
        exact absurd (Nat.le_of_dvd hn hpd) (not_le.2 h)
      calc p = n.minFac := hmin.symm
        _ ≤ (n / p).minFac :=
          Nat.minFac_le_of_dvd (Nat.minFac_prime hk).two_le
            ((Nat.minFac_dvd _).trans (Nat.div_dvd_of_dvd hpd))

/-- The bilinear term counts the `n ∈ A`, `n ≠ 1`, with `z ≤ P⁻(n) < √m` (each once, at `p₁ = P⁻(n)`). -/
lemma bilinear_eq (m z : ℕ) (A : Finset ℕ) (hA : ∀ n ∈ A, 0 < n ∧ n < m) :
    bilinear m z A = #{n ∈ A | n ≠ 1 ∧ z ≤ n.minFac ∧ n.minFac * n.minFac < m} := by
  classical
  rw [card_eq_sum_card_fiberwise (f := Nat.minFac)
    (t := (range m).filter (fun p => p.Prime ∧ z ≤ p ∧ p * p < m))]
  · unfold bilinear
    refine sum_congr rfl fun p hp => ?_
    simp only [mem_filter, mem_range] at hp
    rw [filter_filter]
    refine congrArg card (filter_congr fun n hn => ?_)
    rw [dvd_rough_iff hp.2.1 (hA n hn).1]
    constructor
    · rintro ⟨hn1, rfl⟩
      exact ⟨⟨hn1, hp.2.2.1, hp.2.2.2⟩, rfl⟩
    · rintro ⟨⟨hn1, -⟩, h⟩
      exact ⟨hn1, h⟩
  · intro n hn
    simp only [coe_filter, Set.mem_ofPred_eq] at hn
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    have h1 : 1 ≤ n.minFac := (Nat.minFac_pos n)
    refine ⟨?_, Nat.minFac_prime hn.2.1, hn.2.2.1, hn.2.2.2⟩
    nlinarith [hn.2.2.2]

/-- **Lemma C (exact Buchstab identity), general form.** For any finite set `A` of integers in
`[1, m)` and any `z` with `z ≤ √m` (written `z * z ≤ m`):
`#{primes n ≥ √m in A} + B + [1 ∈ A] = S(A, z)`. -/
theorem buchstab_identity (m z : ℕ) (A : Finset ℕ) (hA : ∀ n ∈ A, 0 < n ∧ n < m)
    (hz : z * z ≤ m) :
    primeCount m A + bilinear m z A + (if 1 ∈ A then 1 else 0) = sifted z A := by
  classical
  rw [bilinear_eq m z A hA, primeCount, sifted, card_filter, card_filter, card_filter,
    ← sum_ite_eq' A 1 (fun _ => (1 : ℕ)), ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  obtain ⟨hn0, hnm⟩ := hA n hn
  by_cases h1 : n = 1
  · subst h1; simp [Nat.not_prime_one]
  have hpos : 1 ≤ n.minFac := Nat.minFac_pos n
  by_cases hzn : z ≤ n.minFac
  · by_cases hsq : n.minFac * n.minFac < m
    · have hnp : ¬ (n.Prime ∧ m ≤ n * n) := by
        rintro ⟨hp, hle⟩
        rw [hp.minFac_eq] at hsq
        omega
      simp [hnp, h1, hzn, hsq]
    · have hp : n.Prime := by
        by_contra hnp
        have := Nat.minFac_sq_le_self hn0 hnp
        rw [sq] at this
        omega
      have hle : m ≤ n * n := by
        rw [hp.minFac_eq] at hsq; omega
      rw [hp.minFac_eq] at hzn hsq
      simp [hp, hle, h1, hzn, hsq]
  · have hnp : ¬ (n.Prime ∧ m ≤ n * n) := by
      rintro ⟨hp, hle⟩
      rw [hp.minFac_eq] at hzn
      have : n * n < z * z := Nat.mul_lt_mul'' (not_le.1 hzn) (not_le.1 hzn)
      omega
    simp [hnp, h1, hzn]

/-! ### The set `A_a` -/

/-- `P = {p ≤ m prime, p ∤ m}`. -/
def primesP (m : ℕ) : Finset ℕ := (range (m + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ m)

/-- `A_a = {a·p̄ mod m : p ∈ P}`, as least non-negative residues (`ZMod.val`). For `m ≥ 2` and a
unit `a` these lie in `[1, m)` (`mem_Aset`). -/
def Aset (m : ℕ) (a : ZMod m) : Finset ℕ := (primesP m).image (fun q : ℕ => (a * (q : ZMod m)⁻¹).val)

lemma mem_primesP {m q : ℕ} : q ∈ primesP m ↔ q ≤ m ∧ q.Prime ∧ ¬ q ∣ m := by
  simp [primesP]

lemma coprime_of_mem_primesP {m q : ℕ} (hq : q ∈ primesP m) : q.Coprime m := by
  rw [mem_primesP] at hq
  exact (Nat.Prime.coprime_iff_not_dvd hq.2.1).2 hq.2.2

lemma lt_of_mem_primesP {m q : ℕ} (hq : q ∈ primesP m) : q < m := by
  rw [mem_primesP] at hq
  rcases hq.1.lt_or_eq with h | h
  · exact h
  · exact absurd (h ▸ dvd_refl q) hq.2.2

/-- Basic facts about `n ∈ A_a`: `n ∈ [1, m)`, `(n, m) = 1`, and `n q ≡ a` for some `q ∈ P`. -/
lemma mem_Aset {m : ℕ} [NeZero m] (hm : 2 ≤ m) {a : ZMod m} (ha : IsUnit a) {n : ℕ}
    (hn : n ∈ Aset m a) :
    0 < n ∧ n < m ∧ n.Coprime m ∧ ∃ q ∈ primesP m, ((n * q : ℕ) : ZMod m) = a := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hn
  have hqc := coprime_of_mem_primesP hq
  have hq1 : (q : ZMod m) * (q : ZMod m)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one q hqc
  have hu : IsUnit (a * (q : ZMod m)⁻¹) :=
    ha.mul (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans hq1))
  have hcop : (a * (q : ZMod m)⁻¹).val.Coprime m := by
    obtain ⟨u, hu⟩ := hu
    rw [← hu]; exact ZMod.val_coe_unit_coprime u
  refine ⟨?_, ZMod.val_lt _, hcop, q, hq, ?_⟩
  · rcases Nat.eq_zero_or_pos (a * (q : ZMod m)⁻¹).val with h | h
    · rw [h, Nat.coprime_zero_left] at hcop; omega
    · exact h
  · push_cast
    rw [ZMod.natCast_zmod_val, mul_assoc, mul_comm _ (q : ZMod m), hq1, mul_one]

lemma Aset_bounds {m : ℕ} [NeZero m] (hm : 2 ≤ m) {a : ZMod m} (ha : IsUnit a) :
    ∀ n ∈ Aset m a, 0 < n ∧ n < m := by
  intro n hn
  exact ⟨(mem_Aset hm ha hn).1, (mem_Aset hm ha hn).2.1⟩

/-- **Lemma C (exact Buchstab identity) for `A_a`.** For `m ≥ 2`, a unit `a` mod `m`, and
`z ≤ √m` (written `z * z ≤ m`; no lower bound on `z` is needed):
`#{primes n ≥ √m in A_a} = S(A_a, z) − B(a) − [1 ∈ A_a]`. -/
theorem lemmaC {m : ℕ} [NeZero m] (hm : 2 ≤ m) {a : ZMod m} (ha : IsUnit a) {z : ℕ}
    (hz : z * z ≤ m) :
    (primeCount m (Aset m a) : ℤ) =
      sifted z (Aset m a) - bilinear m z (Aset m a) - (if 1 ∈ Aset m a then 1 else 0) := by
  have := buchstab_identity m z (Aset m a) (Aset_bounds hm ha) hz
  rw [← this]; push_cast; ring

/-! ### Lemma C′: the finite certificate -/

/-- `𝒦 = {units k ≤ m/M : k = 1 or P⁻(k) ≥ M}`; `k ≤ m/M` is written `k * M ≤ m`. -/
def roughUnits (m M : ℕ) : Finset ℕ :=
  (range (m + 1)).filter (fun k => 0 < k ∧ k.Coprime m ∧ k * M ≤ m ∧ (k = 1 ∨ M ≤ k.minFac))

/-- `π_I(c) = #{p₁ ∈ I prime, p₁ ∤ m : c·p̄₁ ∈ P}`. -/
def blockCount (m : ℕ) (I : Finset ℕ) (c : ZMod m) : ℕ :=
  #{p ∈ I | p.Prime ∧ ¬ p ∣ m ∧ (c * (p : ZMod m)⁻¹).val ∈ primesP m}

/-- `δ_I(c) = π_I(c) − ν`; §2.3 takes `ν = ρ|I|` (see `rho`, `primesIn`). -/
noncomputable def delta (m : ℕ) (I : Finset ℕ) (ν : ℝ) (c : ZMod m) : ℝ :=
  (blockCount m I c : ℝ) - ν

/-- `Σ_{k∈K} #{p ∈ I : R k p} = #{(k, p) ∈ K × I : R k p}`. -/
lemma sum_card_filter_eq_card_product (K I : Finset ℕ) (R : ℕ → ℕ → Prop)
    [∀ k p, Decidable (R k p)] :
    ∑ k ∈ K, #{p ∈ I | R k p} = #{x ∈ K ×ˢ I | R x.1 x.2} := by
  rw [card_filter, sum_product]
  simp only [card_filter]

/-- **Inclusion (2.1)** of the analytic note, with positivity absorbing the cut-off `p₁ k < m`
and the dependence of the roughness condition on `p₁`. The blocks `I j` (`j ∈ J`) need only
cover the primes `p ∤ m` in `[z, √m)` and lie above `M j`; they may overlap. -/
lemma bilinear_le_sum {m : ℕ} [NeZero m] (hm : 2 ≤ m) {a : ZMod m} (ha : IsUnit a) (z : ℕ)
    {ι : Type*} (J : Finset ι) (M : ι → ℕ) (I : ι → Finset ℕ)
    (hcov : ∀ p, p.Prime → ¬ p ∣ m → z ≤ p → p * p < m → ∃ j ∈ J, p ∈ I j)
    (hlow : ∀ j ∈ J, ∀ p ∈ I j, M j ≤ p) :
    bilinear m z (Aset m a) ≤
      ∑ j ∈ J, ∑ k ∈ roughUnits m (M j), blockCount m (I j) (a * (k : ZMod m)⁻¹) := by
  classical
  rw [bilinear_eq m z _ (Aset_bounds hm ha)]
  set s := {n ∈ Aset m a | n ≠ 1 ∧ z ≤ n.minFac ∧ n.minFac * n.minFac < m} with hs
  -- Every `n ∈ s` has its least prime factor in some block.
  have hsub : s ⊆ J.biUnion (fun j => s.filter (fun n => n.minFac ∈ I j)) := by
    intro n hn
    have hn' := hn
    rw [hs, mem_filter] at hn'
    obtain ⟨hnA, hn1, hzn, hsq⟩ := hn'
    obtain ⟨-, -, hcop, -⟩ := mem_Aset hm ha hnA
    have hp := Nat.minFac_prime hn1
    have hpm : ¬ n.minFac ∣ m := fun h =>
      hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop (Nat.minFac_dvd n) h)
    obtain ⟨j, hj, hpj⟩ := hcov _ hp hpm hzn hsq
    exact mem_biUnion.2 ⟨j, hj, mem_filter.2 ⟨hn, hpj⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun j hj => ?_))
  unfold blockCount
  rw [sum_card_filter_eq_card_product]
  refine card_le_card_of_injOn (fun n => (n / n.minFac, n.minFac)) ?_ ?_
  · intro n hn
    simp only [coe_filter, Set.mem_ofPred_eq, hs, mem_filter] at hn
    obtain ⟨⟨hnA, hn1, hzn, hsq⟩, hpI⟩ := hn
    obtain ⟨hn0, hnm, hcop, q, hq, hnq⟩ := mem_Aset hm ha hnA
    have hp := Nat.minFac_prime hn1
    set p := n.minFac with hpdef
    have hpd : p ∣ n := Nat.minFac_dvd n
    have hkp : n / p * p = n := Nat.div_mul_cancel hpd
    set k := n / p with hkdef
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro h; rw [h, zero_mul] at hkp; omega)
    have hkcop : k.Coprime m := Nat.Coprime.coprime_dvd_left ⟨p, hkp.symm⟩ hcop
    have hpcop : p.Coprime m := Nat.Coprime.coprime_dvd_left hpd hcop
    have hpm : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hp).1 hpcop
    have hMp : M j ≤ p := hlow j hj p hpI
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, roughUnits, mem_filter, mem_range]
    refine ⟨⟨⟨?_, hk0, hkcop, ?_, ?_⟩, hpI⟩, hp, hpm, ?_⟩
    · nlinarith [hp.pos]
    · calc k * M j ≤ k * p := Nat.mul_le_mul_left _ hMp
        _ = n := hkp
        _ ≤ m := hnm.le
    · by_cases hk1 : k = 1
      · exact Or.inl hk1
      · right
        refine hMp.trans ?_
        exact Nat.minFac_le_of_dvd (Nat.minFac_prime hk1).two_le
          ((Nat.minFac_dvd k).trans ⟨p, hkp.symm⟩)
    · -- `a k̄ p̄ = q`.
      have hk1 : (k : ZMod m) * (k : ZMod m)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one k hkcop
      have hp1 : (p : ZMod m) * (p : ZMod m)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one p hpcop
      have : a * (k : ZMod m)⁻¹ * (p : ZMod m)⁻¹ = q := by
        rw [← hnq, ← hkp]; push_cast
        calc (k : ZMod m) * p * q * (k : ZMod m)⁻¹ * (p : ZMod m)⁻¹
            = q * ((k : ZMod m) * (k : ZMod m)⁻¹) * ((p : ZMod m) * (p : ZMod m)⁻¹) := by ring
          _ = q := by rw [hk1, hp1]; ring
      rw [this, ZMod.val_cast_of_lt (lt_of_mem_primesP hq)]
      exact hq
  · intro n₁ hn₁ n₂ hn₂ h
    simp only [Prod.mk.injEq] at h
    rw [← Nat.div_mul_cancel (Nat.minFac_dvd n₁), ← Nat.div_mul_cancel (Nat.minFac_dvd n₂),
      h.1, h.2]

/-- If the sifted count beats the bilinear term plus `1`, then `A_a` contains a prime, so
`a ≡ p q` with primes `p, q ≤ m` (in fact `p < m`). -/
theorem exists_prime_mul_of_bilinear_lt {m : ℕ} [NeZero m] (hm : 2 ≤ m) {a : ZMod m}
    (ha : IsUnit a) {z : ℕ} (hz : z * z ≤ m)
    (h : (bilinear m z (Aset m a) : ℝ) < sifted z (Aset m a) - 1) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ m ∧ q ≤ m ∧ ((p * q : ℕ) : ZMod m) = a := by
  have hid := buchstab_identity m z (Aset m a) (Aset_bounds hm ha) hz
  have hpos : 0 < primeCount m (Aset m a) := by
    have hite : (if 1 ∈ Aset m a then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have h' : ((primeCount m (Aset m a) : ℕ) : ℝ) + bilinear m z (Aset m a)
        + ((if 1 ∈ Aset m a then 1 else 0 : ℕ) : ℝ) = sifted z (Aset m a) := by
      exact_mod_cast hid
    have hite' : ((if 1 ∈ Aset m a then 1 else 0 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hite
    have : (0 : ℝ) < primeCount m (Aset m a) := by linarith
    exact_mod_cast this
  obtain ⟨n, hn⟩ := card_pos.1 hpos
  rw [mem_filter] at hn
  obtain ⟨-, hnm, -, q, hq, hnq⟩ := mem_Aset hm ha hn.1
  exact ⟨n, q, hn.2.1, (mem_primesP.1 hq).2.1, hnm.le, (mem_primesP.1 hq).1, hnq⟩

/-- Power mean via Cauchy–Schwarz twice: `(Σ x)⁴ ≤ |s|³ Σ x⁴`. -/
lemma sum_pow_four_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∑ i ∈ s, x i) ^ 4 ≤ (#s : ℝ) ^ 3 * ∑ i ∈ s, x i ^ 4 := by
  have h1 : (∑ i ∈ s, x i) ^ 2 ≤ #s * ∑ i ∈ s, x i ^ 2 := by
    have := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) x
    simpa using this
  have h2 : (∑ i ∈ s, x i ^ 2) ^ 2 ≤ #s * ∑ i ∈ s, x i ^ 4 := by
    have := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => x i ^ 2)
    simpa [← pow_mul] using this
  have hn : (0 : ℝ) ≤ #s := Nat.cast_nonneg _
  calc (∑ i ∈ s, x i) ^ 4 = ((∑ i ∈ s, x i) ^ 2) ^ 2 := by ring
    _ ≤ (#s * ∑ i ∈ s, x i ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (#s : ℝ) ^ 2 * (∑ i ∈ s, x i ^ 2) ^ 2 := by ring
    _ ≤ (#s : ℝ) ^ 2 * (#s * ∑ i ∈ s, x i ^ 4) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (#s : ℝ) ^ 3 * ∑ i ∈ s, x i ^ 4 := by ring

/-- **Hölder (4/3, 4)** in the form used in (2.2): if `Σ x⁴ ≤ Y` then `Σ x ≤ |s|^{3/4} Y^{1/4}`. -/
lemma sum_le_holder_four {ι : Type*} (s : Finset ι) (x : ι → ℝ) {Y : ℝ}
    (hY : ∑ i ∈ s, x i ^ 4 ≤ Y) :
    ∑ i ∈ s, x i ≤ (#s : ℝ) ^ (3 / 4 : ℝ) * Y ^ (1 / 4 : ℝ) := by
  have hY0 : 0 ≤ Y := le_trans (sum_nonneg fun i _ => by positivity) hY
  have hn : (0 : ℝ) ≤ #s := Nat.cast_nonneg _
  rcases le_or_gt (∑ i ∈ s, x i) 0 with h | h
  · exact h.trans (by positivity)
  have h4 : (∑ i ∈ s, x i) ^ 4 ≤ (#s : ℝ) ^ 3 * Y :=
    (sum_pow_four_le s x).trans (mul_le_mul_of_nonneg_left hY (by positivity))
  calc ∑ i ∈ s, x i = ((∑ i ∈ s, x i) ^ 4) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h.le]; norm_num
    _ ≤ ((#s : ℝ) ^ 3 * Y) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) h4 (by norm_num)
    _ = (#s : ℝ) ^ (3 / 4 : ℝ) * Y ^ (1 / 4 : ℝ) := by
        rw [Real.mul_rpow (by positivity) hY0, ← Real.rpow_natCast, ← Real.rpow_mul hn]
        norm_num

/-- **Cauchy–Schwarz** in the same shape: if `Σ x² ≤ Y` then `Σ x ≤ |s|^{1/2} Y^{1/2}`. -/
lemma sum_le_cauchy_schwarz {ι : Type*} (s : Finset ι) (x : ι → ℝ) {Y : ℝ}
    (hY : ∑ i ∈ s, x i ^ 2 ≤ Y) :
    ∑ i ∈ s, x i ≤ (#s : ℝ) ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) := by
  have hY0 : 0 ≤ Y := le_trans (sum_nonneg fun i _ => by positivity) hY
  have hn : (0 : ℝ) ≤ #s := Nat.cast_nonneg _
  rcases le_or_gt (∑ i ∈ s, x i) 0 with h | h
  · exact h.trans (by positivity)
  have h2 : (∑ i ∈ s, x i) ^ 2 ≤ (#s : ℝ) * Y := by
    have := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) x
    simp only [one_pow, sum_const, nsmul_eq_mul, mul_one, one_mul] at this
    exact this.trans (mul_le_mul_of_nonneg_left hY hn)
  calc ∑ i ∈ s, x i = ((∑ i ∈ s, x i) ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h.le]; norm_num
    _ ≤ ((#s : ℝ) * Y) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) h2 (by norm_num)
    _ = (#s : ℝ) ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) := Real.mul_rpow hn hY0

/-- The classes `a·k̄`, `k ∈ 𝒦`, are distinct units, so a sum of a non-negative function over
them is at most its sum over `G = (ℤ/mℤ)ˣ`. -/
lemma sum_roughUnits_le_sum_units {m : ℕ} [NeZero m] (hm : 2 ≤ m) {a : ZMod m} (ha : IsUnit a)
    (M : ℕ) (h : ZMod m → ℝ) (hh : ∀ c, 0 ≤ h c) :
    ∑ k ∈ roughUnits m M, h (a * (k : ZMod m)⁻¹) ≤ ∑ c ∈ univ.filter IsUnit, h c := by
  classical
  have hmem : ∀ k ∈ roughUnits m M, 0 < k ∧ k < m ∧ k.Coprime m := by
    intro k hk
    simp only [roughUnits, mem_filter, mem_range] at hk
    refine ⟨hk.2.1, ?_, hk.2.2.1⟩
    rcases (Nat.lt_succ_iff.1 hk.1).lt_or_eq with h | h
    · exact h
    · have := hk.2.2.1; rw [h, Nat.coprime_self] at this; omega
  have hinj : Set.InjOn (fun k : ℕ => a * (k : ZMod m)⁻¹) (roughUnits m M) := by
    intro k₁ hk₁ k₂ hk₂ hk
    obtain ⟨-, hk₁m, hc₁⟩ := hmem k₁ hk₁
    obtain ⟨-, hk₂m, hc₂⟩ := hmem k₂ hk₂
    have hinv : (k₁ : ZMod m)⁻¹ = (k₂ : ZMod m)⁻¹ := ha.mul_left_cancel hk
    have e1 := ZMod.coe_mul_inv_eq_one k₁ hc₁
    have e2 := ZMod.coe_mul_inv_eq_one k₂ hc₂
    have : (k₁ : ZMod m) = k₂ := by
      calc (k₁ : ZMod m) = k₁ * ((k₂ : ZMod m) * (k₂ : ZMod m)⁻¹) := by rw [e2, mul_one]
        _ = k₂ * ((k₁ : ZMod m) * (k₁ : ZMod m)⁻¹) := by rw [← hinv]; ring
        _ = k₂ := by rw [e1, mul_one]
    have := congrArg ZMod.val this
    rwa [ZMod.val_cast_of_lt hk₁m, ZMod.val_cast_of_lt hk₂m] at this
  rw [← sum_image hinj]
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun c _ _ => hh c)
  intro c hc
  obtain ⟨k, hk, rfl⟩ := mem_image.1 hc
  obtain ⟨-, -, hck⟩ := hmem k hk
  have e := ZMod.coe_mul_inv_eq_one k hck
  simp only [mem_filter, mem_univ, true_and]
  exact ha.mul (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans e))

/-- Block bound: `Σ_{k∈𝒦} π_I(a k̄) = ν|𝒦| + Σ_{k∈𝒦} δ_I(a k̄)`. -/
lemma sum_blockCount_eq {m : ℕ} (a : ZMod m) (M : ℕ) (I : Finset ℕ) (ν : ℝ) :
    ((∑ k ∈ roughUnits m M, blockCount m I (a * (k : ZMod m)⁻¹) : ℕ) : ℝ) =
      ν * #(roughUnits m M) + ∑ k ∈ roughUnits m M, delta m I ν (a * (k : ZMod m)⁻¹) := by
  simp only [delta, Nat.cast_sum, sum_sub_distrib, sum_const, nsmul_eq_mul]
  ring

/-- **Lemma C′ (finite Buchstab certificate), general form, fourth moment.**
Let `m ≥ 2`, `a` a unit mod `m`, `z * z ≤ m`. Let blocks `I j` (`j ∈ J`) cover the primes
`p ∤ m` in `[z, √m)`, with every element of `I j` at least `M j`. Let `ν j` be any reals and
`Y j ≥ Σ_{c ∈ G} δ_j(c)⁴`, where `δ_j(c) = π_{I j}(c) − ν j`. If
`S(A_a, z) − 1 − Σ_j (ν_j |𝒦_j| + |𝒦_j|^{3/4} Y_j^{1/4}) > 0`, then `a ≡ p q` with primes
`p, q ≤ m`. (§2.3 takes `ν_j = ρ|I_j|`; the statement holds for every choice of `ν_j`.) -/
theorem buchstab_certificate {m : ℕ} [NeZero m] (hm : 2 ≤ m) {a : ZMod m} (ha : IsUnit a)
    {z : ℕ} (hz : z * z ≤ m)
    {ι : Type*} (J : Finset ι) (M : ι → ℕ) (I : ι → Finset ℕ) (ν Y : ι → ℝ)
    (hcov : ∀ p, p.Prime → ¬ p ∣ m → z ≤ p → p * p < m → ∃ j ∈ J, p ∈ I j)
    (hlow : ∀ j ∈ J, ∀ p ∈ I j, M j ≤ p)
    (hY : ∀ j ∈ J, ∑ c ∈ univ.filter IsUnit, delta m (I j) (ν j) c ^ 4 ≤ Y j)
    (hcert : 0 < (sifted z (Aset m a) : ℝ) - 1 - ∑ j ∈ J, (ν j * #(roughUnits m (M j)) +
        (#(roughUnits m (M j)) : ℝ) ^ (3 / 4 : ℝ) * Y j ^ (1 / 4 : ℝ))) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ m ∧ q ≤ m ∧ ((p * q : ℕ) : ZMod m) = a := by
  refine exists_prime_mul_of_bilinear_lt hm ha hz ?_
  have hB := bilinear_le_sum hm ha z J M I hcov hlow
  have hB' : (bilinear m z (Aset m a) : ℝ) ≤ ∑ j ∈ J, (ν j * #(roughUnits m (M j)) +
      (#(roughUnits m (M j)) : ℝ) ^ (3 / 4 : ℝ) * Y j ^ (1 / 4 : ℝ)) := by
    refine (Nat.cast_le.2 hB).trans ?_
    rw [Nat.cast_sum]
    refine sum_le_sum fun j hj => ?_
    rw [sum_blockCount_eq a (M j) (I j) (ν j)]
    refine (add_le_add_iff_left _).2 (sum_le_holder_four _ _ ?_)
    exact (sum_roughUnits_le_sum_units hm ha (M j) (fun c => delta m (I j) (ν j) c ^ 4)
      (fun c => by positivity)).trans (hY j hj)
  linarith

/-- **Lemma C′, second-moment (Cauchy–Schwarz) variant.** As `buchstab_certificate`, with
`Y j ≥ Σ_{c ∈ G} δ_j(c)²` and `|𝒦_j|^{1/2} Y_j^{1/2}` in place of `|𝒦_j|^{3/4} Y_j^{1/4}`. -/
theorem buchstab_certificate_two {m : ℕ} [NeZero m] (hm : 2 ≤ m) {a : ZMod m} (ha : IsUnit a)
    {z : ℕ} (hz : z * z ≤ m)
    {ι : Type*} (J : Finset ι) (M : ι → ℕ) (I : ι → Finset ℕ) (ν Y : ι → ℝ)
    (hcov : ∀ p, p.Prime → ¬ p ∣ m → z ≤ p → p * p < m → ∃ j ∈ J, p ∈ I j)
    (hlow : ∀ j ∈ J, ∀ p ∈ I j, M j ≤ p)
    (hY : ∀ j ∈ J, ∑ c ∈ univ.filter IsUnit, delta m (I j) (ν j) c ^ 2 ≤ Y j)
    (hcert : 0 < (sifted z (Aset m a) : ℝ) - 1 - ∑ j ∈ J, (ν j * #(roughUnits m (M j)) +
        (#(roughUnits m (M j)) : ℝ) ^ (1 / 2 : ℝ) * Y j ^ (1 / 2 : ℝ))) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ m ∧ q ≤ m ∧ ((p * q : ℕ) : ZMod m) = a := by
  refine exists_prime_mul_of_bilinear_lt hm ha hz ?_
  have hB := bilinear_le_sum hm ha z J M I hcov hlow
  have hB' : (bilinear m z (Aset m a) : ℝ) ≤ ∑ j ∈ J, (ν j * #(roughUnits m (M j)) +
      (#(roughUnits m (M j)) : ℝ) ^ (1 / 2 : ℝ) * Y j ^ (1 / 2 : ℝ)) := by
    refine (Nat.cast_le.2 hB).trans ?_
    rw [Nat.cast_sum]
    refine sum_le_sum fun j hj => ?_
    rw [sum_blockCount_eq a (M j) (I j) (ν j)]
    refine (add_le_add_iff_left _).2 (sum_le_cauchy_schwarz _ _ ?_)
    exact (sum_roughUnits_le_sum_units hm ha (M j) (fun c => delta m (I j) (ν j) c ^ 2)
      (fun c => by positivity)).trans (hY j hj)
  linarith

/-! ### The block form of §2.3: boundaries `M₀ ≤ z`, `M_J ≥ √m`, `I_j = [M_j, M_{j+1})` -/

/-- `ρ = |P|/φ(m)`. -/
noncomputable def rho (m : ℕ) : ℝ := (#(primesP m) : ℝ) / m.totient

/-- `|I|′ = #{p ∈ I prime, p ∤ m}`. -/
def primesIn (m : ℕ) (I : Finset ℕ) : ℕ := #{p ∈ I | p.Prime ∧ ¬ p ∣ m}

/-- Half-open blocks `[M_j, M_{j+1})`, `j < J`, with `M₀ ≤ z` and `M_J ≥ √m`, cover `[z, √m)`.
(Monotonicity of `M` is not needed.) -/
lemma blocks_cover (M : ℕ → ℕ) (J z m : ℕ) (h0 : M 0 ≤ z) (hJ : m ≤ M J * M J) {p : ℕ}
    (hzp : z ≤ p) (hpm : p * p < m) :
    ∃ j ∈ range J, p ∈ Ico (M j) (M (j + 1)) := by
  classical
  have hpJ : p < M J := by
    by_contra h
    have h := not_lt.1 h
    have := Nat.mul_le_mul h h
    omega
  have hJ0 : J ≠ 0 := by rintro rfl; omega
  have hex : ∃ i, p < M (i + 1) := ⟨J - 1, by rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hJ0)]⟩
  set i := Nat.find hex with hi
  have hpi : p < M (i + 1) := Nat.find_spec hex
  have hiJ : i < J := by
    by_contra h
    have h := not_lt.1 h
    have := Nat.find_min' hex (show p < M (J - 1 + 1) by
      rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hJ0)])
    omega
  refine ⟨i, mem_range.2 hiJ, mem_Ico.2 ⟨?_, hpi⟩⟩
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h]; omega
  · have := Nat.find_min hex (show i - 1 < i by omega)
    rw [Nat.sub_add_cancel h] at this
    omega

/-- **Lemma C′ (finite certificate), as stated in §2.3.** Let `m ≥ 2`, `a` a unit mod `m`,
`z * z ≤ m`, and boundaries `M 0 ≤ z`, `M J * M J ≥ m`; put `I_j = [M_j, M_{j+1})`,
`𝒦_j = roughUnits m M_j`, `δ_j(c) = π_{I_j}(c) − ρ|I_j|′` and suppose
`Y_j ≥ Σ_{c∈G} δ_j(c)⁴`. If `S(A_a, z) − 1 − Σ_{j<J} (ρ|I_j|′|𝒦_j| + |𝒦_j|^{3/4} Y_j^{1/4}) > 0`,
then `a ≡ p q` with primes `p, q ≤ m`. -/
theorem lemmaC' {m : ℕ} [NeZero m] (hm : 2 ≤ m) {a : ZMod m} (ha : IsUnit a)
    {z : ℕ} (hz : z * z ≤ m) (M : ℕ → ℕ) (J : ℕ) (h0 : M 0 ≤ z) (hJ : m ≤ M J * M J)
    (Y : ℕ → ℝ)
    (hY : ∀ j < J, ∑ c ∈ univ.filter IsUnit,
      delta m (Ico (M j) (M (j + 1))) (rho m * primesIn m (Ico (M j) (M (j + 1)))) c ^ 4 ≤ Y j)
    (hcert : 0 < (sifted z (Aset m a) : ℝ) - 1 - ∑ j ∈ range J,
      (rho m * primesIn m (Ico (M j) (M (j + 1))) * #(roughUnits m (M j)) +
        (#(roughUnits m (M j)) : ℝ) ^ (3 / 4 : ℝ) * Y j ^ (1 / 4 : ℝ))) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ m ∧ q ≤ m ∧ ((p * q : ℕ) : ZMod m) = a :=
  buchstab_certificate hm ha hz (range J) M (fun j => Ico (M j) (M (j + 1)))
    (fun j => rho m * primesIn m (Ico (M j) (M (j + 1)))) Y
    (fun _ _ _ hzp hpm => blocks_cover M J z m h0 hJ hzp hpm)
    (fun _ _ _ hp => (mem_Ico.1 hp).1)
    (fun j hj => hY j (mem_range.1 hj)) hcert

/-- The per-block inequality of hypothesis H4(η) (`notes/brainstorm/r1-analytic.md` §2.3):
`Σ_{c∈G} δ_I(c)⁴ ≤ (η/2)⁴ ρ⁴ |I|′⁴ |𝒦_M|`, with `δ_I(c) = π_I(c) − ρ|I|′`.
This is only the block inequality; the full hypothesis `H4 η` also fixes the block system
(`λ = η/(4C₁)`, blocks in `[m^η, (1+λ)√m]`) and quantifies over all large `m`.
H4 is stronger than EOS and is not known to follow from GRH. -/
def H4Block (m : ℕ) [NeZero m] (I : Finset ℕ) (M : ℕ) (η : ℝ) : Prop :=
  ∑ c ∈ univ.filter IsUnit, delta m I (rho m * primesIn m I) c ^ 4 ≤
    (η / 2) ^ 4 * rho m ^ 4 * (primesIn m I : ℝ) ^ 4 * #(roughUnits m M)

lemma rpow_three_quarters_mul (K t : ℝ) (hK : 0 ≤ K) (ht : 0 ≤ t) :
    K ^ (3 / 4 : ℝ) * (t ^ 4 * K) ^ (1 / 4 : ℝ) = t * K := by
  rw [Real.mul_rpow (by positivity) hK, ← Real.rpow_natCast, ← Real.rpow_mul ht]
  have : K ^ (3 / 4 : ℝ) * K ^ (1 / 4 : ℝ) = K := by
    rw [← Real.rpow_add' hK (by norm_num)]; norm_num
  norm_num
  linear_combination t * this

/-- **Corollary H4 without its asymptotic layer.** If every block `I_j = [M_j, M_{j+1})` satisfies
the H4(η) block inequality (`η ≥ 0`), then
`S(A_a, z) − 1 − (1 + η/2) ρ Σ_{j<J} |I_j|′ |𝒦_j| > 0` implies `a ≡ p q` with primes `p, q ≤ m`.
(The remaining steps of Cor H4, Lemma 2.2 and Lemma 2.1, are asymptotic and not formalized.) -/
theorem lemmaC'_of_H4Block {m : ℕ} [NeZero m] (hm : 2 ≤ m) {a : ZMod m} (ha : IsUnit a)
    {z : ℕ} (hz : z * z ≤ m) (M : ℕ → ℕ) (J : ℕ) (h0 : M 0 ≤ z) (hJ : m ≤ M J * M J)
    {η : ℝ} (hη : 0 ≤ η) (hH : ∀ j < J, H4Block m (Ico (M j) (M (j + 1))) (M j) η)
    (hcert : 0 < (sifted z (Aset m a) : ℝ) - 1 - (1 + η / 2) * rho m *
      ∑ j ∈ range J, (primesIn m (Ico (M j) (M (j + 1))) : ℝ) * #(roughUnits m (M j))) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ m ∧ q ≤ m ∧ ((p * q : ℕ) : ZMod m) = a := by
  have hρ : 0 ≤ rho m := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine lemmaC' hm ha hz M J h0 hJ
    (fun j => (η / 2) ^ 4 * rho m ^ 4 * (primesIn m (Ico (M j) (M (j + 1))) : ℝ) ^ 4 *
      #(roughUnits m (M j))) hH ?_
  convert hcert using 2
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have := rpow_three_quarters_mul (#(roughUnits m (M j)) : ℝ)
    ((η / 2) * rho m * (primesIn m (Ico (M j) (M (j + 1))) : ℝ)) (Nat.cast_nonneg _)
    (by positivity)
  rw [show (η / 2) ^ 4 * rho m ^ 4 * (primesIn m (Ico (M j) (M (j + 1))) : ℝ) ^ 4 *
      (#(roughUnits m (M j)) : ℝ) = ((η / 2) * rho m * (primesIn m (Ico (M j) (M (j + 1))) : ℝ)) ^ 4
      * #(roughUnits m (M j)) by ring, this]
  ring

/-- If the certificate of `lemmaC'` (with any boundaries and any `Y`) holds for every unit `a`,
then `CoveredBy m m`. -/
theorem coveredBy_of_certificate {m : ℕ}
    (h : ∀ a : ZMod m, IsUnit a →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ m ∧ q ≤ m ∧ ((p * q : ℕ) : ZMod m) = a) :
    CoveredBy m m := by
  intro a ha
  obtain ⟨p, q, hp, hq, hpm, hqm, hpq⟩ := h a ha
  exact ⟨p, q, hp, hq, by exact_mod_cast hpm, by exact_mod_cast hqm, hpq⟩

end EOS.Buchstab
