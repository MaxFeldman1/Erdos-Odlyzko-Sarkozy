# Route F: prime × squarefree (Estermann analogue) and prime × (x² + y²) (Hooley–Linnik analogue)

Written 2026-11-23. Scripts and output: `compute/estermann/`.
Labels: **proved** / **sketched** / **heuristic** / **computed** / **[UNVERIFIED]**; [READ] = read in the source this session.

Notation (as in `00-setup.md` and `EOS/EOS/Buchstab.lean`). m ≥ 2, G = (Z/mZ)^×, φ = φ(m),
P = {p ≤ m prime, p ∤ m} (`primesP m`), a a unit, n_p = the residue of a·p̄ in [1, m),
A_a = {n_p : p ∈ P} (`Aset m a`). p ↦ n_p is injective, so |A_a| = |P|; every n ∈ A_a is coprime to m.
σ = Σ_{q prime} q^{−2} = 0.45225… . Elementary bound used in proofs: σ ≤ 1/4 + 1/9 + Σ_{n≥5} 1/(n(n−1)) = 11/18.
(CH) denotes the Chebyshev bound |P| ≥ m/(2 log m) for m ≥ m_c (from π(m) ≥ 0.9m/log m and ω(m) ≤ log₂ m).

---

## 0. Summary

| # | Statement | Input | Status |
|---|---|---|---|
| F0 | every unit a ≡ p·s, p ≤ m prime, s squarefree, s < m·(27m/\|P\| + 6) ≤ 56 m log m | nothing (CH only for the last form) | **proved**, elementary |
| F1 | every unit a ≡ p·s, p ≤ m prime, s ≤ m squarefree, for m ≥ m₀ | `TypeISmall` (Type I for A_a at moduli q² ≤ 625 log² m; Fouvry–Shparlinski) | **proved** from the named input |
| F1′ | same, and s has all prime factors ≥ m^η (so ω(s) < 1/η) | existing `TypeISifted` (GapH4.lean) | **proved** from the named input |
| F1″ | #{p ∈ P : n_p squarefree} = (1 + o(1))·\|P\|·Π_{q∤m}(1 − q^{−2}) uniformly in a | `TypeISmall` | **proved** from the named input |
| G | GRH alone (`GRHSmoothBound`, or any bound on \|S(χ)\|) does **not** give F1 by a Parseval/size argument: deficit ≥ √(\|B\|/\|P\|) ≍ √(log m) for every admissible choice of weights | — | **proved** as a statement about the method (§1.4) |
| — | Novelty of F1 | — | **Not new**: Yau, arXiv:1907.06016, Thm 3.1 [READ] (§1.6). F0 is a trivial remark; I did not find it stated. |
| H1 | m odd: `TypeIHalf` (Type I for A_a in classes mod 4d, **all** d < √m, total error ≤ \|P\|/log m) ⇒ every unit a ≡ p·n, p ≤ m prime, n < m, n = x² + y² | `TypeIHalf` (a hypothesis, not a theorem) | **proved** reduction (§2.2) |
| H2 | the same from level m^{1/2−ε} (or √m/log^B) only | needs a bound for the window sum W(a); Hooley's treatment does not transfer for free | **not proved**; obstruction identified (§2.3) |
| H3 | known level 1/16: n = (x² + y²)·c, c a product of an even number ≤ 16 of primes ≡ 3 (4), each ≥ m^{1/17} | IN-T1 in classes mod 4d + half-dimensional sieve | **sketched** (§2.4) |
| H4 | all but O(m^{1−δ}) units a are p·(x² + y²), p, n ≤ m, unconditionally | Burgess | **sketched** (§2.4) |

**Answer to the question "does the constant density of squarefrees remove the Parseval wall?"** No. The L² bound for
the pair (P, Q), Q = squarefree units ≤ m, is √(|P||Q|) against a main term |P||Q|/φ; the deficit is
φ/√(|P||Q|) ≍ √(log m). The wall is governed by the *product* of the densities, and it only disappears when
|P||Q| > φ², which is the pigeonhole range. What the constant density does buy: (a) the wall can be passed with Type I
data at moduli ≤ (log m)^2 only, which is known unconditionally; (b) if s is allowed to run to m·C log m the
problem is trivial (F0).

---

## 1. Task 1: prime × squarefree

### 1.1 Theorem F0 (elementary; proved)

**Theorem F0.** Let m ≥ 2 with P ≠ ∅, and let K be an integer with K > 27m/|P| and 6 | K. Then for every unit a there are
p ∈ P and a squarefree s with 1 ≤ s < Km and p·s ≡ a (mod m). In particular (CH) every unit is p·s with
p ≤ m, s ≤ 56 m log m, for m ≥ m_c.

*Proof.* Consider the pairs (p, j), p ∈ P, 0 ≤ j < K, and s(p, j) = n_p + jm ∈ [1, Km). The map (p, j) ↦ s is injective
(s mod m determines n_p, hence p) and p·s ≡ a. Call (p, j) *bad* if q² | s(p, j) for some prime q. Then q ∤ m, because
(n_p, m) = 1. Put z = K/6.
- *q ≤ z.* For fixed p and q ∤ m, the j with q² | n_p + jm form one residue class mod q², so there are ≤ K/q² + 1 of
  them in [0, K). Summing over primes q ≤ z and over p: at most |P|(σK + z) ≤ |P|(11K/18 + K/6) = (7/9)K|P| bad pairs.
- *q > z.* By injectivity the number of such bad pairs is ≤ #{s < Km : d² | s for some d > z} ≤ Σ_{d ≥ z+1} Km/d² ≤ Km/z = 6m.
So the number of good pairs is ≥ (2/9)K|P| − 6m > 0. ∎

Remarks. (i) Using π(z) ≤ 2z/log z instead of z gives s ≤ C m log m/log log m (**sketched**). (ii) No analytic input.
(iii) Lean statement, hypothesis-free:

```lean
theorem estermann_long (m : ℕ) (hm : 2 ≤ m) (K : ℕ) (hK6 : 6 ∣ K)
    (hK : 27 * (m : ℝ) < K * #(primesP m)) (a : ZMod m) (ha : IsUnit a) :
    ∃ p s : ℕ, p.Prime ∧ p ≤ m ∧ Squarefree s ∧ s < K * m ∧ ((p * s : ℕ) : ZMod m) = a
```

### 1.2 The named input `TypeISmall` and Theorem F1 (proved from it)

**IN-T1s (`TypeISmall`; quoted).** For every ε > 0 and A > 0 there is m₀(ε, A) such that for all m ≥ m₀, all units a
and all 1 ≤ d ≤ (log m)^A with (d, m) = 1:

 |#{n ∈ A_a : d | n} − |P|/d| ≤ ε·|P|/d.

Source: it is the special case d ≤ (log m)^A of IN-T1 in `E-buchstab-H4.md` §2
(|#{n ∈ A_a : d | n} − |P|/d| ≤ m^{15/16+ε}, Shparlinski arXiv:1705.06087 Lemma 5.4 and §7, resting on
Fouvry–Shparlinski, Acta Arith. 150 (2011), Thm 3.1). Indeed m^{15/16+ε′} ≤ ε|P|/(log m)^A for large m.
The same statement is Yau's Lemma 4.3 [READ] (Erdős–Turán plus Fouvry–Shparlinski Thms 3.1, 3.2, eq. (3.13)).

```lean
/-- Type I for `A_a` at moduli `d ≤ (log m)^A`, uniformly in `a`. Fouvry–Shparlinski, Acta Arith. 150 (2011),
Thm 3.1; interval form: Shparlinski arXiv:1705.06087 Lemma 5.4, Yau arXiv:1907.06016 Lemma 4.3. -/
def TypeISmall : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ A : ℝ, 0 < A → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ a : ZMod m, IsUnit a →
    ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ (Real.log m) ^ A → d.Coprime m →
      |(#{n ∈ Aset m a | d ∣ n} : ℝ) - #(primesP m) / d| ≤ ε * #(primesP m) / d
```

**Theorem F1.** Assume `TypeISmall` (used only with ε = 1/2, A = 3, d = q², q prime) and (CH). Then there is m₀ such
that for all m ≥ m₀ and every unit a there are a prime p ≤ m and a squarefree s < m with p·s ≡ a (mod m). More precisely

 #{p ∈ P : n_p squarefree} ≥ |P|/12 − m/⌊25 log m⌋ ≥ |P|/300.

*Proof.* Let Z = 25 log m; for large m, q ≤ Z implies q² ≤ (log m)³. If n ∈ A_a is not squarefree, then q² | n for a prime
q ∤ m. By the input, for q ≤ Z: #{n ∈ A_a : q² | n} ≤ (3/2)|P|/q²; the sum over q is ≤ (3/2)σ|P| ≤ (11/12)|P|.
For q > Z use A_a ⊂ [1, m): #{n < m : d² | n for some d > Z} ≤ Σ_{d ≥ ⌊Z⌋+1} m/d² ≤ m/⌊Z⌋. So
#{n ∈ A_a squarefree} ≥ |P|/12 − m/⌊Z⌋. By (CH), m/⌊Z⌋ ≤ 2|P| log m/(25 log m − 1) ≤ 0.0801|P| once log m ≥ 10, and
1/12 − 0.0801 > 1/300. Take s = n_p. ∎

(For the Lean proof take Z = 50 log m and A = 3: then the tail is ≤ 0.041|P| and the margin is comfortable. With the true
value σ = 0.4523 one can take ε up to 1.2: only an *upper* bound #{n ∈ A_a : q² | n} ≤ 2.2|P|/q² for q ≤ C log m is needed.)

```lean
theorem estermann_of_typeISmall (hT : TypeISmall) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ a : ZMod m, IsUnit a →
      ∃ p s : ℕ, p.Prime ∧ p ≤ m ∧ Squarefree s ∧ s ≤ m ∧ ((p * s : ℕ) : ZMod m) = a
```

**Theorem F1″ (asymptotic; proved from `TypeISmall`).** For every δ > 0 and m ≥ m₀(δ), every unit a:
|#{p ∈ P : n_p squarefree} − c_m|P|| ≤ δ|P|, c_m = Π_{q ∤ m}(1 − q^{−2}) ∈ [6/π², 1).
*Proof.* μ²(n) = Σ_{d²|n} μ(d). Split at D = (log m)^{3/2}. For d ≤ D, (d, m) = 1, the input with A = 3 gives
#{n ∈ A_a : d² | n} = (1 + θ_dε)|P|/d². For d > D the trivial bound gives a total ≤ m/⌊D⌋ = o(|P|). The d with
(d, m) > 1 contribute 0. So the count is |P|Σ_{d ≤ D, (d,m)=1} μ(d)/d² + O(ε|P|π²/6) + O(m/D), and the completed sum is c_m + O(1/D). ∎

### 1.3 Theorem F1′: from the existing `TypeISifted` (proved from it)

**Theorem F1′.** Assume `TypeISifted` (GapH4.lean; used with ε = 1/4) and (CH). Fix η ∈ (0, min(η₁, 1)]. For m ≥ m₀(η)
and every unit a there are a prime p ≤ m and a squarefree s < m, all of whose prime factors are ≥ m^η, with p·s ≡ a.

*Proof.* Let y = m^η. `TypeISifted` gives S(A_a, y) ≥ ρ((1 − η/4)Φ_m(m, y) − π(m)/4).
- Φ_m(m, y) ≥ #{p ∈ P : p ≥ y} ≥ |P| − y (`PhiCop` counts every prime ≥ y coprime to m).
- π(m) ≤ |P| + ω(m) ≤ |P| + log₂ m.
So S(A_a, y) ≥ ρ(|P|/2 − y − log₂ m) ≥ ρ|P|/4 ≥ |P|²/(4m) once |P| ≥ 4(m^η + log₂ m) (uses η < 1 and (CH); for η = 1 shrink η).
An n < m counted by S(A_a, y) (n = 1 or P⁻(n) ≥ y) that is not squarefree has q² | n with q ≥ y; there are at most
Σ_{d ≥ ⌈y⌉} m/d² ≤ m/(⌈y⌉ − 1) ≤ 2m^{1−η} such n < m (y ≥ 2). By (CH), |P|²/(4m) ≥ m/(16 log² m) > 2m^{1−η} for large m. ∎

This is the cheapest Lean target at s ≤ m: no new hypothesis, and `GapH4.lean` already has `rho`, `PhiCop`, `siftedR`,
`mem_Aset`, `rho_ge`. It is a weak form of Shparlinski 2013 (prime × P_ℓ). The conclusion "ω(s) < 1/η" is free.

```lean
theorem estermann_of_typeISifted (hT : TypeISifted) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ a : ZMod m, IsUnit a →
      ∃ p s : ℕ, p.Prime ∧ p ≤ m ∧ Squarefree s ∧ s ≤ m ∧ ((p * s : ℕ) : ZMod m) = a
```

Both F1 and F1′ need a Chebyshev lower bound |P| ≥ c·m/log m (F1′ needs only |P| ≥ m^{1−η/3}). If Mathlib's cache has
no such bound, state it as a hypothesis `ChebyshevLower : ∃ c > 0, ∀ m ≥ 2, c·m/log m ≤ π(m)` (Chebyshev 1852;
Mathlib has Bertrand's postulate machinery but I did not check for a ready lemma) **[UNVERIFIED that Mathlib has it]**.

### 1.4 Does GRH alone suffice? No, not by any size argument (proved as a statement about the method)

Let Q = squarefree units in [1, m), B = non-squarefree units in [1, m), S(χ) = Σ_{p∈P} χ(p), Q(χ) = Σ_{s∈Q} χ(s).
N^♯(a) = #{(p, s) ∈ P × Q : ps ≡ a} = |P||Q|/φ + (1/φ)Σ_{χ≠χ₀} χ̄(a)S(χ)Q(χ).

1. **L² × L² (Parseval).** (1/φ)Σ_{χ≠χ₀}|S||Q| ≤ √(|P|(1−ρ)·|Q||B|/φ). Main term |P||Q|/φ. Ratio
   error/main = √((1−ρ)|B|φ/(|P||Q|)) ≍ √(log m) whenever |B| ≍ φ (e.g. m prime: |B|/φ → 1 − 6/π²). **Fails by √(log m).**
2. **No choice of weights helps (proved).** Let v ≥ 0 on P and let w be any real weight on G with w ≤ 0 on B
   (every minorant of 1_Q, e.g. Bonferroni or sieve weights). Σ_p v(p)w(a p̄) = w̄Σv + Σ_p v(p)(w − w̄)(a p̄), w̄ = mean of w
   over G. An L² argument needs ‖v‖₂‖w − w̄‖₂ < w̄Σv. But (Σv)² ≤ |P|‖v‖₂² and ‖w − w̄‖₂² ≥ |B|w̄² (on B, w − w̄ ≤ −w̄).
   So the argument needs |B| < |P|. For |B| ≥ |P| it cannot work, whatever GRH says about S(χ).
   (When |B| < |P| the theorem is pigeonhole: this happens for primorial-like m, where |B|/φ ≍ 1/(q₀ log q₀),
   q₀ the least prime not dividing m; **sketched**.)
3. **L^∞(S) × L¹(Q).** GRH: |S(χ)| ≤ C√m log m (χ ≠ χ₀). Error ≤ C√m log m·(1/φ)Σ_χ|Q(χ)|. To win one needs
   (1/φ)Σ_χ|Q(χ)| ≤ c√m/log² m, i.e. the L¹ mean of Q(χ) smaller than its L² mean (√(|Q||B|/φ) ≍ √m) by log² m.
   **Computed** (§3): the ratio L¹/L² is 0.861, 0.864, 0.863 at m = 10007, 100003, 1000003 (needed: ≲ 1/log² m ≈ 0.005–0.01). **Fails by log² m** (computed, not proved).
4. **L^∞(Q) × L¹(S).** Needs sup_{χ≠χ₀}|Q(χ)| ≤ c√(m/log m), which is false in mean square. Under GRH the contour
   bound for Σ_{s≤x} μ²(s)χ(s) (generating function L(s,χ)/L(2s,χ²)) is x^σ(m)^{1/2−σ+ε} = m^{1/2+ε} at x = m for every
   σ ∈ [1/4, 1/2]: no gain (**sketched**).
5. **Structural reason (proved in `lit/04` §2.1).** For d = q², #{n ∈ A_a : d | n} = (1/φ)Σ_χ χ̄(a)χ(d)S(χ)T_{m/d}(χ) with
   Parseval error √(|P|m/d) against the main term |P|/d: useless for every d ≥ 2. Position of a·p̄ in an interval is
   an additive condition on p̄; it is governed by Kloosterman sums over primes, on which GRH for Dirichlet
   L-functions is silent. F1 needs exactly this at d = 4, 9, 25, … ≤ C log² m.

**Verdict.** GRH is neither sufficient (by any known mechanism) nor needed. `GRHSmoothBound` should not be an
hypothesis of the Estermann theorem. Per CLAUDE.md, do not add it as an unused hypothesis.
What cannot be excluded: a non-size use of GRH (heuristic that none exists: the set P* = random subset of a·B^{−1}
of size |P| has S*(χ) ≈ (|P|/|B|)·χ(a)·conj(B̂(χ)) + O(√|P| log), which satisfies the GRH bound iff
sup_χ|Q(χ)| ≪ √m log² m, expected but not known; **heuristic**).

### 1.5 Which input is cleanest: recommendation

1. **Lean target 1 (no hypotheses):** `estermann_long` (F0). Pure finite combinatorics.
2. **Lean target 2:** `estermann_of_typeISifted` (F1′). Reuses the existing named Prop; proof is ~1 page.
3. **Lean target 3 (optional, conceptually minimal input):** `TypeISmall` and `estermann_of_typeISmall` (F1). Needs
   Σ_{q prime} q^{−2} ≤ 11/18, i.e. a finite-sum bound over q ≤ 25 log m.

### 1.6 Literature (novelty status: known)

- **Yau, K. H., "On products of primes and square-free integers in arithmetic progressions", arXiv:1907.06016v2 (2020)** [READ, whole paper].
  Thm 3.1: N^♯_{a,q}(P, S) = π_q(P)s_q(S)/q + O((PS)^{o(1)}S^{1/2}E), with E = P^{31/32}q^{−(1−ε)/2} + P^{5/6}q^{−(3/4−ε)/2} for q ≥ P^{3/4}.
  Condition (3) for positivity: PS^{16} ≫ (PS)^ε q^{16} and P⁴S^{12} ≫ (PS)^ε q^{15}. At P = S = q = m both hold, so
  **F1 and F1″ (with a power saving m^{−1/32+ε}) are Yau's theorem**; also p, s ≤ m^{16/17+ε}. Method identical to §1.2:
  μ² = Σ_{d²|n}μ(d), Erdős–Turán, Fouvry–Shparlinski. (Yau writes the main term with q in place of φ(q); a slip or a
  different normalisation, not checked.) Journal reference not checked **[UNVERIFIED]**.
- Shparlinski, Period. Math. Hungar. 67 (2013): prime × P_ℓ (`lit/01` §4) [SECONDARY]. F1′ is of this type.
- Estermann 1931; Page 1935; Mirsky 1949; Dudek 2017 (additive problem; as cited by Yau) [SECONDARY].
- F0 (s ≤ Cm log m with no input): not found in a search of the above; it is a remark, not a result.
- The observation of §1.4 item 2 (no L² argument unless |B| < |P|): [OWN].

---

## 2. Task 2: prime × sum of two squares

χ = χ₄ (the character mod 4), r(n) = Σ_{d|n} χ(d) ≥ 0, r₂(n) = 4r(n) (Jacobi). n ≥ 1 is a sum of two squares iff r(n) > 0.
κ_m = Π_{q | m}(1 − χ(q)/q) ≥ φ(m)/m. Throughout §2.1–2.3, **m is odd** (see Remark 2.2(c) for even m).

### 2.1 The hypothesis

For odd d with (d, m) = 1 put N_d(a) = #{n ∈ A_a : n ≡ 1 (mod 4), d | n, n > d²}. This is the number of n ∈ A_a in one
residue class mod 4d inside the interval (d², m). The expected value is |P|·(m − d²)/(4dm).

**`TypeIHalf` (hypothesis; not known).** There is m₀ such that for every odd m ≥ m₀ and every unit a:

 Σ_{d < √m, (d, 2m) = 1} |N_d(a) − |P|(m − d²)/(4dm)| ≤ |P|/log m.

```lean
def TypeIHalf : Prop :=
  ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → Odd m → ∀ a : ZMod m, IsUnit a →
    ∑ d ∈ (Finset.range m).filter (fun d => d * d < m ∧ d.Coprime (2 * m)),
      |(#{n ∈ Aset m a | n % 4 = 1 ∧ d ∣ n ∧ d * d < n} : ℝ)
        - #(primesP m) * ((m : ℝ) - d ^ 2) / (4 * d * m)| ≤ #(primesP m) / Real.log m
```

Comments on the hypothesis.
- It is a Type I statement only (one divisibility condition on n; no bilinear structure), uniform in a, with level
  **exactly** √m and a saving of one log in total. It is strictly of the kind "level of distribution 1/2 for A_a,
  endpoint included". The form `TypeILevel θ` with D = m^{1/2−ε} is *not* enough for the proof below; see §2.3.
- What is known: the same sum restricted to d ≤ m^{1/16−ε} is ≤ m^{1−ε} (IN-T1; the class-mod-4d-in-an-interval version
  follows from the same Kloosterman sums over primes with a phase, as in Shparlinski's Lemma 5.4; **sketched**, not re-read).
- *Heuristic.* In the random model N_d has fluctuation √(|P|/(4d)), so the sum is ≍ √|P|·m^{1/4} = |P|·m^{−1/4+o(1)}.
- *Computed* (§3): the left side is 0.034–0.041·|P| at m = 1000003 (1/log m = 0.072), 0.049–0.071·|P| at m = 100003
  (0.087), 0.062–0.101·|P| at m = 10007 (0.109), for a ∈ {1, 2, −1, 12345}; about 0.75 of the random-model size.
  So the hypothesis as stated (constant 1) is consistent with the data, with little room at m = 10⁴.
  Any right side δ|P| with δ < (π/16)·φ(m)/m would do in Theorem H1.
- In terms of exponential sums: it asks for square-root cancellation on average over h ≤ m^{1/2+o(1)} in
  Σ_{p ≤ m} e_m(h·b·p̄). The smooth analogue (p replaced by all integers x ≤ m/e) is the modular hyperbola in a box of
  volume m^{3/2}/e, which is the Weil barrier. So `TypeIHalf` sits exactly at the Kloosterman barrier, not inside it.

### 2.2 Theorem H1 (proved reduction)

**Theorem H1.** Assume `TypeIHalf`. Then there is m₁ such that for every odd m ≥ m₁ and every unit a there are a prime
p ≤ m and x, y ≥ 0 with n = x² + y² < m and p·n ≡ a (mod m). More precisely, with
R(a) = Σ_{n ∈ A_a, n ≡ 1 (4)} r(n):

 |R(a) − (π/8)κ_m|P|| ≤ 2|P|/log m + 3τ(m)|P|/√m + √m.

*Proof.*
1. *Divisor switching.* Let n ≡ 1 (mod 4). For d | n, χ(d)χ(n/d) = χ(n) = 1 and both are ±1, so χ(n/d) = χ(d). Pairing
   d with n/d: r(n) = 2Σ_{d | n, d² < n} χ(d) + [n = k²]χ(k). (This is the whole of "divisor switching" here: the large
   divisors are replaced by the small ones, and no modulus above √n ever appears.)
2. *Opening.* R(a) = 2Σ_{d < √m, d odd} χ(d)N_d(a) + E, |E| ≤ #{k : k² < m} ≤ √m. If (d, m) > 1 then N_d = 0 because
   elements of A_a are coprime to m.
3. *Hypothesis.* N_d = |P|(m − d²)/(4dm) + θ_d with Σ|θ_d| ≤ |P|/log m. Hence
   R(a) = (|P|/2)(Σ₁ − Σ₂) + 2θ + E, |θ| ≤ |P|/log m, Σ₁ = Σ_{d<√m, (d,m)=1} χ(d)/d, Σ₂ = m^{−1}Σ_{d<√m, (d,m)=1} χ(d)d.
4. *Main term.* By Möbius, Σ_{d<y, (d,m)=1} χ(d)f(d) = Σ_{e | m} μ(e)χ(e)Σ_{d′ < y/e} χ(d′)f(ed′).
   - f = 1/d: Σ_{d′<Y} χ(d′)/d′ = π/4 + ϑ/Y for Y ≥ 1 (alternating series with decreasing terms, |ϑ| ≤ 1), and the sum is
     empty for Y ≤ 1, where |π/4| ≤ 1. Since Σ_{e|m} μ(e)χ(e)/e = κ_m:
     |Σ₁ − (π/4)κ_m| ≤ Σ_{e|m, e<√m} (1/e)(e/√m) + Σ_{e | m, e ≥ √m} 1/e ≤ τ(m)/√m.
   - f = d/m: |Σ_{d′<Y} χ(d′)d′| ≤ Y (Abel; partial sums of χ are 0 or 1), so |Σ₂| ≤ m^{−1}Σ_{e|m, e<√m} e·(√m/e) ≤ τ(m)/√m.
5. So |R(a) − (π/8)κ_m|P|| ≤ (3/2)τ(m)|P|/√m + 2|P|/log m + √m. Since κ_m ≥ φ(m)/m ≫ 1/log log m and τ(m) = m^{o(1)},
   R(a) > 0 for m ≥ m₁. Then some n ∈ A_a has r(n) > 0; n = n_p < m, and p·n ≡ a. ∎

```lean
theorem sumTwoSq_of_typeIHalf (hT : TypeIHalf) :
    ∃ m₁ : ℕ, ∀ m ≥ m₁, Odd m → ∀ a : ZMod m, IsUnit a →
      ∃ p x y : ℕ, p.Prime ∧ p ≤ m ∧ x ^ 2 + y ^ 2 ≤ m ∧ ((p * (x ^ 2 + y ^ 2) : ℕ) : ZMod m) = a
```

Inputs for the formalization, all classical and hypothesis-free:
(J) r(n) > 0 ⇒ n is a sum of two squares (needs r = 1 ∗ χ₄ multiplicative, r(q^k) = 0 for q ≡ 3 (4), k odd, and Mathlib's
`Nat.eq_sq_add_sq_iff`; the full Jacobi formula is not needed);
(L) |Σ_{d<Y} χ₄(d)/d − π/4| ≤ 1/Y (Leibniz series; Mathlib has `Real.tendsto_sum_pi_div_four`);
(φ) φ(m)/m ≥ c/log log m, or simply replace the right side of `TypeIHalf` by φ(m)|P|/(8m) and drop this input;
(τ) τ(m)/√m → 0 (e.g. τ(m) ≤ 2·m^{1/3} for large m; elementary). A cleaner first Lean target: **prime m**
 (τ = 2, κ_m = 1 − χ(m)/m ≥ 1 − 1/m), where the theorem already has its full content and inputs (φ), (τ) disappear.

**Remarks 2.2.**
(a) *Computed* (§3): R(a)/((π/8)|P|) ∈ [0.977, 1.010] at m = 1000003, [0.979, 1.046] at m = 100003 for the four a tested;
 and by FFT over all a, #{p : n_p = x² + y²}/expected ∈ [0.970, 1.030] at m = 1000003, [0.925, 1.072] at 100003,
 [0.846, 1.169] at 10007. The statement "every a is p·(x² + y²)" holds for all a at these three prime moduli.
(b) The theorem counts with weight r. The number of n ∈ A_a that are sums of two squares should be
 ≍ |P|/√(log m) (Landau), which the weighted count does not give; it gives ≥ R(a)/max r ≥ |P|m^{−o(1)}.
(c) *Even m* (**sketched**). If 2 ‖ m, elements of A_a are odd and the proof is unchanged with the same hypothesis.
 If 4 | m, n mod 4 is determined by p mod 4, so one must restrict to p ≡ a (mod 4) and the hypothesis is Type I for
 that half of P; the main term doubles per element and halves in the number of elements.
(d) *Variant with n ≤ X < m* (**proved**, same proof): if the hypothesis holds with (d², m) replaced by (d², X), d < √X,
 expected value |P|(X − d²)/(4dm) and right side |P|X/(m log m), then n < X. In the random model this is consistent
 down to X = (log m)^{C}. It is past the Weil barrier, so it is not a weaker hypothesis in any useful sense.
(e) *Variant n ≤ m(log m)^C*: no gain. For n = n_p + jm, j < K, the moduli run to √(Km) > √m and for d > K the count
 #{(p, j) : d | n_p + jm} still depends on n_p mod d. Unlike F0, r is not handled by a union bound.

### 2.3 Why level m^{1/2−ε} (or √m/log^B) alone is not shown to suffice; the window

Let D < √m and split r(n) = 2Σ_{d|n, d ≤ D, d² < n} χ(d) + 2Δ_D(n) + [n = □](±1), Δ_D(n) = Σ_{d | n, D < d < √n} χ(d).
With W(a) = Σ_{n ∈ A_a, n ≡ 1 (4)} Δ_D(n):

**Proposition H2 (proved, trivial).** If the sum in `TypeIHalf` restricted to d ≤ D is ≤ δ|P|, and |W(a)| ≤ w|P|, then
R(a) ≥ ((π/8)κ_m − 2δ − 2w − o(1))|P|. (The main term changes by O(|P|τ(m)/D).)

So the reduction from level D needs **|W(a)| ≤ w|P| with w < (π/16)κ_m**. What is known about W:

1. *In Hooley's additive problem* (n = N − p) the window is √N/log^B < d < √N·log^B and is treated by
   Cauchy–Schwarz, an upper-bound sieve (Brun–Titchmarsh for p ≡ N (mod d), d ≈ √N, which is **free** there), and the
   scarcity of integers with a divisor in a short window. [RECALLED; Hooley's paper was not retrievable, as in `lit/04` §8. **[UNVERIFIED]**]
2. *Here the free input is missing* (**proved** as a statement about the available tools). The analogue of
   Brun–Titchmarsh is #{p ∈ P : d | n_p} ≪ |P|/d for d ≈ √m. Sieving the integers k ≤ m by e | k requires
   #{(k′, l) : k′ ≤ m/e, l ≤ m/d, e·k′·d·l ≡ a (mod m)}, a modular hyperbola in a box of volume m²/(ed). Weil gives an
   asymptotic only for volume > m^{3/2+ε}, i.e. ed < m^{1/2−ε}. For d = √m/log^B this allows e ≤ log^{B−3} only, and the
   sieve bound is |P|/d·(log m/log log m): a loss of a log, where Hooley can afford none. For d ≤ m^{1/2−ε} it gives
   #{p : d | n_p} ≤ C_ε|P|/d, which is fine, but then the window (m^{1/2−ε}, √m) has logarithmic length ε log m.
3. *The long window is not sparse in L².* For integers, (1/m)Σ_{n≤m} Δ_D(n)² ≍ ε log m for D = m^{1/2−ε} (the diagonal
   d₁ = d₂ gives Σ_{D<d<√m} 1/d), and the proportion of n with a divisor in the window is ≍ ε^{δ}(log 1/ε)^{−3/2},
   δ = 0.086 (Ford) [RECALLED]. Cauchy–Schwarz gives √(ε^{1+δ} log m), useless. A bound for the **first** moment
   Σ|Δ_D(n)| is needed.
4. *Computed* (§3): mean of |Δ_D(n)| over n ≡ 1 (4), D = m^{1/2−ε}:

   | ε | m = 10007 | 100003 | 1000003 |
   |---|---|---|---|
   | 0.2 | 0.361 | 0.419 | 0.457 |
   | 0.1 | 0.185 | 0.228 | 0.261 |
   | 0.05 | 0.068 | 0.101 | 0.126 |
   | 0.02 | 0.012 | 0.021 | 0.030 |

   over all integers; over A_a (a = 1, 2, −1, 12345) the values agree within 3% at m = 1000003. The threshold for
   Proposition H2 is mean|Δ| < π/4 = 0.785 (per n ≡ 1 (4)). The means **increase slowly with m** at fixed ε; whether
   they stay bounded (and → 0 with ε) is not settled by this data. **Heuristic:** yes, because a typical integer
   with a divisor in the window has O(1) of them.
5. So the honest formulation of the "Hooley–Linnik reduction" from level m^{1/2−ε} is:

   **Conditional statement (sketched).** Type I for A_a at level m^{1/2−ε} (asymptotic, in classes mod 4d and intervals)
   **plus** the first-moment window bound Σ_{n ∈ A_a, n≡1(4)} |Δ_{m^{1/2−ε}}(n)| ≤ (π/16 − η)κ_m|P| imply the conclusion of H1.
   The window bound is an upper-bound statement, so it would follow from a Nair–Tenenbaum/Shiu-type inequality for
   A_a restricted to integers with a divisor in the window; that inequality needs upper-bound Type I information for
   A_a at moduli up to √m, i.e. again endpoint information. I could not derive it from level m^{1/2−ε}. **Open.**

**Verdict on Task 2.** The reduction is *proved* from `TypeIHalf` (endpoint level 1/2, saving one log, classes mod 4d
with the cut n > d²). It is *not* proved from level m^{1/2−ε}; the gap is the window sum W(a), and the tool that
closes it in the additive problem (Brun–Titchmarsh at modulus √N) is itself at the Weil barrier here.
`lit/04` §2.1 and §7 item 1 ("θ = 1/2 − ε plus the sparse-window lemma ⇒ every a is p·(x² + y²)") should be read with
this correction: the window lemma is not a lemma about integers alone.

### 2.4 What the known level 1/16 gives

1. **H3 (sketched).** Sift A_a ∩ {n ≡ 1 (4)} by the primes q ≡ 3 (mod 4), q < z. This is a sieve of dimension 1/2, whose
   lower-bound function is positive for s = log D/log z > β = 1 (Iwaniec, "The half dimensional sieve", Acta Arith. 29
   (1976) [RECALLED, **UNVERIFIED** details]). With D = m^{1/16−ε} (IN-T1 in classes mod 4d, m odd) and z = m^{1/16−2ε}:
   #{n ∈ A_a : n ≡ 1 (4), no prime factor q ≡ 3 (4) below z} ≫ |P|/√(log m) > 0. Such n < m has at most 16 prime
   factors ≡ 3 (4) (z^{17} > m), and an even number of them because n ≡ 1 (4). Hence:
   **every unit a (m odd, large) is p·n with p ≤ m prime, n < m, n = (x² + y²)·q₁⋯q_{2j}, 0 ≤ j ≤ 8, q_i ≡ 3 (4) primes ≥ m^{1/17}.**
   With a level θ > 1/4 the same argument gives j ≤ 1: n = x² + y² or n = q₁q₂(x² + y²). Level 1/2 − ε does not
   remove the case j = 1 by the sieve alone (that is the parity-type obstruction of this route; removing it is what
   the weighted count of §2.2 does).
2. **F1′** (proved from `TypeISifted`): n squarefree with fewer than 1/η prime factors. No information on their classes mod 4.
3. **H4: almost all a, unconditionally (sketched).** R′(a) = Σ_{n ∈ A_a} r(n) = (1/φ)Σ_χ χ̄(a)S(χ)V(χ), V(χ) = Σ_{n<m} r(n)χ(n).
   Parseval on S: Σ_a |R′(a) − main|² = (1/φ)Σ_{χ≠χ₀}|S(χ)|²|V(χ)|² ≤ |P|·sup_{χ≠χ₀}|V(χ)|². V(χ) is a divisor sum for the
   pair (χ, χχ₄); by the hyperbola method it is a combination of character sums of length ≥ √m to moduli m and 4m, and
   Burgess (r = 2, 3, any modulus) gives V(χ) ≪ m^{1−δ}. So #{a : R′(a) = 0} ≪ m^{2−2δ}/(κ_m²|P|) ≪ m^{1−2δ+o(1)}.
   No Type I input is used; the level 1/16 is irrelevant here. The same argument gives the squarefree case for almost
   all a, which is weaker than F1.
4. Nothing at level 1/16 gives n = x² + y² for **every** a: the weighted count needs the divisors up to √n.

---

## 3. Numerics (`compute/estermann/`)

- `estermann_check.py m…` → `out_estermann_check.txt`. Prime m = 10007, 100003, 1000003; all units a by FFT on G.
  - Squarefree: min_a Nsf(a)/expected = 0.915, 0.962, 0.987; max = 1.086, 1.038, 1.014; std/expected ≈ 0.47·√|P|/expected
    (square-root fluctuations). F1 holds for every a at these m.
  - Type I at d = 4, 9, 25, 49: #{n ∈ A_a : d | n}/(|P|/d) ∈ [0.972, 1.026], [0.952, 1.047], [0.916, 1.079], [0.886, 1.125] at m = 1000003, over all a.
    The bound needed in F1 is ≤ 1.5 (or 2.2 with the true σ).
  - Individual moduli up to m^{0.6}: rms deviation of #{d | n} over a is 0.97–0.98·√(|P|/d); max over a is 5–6 times that.
  - Two squares: min_a/expected = 0.846, 0.925, 0.970.
  - Q(χ): L¹/L² = 0.861, 0.864, 0.863; sup|Q(χ)|/√m = 2.08, 2.55, 2.77; sup|S(χ)|/√m = 0.78, 0.84, 0.81.
    Parseval deficit φ/√(|P||Q|) = 3.66, 4.14, 4.58 (√(log m) = 3.03, 3.39, 3.72).
- `typeI_half_check.py m [a…]` → `out_typeI_half_check.txt`. The `TypeIHalf` sum, R(a), and the window means of §2.3.
- Not computed: composite and even m; F0's optimal K.

## 4. Not checked / caveats

- Fouvry–Shparlinski Thm 3.1 itself was not read; IN-T1 is as in `E-buchstab-H4.md` (Shparlinski's Lemma 5.4 read there). Yau's paper was read in full this session.
- The class-mod-4d-in-an-interval form of IN-T1 used in §2.4 item 1 is the standard extension; not re-derived line by line.
- Iwaniec's half-dimensional sieve (β = 1) and Ford's exponent: recalled.
- Hooley's treatment of the critical window: recalled, not read. §2.3 item 2 does not depend on it.
- Whether Mathlib has a Chebyshev lower bound for π(x) in the pinned revision: not checked. Lean was not run.
- MathSciNet not available; novelty search = the repo's `lit/01` plus Yau's reference list.
