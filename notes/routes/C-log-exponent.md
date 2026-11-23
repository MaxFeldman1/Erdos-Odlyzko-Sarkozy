# Route C: the strongest rigorous GRH theorem toward EOS, and the log exponent

Written 2026-11-22. Hypothesis throughout: GRH for Dirichlet L-functions (including RH for ζ).
One result (Theorem B) also uses an unconditional upper-bound sieve theorem; this is flagged where used.
Nothing else is assumed.

**Status tags.** *proved* = complete argument written here, relying only on cited textbook facts.
*sketched* = argument believed complete but some step only indicated. *heuristic* = not a proof.
[RECALLED] = a citation whose theorem number or exact wording I did not re-read this session.

---

## 0. Summary

Notation: φ = φ(m), L = log m, G = (Z/mZ)^*. "Represented with p ≤ Y₁, q ≤ Y₂" means a ≡ pq (mod m) with p, q prime.

| # | Statement (GRH; all large m; every a coprime to m unless said otherwise) | Status |
|---|---|---|
| Thm 1 | Smoothed bound H: \|ψ̃(x,χ) − [χ=χ0] x/2\| ≤ C √x log(2q), all q ≥ 1, all χ mod q, all x ≥ 1 | proved |
| Thm A | If K L ≤ X₂ ≤ m, X₁ ≤ m³ and X₁X₂ ≥ K φ² L² log X₂, then a is represented with p ≤ X₂, q ≤ X₁ | proved from H |
| Cor A1 | p ≤ m, q ≤ K (φ²/m) L³ ≤ K m L³ | proved from H |
| Cor A2 | p ≤ m^θ, q ≤ K θ φ² L³ / m^θ (0 < θ ≤ 1) | proved from H |
| Thm S | p, q ≤ K φ L² | proved from H |
| Thm B | p ≤ φ L, q ≤ K φ L² (so pq ≤ K φ² L³) | proved from H + twin-prime upper-bound sieve (unconditional, cited) |
| Thm E | For X₂ ≤ m: #{a not represented with p ≤ X₂, q ≤ X₁} ≤ K φ² L² log X₂ /(X₁X₂). At X₁ = X₂ = m this is K (φ/m)² L³ | proved from H |
| Prop L | The inputs {Θ ≥ 0, total mass, sup-bound \|Θ̂(χ)\| ≤ C√X L} cannot give a symmetric range below c φ L² | proved (uses Spencer's theorem) |
| §6 | Saving a log in both variables needs a prime-pair upper bound with constant < 2 (the sieve's parity constant), averaged over the shifts km | reduction proved; "no sieve gives < 2" is heuristic |

**What beats the literature recorded in notes/lit/.**
- Thm S (log⁴ → log²) was already sketched in lit notes 01 §8 and 03 §0.1; here it is proved with all steps.
- Thm A / Cor A1 (p ≤ m exactly, q ≤ K m log³ m) and Thm B (p ≤ φ log m, q ≤ K φ log² m) do not appear in the
  lit notes. They are not comparable with EOS 1987 Cor. 3 in the strict sense for Cor A1 (one factor is at
  the conjectured range, the other is log³ off), and Thm B strictly improves Thm S in one coordinate.
  In product size: pq ≤ K φ² L³, against K² φ² L⁴ from Thm S and C² m² L⁸ from EOS 1987.
  I did not do a fresh literature search; novelty is relative to notes/lit/ only.
- Thm E at X₁ = X₂ = m gives O((φ/m)² log³ m). Banks–Shparlinski Thm 1.4 as transcribed in the lit notes reads
  O((φ/m) log³ m) under GRH; the extra factor φ/m is at most a log log saving and may just be bookkeeping. [UNVERIFIED against their text]
- **No improvement of the exponent 2 for the symmetric all-a statement, and none of the exponent 3 for the exceptional set at range exactly m.**
  §6 explains what blocks each.

---

## 1. The analytic input: explicit formula with Cesàro weight (proved)

### 1.1 Definitions

For a Dirichlet character χ mod q and x ≥ 1,

  ψ̃(x, χ) := Σ_{n ≤ x} Λ(n) χ(n) (1 − n/x).

This is the Fejér/Cesàro weight used by Banks–Shparlinski (their Lemma 2.5). I use it rather than a
C_c^∞ bump because it is concrete (good for Lean), and because under GRH the proof needs no bump function,
no functional equation and no trivial zeros: the contour is moved only to Re s = 1/4.

### 1.2 Facts used (textbook)

Let χ be a **primitive** character mod q ≥ 1 (q = 1 is ζ), κ ∈ {0,1} its parity, ρ = β + iγ its nontrivial zeros.

- **(F1) Mellin kernel.** For y > 0 and c > 0: (1/2πi) ∫_{(c)} y^s ds/(s(s+1)) = (1 − 1/y) if y ≥ 1, and 0 if y ≤ 1.
  (Shift the contour left for y ≥ 1, picking up residues 1 at s = 0 and −1/y at s = −1; right for y ≤ 1. The arcs vanish since the integrand is O(|s|^{-2}).)
- **(F2) Hadamard partial fractions.** Davenport, *Multiplicative Number Theory*, ch. 12, eqs (17)–(18) [RECALLED numbering]: for q > 1,
  L′/L(s,χ) = −½ log(q/π) − ½ (Γ′/Γ)((s+κ)/2) + B(χ) + Σ_ρ (1/(s−ρ) + 1/ρ), with Re B(χ) = −Σ_ρ Re(1/ρ).
  Hence, for every s that is not a zero,

  (1.1) Σ_ρ Re 1/(s−ρ) = Re L′/L(s,χ) + ½ log(q/π) + ½ Re (Γ′/Γ)((s+κ)/2).

  For q = 1 the same holds with the standard modifications (Γ-argument s/2 + 1, log π in place of log(q/π), and an extra term Re 1/(s−1) on the right; Davenport ch. 12 (8)–(11) [RECALLED numbering]). These change only absolute constants below.
- **(F3)** For Re s = σ > 1: |L′/L(s,χ)| ≤ −ζ′/ζ(σ). Numerically −ζ′/ζ(3/2) = 1.5053, −ζ′/ζ(2) = 0.5700 (checked with mpmath).
- **(F4) Digamma.** Re (Γ′/Γ)(z) ≤ log|z| for Re z ≥ 1; and |ψ′(z)| ≤ Σ_{n≥0} |z+n|^{-2} ≤ 64 + π²/6 for Re z ≥ 1/8.
  Values: (Γ′/Γ)(3/4) = −1.0859, (Γ′/Γ)(5/4) = −0.2275.

### 1.3 Zero sums under GRH

**Lemma 1.1 (proved).** Assume GRH. For primitive χ mod q > 1,

  Σ_ρ 1/(1+γ²) ≤ ½ log q + 0.82, and Σ_ρ 1/|ρ(ρ+1)| ≤ (2/3) log q + 1.1.

For q = 1 the same sums are bounded by an absolute constant.

*Proof.* Put s = 3/2 in (1.1). Under GRH, Re 1/(3/2 − ρ) = 1/(1+γ²). By (F3), (F4):
Σ_ρ 1/(1+γ²) ≤ 1.5053 + ½ log q − ½ log π + ½ max((Γ′/Γ)(3/4), (Γ′/Γ)(5/4)) ≤ ½ log q + 0.82.
Next, |ρ(ρ+1)|² = (¼+γ²)(9/4+γ²), and (1+u)²/((¼+u)(9/4+u)) is decreasing in u ≥ 0 with value 16/9 at u = 0,
so 1/|ρ(ρ+1)| ≤ (4/3)/(1+γ²). For q = 1 the extra terms in (1.1) are bounded. ∎

The sums are over zeros with multiplicity. Absolute convergence is part of the statement.

**Lemma 1.2 (proved).** Assume GRH. For primitive χ mod q ≥ 1 and real t,

  (1.2) Σ_ρ 1/(9/4 + (t−γ)²) ≤ (1/3) log q + (1/3) log(|t|+3) + C₀,
  (1.3) |L′/L(¼ + it, χ)| ≤ 3.5 log(q(|t|+3)) + C₀′ (for q = 1 add the bounded term 1/|s−1| ≤ 4/3),

with absolute constants C₀, C₀′. Moreover for each T₀ ≥ 2 there is T ∈ [T₀, T₀+1] with
|L′/L(σ ± iT, χ)| ≤ C₀″ log²(q(T+3)) uniformly for ¼ ≤ σ ≤ 2.

*Proof.* (1.2): put s = 2 + it in (1.1). Under GRH Re 1/(s−ρ) = (3/2)/(9/4+(t−γ)²), the right side is
≤ 0.57 + ½ log q + ½ log|(2+κ+it)/2| ≤ ½ log q + ½ log(|t|+3) + 0.57.

(1.3): subtract (F2) at s = ¼+it and at s₁ = 2+it. The constants B(χ) and log(q/π) cancel:

  L′/L(s) − L′/L(s₁) = −½[(Γ′/Γ)((s+κ)/2) − (Γ′/Γ)((s₁+κ)/2)] + Σ_ρ [1/(s−ρ) − 1/(s₁−ρ)].

The digamma difference is ≤ (7/8)(64 + π²/6) by (F4), since both arguments have real part ≥ 1/8.
Each zero term has modulus (7/4)/(|s−ρ||s₁−ρ|). With u = (t−γ)², |s−ρ|² = 1/16 + u ≥ (1/36)(9/4+u) and |s₁−ρ|² = 9/4+u,
so the term is ≤ 10.5/(9/4+u). Sum with (1.2). Finally |L′/L(s₁)| ≤ 0.57.

Horizontal lines: by (1.2) the number of zeros with |γ − T₀| ≤ 2 is at most N₀ := C log(q(T₀+3)).
Choose T ∈ [T₀, T₀+1] at distance ≥ 1/(2N₀+2) from every γ. Repeat the subtraction with s = σ + iT, ¼ ≤ σ ≤ 2.
Zeros with |γ − T| ≤ 1 contribute ≤ N₀ · 2·(2N₀+2)/(3/2); the others contribute ≤ C/(9/4+(T−γ)²) each. ∎

### 1.4 The smoothed explicit formula

**Proposition 1.3 (proved).** Assume GRH. For primitive χ mod q ≥ 1 and x ≥ 1,

  ψ̃(x,χ) = [q=1]·x/2 − Σ_ρ x^ρ/(ρ(ρ+1)) + R(x,χ), |R(x,χ)| ≤ x^{1/4} (C₁ log q + C₂),

with absolute C₁, C₂, and the sum over ρ converges absolutely.

*Proof.*
1. By (F1) with c = 2 and y = x/n, and absolute convergence (Σ Λ(n) n^{-2} < ∞, ∫_{(2)} |ds|/|s(s+1)| < ∞),
   ψ̃(x,χ) = (1/2πi) ∫_{(2)} (−L′/L(s,χ)) x^s ds/(s(s+1)).
2. Move the contour to Re s = 1/4 through rectangles with horizontal sides at heights ±T_j, T_j → ∞ chosen as in Lemma 1.2.
   On the horizontal sides the integrand is ≤ C log²(qT_j) x² T_j^{-2}, so their contribution tends to 0.
3. Poles of the integrand in ¼ < Re s < 2: under GRH these are the nontrivial zeros (all on Re s = ½; a zero of multiplicity k
   gives residue −k x^ρ/(ρ(ρ+1))), and for q = 1 the pole of ζ at s = 1 with residue x/(1·2) = x/2.
   The poles of 1/(s(s+1)) at 0, −1 and the trivial zeros (at s ≤ 0) are **not** crossed.
4. The remaining integral on Re s = ¼ is ≤ (x^{1/4}/2π) ∫ (3.5 log(q(|t|+3)) + C)/(|¼+it||5/4+it|) dt ≤ x^{1/4}(C₁ log q + C₂) by (1.3).
5. Absolute convergence of Σ_ρ is Lemma 1.1. ∎

**Theorem 1 (H; proved).** Assume GRH. There is an absolute constant C_H such that for every q ≥ 1, every
Dirichlet character χ mod q (primitive or not, principal or not) and every real x ≥ 1,

  |ψ̃(x,χ) − [χ = χ0]·x/2| ≤ C_H √x log(2q).

*Proof.*
- *Primitive, q > 1.* Prop. 1.3 and Lemma 1.1: |ψ̃| ≤ √x((2/3) log q + 1.1) + x^{1/4}(C₁ log q + C₂).
- *q = 1.* Prop. 1.3 and Lemma 1.1 give |ψ̃(x,1) − x/2| ≤ C√x. (Only RH for ζ is used.)
- *Imprimitive χ mod q induced by primitive χ\* mod q\* | q* (this includes χ = χ0, where χ\* is the trivial character mod 1).
  χ(n) = χ\*(n) unless n shares a prime factor with q, so
  |ψ̃(x,χ) − ψ̃(x,χ\*)| ≤ Σ_{p | q} Σ_{k: p^k ≤ x} log p ≤ ω(q) log x ≤ (log q/log 2)·(2/e)√x ≤ 1.1 √x log q.
  Then apply the primitive case to χ\*, using log q\* ≤ log q. ∎

Remarks.
- Dependence on m: the main term of the bound is √x·(2/3) log q\*; the proof gives C_H explicitly in principle. Numerically (§7) the true maximum over χ mod m at x ≈ m is ≈ 0.37 √x log m.
- The bound holds for **all** x ≥ 1, with no restriction relating x and q. This is what makes H easy to state.
- Citable sources for H: Banks–Shparlinski arXiv:2610.19597 Lemma 2.5 (same weight; they derive it from Montgomery–Vaughan (13.28)) [READ in lit note 01, not re-read here];
  Iwaniec–Kowalski Thm 5.11 + Prop. 5.7 for general smooth weights [RECALLED numbering].
- Smooth compactly supported weights w ∈ C_c²((½,1)): the same proof works with x^s/(s(s+1)) replaced by W(s)x^s, W(s) = ∫ w(u)u^{s−1}du,
  using |W(¼+it)|, |W(½+it)| ≤ A_w/(4+t²) (two integrations by parts). One gets
  |Σ Λ(n)χ(n)w(n/x) − [χ=χ0] W(1) x| ≤ C_w √x log(2q). [sketched; identical steps.] I do not use it below.

### 1.5 Lean-ready statement of H

Checked: the two definitions and `CoveredByAsym` typecheck against the project's Mathlib (`lake env lean` on a scratch file; not added to the repo). The `coveredBy_log_sq` statement was checked with `CoveredBy` unfolded by hand, not with the import of `EOS.Statement`.

```lean
/-- Cesàro-smoothed twisted Chebyshev sum `ψ̃(x, χ) = Σ_{n ≤ x} Λ(n) χ(n) (1 - n/x)`. -/
noncomputable def psiCesaro {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Iic ⌊x⌋₊,
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ n * (1 - (n : ℂ) / (x : ℂ))

/-- **Analytic input H (consequence of GRH).** Absolute `C` with
`|ψ̃(x, χ) - [χ = 1] x/2| ≤ C √x log (2q)` for all `q ≥ 1`, all `χ` mod `q`, all `x ≥ 1`.
Proof from GRH: notes/routes/C-log-exponent.md §1. Literature: Banks–Shparlinski,
arXiv:2610.19597, Lemma 2.5; Montgomery–Vaughan, Multiplicative Number Theory I, §13.2. -/
def GRHSmoothBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ), 1 ≤ x →
    ‖psiCesaro χ x - (if χ = 1 then ((x / 2 : ℝ) : ℂ) else 0)‖
      ≤ C * Real.sqrt x * Real.log (2 * q)

/-- Asymmetric covering: every unit mod `m` is `p * q` with primes `p ≤ Y₁`, `q ≤ Y₂`. -/
def CoveredByAsym (m : ℕ) (Y₁ Y₂ : ℝ) : Prop :=
  ∀ a : ZMod m, IsUnit a →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (p : ℝ) ≤ Y₁ ∧ (q : ℝ) ≤ Y₂ ∧ ((p * q : ℕ) : ZMod m) = a

-- Targets (statements typecheck; proofs are §2–§3 below).
theorem coveredBy_log_sq (h : GRHSmoothBound) :            -- Theorem S
    ∃ K : ℝ, 0 < K ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀,
      CoveredBy m (K * (Nat.totient m : ℝ) * (Real.log m) ^ 2) := sorry

theorem coveredByAsym_m_log_cube (h : GRHSmoothBound) :    -- Corollary A1
    ∃ K : ℝ, 0 < K ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀,
      CoveredByAsym m m (K * (Nat.totient m : ℝ) ^ 2 / m * (Real.log m) ^ 3) := sorry
```

Comparison with the existing `GRHBounds`: that one has (log(qx))² and a sharp cutoff. `GRHSmoothBound` is not implied by
`GRHBounds` (partial summation from the sharp bound loses the logs again), so it must be a separate named hypothesis.
`eos_of_grhBounds` remains out of reach; the fallback targets are the two theorems above.

---

## 2. The deduction H ⇒ theorems, as lemmas (proved)

Fix m ≥ 3, φ = φ(m), L = log m, G = (Z/mZ)^*, χ0 the principal character mod m. All sums over p, q are over primes.

**Definitions.** For X ≥ 1, b ∈ G, χ mod m:

  Θ(X; b) := Σ_{p ≤ X, p ≡ b (m)} log p (1 − p/X) ≥ 0,
  ϑ̃(X, χ) := Σ_{p ≤ X} log p χ(p) (1 − p/X) = Σ_{b∈G} Θ(X;b) χ(b),
  T(X) := ϑ̃(X, χ0) = Σ_b Θ(X;b),
  V°(X) := (1/φ) Σ_{χ≠χ0} |ϑ̃(X,χ)|² = Σ_b Θ(X;b)² − T(X)²/φ = Σ_b (Θ(X;b) − T(X)/φ)²,
  M(X) := max_{χ≠χ0} |ϑ̃(X,χ)|,
  R(a) = R(a; X₁, X₂) := Σ_{p ≤ X₁, q ≤ X₂, pq ≡ a (m)} log p log q (1−p/X₁)(1−q/X₂).

R(a) > 0 iff there are primes p < X₁, q < X₂ with pq ≡ a. Everything is prime-supported; H is about Λ, and D0 bridges.

**Lemma D0 (prime powers; proved).** For x ≥ 1 and any χ: |ψ̃(x,χ) − ϑ̃(x,χ)| ≤ Σ_{p^k ≤ x, k ≥ 2} log p
≤ Σ_{k=2}^{⌊log₂ x⌋} θ(x^{1/k}) ≤ (log 4)√x · log₂ x = 2√x log x. (Uses Chebyshev θ(y) ≤ y log 4, which I believe is in Mathlib [UNVERIFIED].)
The crude factor log x is harmless because all ranges are ≤ m³, so log x ≤ 3 log m.

**Lemma D1 (orthogonality; proved).** R(a) = Σ_{b∈G} Θ(X₁;b) Θ(X₂; a b^{-1}) = (1/φ) Σ_χ χ̄(a) ϑ̃(X₁,χ) ϑ̃(X₂,χ).
Parseval: Σ_χ |ϑ̃(X,χ)|² = φ Σ_b Θ(X;b)². So

  R(a) = T(X₁)T(X₂)/φ + E(a), E(a) := (1/φ) Σ_{χ≠χ0} χ̄(a) ϑ̃(X₁,χ) ϑ̃(X₂,χ).

**Lemma D2 (main term; proved from H at q = 1).** There are absolute X₀, such that T(X) ≥ X/8 whenever X ≥ max(X₀, 8L).

*Proof.* T(X) = ϑ̃(X, 1) − Σ_{p | m, p ≤ X} log p (1−p/X) ≥ ϑ̃(X,1) − L, where 1 is the trivial character mod 1.
By H and D0, ϑ̃(X,1) ≥ X/2 − C_H √X log 2 − 2√X log X ≥ X/4 for X ≥ X₀. Then X/4 − L ≥ X/8. ∎
(Only a Chebyshev-type lower bound is needed; H at q = 1 is a convenient way to get it. Also T(X) ≤ X.)

**Lemma D3 (sup bound; proved from H).** For χ ≠ χ0 mod m and 1 ≤ X ≤ m³: |ϑ̃(X,χ)| ≤ C₃ √X L, with C₃ = C_H(1 + log 2) + 6.
So M(X) ≤ C₃ √X L.

*Proof.* H gives |ψ̃(X,χ)| ≤ C_H √X log(2m); D0 adds ≤ 2√X log X ≤ 6√X L. Also log(2m) ≤ (1 + log 2)L since L ≥ 1. ∎

**Lemma D4 (second moment; proved).**
- (a) If X ≤ m: Σ_b Θ(X;b)² = Σ_{p ≤ X, p∤m} log² p (1−p/X)² ≤ (log 4) X log X. Hence V°(X) ≤ (log 4) X log X.
  *Proof.* Distinct primes p ≤ X ≤ m with p ∤ m lie in distinct classes of G, so each Θ(X;b) has at most one term. Then Σ log² p ≤ log X · θ(X). ∎
- (b) Always: V°(X) ≤ M(X)² ≤ C₃² X L² (for X ≤ m³). *Proof.* Average ≤ max. ∎
- (c) [uses the sieve; only needed for Thm B] For m ≤ X ≤ m²: Σ_b Θ(X;b)² ≤ (log 4) X log X + C₄ X²/φ. See §4.

**Lemma D5 (error bound; proved).** |E(a)| ≤ M(X₁) · V°(X₂)^{1/2}.

*Proof.* |E(a)| ≤ (1/φ) Σ_{χ≠χ0} |ϑ̃(X₁,χ)||ϑ̃(X₂,χ)| ≤ M(X₁) (1/φ) Σ_{χ≠χ0} |ϑ̃(X₂,χ)|
≤ M(X₁) (1/φ) (φ−1)^{1/2} (Σ_{χ≠χ0} |ϑ̃(X₂,χ)|²)^{1/2} ≤ M(X₁) V°(X₂)^{1/2}. ∎

**Lemma D6 (second moment of E; proved).** Σ_{a∈G} E(a)² = (1/φ) Σ_{χ≠χ0} |ϑ̃(X₁,χ)|² |ϑ̃(X₂,χ)|² ≤ M(X₁)² V°(X₂).
(Parseval on G applied to a ↦ E(a), whose Fourier coefficients are ϑ̃₁ϑ̃₂ at χ ≠ χ0 and 0 at χ0.)

**Lemma D7 (positivity criterion; trivial).** If M(X₁) V°(X₂)^{1/2} < T(X₁)T(X₂)/φ then R(a) > 0 for every a ∈ G.
In general #{a ∈ G : R(a) = 0} ≤ φ² M(X₁)² V°(X₂) / (T(X₁)T(X₂))².
(If R(a) = 0 then E(a) = −T₁T₂/φ; sum E(a)² over such a and use D6.)

Suggested Lean order: D1 (pure finite Fourier analysis on `DirichletCharacter ℂ m`; Mathlib has character orthogonality
for Dirichlet's theorem), D4(a) (injectivity of p ↦ (p : ZMod m) on primes ≤ m), D5–D7 (Cauchy–Schwarz), then D0, D2, D3 (real-analysis bookkeeping with H).
None of D1, D4(a), D5, D6, D7 uses H.

---

## 3. Theorems (proved from H)

**Theorem A (asymmetric, general).** Assume GRH (only through H). There are absolute K, m₀ such that for all m ≥ m₀, all a ∈ G and all real X₁, X₂ with

  K log m ≤ X₂ ≤ m, X₁ ≤ m³, X₁ X₂ ≥ K φ(m)² (log m)² log X₂,

there are primes p ≤ X₂ and q ≤ X₁ with pq ≡ a (mod m).

*Proof.* X₁ ≥ Kφ²L² log X₂/m ≥ max(X₀, 8L) for large m, and X₂ ≥ K L ≥ max(X₀, 8L). By D2, T₁T₂/φ ≥ X₁X₂/(64φ).
By D3 and D4(a), M(X₁) V°(X₂)^{1/2} ≤ C₃ √X₁ L · (1.39 X₂ log X₂)^{1/2}.
D7 applies as soon as X₁X₂/(64φ) > 1.18 C₃ L √(X₁X₂ log X₂), i.e. X₁X₂ > (76 C₃)² φ² L² log X₂. Take K = (76 C₃)². ∎

**Corollary A1.** For m ≥ m₀ every a ∈ G is pq with **p ≤ m and q ≤ K φ(m)² (log m)³ / m ≤ K m (log m)³**. (X₂ = m.)

**Corollary A2.** For 0 < θ ≤ 1 and m ≥ m₀(θ): p ≤ m^θ and q ≤ K θ φ(m)² (log m)³ / m^θ. (X₂ = m^θ.)
At the other extreme, p ≤ K log m and q ≤ K φ² L log L (X₂ = K log m). For comparison the trivial route (p = least prime not dividing m,
q = least prime in the class a p̄, Lamzouri–Li–Soundararajan) gives q ≤ (φ L)², so Theorem A wins in q by a factor ≍ X₂/log X₂ = number of primes used.

**Theorem S (symmetric).** Assume GRH (through H). For m ≥ m₀ every a ∈ G is pq with p, q ≤ K′ φ(m) (log m)².

*Proof.* X₁ = X₂ = X ≤ m³. By D4(b) and D5, |E(a)| ≤ M(X)² ≤ C₃² X L². By D2 the main term is ≥ X²/(64φ). So X > 64 C₃² φ L² suffices. ∎

**Theorem E (exceptional sets).** Assume GRH (through H). For m ≥ m₀, K L ≤ X₂ ≤ m, X₁ ≤ m³, X₁ ≥ max(X₀, 8L):

  #{a ∈ G : a ≠ pq for all primes p ≤ X₂, q ≤ X₁} ≤ K φ² L² log X₂ / (X₁ X₂).

At X₁ = X₂ = m this is ≤ K (φ/m)² (log m)³ (the Banks–Shparlinski bound, with (φ/m)² in place of their φ/m as transcribed).
With q ≤ m·Λ, Λ ≥ 1, the bound is K (φ/m)² L³/Λ: the exceptional set shrinks linearly in the extra range and is empty at Λ = K L³ (Cor A1).

*Proof.* D7 with D2, D3, D4(a). ∎

*Remark (a √log saving when one range is ≤ √m; proved).* If X₂ < √m and X₁ ≤ m, then q q′ ≡ a has q q′ determined as an integer, so
Σ_χ |ϑ̃(X₂,χ)|⁴ ≤ 2φ (1.39 X₂ log X₂)². Cauchy–Schwarz in D6, with Σ_{χ≠χ0}|ϑ̃(X₁,χ)|⁴ ≤ M₁² φ V°(X₁) and D4(a) for X₁, gives
Σ_a E(a)² ≤ √2 M₁ V°(X₁)^{1/2} · 1.39 X₂ log X₂, hence an exceptional set ≪ φ² L (log X₁)^{1/2} log X₂/(X₁X₂).
This is nontrivial (o(φ)) once X₁X₂ ≥ φ L^{5/2+ε}; it says nothing near X₁ = X₂ = m.

---

## 4. Theorem B: p ≤ φ log m, q ≤ K φ log² m (proved from H + a cited sieve bound)

**Sieve input (unconditional).** There is an absolute C₅ such that for all x ≥ 2 and all integers h ≠ 0,

  #{p ≤ x : p + |h| prime} ≤ C₅ Π_{p | h}(1 + 1/p) · x/(log x)².

Source: Halberstam–Richert, *Sieve Methods*, Thm 3.11 (Selberg sieve, uniform in h, with the sharper constant 8·𝔖(h)(1+o(1))),
or Thm 2.4 (Brun) [RECALLED numbering]. Uniformity in h is essential and is part of those statements. For odd h the left side is ≤ 1.

**Proof of Lemma D4(c).** Σ_b Θ(X;b)² ≤ Σ_{p,p′ ≤ X, p ≡ p′ (m)} log p log p′. The diagonal is ≤ (log 4) X log X.
Off the diagonal, p′ = p + km with 1 ≤ |k| ≤ X/m, so the contribution is
≤ 2 (log X)² Σ_{1≤k≤X/m} #{p ≤ X : p + km prime} ≤ 2 C₅ X Σ_{k ≤ X/m} Π_{p | km}(1+1/p).
Now Π_{p|km}(1+1/p) ≤ (m/φ(m)) · σ(k)/k and Σ_{k ≤ Y} σ(k)/k = Σ_d (1/d)⌊Y/d⌋ ≤ ζ(2) Y. Total ≤ 2ζ(2)C₅ X²/φ. ∎

**Theorem B.** Assume GRH (through H). There are absolute K″, m₀ such that for m ≥ m₀ and every a ∈ G there are primes
**p ≤ φ(m) log m and q ≤ K″ φ(m) (log m)²** with pq ≡ a (mod m). More generally Theorem A holds with the condition X₂ ≤ m relaxed to X₂ ≤ φ(m) log m.

*Proof.* Let m < X₂ ≤ φL. By D4(c), V°(X₂) ≤ 1.39 X₂ log X₂ + C₄ X₂²/φ ≤ (2.78 + C₄) X₂ L. Then D5, D2, D3 as in Theorem A:
need X₁X₂/(64φ) > C₃ √X₁ L ((2.78 + C₄) X₂ L)^{1/2}, i.e. X₁X₂ > K″ φ² L³. With X₂ = φL this is X₁ > K″ φ L². ∎

So GRH plus the sieve reaches the variance wall (≈ φ log m) in **one** of the two variables. The other variable stays at φ log² m, and it must with
this method: for X₂ ≥ φL one has V°(X₂) ≍ X₂²/φ at best from the sieve, and D5 then forces X₁ ≥ Kφ L² regardless of X₂.

**The frontier proved here**, in the (X₂, X₁)-plane with X₂ ≤ X₁: X₁X₂ ≥ K φ² L² log X₂ for K L ≤ X₂ ≤ φ L, and X₁ ≥ K φ L² for X₂ ≥ φ L.

---

## 5. Limits of the method (proved, as statements about inputs)

**Proposition L (the exponent 2 is sharp for the inputs used in Theorem S).** There is an absolute K₀ with the following property.
For every m, every a ∈ G and every X > 0 there is a function Θ\* : G → [0, ∞) with
- Σ_b Θ\*(b) = X(1 − r/φ), where r = #{x ∈ G : x² = a} ≤ 2^{ω(m)+2};
- |Σ_b Θ\*(b) χ(b)| ≤ (X/φ)(K₀ √φ + r) for all χ ≠ χ0;
- Θ\*(b) ≤ 2X/φ for all b (a Brun–Titchmarsh-type bound with the sharp sieve constant 2);
- Σ_b Θ\*(b) Θ\*(a b^{-1}) = 0.

Consequently, if X ≤ c φ (log m)² then Θ\* satisfies the sup bound |Θ̂\*(χ)| ≤ (K₀√c + o(1)) √X log m, yet "a is not represented".
Any proof of a symmetric range o(φ log² m) must therefore use more than nonnegativity, total mass, and the size of |ϑ̃(X,χ)| at the scale X.

*Proof.* Partition G minus the r fixed points of x ↦ a x^{-1} into (φ−r)/2 orbits {x, a x^{-1}}. For signs ε_o ∈ {±1} put f(x) = ε_o, f(a x^{-1}) = −ε_o on each orbit o,
and f = 0 at fixed points. For each χ, f̂(χ) = Σ_o ε_o (χ(x_o) − χ(a x_o^{-1})) is a linear form in the ε_o with coefficients of modulus ≤ 2.
Taking real and imaginary parts gives 2φ real linear forms in (φ−r)/2 variables. By Spencer's theorem ("six standard deviations", Trans. AMS 289 (1985); in the form:
N variables, M ≥ N forms with coefficients in [−1,1] ⇒ some signing has all forms ≤ K√(N log(2M/N))) there are signs with |f̂(χ)| ≤ K₀√φ for all χ.
Let A = {f = 1}, so A ∩ aA^{-1} = ∅ and 1_A = (1_{non-fixed} + f)/2. Put Θ\* = (2X/φ) 1_A. For χ ≠ χ0, Σ_{non-fixed} χ = −Σ_{fixed} χ has modulus ≤ r. ∎

Remarks.
- A *random* signing only gives |f̂| ≪ √(φ log φ), which is consistent with the sup bound only up to X ≍ φ log m. The discrepancy-theoretic signing is what pushes the model to φ log² m.
- Θ\* has Σ_bΘ\*² = 2X²/φ, i.e. V° = X²/φ = main term. This is the equality case of the variance wall of lit note 03 §0.2.
- The model lives at X ≥ φ log m > m; it says nothing about X ≤ m, where Parseval is exact.
- The model does **not** show that GRH cannot give more. GRH constrains ϑ̃(Y,χ) at all scales Y simultaneously through the same zeros, and the primes satisfy sieve bounds for prime pairs. I could not turn either into a gain (§6).

**The asymmetric bound and its inputs (heuristic).** In Theorem A the loss against the "natural" threshold X₁X₂ ≍ φ² L² (which is what the model
"Θ₁ = uniform minus the classes a·P₂^{-1}" would give) is one factor log X₂. It comes from D5: equality needs
ϑ̃(X₁,χ) = −M₁ · χ(a) · conj(phase of ϑ̃(X₂,χ)) for all χ, a conspiracy of phases with a flat modulus. Nonnegativity of Θ(X₁;·) does not exclude this
when X₁ ≥ φ L³ (the inverse transform of a unimodular sequence can have sup norm ≈ √(L/φ)). So within the inputs of §2, Theorem A is sharp up to the constant for X₂ ≤ m/L^{O(1)},
and borderline at X₂ = m. I did not make this rigorous.

---

## 6. Push further: what was tried, and why each fails

### 6.1 Symmetric K φ log^{1+ε} m or K φ log m (log log m)^C for all a: not obtained

By the wall (lit 03 §0.2) and Prop. L, one needs V°(X) < T(X)²/φ ≈ X²/(4φ) at the scale used, i.e. (after D1)

  Σ_b Θ(X;b)² < 2 T²/φ, i.e. Σ_{k≠0} Σ_{p, p+km ≤ X} log p log(p+km)(1−p/X)(1−(p+km)/X) < 2T²/φ − (diagonal ≈ X log X/3).

The Hardy–Littlewood prediction for the left side is ≈ T²/φ. In words: **one needs an upper bound for prime pairs (p, p + km), summed over
1 ≤ |k| ≤ X/m, with constant < 2 times the Hardy–Littlewood prediction** (for X a large multiple of φ log m, so that the diagonal is negligible).
- The Selberg sieve gives constant 8, and 4 with level-½ information (GRH supplies this for the individual moduli involved). The parity limit of the sieve is 2.
  So the sieve stops **exactly** at the constant that would be needed (proved as far as: D4(c) holds with some constant; a constant < 2 would give Theorem S at X ≍ φ log m. That no sieve gives < 2 is the standard parity statement, heuristic here).
- GRH alone gives only V° ≤ M² ≤ C X L², which is the Theorem S argument.
- Known asymptotics for prime pairs on average over shifts need many more shifts than X/m = (log m)^{O(1)}, and here the shifts are the multiples of m. Not available.
- Conclusion: one log can be saved in **one variable** (Theorem B), not in both. Status of "cannot": Prop. L is a proof for the stated inputs; for "GRH + sieve" in general it is heuristic.

### 6.2 "Only low-lying zeros matter"

In Thm 1 the bound is √x Σ_ρ 1/|ρ(ρ+1)|, dominated by the ≍ log q zeros with |γ| ≤ 1. Could these be prevented from aligning at x = m(log m)^A?
- Alignment at scale x needs the zeros near height 0 to be spaced ≈ 2π/log x. The mean spacing is 2π/log(q/2π)+…, and log x = log m + A log log m.
  Under GRH, S(t,χ) ≪ log q/log log q, so the local density of zeros can deviate from its mean by a relative factor 1/log log q.
  A relative change A log log m/log m in spacing is far inside that freedom. So zero counting under GRH does **not** exclude alignment at x = m (log m)^A. (heuristic, but the comparison of sizes is rigorous)
- Changing the weight: for a weight with Mellin transform W, the bound is Σ_γ |W(½+iγ)| ≈ (log m/2π) ∫|W(½+it)|dt, and ∫|W(½+it)|dt ≥ 2π sup_u w(e^u)e^{u/2}.
  Because of the factor e^{u/2}, only an O(1)-wide window in log-scale near the top of the support contributes to the main term, so long supports gain nothing.
  Optimizing w changes K only (this is the Carneiro–Milinovich–Quesada-Herrera–Ramos regime). (sketched)

### 6.3 Mixing ranges

This is the one idea that pays: with X₂ ≤ m Parseval is exact (D4(a)) and replaces M(X₂)² = X₂L² by X₂ log X₂. This is Theorem A, and with the sieve Theorem B.
Other mixtures give nothing new:
- any nonnegative coefficients c(p) on primes p ≤ m in place of log p (1−p/X₂): the quantity (Σc)/(Σc²)^{1/2} is maximized by flat weights, giving the same X₁ ≥ Kφ²L³/m;
- m < X₂ ≤ φL without the sieve: the trivial bound Θ(X₂;b) ≤ (X₂/m+1) log X₂ gives V° ≤ (X₂/m+1)X₂ log X₂, and X₁ does not decrease;
- using L^∞ on both factors and L² on both factors together: the extremal problem max Σ|S₁||S₂| under |S_i| ≤ M_i, Σ|S_i|² ≤ φV_i has value min(M₁√V₂, M₂√V₁, √(V₁V₂))·φ, which is what D5 uses.

### 6.4 Exceptional set at range exactly m: O(log³ m) not improved

#bad · (m²/(4φ))² ≤ Σ_a E(a)² = (1/φ) Σ_{χ≠χ0}|ϑ̃|⁴ ≤ M² V°, and at X = m both factors are what they are: V° = (1/3 + o(1)) m log m exactly, M ≤ C₃√m log m from GRH.
An improvement needs either M = o(√m log m) (not a consequence of GRH) or a fourth-moment bound Σ_{χ≠χ0}|ϑ̃|⁴ ≪ φ m² L^{3−δ}, i.e. the multiplicative energy of primes ≤ m
to relative accuracy L^{3−δ}/m. The sieve bounds the energy only up to a constant factor of the main term, which is useless here. (sketched)
The expected truth is Σ_a E(a)² ≍ (m log m)², i.e. O(log² m) by this method, and no exceptions at all.

### 6.5 The final log

Nothing here touches it. Theorems A, B, E all end in Cauchy–Schwarz over characters and are subject to the wall. No phase information is obtained from GRH.

---

## 7. Numerical checks

Script: `compute/routeC/routeC_check.py` (output in `compute/routeC/out_check.txt`). Prime m, Cesàro weights, all characters via FFT over a primitive root.
It verifies the identity chain D1/D5 exactly and reports the sizes entering the theorems.

| m | X | max_{χ≠χ0}\|ϑ̃\|/(√X log m) | V°/(X log m) | V°/(X²/φ) | classes with no prime ≤ X |
|---|---|---|---|---|---|
| 10007 | m | 0.359 | 0.236 | 2.18 | 8777 |
| 10007 | m L | 0.358 | 0.232 | 0.232 | 3357 |
| 10007 | m L² | 0.378 | 0.229 | 0.025 | 4 |
| 10007 | m L³ | 0.387 | 0.233 | 0.0027 | 0 |
| 100003 | m | 0.377 | 0.257 | 2.96 | 90410 |
| 100003 | m L | 0.381 | 0.253 | 0.253 | 34414 |
| 100003 | m L² | 0.370 | 0.249 | 0.022 | 2 |

- H is consistent with the data, with observed constant ≈ 0.37 (the proof gives 2/3 + o(1) for the zero sum).
- V° ≈ 0.25 X log m for X up to m L³, i.e. Hooley-type behaviour V° ≍ X log m persists beyond m. GRH only proves V° ≪ X L²; the sieve proves V° ≪ X L for X ≤ φL (D4(c)).
- The inequality |E(a)| ≤ M(X₁)V°(X₂)^{1/2} held in all 25 tested pairs (as it must).
- "Proof ratio" M₁V₂^{1/2}/(T₁T₂/φ), which must be < 1 for the proof to certify all a: at m = 100003 it is 30.1 at (m, m), 8.9 at (mL, m), 2.56 at (mL², m), 0.745 at (mL², mL), 0.218 at (mL², mL²);
  at m = 10007 it is 0.766 at (mL³, m). This matches Cor A1 (certified at (m, mL³) with constant ≈ 1), Theorem B (certified at (mL, mL²)), Theorem S.
- In reality min_a R(a)/main is already 0.785 at (m, m) for m = 100003: the truth is far ahead of the proof, as expected.

---

## 8. Final statements

**Best rigorous theorems (GRH, via H = `GRHSmoothBound`).** There are absolute constants K, m₀ such that for all m ≥ m₀ and all a coprime to m:
1. (Cor A1) a ≡ pq with p ≤ m and q ≤ K φ(m)² (log m)³/m ≤ K m (log m)³.
2. (Thm S) a ≡ pq with p, q ≤ K φ(m) (log m)².
3. (Thm B; additionally uses the unconditional uniform twin-prime upper-bound sieve) a ≡ pq with p ≤ φ(m) log m, q ≤ K φ(m)(log m)².
4. (Thm E) all but ≤ K (φ(m)/m)² (log m)³/Λ classes a are pq with p ≤ m, q ≤ Λ m, for any 1 ≤ Λ ≤ m².

**Extra hypotheses beyond GRH:** none. Theorem B uses a published unconditional sieve theorem (Halberstam–Richert Thm 3.11) that would itself need formalizing or naming as a hypothesis in Lean.

**Open after this route:** symmetric exponent below 2; asymmetric exponent below 3 at p ≤ m; exceptional exponent below 3 at range m; and the final log.
