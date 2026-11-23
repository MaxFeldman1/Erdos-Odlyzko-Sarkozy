# Round 1, analytic persona: Type II via Buchstab + a fourth moment

Written 2026-11-22. Standing hypothesis: GRH for Dirichlet L-functions. Anything more is flagged **[EXTRA]**.
Scripts and outputs: `compute/brainstorm/analytic/` (`h4_moments.py`, `buchstab_all_a.py`, `out_*.txt`).

**Status tags.** *proved* = complete argument here, relying only on quoted results. *sketched* = all steps
indicated, some bookkeeping not written out. *heuristic* = not a proof. *computed* = script output.
Quoted inputs keep the status they have in `notes/lit/` and route A; I did not re-read sources.

Notation as in `00-setup.md` and route A: G = (Z/mZ)^*, φ = φ(m), L = log m, P = {p ≤ m prime, p ∤ m},
ρ = |P|/φ, μ = |P|²/φ, A_a = {a·p̄ mod m : p ∈ P} ⊂ [1,m], F(n) = 1_P(a·n̄ mod m) for (n,m) = 1 (periodic
in n, and F = 1_{A_a} on [1,m]), F(n) = 0 if (n,m) > 1.

---

## 0. Summary

**No proof of EOS.** What this note adds to route A:

| # | Item | Status |
|---|---|---|
| Thm BH (§2) | With Buchstab's identity in place of Vaughan's, EOS at a (in the form N(a) ≥ 0.4μ) follows from a **one-sided** Type II inequality with **constant** relative precision η, on rough k only, for M ≤ √m only. Route A's Proposition E needs two-sided precision ε/log m on all k, for M up to m^{1−η}. | proved from two quoted inputs (Fouvry–Shparlinski Type I, fundamental lemma); the main-term comparison Lemma 2.2 is sketched |
| Cor H4 (§2.3) | Hölder (4/3, 4) and positivity give an a-independent sufficient hypothesis **H4(η)**: Σ_{c∈G} δ_I(c)⁴ ≤ (η⁴/16)·ρ⁴\|I\|⁴\|𝒦_M\| for short blocks I ⊂ [m^η, √m]. This is "five logs" below the trivial bound. Route A's M4 asked for ten, plus a sup bound that was not available for M < √m. | proved |
| Cor LD (§2.4) | Weak-type form: it suffices that #{c : δ_I(c) > T} beats Chebyshev by a factor ≍ (log m)³ for T ≥ ηρ\|I\|/4. | proved |
| Prop S (§3.1) | H4(η) is sharp up to the constant against every parity-type counterexample (any P* with the Type I data of A_a and no primes in a·P*^{-1} violates H4 with η replaced by 1.7η). | proved |
| Prop Q (§3.2) | The conjugate (quotient-problem) fourth moment is **provably too large**: Σ_c δ⁻_I(c)⁴ ≥ (m/(3M))·(ρ\|I\|)⁴. So H4 is true-looking for products and false for quotients. It is not blind to S² versus \|S\|². | proved; computed |
| §4 | Numerics: δ_I is Gaussian plus the expected Poisson correction over all c ∈ G (kurtosis 3.02–3.29 against 3.02–3.38 predicted, max 5.7–7.4σ); the conjugate has outliers at 16–83σ. The Buchstab sum over **all** a at m = 4·10⁶ is within 5% of its mean. | computed |
| §5 | What I tried in order to derive H4 or LD. GRH sup bounds, Halász–Montgomery, and majorant/restriction arguments all return Chebyshev. A uniform Hardy–Littlewood 4-tuple hypothesis with power-saving error gives H4 only for M ≤ m^{1/5−ε}, which is not enough. | sketched / heuristic |
| Routes 2, 3 (§6, §7) | Two partial-result routes. Neither reaches EOS. | proposals |

**Honest probabilities.** Thm BH and its corollaries are correct as stated: 85%. H4(η) or LD provable from
GRH: about 1%. EOS through this route: under 1%.

---

## 1. The three routes

### Route 1 (best): Buchstab + Hölder, hypothesis H4(η)

- **Mechanism.** Sieve A_a for primes with one Buchstab step. The sifted main term S(A_a, z), z = m^η, is
  known from the Type I level m^{1/16} (unconditional). The Buchstab sum Σ_{z ≤ p₁ < √m} S(A_{p₁}, p₁) is a
  positive bilinear sum; EOS needs only an **upper** bound for it within a factor 1 + η of its mean.
  Positivity removes the cut-off and decoupling problems. Hölder with exponents (4/3, 4) and extension of the
  arc {a·k̄} to all of G turn this into the a-independent fourth-moment bound H4(η).
- **Extra hypotheses.** **[EXTRA]** H4(η) (or the weaker LD). Not known to follow from GRH.
- **First lemma.** Thm BH and Cor H4 (done, §2). Next: any saving, even one log, over the trivial bound for
  Σ_c δ_I(c)⁴, or the same for the model problem of Route 2.
- **Probability.** Reduction correct 85%; H4 from GRH about 1%; EOS under 1%.

Barrier checklist (details in §3):

| Barrier | Verdict | Reason |
|---|---|---|
| (1) random pairing-avoiding set R | **pass** | The route uses P in two different roles: as the set inverted to form A (through Type I and H4), and as the sieve target (integers that are prime). For R it proves a ∈ R·P, which is true. It never proves a ∈ R·R. |
| (2) deletion of ≈ 1/log m of the primes | **pass** | P′ = P ∖ R_a keeps every Type II sum (route A, Prop C) but breaks the Type I input at d = 1: \|A′\| = \|P\| − N(a), while the densities for d > 1 still give \|P\|. The fundamental lemma then has remainder ≍ N(a) log D ≫ main term. The exact identity used is \|A_a\| = \|P\| (injectivity of p ↦ a·p̄). |
| (3) parity | **pass, conditional on H4** | H4 is bilinear (Type II) information. Prop S: every parity counterexample violates it. |
| (4) route A's A* | **pass, conditional on H4** | A* has the Type I data and no primes, so by Prop S its fourth moment exceeds the H4 threshold by a constant factor. H4 is not implied by Type I plus sizes. |
| (5) route C's Prop L | **pass** | H4 is a four-point, phase-sensitive statement, not a sup or Parseval bound. A Prop L-type object in the role of P either lacks the Type I data or is covered by Prop S. |
| (6) Thm G conjugation | **pass** | Twice over. The Type I data of {−p mod m} fail at d = 2. And the conjugate fourth moment is provably above the threshold (Prop Q). On the character side Σ_c δ⁴ = φ^{-3} Σ_{χ₁χ₂χ₃χ₄=1} Π S(χ_i)U(χ_i), and the conjugate has Ū in place of U. |

So all six barriers are passed, and all the difficulty sits in H4. That is the expected shape: the barriers
say what a proof must contain, and H4 contains exactly that.

### Route 2: the shrinking-box model, where the fourth moment is accessible

- **Mechanism.** Replace the outer primes P by the integers x ≤ X = m^{1−δ}. The sifted sequence is
  A^X_a = {a·x̄ mod m : x ≤ X}. Type I level is m^{1/2−δ−ε} by Weil for the hyperbola xt ≡ c in a box. Type II
  sums are bilinear Kloosterman sums with arbitrary coefficients, because the interval [1,X] has additive
  Fourier L¹ norm ≪ log m. In this model the analogue of H4 is the additive energy of reciprocals, which is
  known (Bourgain–Garaev, `lit/02` §1.4), and Cauchy–Schwarz plus Weil already gives the Type II range
  M ∈ [m^{2δ+ε}, m^{1/2−2δ−ε}] (sketched, §6). Target theorem: every a is q·x with q ≤ m prime and
  x ≤ m^{1−δ}, for some δ > 1/16 (Fouvry–Shparlinski give δ < 1/16 directly).
- **Why it is on the list.** It is the same architecture as Route 1 with every step provable, so it tests the
  bookkeeping. It also isolates what is special about primes on the outside: Σ_h |P̂(h)| is huge, Σ_h |Î(h)|
  is not.
- **Extra hypotheses.** None.
- **First lemma.** A Harman-sieve computation for the gap p₁ ∈ [m^{1/2−2δ}, m^{1/2}], where neither Type I
  nor Type II is available. Whether the outcome beats δ = 1/16 is open (§6).
- **Checklist.** This is not EOS, so the barriers apply only as follows. (1), (2), (5), (6): not applicable
  (the outer set is an interval, nothing is deleted, no character sums are used). (3) parity: **passed for
  the model** (Type II information exists). (4) A*: not applicable. For EOS itself the route **fails all six
  by design**; it proves nothing about two primes.
- **Probability.** A clean theorem with some δ > 0 by the sieve: 80%. With δ > 1/16: 35%. That it is new:
  [UNVERIFIED], perhaps 25% (Baker 2012 on Kloosterman sums with prime variable may cover it). EOS: 0.

### Route 3: special moduli, to weaken the Type II hypothesis and improve r in a ≡ p·P_r

- **Mechanism.** In Thm BH the admissible η is tied to the Type I level θ of A_a by e^{−θ/η} ≪ η. With
  θ = 1/16 one needs η ≈ 1/100, so the Type II precision is about 2%. If θ were close to 1/2 (smooth m or
  m = ℓ^k, via q-van der Corput or p-adic van der Corput for short Kloosterman sums) one could take η ≈ 1/8,
  where the allowed one-sided error is about 28% and the Type II range shrinks to [m^{1/8}, m^{1/2}]. The same
  level improvement gives a ≡ p·P_r with smaller r (D §4.2).
- **Extra hypotheses.** None for the almost-prime statement. For EOS, H4(η) with the larger η. **[EXTRA]**
- **First lemma.** For m = ℓ^k: Σ_{u∼U, v∼V} α_u β_v e(h·ū·v̄/m) ≪ UV·m^{−c} with U ≈ V ≈ √m and explicit c.
  My back-of-envelope with the exponent pair (1/6, 2/3) gives a saving m^{1/24} in the balanced range
  (heuristic, not checked), which is smaller than 1/16, so the gain must come from the unbalanced ranges.
- **Checklist for EOS.** (3) parity: **fail** without H4. (4) A*: **fail** without H4 (Type I only).
  (6) Thm G: pass (joint Type I data). (1), (2): pass for the almost-prime statement. (5): not applicable.
  With H4(η) added the verdicts are those of Route 1.
- **Probability.** Some improvement of the level for special moduli: 30%. EOS: 0 without H4.

---

## 2. Route 1 in detail: the reduction

### 2.1 Inputs

Fix 0 < η ≤ η₀ (η₀ absolute, small), z = m^η, D = m^{1/17}, s = 1/(17η).

- **(T1) Type I (quoted: Fouvry–Shparlinski, `lit/02` §1.2).** For (d,m) = 1, d ≤ m:
  #{n ∈ A_a : d | n} = |P|/d + O(m^{15/16+o(1)}), uniformly in a and d. If (d,m) > 1 the set is empty.
- **(FL) Fundamental lemma (quoted, e.g. Halberstam–Richert Thm 2.5 [RECALLED numbering]).** For a finite
  set 𝒜 with #𝒜_d = Y/d + r_d for squarefree d | P_m(z) := Π_{p<z, p∤m} p:
  S(𝒜, z) = Y·V(z)·(1 + O(e^{−s})) + O(Σ_{d<D, d|P_m(z)} |r_d|), V(z) = Π_{p<z, p∤m}(1 − 1/p).
- Integer model 𝒩 = {n ≤ m : (n,m) = 1}, Φ_m(x,y) = #{n ≤ x : (n,m) = 1, P⁻(n) ≥ y}.
  #𝒩_d = φ/d + O(2^{ω(m)}).

**Lemma 2.1 (proved from T1, FL).** S(A_a, z) = ρ·Φ_m(m,z)·(1 + O(e^{−s})) + O(m^{1−1/300}).

*Proof.* Apply FL to A_a (Y = |P|, Σ_{d<D}|r_d| ≤ D·m^{15/16+o(1)}) and to 𝒩 (Y = φ, remainder ≤ D·2^{ω(m)}),
and divide. ∎

### 2.2 Buchstab and the one-sided Type II inequality

Buchstab's identity for any finite 𝒜 ⊂ [1,m]:
S(𝒜, √m) = S(𝒜, z) − Σ_{z ≤ p₁ < √m} S(𝒜_{p₁}, p₁), where S(𝒜_{p₁}, p₁) = #{n = p₁k ∈ 𝒜 : P⁻(k) ≥ p₁ or k = 1}.
An n ≤ m with all prime factors ≥ √m is 1, a prime, or p² with p² = m. Put

  B(a) := Σ_{z ≤ p₁ < √m} S((A_a)_{p₁}, p₁) = Σ_{z ≤ p₁ < √m} Σ_{k ≤ m/p₁, P⁻(k) ≥ p₁} F(p₁k),
  B₀ := Σ_{z ≤ p₁ < √m, p₁∤m} Φ_m(m/p₁, p₁) = Φ_m(m,z) − S(𝒩, √m).

**Theorem BH (proved from T1, FL).** There are absolute η₀ > 0 and m₀(η) such that for 0 < η ≤ η₀,
m ≥ m₀(η) and (a,m) = 1:

  **if B(a) ≤ (1 + η)·ρ·B₀, then N(a) ≥ 0.4·μ.**

*Proof.* N(a) ≥ #{primes in A_a} ≥ S(A_a, √m) − 2 = S(A_a, z) − B(a) − 2. By Lemma 2.1 and the hypothesis,

  N(a) ≥ ρ(Φ_m(m,z) − B₀) − ρ(C e^{−s}Φ_m(m,z) + ηB₀) − O(m^{1−1/300}) ≥ ρ·S(𝒩,√m) − ρ(Ce^{−s} + η)Φ_m(m,z) − O(m^{1−1/300}).

Now S(𝒩, √m) ≥ π(m) − π(√m) − ω(m) = (1 + o(1))m/L. By FL for 𝒩 and Mertens,
Φ_m(m,z) ≤ (1 + O(e^{−s}))·φ·V(z) = (1 + o(1) + O(e^{−s}))·e^{−γ}·m/(ηL). (The factor Π_{p|m, p≥z}(1−1/p)^{-1} is
1 + O(ω(m)/z).) Hence N(a) ≥ ρ(m/L)[1 − e^{−γ} − C′e^{−1/(17η)}/η − o(1)], and 1 − e^{−γ} = 0.4385. Since
μ = ρ|P| ≤ ρ(1+o(1))m/L, the claim follows for η ≤ η₀. ∎

Remarks.
- The same proof gives N(a) > 0 from B(a) ≤ (1 + 1.7η)ρB₀. The exact threshold is θ₀ = S(𝒩,√m)/B₀ ≈ e^γ η.
- **Only an upper bound is needed, and its precision is a constant.** With Vaughan (route A, Thm A) the
  coefficient b_k lives on all k and the signal is a 1/log m fraction of the trivial bound. With Buchstab the
  coefficient lives on rough k, of density ≍ 1/log M, and the trivial bound is of the size of the main term.
- The price is that η is tied to the Type I level: e^{−(1/17)/η} ≪ η forces η ≲ 1/100 with the level m^{1/16}.
- The range of the bilinear sum is z ≤ p₁ < √m only.

### 2.3 Hölder and the hypothesis H4(η)

Fix λ ∈ (0, 1]. For M_j = z(1+λ)^j < √m let I_j = (M_j, (1+λ)M_j], let |I_j|′ be the number of primes in I_j
not dividing m, and

  𝒦_j := {1 ≤ k ≤ m/M_j : (k,m) = 1, P⁻(k) > M_j or k = 1},
  π_j(c) := #{p₁ ∈ I_j prime : c·p̄₁ mod m ∈ P}, δ_j(c) := π_j(c) − ρ|I_j|′ (c ∈ G).

Since F ≥ 0, F(p₁k) = 1_P(a·k̄·p̄₁) and {k ≤ m/p₁, P⁻(k) ≥ p₁} ⊂ 𝒦_j for p₁ ∈ I_j,

  (2.1) B(a) ≤ Σ_j Σ_{k∈𝒦_j} π_j(a·k̄) = ρ Σ_j |I_j|′|𝒦_j| + Σ_j Σ_{k∈𝒦_j} δ_j(a·k̄).

Positivity has absorbed both the cut-off p₁k ≤ m and the dependence of the roughness condition on p₁.

**Lemma 2.2 (sketched).** Σ_j |I_j|′|𝒦_j| ≤ (1 + C₁λ)B₀ + O(λm/(η³L²)), with C₁ absolute.

*Sketch.* The excess consists of (i) k ∈ (m/p₁, m/M_j] with P⁻(k) > M_j: an interval of length ≤ λm/M_j ≥ λM_j,
so the upper-bound sieve gives ≪ λ(m/M_j)/log M_j ≍ λ|𝒦_j| per p₁; (ii) k with P⁻(k) ∈ (M_j, p₁): then
k = p′k′ with p′ ∈ I_j, and the number of (p₁, p′, k′) is ≪ |I_j|′²(1 + m/(M_j² log M_j)); summed over the
≤ L/λ blocks this is ≪ λm/L² + λm/(η³L²); (iii) the last block overshooting √m, which is O(λ) of the top
block. Against B₀ ≍ m/(ηL), (ii) and (iii) are negligible. ∎

The classes a·k̄, k ∈ 𝒦_j, are distinct elements of G (k < m, (k,m) = 1). By Hölder,

  (2.2) Σ_{k∈𝒦_j} δ_j(a·k̄) ≤ |𝒦_j|^{3/4} (Σ_{k∈𝒦_j} δ_j(a·k̄)⁴)^{1/4} ≤ |𝒦_j|^{3/4} (Σ_{c∈G} δ_j(c)⁴)^{1/4}.

> **Hypothesis H4(η) [EXTRA; a-independent].** With λ = η/(4C₁), for every block I_j ⊂ [m^η, (1+λ)√m]:
>
>  **Σ_{c∈G} δ_j(c)⁴ ≤ (η/2)⁴ · ρ⁴ |I_j|′⁴ |𝒦_j|.**

**Corollary H4 (proved, given Lemma 2.2).** GRH is not needed for this step. For η ≤ η₀ and m ≥ m₀(η):
H4(η) implies B(a) ≤ (1+η)ρB₀ for every a, hence N(a) ≥ 0.4μ for every (a,m) = 1.

*Proof.* By (2.2) and H4, Σ_{k∈𝒦_j} δ_j(a k̄) ≤ (η/2)ρ|I_j|′|𝒦_j|. By (2.1) and Lemma 2.2,
B(a) ≤ ρ(1 + η/2)(1 + C₁λ)B₀(1 + o(1)) ≤ (1+η)ρB₀. Apply Thm BH. ∎

So the whole of EOS is in H4(η); GRH enters only if one tries to prove H4. (The route is "GRH-free
conditional on H4", which says how far H4 is from GRH, not that it is easy.)

**Sizes.** |I_j|′ ≍ λM/log M and |𝒦_j| ≍ (m/M)/log M (Buchstab's function is in [1/2, 1]). So the right side
of H4 is ≍ η⁴λ⁴ ρ⁴ m M³/(log M)⁵.
- *Truth (Gaussian model).* δ_j(c) has variance ≈ ρ|I_j|′, so Σ_c δ⁴ ≈ 3φρ²|I_j|′². H4 then holds as soon as
  M ≥ C(η)(log m)⁵. There is a factor M/(log m)^{5} of room.
- *Trivial bound.* |δ_j| ≤ |I_j|′ and Σ_c δ_j² = (1/φ)Σ_{χ≠χ0}|S(χ)|²|U_j(χ)|² ≤ |P|·max_χ|U_j(χ)|², which under GRH
  is ≪ |P|·M log² m. Even with the true variance, the trivial bound is ρφ|I_j|′³, which exceeds the H4
  threshold by ≍ (log m)⁵/(η⁴λ). **H4 asks for five logs.**
- *Comparison with route A.* M4 there: Σ_c δ_M⁴ ≪ mM³(log m)^{−12} in Λ-normalisation, a saving of (log m)^{10},
  for all M ∈ [m^η, m^{1−η}], plus a sup bound available only for M ≥ m^{1/2+ε}. Here: a saving of (log m)⁵,
  M ≤ √m, no sup bound, no cut-off terms.

### 2.4 Weak-type form

**Corollary LD (proved).** Put T_j = ηρ|I_j|′/4 and E_j(T) = #{c ∈ G : δ_j(c) > T}. If for every block

  **E_j(T) ≤ (1/4)·|𝒦_j|·(T_j/T)² for all T ≥ T_j,**

then B(a) ≤ (1+η)ρB₀ for every a.

*Proof.* Σ_{k∈𝒦_j} δ_j(a k̄) ≤ T_j|𝒦_j| + Σ_{i≥0} 2^{i+1}T_j·E_j(2^i T_j) ≤ T_j|𝒦_j|(1 + Σ_i 2^{i+1}·4^{−i}/4) = 2T_j|𝒦_j| = (η/2)ρ|I_j|′|𝒦_j|. ∎

Chebyshev gives E_j(T) ≤ ρφ|I_j|′/T² (true variance). The ratio to the requirement is
4ρφ|I_j|′/(|𝒦_j|T_j²) = 64φ/(η²ρ|I_j|′|𝒦_j|) ≍ (log m)³/(η²λ). **LD asks to beat Chebyshev by three logs, for
one-sided deviations of constant relative size.** In words: the number of classes c for which the count of
representations c ≡ p·p₁ (p ≤ m, p₁ ∈ I) exceeds its mean by a factor 1 + η/4 must be smaller than the
number of rough k ≤ m/M. At M = m this would read "fewer than one exceptional class", which is EOS; at
M ≤ √m it is an exceptional-set statement for an unbalanced problem. Banks–Shparlinski's (log m)³ exceptional
set for the balanced problem is the same three logs.

---

## 3. Sharpness and the barriers

### 3.1 H4 is exactly at the parity threshold

**Proposition S (proved).** Let P* ⊂ G be any set of residues such that A* = a·(P*)^{-1} ∩ [1,m] satisfies (T1)
with |P*| in place of |P|, and A* contains no prime in [√m, m]. Then for η ≤ η₀ and large m, the analogue of
H4 for P* fails with η replaced by 1.7η: for some block,
Σ_c δ*_j(c)⁴ > (0.8η)⁴ρ⁴|I_j|′⁴|𝒦_j|.

*Proof.* Thm BH and Cor H4 use nothing about P beyond (T1), F ≥ 0 and the injectivity of k ↦ a·k̄. If the
fourth-moment bound held with constant (0.8η)⁴ for all blocks, then B*(a) ≤ (1 + 1.7η)ρB₀ and the remark
after Thm BH would give a prime in A*. ∎

So the constant in H4 cannot be improved by more than a factor ≈ (1.7·2)⁴ ≈ 130 without becoming false for
route A's A* and for every other parity counterexample with correct Type I data. For A* itself the
mechanism is visible: δ*_j(a k̄) ≈ κρ|I_j|′ for every k ∈ 𝒦_j, with κ ≈ e^γ η, so the arc alone contributes
≈ κ⁴ρ⁴|I_j|′⁴|𝒦_j|.

**Deletion.** For P′ = P ∖ R_a the arc values shift only by ρ_R|I_j|′ with ρ_R = N(a)/φ ≈ ρ², a relative
1/log m, far below η. So H4 does not detect deletion, and it does not need to: Lemma 2.1 fails for A′,
because |A′_d| = |A_d| + O(1) for d > 1 but |A′| = |P| − N(a), and Σ_{d<D}|r′_d| ≍ N(a) log D, which is larger
than the sifted main term |P|V(z) ≍ |P|/(ηL) by a factor ≍ ηL. In the Buchstab formulation the deletion
barrier is carried by the exact cardinality |A_a| = |P|, and the parity barrier by H4. (In route A's Vaughan
formulation the precision 1/log m made the two coincide at the threshold.)

### 3.2 H4 is not blind to conjugation

For the quotient problem p ≡ a·q the sifted sequence is {ā·p}, and the corresponding object is
δ⁻_j(c) = #{p₁ ∈ I_j : c·p₁ mod m ∈ P} − ρ|I_j|′, on the arc {a·k}.

**Proposition Q (proved).** For every block with (1+λ)M_j ≤ √m,
Σ_{c∈G} δ⁻_j(c)⁴ ≥ (⌊m/((1+λ)M_j)⌋ − 1 − ω(m))·(ρ|I_j|′)⁴ + (1−ρ)⁴|I_j|′⁴.

*Proof.* For an integer 2 ≤ b ≤ m/((1+λ)M_j) coprime to m and p₁ ∈ I_j, the residue b·p₁ mod m is the
integer bp₁ ≤ m, which is composite. So π⁻_j(b) = 0 and δ⁻_j(b) = −ρ|I_j|′. For c = 1, π⁻_j(1) = |I_j|′. ∎

The right side is ≍ (m/M)ρ⁴|I|⁴, which exceeds the H4 threshold (η/2)⁴ρ⁴|I|⁴|𝒦_j| ≍ η⁴ρ⁴|I|⁴(m/M)/log M by the
factor ≍ (log M)/η⁴. So **the conjugate of H4 is false**, for an archimedean reason of exactly the kind
behind Thm G (small-height classes c, where c·p₁ does not wrap around). The direct problem has no such
classes: c ≡ p·p₁ with c of small height forces pp₁ = c + jm with j ≥ 1, a generic equation.

Consequence for barrier (6): a proof of H4 cannot be invariant under U ↦ Ū on the character side. This is
confirmed numerically (§4): the conjugate moments are visibly non-Gaussian.

### 3.3 Random pairing-avoiding set and Prop L

Let R be a random set of density ρ with R ∩ a·R^{-1} = ∅. Then a·R^{-1} has the Type I data of a random set and
R satisfies H4 with high probability (heuristic: δ^R is a sum of nearly independent terms). The route
concludes that a·R^{-1} contains a prime, i.e. a ∈ R·P. That is true and is not a ∈ R·R. The barrier set breaks
only the coupling "outer set = set of primes", and the route uses that coupling through (T1) for A_a
(Kloosterman sums over primes) and through H4 for P. The same remark covers Prop L's Θ*.

---

## 4. Numerics (computed)

### 4.1 Fourth moment and large deviations over all c ∈ G (`h4_moments.py`, `out_h4_moments.txt`)

Prime m; I = (M, (1+λ)M]; Λ-weighted δ_I(c) = Σ_{u∈I} Λ(u)(1_P(c·ū) − ρ) and its conjugate δ⁻ (c·u in place
of c·ū). "pred" is the independent-Bernoulli model: variance ρ(1−ρ)ΣΛ², kurtosis 3 + fourth cumulant.

| m | M = m^e, λ | #u | var/pred | kurtosis (pred) | max\|δ\|/σ (√(2 log φ)) | #{\|δ\| > 5σ} (Gauss) | conj. kurtosis | conj. max/σ |
|---|---|---|---|---|---|---|---|---|
| 1000003 | 100 (e = 1/3), 1 | 21 | 0.955 | 3.289 (3.375) | 7.12 (5.26) | 77 (0.6) | 3.40 | 16.1 |
| 1000003 | 1000 (e = 1/2), 1 | 135 | 0.956 | 3.048 (3.058) | 5.81 | 12 (0.6) | 6.58 | 40.7 |
| 4000037 | 437 (e = 0.4), 1 | 66 | 0.959 | 3.102 (3.140) | 6.07 (5.51) | 82 (2.3) | 3.61 | 30.1 |
| 4000037 | 2000 (e = 1/2), 1 | 247 | 0.959 | 3.023 (3.037) | 5.68 | 13 (2.3) | 7.08 | 58.1 |
| 4000037 | 2000, 0.1 | 24 | 0.995 | 3.375 (3.383) | 7.42 | 621 (2.3) | 3.56 | 17.8 |
| 16000057 | 761 (e = 0.4), 1 | 105 | 0.963 | 3.082 (3.101) | 6.57 (5.76) | 164 (9.2) | 3.65 | 39.8 |
| 16000057 | 4000 (e = 1/2), 1 | 457 | 0.961 | 3.016 (3.023) | 5.73 | 38 (9.2) | 7.77 | 83.1 |

Reading.
- The direct δ is Gaussian with the Poisson correction expected from a sum of #u terms: the kurtosis matches
  the prediction to within 0.01–0.09 and the maximum over 10⁶–1.6·10⁷ classes is 5.7–7.4σ. The excess of 5σ
  events is the positive skew of a count with few terms; it shrinks as #u grows.
- The conjugate δ⁻ has kurtosis up to 7.8 and outliers up to 83σ. The largest is c = 1 (Prop Q).
- The variance is 4% below the Bernoulli prediction for λ = 1 and 0.5% below for λ = 0.1, stably in m.
  I have not explained this. It is an off-diagonal effect in Σ_{u₁≠u₂}(N⁻(u₁/u₂) − λ) and has no bearing on H4.
- **H4 itself is far from testable at these sizes.** In the script's normalisation the ratio
  Q = Σ_c δ⁴/(λ⁴ρ⁴mM³/log M) is 90–520 for λ = 1, where H4 wants Q ≤ η⁴/16. The Gaussian value of Q is
  ≈ 3(log M)³/(λ²ρ²M), which falls below 1 only for M ≳ (log m)⁵ ≈ 10⁶. The numerics support the Gaussian
  model for δ, not H4 at finite m.

### 4.2 The Buchstab inequality for every a (`buchstab_all_a.py`, `out_buchstab_all_a.txt`)

Prime m = 4000037; all φ = 4·10⁶ classes at once by discrete logarithm and FFT. S_z(a) = S(A_a, z);
Buch(a) = #{rough composites in A_a}; E denotes ρ·(size of the integer set); θ₀ = #primes/#rough composites
is the allowed one-sided relative error.

| η | z | θ₀ | S_z(a)/E: min, max | Buch(a)/E: min, max | needed: Buch/E < |
|---|---|---|---|---|---|
| 1/6 | 12.6 | 0.517 | 0.979, 1.019 | 0.978, 1.022 | ≈ 1.52 |
| 1/4 | 44.7 | 0.998 | 0.974, 1.027 | 0.969, 1.030 | ≈ 2.00 |
| 1/3 | 158.7 | 1.819 | 0.969, 1.031 | 0.957, 1.047 | ≈ 2.82 |

Per dyadic block of the least prime factor (η = 1/4): the relative deviation of the block sum over all a has
standard deviation 0.012–0.018 (0.88 of the Poisson value throughout) and maximum 0.066–0.091, except the
truncated top block (0.21). At m = 1000003 the totals are within 7.2% of the mean.

Reading. At m = 4·10⁶ the one-sided inequality of Thm BH holds for every a with a margin of a factor 10–40
over what is used. This is a restatement of min_a N(a)/μ ≈ 0.95 (`compute/RESULTS.md`) in the variables of
the route; it shows that the Type II statement needed is of constant precision and has room, nothing more.
Caveat: these η are far larger than what the level m^{1/16} allows (η ≈ 1/100), where θ₀ ≈ 0.02 and the room
is a factor 2–4 only at this m.

---

## 5. Can H4 or LD be derived from something standard?

What I tried, with outcomes.

1. **GRH sup bounds (proved).** |δ_j(c)| ≤ (1/φ)Σ_{χ≠χ0}|S||U_j| ≤ max|U_j|·|P|^{1/2} ≪ (mM)^{1/2}(log m)^{1/2}, which
   is below ρ|I_j| only for M ≥ m(log m)^C. So the fourth moment is controlled by GRH exactly in the range
   M ≥ m(log m)^C, which is the range of route C's Corollary A1 and is disjoint from M ≤ √m.
2. **Young / Hausdorff–Young (proved).** Σ_c δ⁴ ≤ φ^{-3}(Σ_χ|SU_j|^{4/3})³ ≈ m²M² for a flat spectrum, worse than
   trivial for M < m. The loss is the factor m from the phases, as in `lit/02` §2.2.
3. **Halász–Montgomery large values (proved; no gain).** For 𝔈 = {δ_j > T}:
   T|𝔈| ≤ ⟨1_P − ρ, U_j ⋆ 1_𝔈⟩ ≤ |P|^{1/2}·E(U_j, 𝔈)^{1/2}, where E is the multiplicative energy. For 𝔈 inside
   an arc the energy is diagonal (p₁k′ = p₁′k as integers), and one gets |𝔈| ≤ |P||I|/T², which is
   Chebyshev. The loss is the factor |P|^{1/2}: Cauchy–Schwarz over p forgets that P is sparse.
4. **Sieve majorant / restriction (proved; no gain).** Replacing 1_P by an upper-bound sieve weight ν in
   step 3 uses bilinear Kloosterman sums with one arbitrary set, which do have a power saving. The outcome
   is Σ_{c∈𝔈}π_j(c) ≤ Cρ|I||𝔈| with a sieve constant C ≥ 2. That bounds deviations of relative size C − 1, not
   η. Restriction estimates for primes control the large spectrum at the trivial scale only. This is the
   parity barrier in the usual form.
5. **Hardy–Littlewood (heuristic).** Σ_c δ_j(c)⁴ = Σ_{u₁,…,u₄∈I} C₄(u), where
   C₄(u) = Σ_x Π_i f(x·v_i mod m), f = 1_P − ρ, v_i = Π_{l≠i} u_l ≈ M³. On each interval of x of length ≈ m/M³ the
   four residues are linear forms v_i x − j_i m, so C₄ is a sum of ≈ M³ centred prime 4-tuple counts on
   intervals of length Y = m/M³. **[EXTRA]** Under a uniform Hardy–Littlewood conjecture with error
   O(Y^{1/2}m^ε) for forms with coefficients up to m (the kind of hypothesis Montgomery–Soundararajan use for
   moments of primes in short intervals), the total error is M⁷·(m/M³)^{1/2}m^ε, which is below the H4
   threshold iff **M ≤ m^{1/5−ε}**. The centred singular-series sums should then give the Gaussian value.
   For M > m^{1/3} the intervals have length < 1 and the correlation is genuinely modular; Hardy–Littlewood
   says nothing.
   - Is the range M ≤ m^{1/5} enough with Harman's sieve? No. The uncovered Buchstab terms include the
     products p₁p₂ ≤ m with p₁ ∈ [m^{1/5}, m^{1/2}], whose density among integers is (log 4)/log m, larger than
     that of the primes. Any constant loss there is fatal.
   - So "uniform Hardy–Littlewood ⇒ EOS" does not follow this way. It would need the fourth moment in the
     modular range m^{1/5} ≤ M ≤ m^{1/2}.
6. **Character side.** Σ_c δ⁴ = φ^{-3}Σ_{χ₁χ₂χ₃χ₄=1, χ_i≠χ0} Π_i S(χ_i)U_j(χ_i). H4 is a statement about the phases of
   S·U_j along multiplicative quadruples. It is of the same type as route B's TwistedRatios input, in a
   moment form. I do not see a standard conjecture about individual L-functions that implies it.

**Conclusion.** H4 and LD are a-independent, one-sided, constant-precision, and need 5 and 3 logs. They are
still phase statements. I could not derive either from GRH, and items 3–4 show that the two obvious
"beyond second moment" tools return exactly Chebyshev or a sieve constant.

---

## 6. Route 2 in more detail (sketched)

Model: A^X = {a·x̄ mod m : x ≤ X, (x,m) = 1}, X = m^{1−δ}, m prime for simplicity.

- **Type I.** #{x ≤ X : d | (a x̄ mod m)} = #{(x,t) : x ≤ X, t ≤ m/d, xt ≡ a·d̄} = X/d·(1 + o(1)) + O(m^{1/2+o(1)}) by
  Weil. Level D = m^{1/2−δ−ε}.
- **Type II.** For 1-bounded α_u (u ∼ M), β_k (k ∼ K), MK ≤ m:
  Σ α_uβ_k 1_{[1,X]}(a·\overline{uk}) = (X/m)Σα_uβ_k + Σ_{h≠0} ĉ_X(h) B(ha), with Σ_{h≠0}|ĉ_X(h)| ≪ log m and
  B(c) = Σ α_uβ_k e(c·\overline{uk}/m). Cauchy–Schwarz in k and Weil for incomplete Kloosterman sums give
  |B(c)| ≤ MK(1/M + m^{1/2}log m/K)^{1/2}. The error is below (X/m)MK(log m)^{−A} iff M ≥ m^{2δ+ε} and
  K ≥ m^{1/2+2δ+ε}. So Type II holds for M ∈ [m^{2δ+ε}, m^{1/2−2δ−ε}], and by symmetry for the complementary
  range of the other variable.
- **The fourth-moment version.** δ^X_I(c) = Σ_{u∈I}(1_{[1,X]}(c ū) − X/m) = Σ_{h≠0} ĉ_X(h) W_I(hc), W_I(b) = Σ_{u∈I} e(b ū/m).
  Minkowski gives ‖δ^X_I‖₄ ≤ (log m)·‖W_I‖₄, and Σ_b |W_I(b)|⁴ = m·#{ū₁ + ū₂ ≡ ū₃ + ū₄}, the additive energy of
  reciprocals of primes, which is ≪ |I|²(1 + |I|³/m)·(log)^{O(1)} (Bourgain–Garaev Thm 6, quoted in `lit/02`
  §1.4). So the analogue of H4 is a theorem for M ≤ m^{1/3}, with the 2k-th moment version for smaller M.
  **In the model, H4 is the reciprocal-energy bound.** For primes outside, the same computation fails at
  the first step: Σ_h |P̂(h)| ≈ m|P|^{1/2}.
- **The gap.** p₁ ∈ [m^{1/2−2δ}, m^{1/2}] is covered by neither Type I (level m^{1/2−δ}) nor Type II. The integers
  p₁p₂ ≤ m with p₁ in the gap have density ≈ 8δ/log m. They must be bounded above by a sieve in the range
  p₁ ≤ m^{1/2−δ−ε} and by something else beyond. Whether the resulting δ exceeds 1/16 needs the Harman-sieve
  computation, which I did not do.

Value for EOS: none directly. It is a check that the Buchstab + moment architecture closes when the
moment is available, and it puts the obstruction for primes in one line.

## 7. Route 3 in more detail (heuristic)

With Type I level m^θ for A_a, Thm BH works for η with Ce^{−θ/η}/η < 1 − e^{−γ} − η·e^{−γ}/η·(…); in linear-sieve
terms, with s = θ/η one needs f(s) − (1 − θ₀-part) > 0. Illustration with exact linear-sieve functions:
θ = 1/2 − ε, η = 1/8 gives s = 4, f(4) = (e^γ/2)·log 3 = 0.978, Φ(m, m^{1/8}) ≈ 4.49·m/L, so the Buchstab sum
must be bounded above within a factor ≈ 1.26 of its mean, on the range [m^{1/8}, m^{1/2}] only. That is still
a parity-breaking statement (a sieve gives ≥ 2), but H4(η) with η ≈ 1/8 is a weaker hypothesis than with
η ≈ 1/100, by the factor η⁸ in the constant. So special moduli would not remove the need for H4; they would
make its constant reasonable and its range short.

For the level itself I only have the back-of-envelope in §1: for m = ℓ^k the balanced bilinear Kloosterman
sum should save about m^{1/24} from one p-adic van der Corput step (heuristic), so the improvement of the
overall exponent 15/16 has to come from re-optimising Fouvry–Shparlinski's Type I/II split with short-sum
bounds available. I did not do this.

---

## 8. What was actually established

- **Proved** (from the quoted inputs T1 and FL): Thm BH; Cor H4 and Cor LD given Lemma 2.2; Prop S; Prop Q;
  items 1–4 of §5.
- **Sketched**: Lemma 2.2 (main-term comparison; standard sieve estimates for rough numbers in intervals);
  §6 (Type I and Type II ranges for the model).
- **Heuristic**: §5 item 5 (Hardy–Littlewood range M ≤ m^{1/5−ε}); §7; the claim in §3.3 that a random
  pairing-avoiding set satisfies H4.
- **Computed**: §4.1 (direct δ Gaussian with Poisson correction; conjugate strongly non-Gaussian),
  §4.2 (Buchstab sum within 5% of its mean for all 4·10⁶ classes at m = 4000037).
- **Not established**: H4 or LD, in any range of M ≤ √m, under GRH or otherwise. No new unconditional or
  GRH-conditional partial result toward EOS.

## 9. Not checked

- T1 and FL are quoted; the theorem number for FL is recalled. The uniformity of T1 in d is as stated in
  `lit/02` §1.2.
- The absolute constants η₀, C₁ were not computed. The constant 0.4 uses 1 − e^{−γ} = 0.4385 and a small
  enough η.
- Lemma 2.2 is a sketch; the top blocks near √m were treated by a size argument only.
- Proposition Q is stated for prime-count weights; the script uses Λ-weights. The difference is a factor
  log M in the normalisation.
- §5 item 5: the centred singular-series computation was not done, and the uniform Hardy–Littlewood
  hypothesis is stronger than what is usually called standard.
- Novelty of Route 2's target relative to Baker (2012) and later work is [UNVERIFIED].
- The 4% variance deficit in §4.1 is unexplained.

## 10. Questions for the team (round 2)

1. Skeptics: is there a parity-type set **supported on primes** (route A §4.2's deterministic variant) that
   satisfies T1 and H4? Prop S says no if it has no primes in a·P*^{-1}, but only for sets obeying T1 exactly
   as stated. Check the d = 1 cardinality for that construction.
2. Function-field side: over F_q[t] the analogue of Σ_c δ_I(c)⁴ counts points on
   {p₁u₁ ≡ p₂u₂ ≡ p₃u₃ ≡ p₄u₄}. Is it within reach of Sawin's method for q large, and does it need fewer
   Betti-number bounds than the pointwise statement? If H4 is easier than EOS there, that is evidence it is
   a real intermediate statement and not a restatement.
3. Is there any single-modulus fourth-moment result for bilinear prime sums at length ≥ √m (the modular
   range of §5 item 5)? I know none.
