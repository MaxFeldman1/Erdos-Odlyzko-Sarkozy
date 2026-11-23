# Round 2, technical referee

Written 2026-11-22. Standing hypothesis: GRH for Dirichlet L-functions. Anything more is flagged **[EXTRA]**.
I read all five round-1 write-ups in full and re-derived the lemmas listed below by hand.
New scripts and outputs: `compute/brainstorm/referee/` (`m2_oddchar_full.py`, `var_deficit.py`, `out_*.txt`).

**Status tags.** *checked* = I re-derived the argument and found it correct. *proved* = complete argument here.
*heuristic* = not a proof. *computed* = output of a referee script. [RECALLED] = literature from memory, not re-read.

---

## 0. Summary

**No proposal reaches EOS, and no proposal claims to.** No wrong inequality was found in any lemma marked "proved".
The errors found are in accounting, in one inference from numerics, and in two logical claims about what a statement calibrates.

| # | Finding | Affects | Status |
|---|---|---|---|
| F1 | "Five logs" (H4) and "three logs" (LD) are measured from the *true* variance of δ_I, which is not known under GRH. From the GRH bound the persona quotes, the gaps are 8 and 6 logs. | analytic 1 | checked |
| F2 | The gap in F1 can mostly be closed: wildcard's Lemma M + Lemma S give, under GRH, Σ_c δ_I(c)² ≤ k·(C L³)^{1/k}·\|P\|\|I\| whenever M^k < m. So the true gaps are 5 + 3/k and 3 + 3/k logs. | analytic 1, wildcard 1 | proved (§1.2) |
| F3 | The "unexplained 4% variance deficit" is explained in scaling: deficit ≈ c(λ)·ρ with c(1) ≈ 0.56, independent of M for M ≤ √m, linear in λ for small λ. It is O(1/log m) and is the deficiency of the off-diagonal mean of N⁻(u₁/u₂) at small height. | analytic 1 | computed; mechanism heuristic |
| F4 | Geometer E2, odd characteristic: the m = 2 piece has **rank exactly 4 with monodromy O(4)**, not "rank ≥ 3". Moments 1, 3, 15, 105 are those of O(4), and \|D₄′(a) − Q²\| < 4Q for every a at p = 101, 211, 401, 1009. The characteristic-2 "collapse" is 4 → 2. | geometer 1, 2 | computed |
| F5 | Geometer §3.3: "N(a) = const + ¼D₄′(a) + O(√Q)" is not uniform in a. At a = 1, Q = 128 the persona's own table has e = 3.92 while \|D₄′ − Q²\|/Q ≤ 2. | geometer 1 | checked from their output |
| F6 | **EOS does not imply WL.** WL asks for Ω(n·ι_a(n)) odd; an EOS pair has Ω = 2. "If the team cannot do WL it cannot do EOS" is a heuristic, not an implication. | combinatorial 1 | proved (one line) |
| F7 | WL is not free of a size deficit under GRH. Every GRH route to WL that I tried sits at volume exactly m² with losses m^{o(1)}, worse than log powers. | combinatorial 1 | checked (§4.1) |
| F8 | Theorem W, Cor W1, Cor W2, the energy inequality, Lemma B, Theorem W-Linnik (given C_s), and the F_q[t] transcription: all exponents and constants re-derived, no error. | wildcard 1–3 | checked |
| F9 | Lemma H and Lemma K re-derived, correct. The correction to D §4.1(iii) stands. | automorphic K | checked |
| F10 | Prop Q's count "−ω(m)" is wrong for composite m (the number of b ≤ B with (b,m) > 1 is not ≤ ω(m)). Correct for prime m. The conclusion is unaffected in order of magnitude. | analytic 1 | checked |

Circularity: I found **no hypothesis that is EOS in disguise**. H4 and LD are strictly stronger than EOS (they imply it unconditionally), a-independent, and I see no reverse implication. Hypothesis V and "C_s < 2" are the route C §6.1 hypothesis, as their authors say.

---

## 1. Analytic persona

### 1.1 Route 1 (Buchstab + Hölder, H4): verdict **alive**

Checked, correct:
- **Thm BH.** Buchstab identity; N(a) ≥ S(A_a, √m) − 2; Lemma 2.1 with D = m^{1/17} (remainder m^{1/17+15/16+o(1)} ≤ m^{1−1/300}, since 1/16 − 1/17 = 1/272); ηB₀ ≈ e^{−γ}m/L; constant 1 − e^{−γ} = 0.4385. The threshold θ₀ ≈ e^γ η is right.
- **(T1) is quoted correctly.** `lit/02` §1.2 states \|#A_a(d) − π(m)/d\| ≤ m^{15/16+o(1)} uniformly in d, (d,m) = 1, tagged READ.
- **(2.1), (2.2), Cor H4.** Positivity does absorb the cut-off. The classes a·k̄ are distinct. Powers of η, λ are consistent.
- **Lemma 2.2 (sketch).** I redid (ii): per block \|I\|²·m/(M² log M) = λ²m/log³M, times L/(2λ) blocks, gives ≤ λm/(η³L²), relative size λ/(η²L) against B₀. Fine. C₁ is a sieve constant of size about 4–8.
- **Cor LD.** The layer-cake sum is 2T_j\|𝒦_j\| as stated.
- **Sizes.** Threshold ≍ η⁴λ⁴ρ⁴mM³/(log M)⁵; Gaussian value 3φρ²\|I\|²; H4 holds in the Gaussian model once M ≥ C(log m)⁵/(λ²η⁴).
- **Prop S.** A correct contrapositive of Thm BH + Cor H4. It applies to route A's A\* (A\* has Type I error O(√(m log m)) and no primes in (D, m], `A-typeII.md` l.234–242).
- **Prop Q.** Correct for prime m. For composite m replace "− ω(m)" by the number of b ≤ m/((1+λ)M) with (b,m) > 1 (F10).
- **Deletion.** S(A′, z) = S(A, z) − N(a) because the deleted elements are primes > z. So the deletion barrier is carried by the d = 1 cardinality, as stated. This is a tautology of the sieve identity, which is the right shape.

Objections.

1. **Log accounting (F1).** §2.3 says "even with the true variance, the trivial bound is ρφ\|I\|³" and counts five logs from there. The GRH-provable bound quoted in the same paragraph is Σ_c δ² ≤ \|P\|·M·L². With it:
   - H4: sup² × variance = \|I\|²\|P\|ML² against η⁴ρ⁴\|I\|⁴\|𝒦\|. Ratio L⁵(log M)³/(η⁴λ²). **Eight logs.**
   - LD: Chebyshev gives \|P\|ML²/T² against \|𝒦\|/4. Ratio ≍ L³(log M)³/(η²λ²). **Six logs.**
   The comparison "five against route A's ten" compares a true-variance count with a count from a provable bound. See §1.2 for the repair.
2. **Nothing below the hypothesis is proved.** Not even the variance asymptotic Σ_c δ_I(c)² ~ ρφ\|I\| is known under GRH. A sieve upper bound for N⁻(u₁/u₂) (wildcard's C_s) gives only Σ_c δ² ≪ ρ²φ\|I\|², the trivial size.
3. **η is tiny.** With level m^{1/16} and the honest fundamental-lemma error e^{−s log s}, s = 1/(17η), one needs η ≈ 1/100 to 1/150. Then θ₀ ≈ 0.02, the H4 constant is (η/2)⁴ ≈ 10⁻⁹, and the Gaussian threshold is M ≥ 10¹²·(log m)⁵/λ². The numerics of §4.2 (η = 1/6..1/3) test a different regime, as the persona says.
4. **The numerics do not test H4.** They test Gaussianity of δ_I at M ≤ 4000, where Q = 90–520 against a requirement Q ≤ η⁴/16. The persona says this. The digest line "COMPUTED … H4 true-looking" should read "Gaussian model supported; H4 untested".
5. **Barrier (5).** "H4 is not sup + Parseval" is true but is a statement about H4, not about a method. Any attempt to *prove* H4 from GRH sup bounds and Parseval is still limited by Prop L. The verdict should be "pass conditional on H4", like (3) and (4).

Is H4 EOS in disguise? No. H4 ⇒ EOS unconditionally (T1 is unconditional). The converse fails in every model I can build: EOS constrains one class at precision "≥ 1", H4 constrains a fourth moment over all of G at many scales. H4 at M ≈ √m in the LD form says: the set of c with #{(p, p₁) : pp₁ ≡ c, p ≤ m, p₁ ∈ I} above (1 + η/4)·mean has fewer than \|𝒦\|/4 ≈ √m/(λ log m) elements. That is a log-power exceptional-set statement for an unbalanced binary problem. It is the same *kind* of difficulty as EOS (log powers, phases), relocated to an a-independent object. That is a fair gain and no more.

### 1.2 Repair of the log count: the variance under GRH (proved; new)

**Proposition R1.** Assume GRH in the form \|S(χ)\| ≤ C₁√m·L for χ ≠ χ0. Let I be a set of primes in (M, M′], coprime to m, and k ≥ 1 an integer with M′^k < m. Then

  Σ_{c∈G} δ_I(c)² ≤ (k!)^{1/k}·(C₁² L³·(1+o(1)))^{1/k}·\|P\|·\|I\|.

*Proof.* Σ_c δ_I(c)² = (1/φ)Σ_{χ≠χ0}\|S(χ)\|²\|U_I(χ)\|². Hölder with exponents k/(k−1) and k:
Σ\|S\|²\|U\|² ≤ (Σ_{χ≠χ0}\|S\|^{2k/(k−1)})^{(k−1)/k}·(Σ_χ\|U\|^{2k})^{1/k}.
First factor: \|S\|^{2k/(k−1)} ≤ M_S^{2/(k−1)}\|S\|², and Σ_χ\|S\|² = φ\|P\| exactly, so it is ≤ M_S^{2/k}(φ\|P\|)^{1−1/k}.
Second factor: Σ_χ\|U\|^{2k} = φE_k(I) ≤ φ·k!·\|I\|^k by wildcard's Lemma S (products of k elements of I are < m, so congruences are equalities).
Multiply and divide by φ: M_S^{2/k}\|P\|^{1−1/k}(k!)^{1/k}\|I\| = \|P\|\|I\|·(k!)^{1/k}(M_S²/\|P\|)^{1/k}, and M_S²/\|P\| ≤ C₁²L³(1+o(1)). ∎

The true value is ρφ\|I\| = \|P\|\|I\|. So under GRH the variance is right up to the factor k·(CL³)^{1/k}:

| block location | k | loss in the variance |
|---|---|---|
| M just below √m | 1 | L³ (the bound the persona quotes) |
| M ≤ m^{1/2}/(1+λ) | 2 | 2·L^{3/2} |
| M ≈ m^{1/3} | 2 (3 needs M′³ < m) | 2·L^{3/2} |
| M ≈ m^η, η ≈ 1/100 | 100 | 100·L^{0.03} |

Consequences.
- LD asks to beat a **GRH-provable** Chebyshev bound by 3 + 3/k logs, and H4 asks for 5 + 3/k logs over a GRH-provable trivial bound, with k = ⌊log m/log((1+λ)M)⌋. The persona's "3" and "5" are correct in the limit of small blocks and off by 3/2 logs at the top blocks.
- An unconditional weak-type bound of the same kind (proved, same Hölder with 1̂_𝔈 in L^{2k/(k−1)}): for 𝔈 = {c : δ_I(c) > T}, \|𝔈\| ≤ (k·\|P\|\|I\|/T²)^{k/(k−1)}. No GRH. It is Chebyshev to the power k/(k−1), so it does not reach LD either.
- This is the only place where two round-1 routes combine into something neither had. It does not touch the fourth moment: Σ_c δ⁴ is a four-fold convolution on the character side and Hölder against \|U\| does not apply.

### 1.3 The variance deficit (F3; computed, `var_deficit.py`)

m = 1000003. var/pred with pred = ρ(1−ρ)ΣΛ², and deficit/(λρ):

| M | λ = 1 | λ = 0.5 | λ = 0.25 | λ = 0.1 |
|---|---|---|---|---|
| 300 | 0.9568 (0.55) | 0.9731 (0.69) | | |
| 1000 | 0.9559 (0.56) | 0.9709 (0.74) | 0.9838 (0.82) | 0.9926 (0.94) |
| 3000 | 0.9562 (0.56) | | 0.9821 (0.91) | |
| 30000 | 0.9810 (0.24) | | 0.9901 (0.50) | |

- Λ-weights and prime-count weights agree to 3 digits.
- For M ≤ √m the deficit is c(λ)·ρ with c(1) ≈ 0.56 and c(λ) ≈ λ as λ → 0. It does not depend on M. The persona's three moduli fit ρ-scaling: 4.5%, 4.1%, 3.8% at ρ = 0.072, 0.071, 0.065.
- Reading (heuristic): the off-diagonal is Σ_{u₁≠u₂}(N⁻(u₁/u₂) − ρ²φ). N⁻(u₁/u₂) counts u₂p − u₁q = jm over even j ≠ 0, \|j\| ≲ M. The singular series averages to 1 over all j including j = 0, and j = 0 (the integer diagonal, one solution) carries excess singular-series mass. So the mean over j ≠ 0 is below 1 by ≍ (log M)/M, and the variance drops by ≍ ρ\|I\|·(log M)/M ≍ λρ. This is the modular form of the −½ log H term in sums of singular series (Montgomery–Soundararajan [RECALLED]).
- It decays like 1/log m and has no bearing on H4.

### 1.4 Route 2 (shrinking box): verdict **wounded**

- The Type I level and the Cauchy–Schwarz + Weil Type II range are right (checked: \|B(c)\| ≤ MK(1/M + √m log m/K)^{1/2}; needs M ≥ m^{2δ+ε}, K ≥ m^{1/2+2δ+ε}).
- The statement "every a is q·x, q ≤ m prime, x ≤ m^{1−δ}" is the same as a bound for Σ_{h ≤ m^δ}\|Σ_{q≤m} e(ah q̄/m)\|. Averaging Kloosterman sums over primes in the frequency h is a standard device (Garaev 2010, Baker 2012, Irving 2013 are in `lit/02` §1.1 for the q-average; I did not find the h-average there). Novelty risk is higher than the persona's 25%. My guess: 10–15% new. [RECALLED, unverified]
- The Bourgain–Garaev energy bound has m^{o(1)} losses. That is harmless in the model, which has power room, and it is the reason the model says nothing about the log-power problem.
- It is not EOS and the persona says so. Its one useful line is the diagnosis Σ_h\|P̂(h)\| ≈ m\|P\|^{1/2} against log m for an interval.

### 1.5 Route 3 (special moduli): verdict **wounded**

Heuristic only, no exponent computed, and the persona's own estimate (m^{−1/24} in the balanced range) is weaker than what is already known. It changes the constant in H4, not the need for it. Overlaps D §4.2. Keep only as a rider on Route 1.

---

## 2. Automorphic persona

### 2.1 Route K: verdict **dead as a route** (the persona agrees); lemmas correct

- **Lemma H (checked).** With C = m, D = −x: Cz_x + D = i, Az_x + B = (−1 + Ai)/m, so γz_x = (A + i)/m with A ≡ −x̄. For D ≠ −x, Im γz_x ≤ 1/(2m) and cosh d ≥ 5/4. For \|C\| ≥ 2m, \|Cz + D\|² ≥ 4. Correct, including the case x² ≡ −1.
- **Correction to D §4.1(iii) (checked).** D's item (iii) is tagged heuristic there. Lemma H shows a fixed kernel isolates c = m, so ≍ m forms suffice. D's verdict is unchanged because (ii) is the operative obstruction.
- **Lemma K (checked).** h = l = 0 gives (m−1)\|P\|²; the two mixed terms give 2\|P\|²; total (m+1)\|P\|². Correct.
- **Kloosterman singular series.** The size check works: at m = 4000037, κ√m/L² = 12.3 and std E ≈ 200 give \|corr\| ≈ 0.06, as reported.
- **θ′² law** is an empirical law (2–3 digits at two moduli). It is not derived.

Objections.
1. "Refines D §1.2: the product problem has a singular series in the dual variable" is fair. The amplitude is √m/L² against λ ≈ m/L², relative size m^{−1/2}. It cannot affect EOS in any class, as the persona says.
2. The barrier table is honest: five fails. One pass on Theorem G is not a route.
3. §1.6 (N and f⋆f differ by computable terms) is sketched and I believe it. It is the same content as analytic's Prop S in symmetric form. The two should be merged.

### 2.2 Route TD: verdict **alive as a side result, dead for EOS**

- The one-log Parseval count is consistent with the general pattern. The reduction to a Kl₂ bilinear form is sketched; I did not verify the Voronoi step.
- "Known bounds save at most about m^{1/4}" and the almost-prime record r = 5 are [RECALLED]; `lit/02` §1.3 tags r = 5 as unverified in the source.
- TD holds for A\*, so it carries no parity information. The persona says so. The 15% for a new almost-prime result is an opinion I cannot check.

### 2.3 Route FE: verdict **wounded**

- No lemma, no experiment. T(χ) ≈ ε_χ·conj T̃(χ) is the approximate functional equation and is not an identity at the sharp cut-off.
- The unbalanced toy sits exactly at the threshold, as claimed (checked by a second-moment count: the number of classes with error ≥ ε√m is ≤ √m/ε², and the family {a/(n₃n₄)} has ≈ √m classes). Its kernel is Kl₂(a·s·r̄), a ratio, so Kowalski–Michel–Sawin bounds for Kl₂(a·mn) with interval supports do not apply directly. 30% is optimistic.
- The analogy with the least prime in a progression under GRH, p ≤ (φ log m)², is correct [RECALLED: Lamzouri–Li–Soundararajan].

---

## 3. Geometer persona

### 3.1 G1 (Schur–Mellin pieces, true ranks): verdict **alive for F_Q[t], nothing for Z**

Checked:
- **L1.** The number of ν ⊢ 2m with empty m-core is C(m,2) + 2m; values ±2 on two runners and ±1 on one; Σχ² = 4C(m,2) + 2m = 2m², the centraliser order of (m,m). The restricted counts C(m,2), (m−1)², (m−1)(2m−3) are mutually consistent: they force m−1 partitions with value ±1 and (m−1)(m−2)/2 with value ±2.
- **L2.** Correct.
- **Tower variance** matches V(m) to three digits. This tests L1 and equidistribution at the level of the fourth moment. It does not test any rank, as the persona says.

**F4. The m = 2 rank in odd characteristic is 4 (computed, `m2_oddchar_full.py`).** The persona sampled random a and concluded "not SU(2), rank ≥ 3". I computed D₄′(a) for **every** a ∈ F_{p²}^× by FFT and normalised t(a) = (D₄′(a) − p²)/p.

| p | var | m4 | m6 | m8 | range of t over all a |
|---|---|---|---|---|---|
| 101 | 0.990 | 2.98 | 14.4 | 95.0 | [−3.87, 3.57] |
| 211 | 0.995 | 2.99 | 14.8 | 102.1 | [−3.79, 3.84] |
| 401 | 0.998 | 3.04 | 15.4 | 108.6 | [−3.91, 3.59] |
| 1009 | 0.999 | 3.00 | 15.0 | 104.8 | [−3.84, 3.97] |

- The trace of a Haar element of O(4) has moments 1, 3, 15, 105: the SO(4) component gives t₁t₂ with moments 1, 4, 25, 196, the other component gives 2cos θ with Sato–Tate moments 1, 2, 5, 14, and the averages are 1, 3, 15, 105. These equal the Gaussian moments through order 8, which is why the persona's moments could not separate "Gaussian" from a small group.
- The range does separate them: \|t\| < 4 for all 10⁴–10⁶ classes at four primes, approaching 4. A Gaussian would reach 5.3 at p = 1009.
- So in odd characteristic the m = 2 second expansion has **four** terms, \|D₄′(a) − Q²\| ≤ 4Q, and in characteristic 2 it has two.

Consequences for G1 and G2.
- The characteristic-2 "collapse" at m = 2 is 4 → 2. In characteristic 2 the observed law is that of the non-identity component of O(4) alone. That is weak evidence for an exponential collapse of ranks, and G2's "the only evidence that this is not absurd" is weaker than it looked.
- Sawin-type bookkeeping at m = 2 (the persona's unverified evaluation 432Q + 60Q^{3/2}) is against a truth of 4Q with no Q^{3/2} term. A factor ≈ 100 at m = 2 is not informative about the exponential rate.

**F5.** In `out_tower_m2.txt` the largest \|e\| is 3.92 at Q = 128 and 2.71 at Q = 2048, at a single class (a = 1), while every other class has \|e\| ≤ 2.27 and 2.08. With \|D₄′ − Q²\| ≤ 2Q for every a, the term the persona calls "const + O(√Q)" must be of size ≍ Q at a = 1. The likely source is Σ_y r₂(y)·1_{U²}(a/y), a curve count that degenerates for special a (heuristic). State §3.3 for generic a.

Other objections.
1. B(m) is defined through r_ν, "its rank, when it is pure of weight m". Purity is not known. The tower data show no weight-(m+1) contribution for the f tested, one f per degree, irreducible over F_2.
2. q₀ ∈ [16, 256] rests on the regular-representation heuristic and on no computed Betti number for m ≥ 3. The 30% is an opinion.
3. There is no transfer mechanism to Z. The persona says so.

### 3.2 G2 (characteristic 2): verdict **wounded**

- The Berlekamp/Swan formula and the Sawin–Shusterman thresholds are recalled, not checked. Only the quadratic case is used.
- By F4 the supporting observation is a factor 2 at m = 2.
- The route has no transfer to Z by design. Its lasting content is the caution C2 (the F_2[t] test bed has parity-breaking structures with no integer shadow), which is correct and should be recorded in D §3.

### 3.3 G3 (geometry over Z): verdict **dead**

Agrees with D §4.1 and §4.10, with no new twist, as the persona says. C1 is correct: binom(m−1, m/2)·Q^{m/4} exceeds Q^{m/2} for Q ≤ 16.

---

## 4. Combinatorial persona

### 4.1 R1 (symmetry space of ι_a): verdict **wounded**

Checked: Lemmas K0–K4, Theorem K5 (the row equation with x_small = 0 is x_{ℓ(n)} + x_{ℓ(ι n)} = 0; coefficient 2 when the two large primes coincide), Corollary K6, and rigidity ⇒ WL.

Objections.

1. **K6 is a tautology.** A dyadic EOS pair {r, r′} is a row of 𝐌_a supported on two pendant columns. The rank statement contains the pair and nothing else. The persona says the route has no mechanism. I agree and add that the reformulation gives no new *necessary* condition either: every statement in §1.3–1.4 is equivalent to listing the edges of Γ_a.

2. **F6. EOS ⇏ WL (proved).** If a ≡ pq then n = p has λ(n)λ(ι_a(n)) = +1. WL needs some n with λ(n)λ(ι_a(n)) = −1, that is an N ≡ a (mod m), N = n₁n₂ with n_i < m, and Ω(N) **odd**. EOS supplies Ω = 2. What EOS excludes is the other symmetry, λ∘ι_a = −λ, and Lemma K3 already excludes that whenever Σ_{n∈U}λ(n) ≠ 0. So WL is a sibling problem (the odd-parity analogue: a ≡ p·q₁q₂ with q₁q₂ < m would do). It is plausible as a calibration problem and it is not a logical prerequisite. The sentences "if the team cannot do this, it cannot do EOS" and "a mechanism that cannot decide WL cannot prove EOS" should be marked heuristic.

3. **F7. WL has a size deficit under GRH, and it is worse than for primes.** The claim "no log deficit" is true only of the target (C_λ(a) ≠ φ). Each route I tried needs volume beyond m²:
   - *Failure of WL is a bias in one progression.* λ∘ι_a = λ ⟺ λ(a₀ + km) = +1 for every 0 ≤ k < m such that a₀ + km has a divisor in (k, m). For k ≤ √m the excluded k are those with a₀ + km = j·(prime), j ≤ k (proved: all prime factors are ≤ k or ≥ m, and the smooth part is ≤ k). So WL fails only if λ = +1 on almost all of {N ≡ a (m), N ≤ m^{3/2}}.
   - *GRH does not exclude that bias.* Σ_{N ≤ x, N ≡ a} λ(N) ≪ x^{1/2}(mx)^{o(1)} is below x/m only for x ≥ m^{2+ε}. The range is x ≤ m².
   - *Ternary relaxation.* p·q·s ≡ a with p ≤ m, qs ≤ m, s ≤ y: main term m/(L² log y), Lemma M error ≍ m·√(k\|𝒲\|)/(L√y)·…, which exceeds the main term for every y. The volume is m².
   - *Large sieve over the classes a·n̄, n ≤ m^θ, with N ≤ m^{1+β}.* Failure of WL forces λ constant on ≈ m^θ classes over m^β terms each. That contradicts the GRH mean square m^{1+β+ε} iff θ + β > 1, and the divisor condition needs θ + β < 1.
   The loss in each case is m^{o(1)} (the GRH bound for λ-sums carries exp(C log m/log log m)), not a power of log. So WL isolates parity from the deletion barrier and from A\*, and it does **not** isolate it from the critical-volume barrier.

4. **Rigidity.** The evidence is clean and small: every class only for m ≤ 2003, 40–60 sampled classes up to 30011, F_2 only above 2003. It is an index-calculus full-rank statement plus the existence of smooth rows in every class, and the second ingredient is the d₄-type toy. So rigidity ⇐ two open statements, one of which is itself at the Parseval threshold. The 2% is fair.

5. Whether WL is in the literature is unverified. "Sign changes of λ in a progression to a large modulus" is a studied topic [RECALLED, no reference checked].

### 4.2 R2 (entropy decrement): verdict **dead**

Lemma E1 and the class-stabiliser lemma are correct. The autopsy is right. Proposition E2 is a sketch whose exponent I did not check, and nothing depends on it.

### 4.3 R3 (coset certificate): verdict **dead for EOS**

- M1 is correct. The threshold check works exactly: T(H) ≈ π + (\|H\|−1)λ_m < 2\|H\|λ_m iff \|H\| + 1 > φ/π, and the computed thresholds 10, 12, 14 against φ/π = 10.54, 12.84, 14.21 fit.
- Hypothesis V is route C §6.1 in group language, as stated.
- **Caution on Hooley's conjecture.** The single-modulus variance asymptotic x log q is conjectured in a range x^{1/2+ε} < q < x^{1−ε} (Friedlander–Goldston), and Fiorilli found deviations from the naive form for q close to x [both RECALLED, unverified]. Hypothesis V is used at q = x/((1+ε) log x), where each class holds about one prime and the variance is governed by the diagonal plus prime pairs p, p + kq with k ≤ log x. "Implied by Hooley's conjecture" should be replaced by "implied by a Hardy–Littlewood pair asymptotic on average over k ≤ log x at one modulus".

---

## 5. Wildcard persona

### 5.1 W1 (Sidon multipliers, Theorem W): verdict **alive** (a correct theorem; 0 as a route to EOS)

Checked line by line:
- **Lemma M.** Exponents: (2r−2)/r = 1/k and 1/r = 1 − 1/2k; powers of φ cancel.
- **Lemma S.** Correct. Needs y^k < m and s ∤ m.
- **Theorem W.** \|𝒲\|m²/(64φ) ≤ (log 4)mL·(C₃²L/log 4)^{1/2k}(k!)^{1/2k}\|𝒲\|^{1/2} gives \|𝒲\| ≤ K₀(φ/m)²L²⌈log L⌉. The inequality is monotone in M and V°, so inserting upper bounds is legitimate. y^k = exp(O((log L)²)) < m.
- **Cor W2.** Σ_χ\|1̂_𝒮\|^{2k} = φE_{2k}(𝒲) needs y^{2k} < m. The output is n_i ≤ K m L(log L)².
- **Comparison with (log m)⁴.** The sup-norm argument needs √y·L ≤ (y/log y)/L′, i.e. y ≥ L⁴(log L)². The gain to L²(log L)² comes from replacing the GRH sup bound on the multiplier by its diagonal high moments. This is a standard large-values device and I believe the result.

Objections.
1. **Novelty is unverified** and the device is standard. Check Banks–Shparlinski and the ternary literature before calling it new.
2. The route is conjugation-blind and cannot reach \|𝒮\| = 1. The persona proves this. The "conservation law" is a heuristic that all current theorems obey.
3. The zero-free-strip variant is tagged unverified by the persona. I did not check it.

### 5.2 W2 (structured targets, Thm W-Linnik): verdict **alive** (one unwritten lemma)

Checked:
- **Energy inequality** and the unconditional bias 1/(89L): \|𝒮\|T²/φ ≤ V°·max\|1̂_𝒮\| gives max ≥ \|𝒮\|m/(64·log 4·φL), and 64·log 4 = 88.7.
- **Lemma B.** F ≥ 1 on ‖θ‖ ≤ 1/(2H′) because \|D_{H′}(θ)\| ≥ 2H′/π there. Diagonal H′\|P\|, off-diagonal ≤ H′²C_sλ.
- **Thm W-Linnik.** Shell sum: each shell contributes (π²/4)φ(2\|P\| + C_sλJ/2^{i+1}); total as stated. The Hölder step uses an *upper* bound for 𝔐 inside 𝔐^{1−1/2k}, which is the right direction. Conclusion \|𝓡\| > C₅²C_s² log L.
- **"Parity is the number 2".** Σ_{χ≠χ0}\|S\|²G(θ_χ) ≤ φĝ(0)\|P\| + (C_s − 1)φλG(0). Correct.

Objections.
1. **The sieve lemma for C_s is not written.** The sketch is standard (reduced basis, λ₁ ≤ C√m so each line carries ≥ c√m points, two linear forms per line). The worst-case singular series is ≪ (uvΔ/φ(uvΔ))^{O(1)} ≪ (log log m)^{O(1)}. I believe it. Until it is written, Thm W-Linnik is "proved given C_s".
2. For g = 2 the hypothesis ord_m(2) ≥ J can fail (m = 2^r − 1 has order r < J). The persona notes the coset fallback and has not written it.
3. The additive-interval corollary depends on an energy bound quoted from memory. Treat as unproved.
4. "\|𝓔\| ≪ L^{2+ε}" needs an inverse theorem with polynomial losses in L. None is known. The 10% is generous.

### 5.3 W3 (F_q[t], all q): verdict **alive**

Checked: M ≤ 2q^{n/2} (at most n − 1 inverse zeros, prime powers negligible), exact Parseval, Lemma M gives \|𝒮\|^{2k} ≤ n^{2k}·4n·E_k(𝒮) (the persona's constants are larger and safe), \|𝒲\| ≤ e·n² log n·(1+o(1)) with k = ⌈log n⌉. For q = 2 this gives d ≈ 2 log₂ n + 2 log₂ log n + C. Correct as a sketch. No computation was run. Novelty unverified. Diagnostic value only.

---

## 6. Cross-proposal consistency

- **Analytic Prop S and automorphic §1.6 are the same fact** (N(a) is determined by Type I data up to a bilinear form in the "flat" part, which parity examples saturate), once in sieve form and once in Fourier form. Neither cites the other.
- **Wildcard's hierarchy and combinatorial R3** give the same threshold \|H\| ≈ L′ for cosets from two derivations and agree numerically. Both reduce to "pair constant < 2".
- **Geometer C1 and combinatorial §1.5 and automorphic FE** all touch the d₄ toy. C1 (smooth sums have worse sup norms at small q; over Z, GRH gives m^{1/4}exp(C log m/log log m)) contradicts any plan that treats the toy as "logs only". Combinatorial §1.5 says "logs only, no parity" for the smooth-row problem. That should read "m^{o(1)} in sup-norm steps".
- **Three personas independently hit volume = m².** Wildcard's conservation law, combinatorial's Parseval equality case, automorphic's "least prime ≤ m²" analogy. F7 adds WL to the list.

## 7. New ideas from the referee pass

1. **Proposition R1 (§1.2)** as a standing lemma: under GRH the second moment of every Type II block count δ_I with M^k < m is correct up to k(CL³)^{1/k}. Cheap to formalise (Lemma M + Lemma S). It makes LD's "beat Chebyshev by three logs" a statement about a provable Chebyshev bound.
2. **Rank by range, not by moments.** F4 shows that the full-class maximum of the normalised error identifies the rank (4 in odd characteristic, 2 in characteristic 2) where eight moments could not. Run the same full-class computation for each Schur piece t_ν separately at m = 3 (three pieces), over F_Q with Q^3 ≤ 2^{27}. If max\|t_ν\| stabilises as Q grows, that is r_ν. This is the first experiment that can measure B(3).
3. **Prove \|D₄′(a) − Q²\| ≤ 4Q** in odd characteristic (and ≤ 2Q in characteristic 2) by identifying the rank-4 orthogonal object. The S₄-quotient of {Π(τ + α_i) = a} is an affine plane, because the equation is linear in the elementary symmetric functions. A natural guess (heuristic) is a tensor induction of H¹ of an elliptic curve from F_{Q²}, which has monodromy O(4) with the swap as the non-identity component. That would be the first sharp second expansion in the notes.
4. **Replace WL by a problem that is a logical prerequisite.** F6 shows WL is not implied by EOS. A calibration problem that EOS does imply and that keeps WL's virtues (no deletion barrier, no A\*): "for every a there is n ∈ U with Ω(n) + Ω(ι_a(n)) ≤ 2r" for fixed r, pointwise in a. For r large this is the almost-prime statement (known, Type I only). The least r for which a GRH proof exists is the honest measure of the parity distance. This is automorphic TD's target in combinatorial language.
5. **H4 in F_Q[t] for large Q** (the analytic persona's question 2) is the right test of whether H4 is an intermediate statement. I add a sharper form: Σ_c δ_I(c)⁴ counts points on a variety with an S₄ × (S_d)⁴ symmetry, so by L1-type bookkeeping only the pieces of type (d,d,d,d) enter. If their number is polynomial in d, as C(m,2) is for EOS, the function-field H4 is no easier than EOS there, and H4 is a restatement in that setting.
