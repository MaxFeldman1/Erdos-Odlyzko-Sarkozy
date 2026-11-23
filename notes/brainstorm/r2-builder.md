# Round 2, builder persona: combining the round-1 routes

Written 2026-11-23. Standing hypothesis: GRH for Dirichlet L-functions. Anything more is flagged **[EXTRA]**.
Scripts (scratch, not in the repo; rerun or copy if wanted):
`/private/tmp/claude-501/-Users-maxfeldman-Desktop-maths-research/9e4c9912-0c7a-4fa9-a228-3de7c709a385/scratchpad/builder/`
(`atlas.py`, `var2.py`, `mers.py`).

**Status tags.** *proved* = complete argument here. *sketched* = steps indicated. *heuristic* = not a proof.
*computed* = script output. [UNVERIFIED] = recalled. Results quoted from round 1 keep the status they have there.

Notation as in `00-setup.md` and round 1: G = (Z/mZ)^*, φ = φ(m), L = log m, P = primes ≤ m not dividing m,
ρ = |P|/φ, λ = |P|²/φ, L′ = φ/|P|, N(a) = #{pq ≡ a}, N⁻(b) = #{p ≡ b q}, A_a = {a p̄ mod m}.

---

## 0. Summary

**No combination I found reaches EOS.** I tried to make the round-1 objects feed each other in six ways. Three
attempts collapse to the same wall and are recorded as no-go computations (§3.2) so nobody repeats them. Three
produce something new:

| # | Item | Sources combined | Status |
|---|---|---|---|
| Atlas (§2) | **Singular-series formula for the quotient counts N⁻(u/v)** on classes of small height: N⁻(u/v)/λ ≈ Σ_j w_j 𝔖_j with explicit weights and local factors. Thm G is the entry b = −1 (𝔖 = 0). | D Thm G, wildcard W2 numerics, combinatorial R3, analytic §4.1 | heuristic (Hardy–Littlewood); computed to 0.5–1% |
| §2.3 | The atlas explains three numbers left unexplained in round 1: analytic's 4% variance deficit (predicted 0.9558 / 0.9534 / 0.9935, observed 0.9546 / 0.9556 / 0.9965); wildcard's max N⁻(b)/λ = 1.29 at b = 2/3, 3/2 (predicted 1.320 flat, 1.299 with log weights); combinatorial's 0.88–0.95 for even-order subgroups. | same | computed |
| §2.4 | **Quantified conjugation barrier.** The quotient problem has an O(1) singular series (values from 0 to 1.32 at small height), the product problem has none of relative size above m^{−1/2} (automorphic Route K). So a conjugation-blind method cannot prove N(a) ~ λ, nor N(a) ≥ cλ for any c above about 0.5, at classes that look generic. | D Thm G + automorphic K | heuristic; computed |
| §2.5 | **Mersenne-type moduli m = 2^n ± 1.** The coset of ⟨2⟩ is the set of digit rotations; \|H\| = n ≈ 1.44 L is just above the certificate threshold L′. The certificate T(H) < 2\|H\|λ holds for every n in 13..24 (ratio 0.54–0.77), so **every unit a mod 2^n ± 1 is p·q·(±)2^j for 13 ≤ n ≤ 24** (proved by computation through combinatorial's Prop M1). In general it needs a prime-pair constant c < 2 − L′/\|H\| on average. | combinatorial R3 + wildcard W2 | computed; conditional statement proved |
| §3 | For EOS proper: analytic's Buchstab reduction is the only round-1 object that passes all six barriers. I record what the other personas can supply to it (Type I level from TD and special moduli), and a no-go lemma for the block Type II sum. | analytic R1 + automorphic TD + wildcard Lemma M | proved (no-go); proposals |
| §4 | Parity-pure ladder: WL restated as "Liouville on the multiplication table in a progression", trivial for half the classes; explicit Kloosterman kernel for square moduli. | combinatorial R1 + D Prop P + automorphic K | proved (small) |

**Honest probabilities.** EOS from any combination below: under 1%. Atlas formula correct as a heuristic: 90%
(numerics agree to 1%). A clean conditional theorem for Mersenne-type moduli under a flagged prime-pair
hypothesis: 80%, but it is a coset statement and is deletion-stable, so it is not on a path to EOS.

---

## 1. What each persona's object can supply to another

| Supplier | Object | Consumer | What it supplies | Outcome |
|---|---|---|---|---|
| wildcard | Lemma M (Hölder + k-fold energy) | analytic LD | bound for heavy classes inside a Sidon-like arc | **no gain**: returns Chebyshev with the true variance, times log L (§3.2) |
| wildcard | Sidon multipliers | analytic BH | average the Buchstab sum over a·s̄ | **no gain**: threshold stays L² log L (§3.2) |
| automorphic | TD (summed Type I level 1/2 for A_a) | analytic BH | larger η, shorter Type II range | parameter gain only; H4 still needed (§3.1) |
| D / automorphic | Thm G, Kloosterman singular series | combinatorial R3, wildcard W2 | the true value of the pair constant C_s on small heights | the atlas (§2) |
| analytic | Prop Q (conjugate fourth moment too large) | atlas | Prop Q is the height-1 column of the atlas | consistent |
| D | Prop P (linearisation, h² \| m) | automorphic K | Kloosterman kernel becomes explicit | identity (§4.2), no power |
| combinatorial | K4 (wrap-around multiplicativity) | wildcard Thm W | turn ternary representations into WL witnesses | **fails**: the witnesses leave the m×m table by exactly the slack L² (§4.1) |
| geometer | Schur–Mellin pieces | analytic H4 | function-field test of H4 | uninformative at large q (logs are free there); at fixed q it is the same problem (§3.3) |

---

## 2. Combined route B1: the quotient atlas and certificates for structured targets

### 2.1 The formula (heuristic)

Let m be prime (composite m needs extra local factors at ℓ | m), u, v nonzero coprime integers with v > 0,
|u|, v small compared with m, b = u/v ∈ G. Then p ≡ b q (mod m) with 0 < p, q < m means v p − u q = j m
for an integer j, and the pairs (p, q) on the line with index j form a one-dimensional lattice
(p, q) = (p₀ + u t, q₀ + v t).

**Local factors (proved, elementary).** For a prime ℓ ≠ m let ν_ℓ(j) be the number of t mod ℓ with
(p₀ + ut)(q₀ + vt) ≡ 0. Then
- ℓ ∤ uv: ν_ℓ = 1 if ℓ | j and 2 otherwise (the two roots coincide iff v p₀ ≡ u q₀, i.e. ℓ | jm);
- ℓ | uv: ν_ℓ = ℓ if ℓ | j (one coordinate is always divisible by ℓ), and 1 otherwise.

So the Hardy–Littlewood constant of line j is 𝔖_j = 0 if j = 0, or gcd(j, uv) > 1, or (uv odd and j odd), and otherwise

  𝔖_j = Π_{ℓ | uv} ℓ/(ℓ−1) · [2 if uv is odd] · Π_{ℓ ≥ 3, ℓ ∤ uv} (1 − 2/ℓ)/(1 − 1/ℓ)² · Π_{ℓ ≥ 3, ℓ | j, ℓ ∤ uv} (ℓ−1)/(ℓ−2).

**Weights (proved).** The integer points of [0,m)² with v p ≡ u q are (p, q) = m·({ut}, {vt}) for t = s/m,
and on that point j = u⌊vt⌋ − v⌊ut⌋ (for u > 0; replace u by |u| and adjust signs for u < 0). So the share of
line j is w_j = meas{t ∈ [0,1) : u⌊vt⌋ − v⌊ut⌋ = j}, a step function with breakpoints at multiples of 1/u, 1/v.

**Atlas (heuristic, Hardy–Littlewood for each line).** N⁻(u/v)/λ ≈ c(u/v) := Σ_j w_j 𝔖_j. A sharper form
replaces w_j by Σ over the integer points of line j of 1/(log p · log q).

Examples: c(−1) = 0 (Thm G: the only line is j = 1, odd, with uv odd). c(2) = 0.660. c(2/3) = c(3/2) = 1.320
(lines j = ±1 carry weight 1/2, 𝔖 = 3 · 0.8802). c(−2/3) = 0.440. c(3) = 0.880.

### 2.2 Numerical check (computed, `atlas.py`)

m = 1000003. "flat" is c(b); "log-weighted" is the sharper prediction of the count itself.

| b | N⁻(b) | N⁻/λ | c(b) flat | log-weighted prediction | obs/pred |
|---|---|---|---|---|---|
| 2/3 | 7961 | 1.292 | 1.320 | 8002 | 0.995 |
| 2 | 3825 | 0.621 | 0.660 | 3848 | 0.994 |
| 4 | 5859 | 0.951 | 0.990 | 5825 | 1.006 |
| 3 | 5113 | 0.830 | 0.880 | 5083 | 1.006 |
| 5/3 | 7176 | 1.165 | 1.174 | 7162 | 1.002 |
| −1 | 0 | 0 | 0 | 0 | — |
| −3 | 5265 | 0.854 | 0.880 | 5278 | 0.998 |
| −2 | 4284 | 0.695 | 0.660 | 4299 | 0.997 |
| −2/3 | 3160 | 0.513 | 0.440 | 3139 | 1.007 |
| 6/5 | 6434 | 1.044 | 1.056 | 6416 | 1.003 |
| 7/5 | 5133 | 0.833 | 0.845 | 5224 | 0.983 |
| −5/7 | 7494 | 1.216 | 1.207 | 7472 | 1.003 |
| 15/7 | 7157 | 1.162 | 1.167 | 7190 | 0.995 |
| 101/103 | 5884 | 0.955 | 0.960 | 5938 | 0.991 |
| −997/1009 | 6137 | 0.996 | 1.001 | 6190 | 0.991 |

At m = 4000037 the rows b = −3, −1/3, −2, −2/3, 6/5, 7/5, −5/7 agree to 0.1–0.7% (only these were run). The deviations are of the size of
the statistical noise √N⁻. The flat form is off by up to 15% on lines confined to a corner of the box
(b = −2/3), which the log weights correct.

### 2.3 Three round-1 numbers explained (computed, `var2.py`)

1. **Analytic §4.1, "variance 4% below Bernoulli, unexplained".** Exactly,
   Var_c π_I(c) = ρ(1−ρ)|I| + ρ² Σ_{u ≠ v ∈ I} (N⁻(u/v)/λ − 1) (proved: expand Σ_c π_I(c)²).
   Inserting the atlas for all pairs of primes u ≠ v in I:

   | block | #I | var/Bernoulli observed | atlas prediction | mean of c − 1 over pairs |
   |---|---|---|---|---|
   | (100, 200] | 21 | 0.9546 | 0.9558 | −0.0259 |
   | (1000, 2000] | 135 | 0.9556 | 0.9534 | −0.0041 |
   | (2000, 2200] | 24 | 0.9965 | 0.9935 | −0.0033 |

   The deficit is the negative secondary term in the mean of the prime-pair singular series over the ≈ M
   admissible lines (the Montgomery–Soundararajan effect [UNVERIFIED attribution]): mean(c − 1) ≈ −κ·(log M)/M,
   so Σ_{v ≠ u}(c − 1) is a constant ≈ −0.55 per u for a dyadic block and the relative deficit is ≈ 0.55·ρ·(block
   width/M). It tends to 0 like 1/log m and has no bearing on H4, as the analytic note guessed.
2. **Wildcard §4, max_{b≠1} N⁻(b)/λ = 1.292 and 1.295 at b = 2/3, 3/2.** Atlas: 1.320 flat, 1.299 log-weighted.
   The maximum of c(b) over all b is attained at height 3 because uv = 6 gives the largest factor Π_{ℓ|uv} ℓ/(ℓ−1)
   that still leaves half of the weight on admissible lines (heuristic; I checked heights up to 15 only).
   So the expected value of wildcard's sieve constant is **C_s = 1.32**, below 2 with room.
3. **Combinatorial R3, off-diagonal mean 0.88–0.95·λ for even-order subgroups.** Such H contain −1 (c = 0) and,
   when they contain small integers, classes like 2, −2 (c = 0.66). For |H| = 10 the entry −1 alone lowers the
   mean by 1/9. Consistent; not recomputed for their moduli.

### 2.4 Quantified conjugation barrier (heuristic; computed)

Thm G says N⁻(−1) = 0. The atlas says this is one entry of a table with relative fluctuations of order 1:
N⁻(−2/3) = 0.51λ, N⁻(2) = 0.62λ, N⁻(2/3) = 1.29λ at m = 10⁶. On the product side, automorphic Route K finds
secondary terms of relative size m^{−1/2} only, and `compute/RESULTS.md` has min_a N(a)/λ ≈ 0.95 at this size.
Consequences for the checklist:
- A conjugation-blind method cannot prove an asymptotic N(a) ~ λ, nor a lower bound N(a) ≥ cλ with c > 0.51 (the observed N⁻(−2/3)/λ; the flat atlas value is 0.44),
  at classes of height 2 or 3. Barrier (6) is not confined to a = −1.
- Any model of {S(χ)} used as a heuristic must reproduce Σ_χ χ̄(b)|S(χ)|² = φ·c(b)·λ for small-height b while
  giving Σ_χ χ̄(a)S(χ)² ≈ φλ(1 + O(m^{−1/2+ε})). The moduli |S(χ)|² carry an O(1/L′) correlation with χ(b) for
  every small-height b (Cor G1 is the case b = −1). The phases of S(χ)² must cancel all of them.

### 2.5 Mersenne-type moduli: the smallest natural coset (computed; conditional statement proved)

Combinatorial's Prop M1: N(aH) ≥ 2|H|λ − T(H), T(H) = Σ_{h∈H} N⁻(h). Wildcard's hierarchy: cosets have Wiener
norm 1, so the threshold is |H| ≈ L′. For m = 2^n − 1 the subgroup H = ⟨2⟩ = {1, 2, …, 2^{n−1}} has order
n = L/log 2 ≈ 1.44 L > L′, and multiplication by 2 is cyclic rotation of the n binary digits. For m = 2^n + 1,
H = ⟨2⟩ = {±2^j} has order 2n. In this family the geometric progression of wildcard's Linnik format **is** a
coset, and T(H) = Σ over necklaces of (number of prime rotations)².

**Proposition B1 (proved from M1).** Let H = ⟨2⟩ mod m, and suppose the off-diagonal mean
c̄ := (|H| − 1)^{-1} Σ_{h ∈ H, h ≠ 1} N⁻(h)/λ satisfies c̄ < (2|H| − L′)/(|H| − 1). Then every unit a mod m is
p·q·2^j with p, q ∈ P. For m = 2^n − 1 with φ/m ≈ 1 the condition is c̄ < 1.31 + o(1); in general it is below 2.

*Proof.* T(H) = |P| + (|H|−1)c̄λ and |P| = L′λ; M1 gives N(aH) > 0. ∎

**Computed (`mers.py`), all n from 13 to 24, both signs:**

| m | φ/m | \|H\| | L′ | T(H)/(2\|H\|λ) | c̄ | needed c̄ < |
|---|---|---|---|---|---|---|
| 2^17 − 1 | 1.000 | 17 | 10.70 | 0.747 | 0.919 | 1.456 |
| 2^19 − 1 | 1.000 | 19 | 12.08 | 0.760 | 0.934 | 1.440 |
| 2^23 − 1 | 0.979 | 23 | 14.55 | 0.769 | 0.946 | 1.429 |
| 2^24 − 1 | 0.396 | 24 | 6.16 | 0.599 | 0.981 | 1.819 |
| 2^16 + 1 | 1.000 | 32 | 10.02 | 0.594 | 0.902 | 1.741 |
| 2^23 + 1 | 0.667 | 46 | 9.91 | 0.574 | 0.953 | 1.824 |
| 2^24 + 1 | 0.984 | 48 | 15.32 | 0.618 | 0.937 | 1.717 |

The certificate ratio is 0.54–0.77 in all 24 cases, so **for 13 ≤ n ≤ 24 every unit mod 2^n ± 1 is p·q·2^j
(with ±2^j for the plus sign)** (proved by computation). The off-diagonal mean c̄ is 0.89–0.98, with
N⁻(2)/λ = 0.62–0.66 for prime-like m as the atlas predicts.

**What stops a proof.** The condition is an average prime-pair upper bound with constant below 2 − L′/|H|.
For small j the count N⁻(2^j) is over 2^{j−1} lines and the Selberg sieve gives constant 4 [UNVERIFIED which
constant is available uniformly in the number of lines]; under Elliott–Halberstam one gets 2 + ε, which still
misses. So this is the hypothesis "C_s < 2" of wildcard W2 and route C §6, in the family where it is needed
with the largest margin. **[EXTRA]** I did not find a digit-theoretic argument: prime pairs (q, rotation of q)
are a binary problem of the same type as reversible primes, where only upper bounds of the right order are
known [UNVERIFIED].

### 2.6 Barrier checklist for B1

| Barrier | Coset/atlas statements | As a route to EOS |
|---|---|---|
| (1) random pairing-avoiding set | pass: avoiding one class leaves every coset of order ≥ 2 covered | **fail**: nothing is said about one class |
| (2) deletion of ≈ 1/L of the primes | pass: emptying a coset of order ≈ 1.44 L costs more than all of P | **fail**: coset counts are deletion-stable |
| (3) parity | **not beaten**: the requirement is a pair constant below 2 − L′/\|H\| | fail |
| (4) A* | not applicable (no sieve on A_a) | fail |
| (5) Prop L | consistent: M1 with equality is L's model; the atlas is extra information about primes (pair correlations on small heights), outside sup + Parseval, but only heuristic | fail |
| (6) Thm G | pass: the certificate uses N⁻ only, and Thm G helps it when −1 ∈ H | **fail, provably**: conjugation-blind |

Extra hypotheses: a prime-pair constant below 2 on average over H (beyond GRH and beyond Elliott–Halberstam).
First step: done (atlas, numerics, Prop B1). Next: write the lattice sieve lemma with the explicit constant for
N⁻(u/v) in terms of 𝔖_j (wildcard's first step), now with the target shape known.

---

## 3. Combined route B2: the Buchstab reduction with inputs from the other personas

Analytic's Thm BH is the only round-1 object that passes all six barriers, at the price of hypothesis H4(η).
I tried to lower that price with the other personas' tools.

### 3.1 What does help: the Type I level (proposal)

In Thm BH the admissible η is tied to the Type I level θ of A_a by C e^{−θ/η}/η < 1 − e^{−γ}. With θ = 1/16,
η ≈ 1/100. Two round-1 objects raise θ:
- **Automorphic TD.** The sieve remainder with well-factorable weights is a trilinear Kloosterman sum over
  (p, d₁, d₂); TD's first lemma is exactly a bound for it. A level θ = 1/4 would allow η ≈ 1/20 (s = 5).
- **Analytic Route 3 / D §4.2 (m = ℓ^k).** Short incomplete Kloosterman sums; the Cauchy–Schwarz diagonal caps
  the level at 1/4 [UNVERIFIED, from D].

With η ≈ 1/20 the hypothesis becomes: for blocks I ⊂ [m^{1/20}, √m], Σ_c δ_I(c)⁴ ≤ (1/40)⁴ρ⁴|I|⁴|𝒦|. The saving
asked is still five logs; only the constant (by 5⁸) and the range improve. **This does not change the
probability of EOS.** It makes the conditional theorem cleaner: "Type I level 1/4 for A_a + H4(1/20) ⇒ EOS".

### 3.2 What does not help: three no-go computations (proved)

Write a block of the Buchstab sum as a ternary count: Σ_{k∈𝒦} δ_I(a k̄) = T(a) − ρ|I||𝒦|,
T(a) = #{(p, p₁, k) ∈ P × I × 𝒦 : p p₁ k ≡ a}. Thm BH needs T(a) − ρ|I||𝒦| ≤ (η/2)ρ|I||𝒦| for each block.

**Lemma N (proved; the block is below the ternary conservation law).** Any bound of the form
(sup of one of |S|, |U|, |𝒦̂|) × (Parseval for the other two), with every sup replaced by its ideal value
(square root of the size of the set), gives |T(a) − ρ|I||𝒦|| ≤ (|P||I||𝒦|)^{1/2}. With |I| ≍ λM/log M and
|𝒦| ≍ (m/M)/log M this exceeds the required (η/2)ρ|I||𝒦| by the factor ≍ L^{3/2}/√λ.

*Proof.* (|P||I||𝒦|)^{1/2}/(ηρ|I||𝒦|) = η^{-1}(φ L′/(|I||𝒦|))^{1/2} and |I||𝒦| ≍ λm/(ηL)². ∎

The three attempts, each of which ends at Lemma N or worse:
1. **Arc energy (wildcard Lemma M on the arc).** For 𝒮 ⊂ a·𝒦^{-1} the two-weight Lemma M gives
   Σ_{c∈𝒮} δ_I(c) ≤ (M_S M_U)^{1/2k}(|P||I|)^{(1−1/2k)/2} E_k(𝒮)^{1/2k}. The arc consists of inverses of primes
   k > √m, whose energy is not diagonal (products exceed m). Swapping roles (arc = {a p̄₁ : p₁ ∈ I}, which is
   Sidon-like up to order log m/log M) gives, for generic subsets, the heavy-class count ≤ C k L^{C/k}|P||𝒦|/T²:
   Chebyshev with the true variance, which under GRH alone costs three more logs to establish. That is a real
   but small gain (GRH + Lemma M recovers the "true variance" Chebyshev bound on Sidon-like arcs), and it is
   still three logs short of Cor LD.
2. **Averaging the Buchstab sum over Sidon multipliers.** Σ_{s∈𝒲} B(a s̄) has error ≤ C√k(|P||R||𝒲|)^{1/2} with R
   the rough composites; the needed η ρ|R||𝒲| forces |𝒲| ≥ C k L²/η. Same threshold as Thm W. The sieve does not
   lower the L² wall for Sidon targets, nor the L wall for cosets.
3. **Switching (Chen).** Bound B(a) from above by sieving the outer prime p over the set {a·(p₁k)^{-1}}. The
   switched set has Type I level about min(M, √m/M)^{1/2} ≤ m^{1/8} by Cauchy–Schwarz and Weil, but the upper
   sieve constant is ≥ 2 against the needed 1 + η. Same conclusion as analytic §5.

**Remark (proved).** Treated as one binary problem, B(a) = #{(p, n) : p ∈ P, n ∈ R, pn ≡ a} with R the z-rough
composites ≤ m, |R| ≈ e^{−γ}m/(ηL). Parseval gives error (|P||R|)^{1/2} against the needed ηρ|R|: a deficit of
≈ 1.3 L/√η, **one log**, the same as EOS (Prop L). The five logs of H4 and three of LD are the cost of cutting
into blocks and Hölder; the true distance is still one log, and no block decomposition I tried recovers it.

### 3.3 The function-field test asked for by the analytic persona (heuristic)

For q → ∞ at fixed degree, Sawin's pointwise bound already gives H4, and powers of the degree n (the "logs")
are free against q^{1/2}; a moment computation by Deligne–Katz gains q^{−1/2} once and loses a Betti number of a
fourth fibre power, so its threshold in q is worse than the pointwise one. At fixed q (the F_2[t] bed) the log
structure is identical to Z and H4 is as hard as over Z. So the function-field analogue cannot tell whether
H4 is easier than EOS. What F_2[t] can test cheaply is the **Gaussian law of δ_I at larger relative sizes**
(n up to 23 gives M ≫ n⁵ blocks), which the integer numerics could not reach.

### 3.4 Barrier checklist for B2

Identical to analytic Route 1, which I re-checked: (1) pass (proves a ∈ R·P for the avoiding set R); (2) pass
(|A_a| = |P| exactly; deletion breaks Type I at d = 1); (3), (4) pass conditional on H4 (Prop S); (5) pass
(H4 is not sup + Parseval), with the caveat of the Remark above: all the difficulty is the one log of Prop L in
another form; (6) pass (Prop Q; atlas §2.4 gives the reason: small-height classes). Extra hypotheses: H4(η)
**[EXTRA]**, now with η ≈ 1/20 if the level is raised. First step: TD's trilinear Kloosterman lemma.
Probability of EOS: under 1%.

---

## 4. Combined route B3: the parity-pure ladder

### 4.1 WL as Liouville on the multiplication table (proved)

Combinatorial's WL(a): some n < m with λ(n) ≠ λ(ι_a(n)). Let a₀ ∈ [1, m) be the residue of a and
𝕋 = {xy : 1 ≤ x, y < m}.

**Lemma B3 (proved).** WL(a) fails iff λ(N) = +1 for every N ≡ a (mod m) in 𝕋. EOS(a) holds iff some
N ≡ a (mod m) in 𝕋 is a product of two primes below m.
- n = 1 gives N = a₀: **WL(a) holds whenever λ(a₀) = −1**, i.e. for about half of all classes, trivially.
- For j < √m, N_j = a₀ + jm lies in 𝕋 unless it is prime or (a j-smooth number) × (a prime > m). So WL(a) holds
  as soon as some N_j, j < √m, is composite with Ω(N_j) odd and P⁺(N_j) < m.

*Proof.* n·ι_a(n) = N ≡ a with both factors below m, and λ(N) = λ(n)λ(ι_a(n)). ∎

So WL is "the least composite N ≡ a (mod m) with λ(N) = −1 inside the table is below m²": a Linnik-type
problem for λ at level 1/2 (automorphic's analogy with the least prime ≤ q² applies verbatim). The progression
{a₀ + jm} has perfect Type I data in j, and Type I data cannot force an odd Ω: this is parity with nothing else
attached, as the combinatorial note says.

**Attempted combination (fails).** Thm W gives a ≡ p q s for small s; K4 would turn (p, q, s) into the witness
N = (ps)·q with λ = −1, but ps < m is needed and the variant of Thm W with p ≤ m/s needs |𝒲| ≥ K(φ s/m)²L², more
classes than there are primes below s. The witnesses leave the table by exactly the slack L² of the
conservation law.

**Ladder (proposal).** D₄ (D §4.3) → unbalanced D₄ (automorphic FE) → TD (automorphic) → WL (combinatorial) →
EOS. Each rung removes one barrier from the next: D₄ has only the one-log Parseval deficit; TD adds a prime;
WL adds parity and removes the log; EOS has all. A method that cannot do rung k cannot do rung k+1. Nobody has
done rung 1.

### 4.2 Square moduli: the Kloosterman kernel is explicit (proved identity; computed)

For an odd prime ℓ and (c, ℓ) = 1: S(1, c; ℓ²) = ℓ Σ_{w² ≡ c (ℓ²)} e(2w/ℓ²) (classical stationary phase; verified
numerically for ℓ = 7, 11, 13 to 10^{-12}). So for m = ℓ² the unit part of automorphic's dual expansion is

  m^{−2} Σ_c Π(c) S(1, ac; m) = m^{−3/2} Σ_{w ∈ G} Π(ā w²) e(2w/m),

supported on c in the square class of a. This is D's Prop P (inversion is affine on fibres mod ℓ:
p̄ ≡ 2b̄ − b̄²p for p ≡ b) in the dual variable. No bound follows; it identifies the two pictures and says that
for square moduli the "Kloosterman singular series" of Route K is a sum of additive characters at square roots.

### 4.3 Barrier checklist for B3

(1) pass vacuously (no subset of G). (2) pass for the statements (exact). (3) **not beaten**: WL is pure parity.
(4) not applicable. (5) not beaten: WL is the Parseval equality case. (6) pass. Extra hypotheses: none proposed.
First step: rung 1 (unbalanced D₄), which belongs to the automorphic persona. Probability of EOS: under 1%.

---

## 5. Verdicts on the round-1 proposals (constructive standpoint)

| Proposal | Verdict | Reason and suggested use |
|---|---|---|
| Analytic R1 (Buchstab + H4) | alive | Only route passing all six barriers. H4 is out of reach; the distance is still one log (§3.2 Remark). Combine with TD for the level (§3.1). |
| Analytic R2 (shrinking box) | alive | Provable theorem, not EOS. Use it to debug the Buchstab bookkeeping (Lemma 2.2). |
| Analytic R3 (special moduli) | alive | Feeds §3.1; for ℓ² use §4.2 and Prop P to compute the level exactly. |
| Automorphic K | wounded | Dead as a route; Lemmas H, K and the dual singular series are kept and are the product-side half of §2.4. |
| Automorphic TD | alive | Its first lemma is the Type I input B2 wants. |
| Automorphic FE | alive | Rung 1 of the ladder. |
| Geometer G1 | alive | Function-field only. Cannot test H4 (§3.3). |
| Geometer G2 | wounded | Characteristic-2 structure, no transfer by design. |
| Geometer G3 | dead | Agreed; the diagnosis (constructibility) stands. |
| Combinatorial R1 (rigidity, WL) | alive | Calibration problem; WL is trivial for half the classes and is a Linnik-type problem for λ otherwise (§4.1). |
| Combinatorial R2 (entropy) | dead | Autopsy accepted. |
| Combinatorial R3 (coset certificate) | alive | Becomes concrete on Mersenne-type moduli (§2.5); needs a pair constant below 2. Deletion-stable. |
| Wildcard W1 (Thm W) | promising | A theorem. Zero for EOS. Lean target: Lemma M. |
| Wildcard W2 (Linnik format) | alive | The atlas gives the expected C_s = 1.32 and the shape of the sieve lemma. For m = 2^n ± 1 the progression is a coset. |
| Wildcard W3 (F_q[t]) | alive | Clean unconditional statement; run the F_2[t] check together with the δ_I Gaussian test of §3.3. |

---

## 6. For round 3

1. **Skeptic's target.** The atlas is Hardy–Littlewood line by line. Check uniformity as the height grows to
   √m (number of lines ≈ height) and the claim that max_b c(b) = 1.320.
2. **Is the atlas usable as a hypothesis?** HL(pairs, height ≤ H) with a constant below 2 − L′/|H| on average
   gives coset statements only. I see no way to make a pair hypothesis on the quotient side speak about a
   single product class; Thm G forbids it.
3. **The one-log question.** B(a) as a binary problem P × R is one log from Parseval (§3.2). R has bilinear
   structure and full Type I data up to level 1; P has neither. Is there a formulation that uses the structure
   of R without paying the L^{3/2} of Lemma N?
4. **F_2[t].** Compute δ_I moments and the necklace certificate analogue (H = ⟨t⟩ mod t^n − 1) there.

## 7. Not checked

- The Selberg/Elliott–Halberstam constants quoted in §2.5; the attribution of the secondary term in §2.3.
- The atlas for composite m (extra local factors at ℓ | m); the Mersenne table uses raw counts only.
- §3.1's claim that level 1/4 gives η ≈ 1/20 uses analytic's constant C′ without recomputation.
- Whether Lemma B3 or Prop B1 are in the literature.
