# Referee report on `notes/routes/C-log-exponent.md`

Written 2026-11-22 by an adversarial referee. Nothing in the refereed file was edited.
Verdict tags: CORRECT / CORRECT WITH FIXES / WRONG / UNCHECKED.
Evidence tags: *re-derived* = I redid the argument by hand; *computed* = checked by a script in `compute/verifyC/`;
*Lean* = typechecked against the project's Mathlib; *fetched* = read from the web this session through a summarising fetch tool
(so second-hand: I did not read the PDF myself); [RECALLED] = from memory.

## 0. Bottom line

- **H (`GRHSmoothBound`) is a true consequence of GRH, exactly as written in Lean. No change to the Lean statement is needed.**
  The proof in §1 is correct up to three cosmetic slips (R1–R3 below). No counterexample exists in the range tested
  (20 moduli, all characters, 1 ≤ x ≤ 10⁶); the worst observed ratio is 1.0570, at q = 1, x = 3.
- **Theorem S and Corollary A1 are correct as deductions from H.** Every inequality in D0–D7 checks. I found no error in the
  constants, in the φ-versus-m bookkeeping, in the handling of prime powers, or in the handling of primes dividing m.
- **Novelty of A1: not in the literature I could find, but it is a two-line corollary of a classical-type estimate**
  (smoothed GRH variance of primes over residue classes, plus pigeonhole; §3 below). It should be presented as an observation, not as a new method.
  Theorem E at X₁ = X₂ = m is Banks–Shparlinski Theorem 1.4; the extra factor φ/m is already in their proof.
- Theorem B and Proposition L are correct as stated, with one small gap in the proof of L (R6).

## 1. Hypothesis H

### 1.1 The Lean statement — CORRECT (Lean, re-derived, computed)

I typechecked the four declarations of §1.5 in a scratch file importing `EOS.Statement` (`lake env lean`, cache only, no Mathlib compilation).
All elaborate; `GRHSmoothBound` uses only the three standard axioms. Three probes also pass:

- `Real.log (2 * q)` is definitionally `Real.log (2 * (q : ℝ))`.
- For `q = 1` every character equals `1` (`Subsingleton`), so the main term x/2 is always present there, as it must be: the sum is ψ̃(x) for ζ.
- `(1 : DirichletCharacter ℂ 4) 2 = 0`. So `χ = 1` means the principal character χ₀ mod q, which vanishes at non-units. It is not the constant function 1.

Point by point, as the brief asked:

| Feature | Verdict | Reason |
|---|---|---|
| Cesàro weight (1 − n/x), sum over n ≤ ⌊x⌋ | correct | n = 0 contributes Λ(0) = 0. The weight is ≥ 0 on the range and vanishes at n = x, so ψ̃ is continuous in x. |
| Main term x/2 only for χ = χ₀ (imprimitive for q > 1) | correct | ψ̃(x, χ₀) differs from ψ̃(x) for ζ by at most Σ_{p∣q} log p · ⌊log x/log p⌋ ≤ ω(q) log x ≤ 1.07 √x log q. This is absorbed. |
| Range x ≥ 1 | correct | For 1 ≤ x < 2 the sum is empty; the claim is x/2 ≤ C √x log(2q), true for C ≥ 1.03. No lower bound on x in terms of q is needed, because the bound is an upper bound and ψ̃ is trivially ≤ 1.04 x. |
| Bound C √x log(2q) | correct | log(2q) ≥ log 2 > 0, so q = 1 is not degenerate. With log q instead, q = 1 would be false. |
| Uniform in q ≥ 1, including q = 1, 2 | correct | q = 1: RH for ζ. q = 2: the only character is χ₀, reduced to ζ. `[NeZero q]` excludes q = 0. |
| Imprimitive nonprincipal χ | correct | Same comparison with the inducing primitive character χ\*, and log q\* ≤ log q. |

A necessary condition on the constant: **C ≥ 1.0570** (q = 1, x = 3, where |ψ̃ − x/2| = 3/2 − (log 2)/3). The remark in §1.4 that "the true maximum is
≈ 0.37 √x log m" concerns χ ≠ χ₀ at x ≈ m only. It must not be read as a value of C_H.

### 1.2 The proof in §1 — CORRECT WITH FIXES (re-derived; constants computed)

The design choice that matters is sound: the contour stops at Re s = 1/4, and imprimitive characters are handled by comparing sums, not L-functions.
Consequently none of the following is ever met, and I confirm none is needed:

- the zeros of the Euler factors Π_{p∣q}(1 − χ\*(p)p^{−s}) on Re s = 0 (the explicit formula is applied to primitive characters only);
- the poles of 1/(s(s+1)) at s = 0 and s = −1;
- the trivial zeros, including the one at s = 0 for even primitive χ.

As an independent check that these omitted terms are what the notes say, I verified the full Cesàro explicit formula for ζ numerically
(x/2 − Σ_ρ x^ρ/(ρ(ρ+1)) − ζ′/ζ(0) + ζ′/ζ(−1)/x − Σ_k x^{−2k}/(2k(2k−1)), 400 zero pairs) against direct summation:
agreement to 2·10⁻³ or better at x = 1, 1.5, 2, 10.5, 100, 1000.3, which is the size of the truncated zero tail.

Step by step:

| Item | Verdict | Comment |
|---|---|---|
| (F1) Mellin kernel | CORRECT | Residues 1 at s = 0 and −1/y at s = −1; both sides are 0 at y = 1. |
| (F2) and (1.1) | CORRECT | Davenport ch. 12 (17)–(18); equation numbers [RECALLED], content standard. The sum is over zeros of ξ(s, χ), so the trivial zero at 0 is not included. |
| (F3), (F4) values | CORRECT | −ζ′/ζ(3/2) = 1.50524, −ζ′/ζ(2) = 0.56996, ψ(3/4) = −1.08586, ψ(5/4) = −0.22745. Re ψ(z) ≤ log\|z\| held on a grid in Re z ≥ 1 (max of the difference −4·10⁻¹¹, at large \|z\|). I did not prove this inequality; only an absolute constant depends on it. |
| Lemma 1.1, Σ 1/(1+γ²) ≤ ½ log q + 0.82 | CORRECT | The constant is 0.81914. |
| Lemma 1.1, Σ 1/\|ρ(ρ+1)\| ≤ (2/3) log q + 1.1 | CORRECT WITH FIX **R1** | The constant is (4/3)·0.81914 = 1.0922 ≤ 1.1. The bound 1/\|ρ(ρ+1)\| ≤ (4/3)/(1+γ²) is true. |
| Lemma 1.2, (1.2) and (1.3) | CORRECT | 1/16 + u ≥ (9/4 + u)/36 holds with equality at u = 0; 10.5 · (1/3) = 3.5. |
| Lemma 1.2, horizontal lines | CORRECT WITH FIX **R2**, **R3** | |
| Prop. 1.3 | CORRECT | Residue of −ζ′/ζ(s) x^s/(s(s+1)) at s = 1 is x/2. The integral on Re s = 1/4 converges absolutely. |
| Theorem 1, primitive case and q = 1 | CORRECT | x^{1/4} ≤ √x for x ≥ 1. |
| Theorem 1, imprimitive case | CORRECT | ω(q) ≤ log q/log 2 and log x ≤ (2/e)√x give 1.062 √x log q. |
| Zero-sum convergence | CORRECT | Absolute, from Lemma 1.1. No conditionally convergent sum appears, which is the point of the Cesàro weight. |

Fixes:

- **R1.** "(1+u)²/((¼+u)(9/4+u)) is decreasing in u ≥ 0" is false. The ratio equals 1 + (7/16 − u/2)/((¼+u)(9/4+u)); it falls to 0.9375 at u = 2.75 and then
  rises back to 1. The conclusion "≤ 16/9 for u ≥ 0" is true: the ratio is decreasing while it is ≥ 1, and it is < 1 afterwards. Replace the word "decreasing" by this.
- **R2.** For complex χ the zeros are not symmetric about the real axis, but the contour has sides at +T and −T. Choose T ∈ [T₀, T₀+1] at distance
  ≥ 1/(4N₀+2) from every γ **and every −γ** (at most 2N₀ points to avoid), or use independent heights T_j⁺, T_j⁻. Nothing else changes.
- **R3.** In the last line of Lemma 1.2 the factor "2" should be 7/4 = |s₁ − s|. Harmless.

Citations: Banks–Shparlinski Lemma 2.5 is (fetched) a bound for the *prime* sum ϑ̃(x, χ) ≪ √x log q, for **nonprincipal** χ mod q and x ≥ 2, derived from
Montgomery–Vaughan (13.28). It does not cover χ₀ or q = 1, and it is not about Λ. So the docstring's "Literature: … Lemma 2.5" supports only part of H.
The self-contained proof of §1 covers all of it. Suggested docstring wording: "nonprincipal case: Banks–Shparlinski Lemma 2.5; principal case: RH for ζ, same argument."

### 1.3 Numerical test of H — no violation (computed)

Script `compute/verifyC/check_H.py`, output `compute/verifyC/out_check_H.txt`. It evaluates
|ψ̃(x, χ) − [χ = χ₀] x/2| / (√x log 2q) for all characters mod q, at every integer x ≤ 10⁶ and at interior points of every interval [N, N+1)
(64 points for N < 2000, 4 beyond, plus the left limit). Arithmetic is float64; the worst point for each q was recomputed with 50-digit mpmath and agreed to all printed digits.

| q | worst ratio | at x | character |
|---|---|---|---|
| 1 | **1.05696** | 3 | trivial |
| 2 | 0.66473 | 5 | χ₀ |
| 3 | 0.48558 | 5 | χ₀ |
| 4 | 0.44315 | 5 | χ₀ |
| 5 | 0.34144 | 7 | χ₀ |
| 8 | 0.33236 | 5 | χ₀ |
| 12 | 0.37138 | 11 | χ₀ |
| 13 | 0.24611 | 49 | nonprincipal |
| 101 | 0.33295 | 855199 | nonprincipal |
| 2310 | 0.33192 | 24413 | nonprincipal |

(Also q = 7, 9, 11, 15, 16, 24, 30, 60, 210, 30030: see the output file; all below 0.36.)

Reading: for small q the worst case is always the principal character at a tiny x, where ψ̃ is still nearly 0 and the "error" is just x/2.
That is the regime where a wrong main term or a wrong range of x would show up, and it does not. The overall worst case is 1.0570.
This is a consistency test over a finite range. It is not evidence for GRH-scale uniformity in q; that rests on the proof.

## 2. The deduction (D0–D7, Theorem S, Corollary A1)

All re-derived. In addition `compute/verifyC/check_deduction.py` (output `out_check_deduction.txt`) tests D1, Parseval, D4(a), D5, D6 for **composite**
m = 2310, 3003, 4096, 6006, 30030 at six pairs (X₁, X₂) each. The author's script covers prime m only. The Fourier coefficients are obtained as
eigenvalues of the convolution matrix, with no character table, so the test is independent of the author's code. All 30 cases pass.

| Claim | Verdict | Comment |
|---|---|---|
| D0 (prime powers) | CORRECT | Σ_{k=2}^{⌊log₂x⌋} θ(x^{1/k}) ≤ (log 4)√x · log₂ x = 2√x log x. Valid for any χ, since \|χ\| ≤ 1 and the weight is in [0,1]. |
| D1 (orthogonality) | CORRECT | pq ≡ a with a a unit forces p, q ∤ m, so R(a) is exactly the convolution of Θ(X₁;·) and Θ(X₂;·) on G. χ mod m kills p ∣ m automatically, so ϑ̃(X, χ₀) = T(X). |
| Exact Parseval (distinct residues), D4(a) | CORRECT | A prime p ≤ X ≤ m with p ∤ m satisfies 1 ≤ p ≤ m − 1 (p = m would divide m). Distinct integers in [1, m−1] are distinct mod m. Computed: Σ_b Θ(X;b)² equals Σ_p log²p (1−p/X)² to 10⁻¹⁵ relative at X = m for all five composite m, and exceeds it by factors 1.9 to 32 for X > m, as it should. |
| D2 (main term) | CORRECT | The primes dividing m cost at most Σ_{p∣m} log p ≤ log m. H is used at q = 1 with log 2. T(X) ≥ X/8 needs X ≥ 8L, which is in the hypotheses. |
| D3 (sup bound) | CORRECT | H at q = m, then D0 with log X ≤ 3L. C₃ = C_H(1 + log 2) + 6 is right (uses L ≥ 1, i.e. m ≥ 3). |
| D4(b) | CORRECT | Average ≤ max. |
| D5 (Cauchy–Schwarz, mixed ranges) | CORRECT | sup over χ on the X₁ factor, then Cauchy–Schwarz on the X₂ factor alone: (1/φ)(φ−1)^{1/2}(φ V°)^{1/2} ≤ V°^{1/2}. The two ranges never need to match. Computed ratio max\|E\|/(M₁√V₂) is between 0.02 and 0.10. |
| D6, D7 | CORRECT | Fourier coefficients of E are ϑ̃₁ϑ̃₂ at χ ≠ χ₀ and 0 at χ₀. |
| Weight positivity | CORRECT | Every term of R(a) is ≥ 0, and is > 0 exactly when p < X₁ and q < X₂. So R(a) > 0 gives primes strictly below the ranges; the theorems state ≤, which is weaker. |
| Theorem A | CORRECT | √1.39 = 1.179; 64 · 1.18 = 75.5 < 76, so "≥" in the hypothesis gives the strict inequality D7 needs. X₁ ≥ Kφ²L³/m → ∞ since φ ≫ m/log log m. |
| **Corollary A1** | **CORRECT** | X₂ = m, X₁ = Kφ²L³/m ≤ K m L³ ≤ m³. The Lean statement `CoveredByAsym m m (K * φ^2 / m * L^3)` parses as ((Kφ²)/m)·L³ and matches. φ and m are used correctly: the main term is X₁X₂/(64φ), the error has no φ, so the threshold is φ²L³/X₂ with X₂ = m. |
| Corollary A2 | CORRECT | log X₂ = θL. The endpoint "p ≤ K log m, q ≤ Kφ²L log L" is right up to the value of K. |
| **Theorem S** | **CORRECT** | \|E\| ≤ M·V°^{1/2} ≤ M² ≤ C₃²XL² against X²/(64φ). The threshold 64C₃²φL² has φ, not m. X ≤ m³ holds. The Lean statement matches. |
| Theorem E | CORRECT | Direct from D7. |
| Remark after Thm E (√log saving for X₂ < √m) | CORRECT | For q, q′ < √m the product qq′ < m is determined as an integer, so each class has at most 2 ordered representations; the fourth-moment bound 2φ(Σw²)² follows. Not used elsewhere. |

No fix is required in §2–§3. Two remarks for the formalisation:

- H is used at exactly two moduli: q = 1 (for D2) and q = m (for D3). D2 could instead use any Chebyshev-type lower bound; then H is needed only for χ ≠ χ₀ mod m.
  A weaker named hypothesis "nonprincipal characters only, plus ϑ̃(X) ≥ X/4 for large X" would suffice, and it is exactly what Banks–Shparlinski Lemma 2.5 states.
- The D0 bound θ(y) ≤ y log 4 is the only number-theoretic input besides H. The notes flag its Mathlib status as unverified; I did not check it either.

## 3. Novelty

Searches run: two web searches on the conjecture with GRH and asymmetric ranges; the arXiv abstract pages of 2610.19597 and 2609.37434; the HTML full text of 2610.19597 (fetched).
I did not search MathSciNet or Google Scholar citation lists, and all readings of the papers are second-hand through the fetch tool.

**Banks–Shparlinski, arXiv:2610.19597 (fetched).**
- Theorem 1.3 (GRH case): every a is ℓ₁ℓ₂ℓ₃ with ℓ₁, ℓ₂ ≤ q and ℓ₃ ≪ (log q)⁴. Three primes.
- Theorem 1.4 (GRH case): the number of classes not of the form p₁p₂, p_i ≤ q, is ≪ (φ(q)/q)(log q)³. The inequalities in their §4.2 give φ(q)²q⁻²(log q)³ before they weaken it with φ ≤ q.
- No two-prime statement with asymmetric ranges, and none with p₁, p₂ ≤ q(log q)².
- Lemma 2.5: as described in §1.2 above.

**Banks, arXiv:2609.37434 (fetched, abstract only).** Unconditional result in Granville's random model for range q^Θ, Θ > 3/4. No GRH theorem about actual primes. Not relevant to A1.

**Assessment.**

- **Corollary A1: not found in the literature. But it is easily implied.** Proof in two lines from the standard smoothed GRH variance:
  by D4(b), Σ_b (Θ(X;b) − T/φ)² = V°(X) ≤ C₃² X L², so the number of classes b ∈ G containing no prime < X is ≤ 64 C₃² φ² L²/X.
  The classes a p⁻¹, p ≤ m, p ∤ m, are π(m) − ω(m) ≥ m/(2L) distinct classes. If X > 128 C₃² φ² L³/m, one of them contains a prime q < X. ∎
  This is the Turán-type estimate (Turán 1937 proved the sharp-cutoff form with log⁴ under GRH [RECALLED]) followed by pigeonhole.
  It is the same Cauchy–Schwarz as D5 read in physical space. With the existing sharp-cutoff `GRHBounds` the same two lines give q ≤ K φ² L⁵/m.
  So A1's content beyond the classical is the exponent 3 in place of 5, and that comes entirely from the Cesàro weight in H.
  I would call A1 a new *statement* and a routine *proof*. It is fair to record it; it is not fair to call it a new technique.
- **A1 versus Banks–Shparlinski Theorem 1.3.** Neither implies the other. They use two primes ≤ q plus a third of size log⁴ q; A1 uses one prime ≤ m and one of size m log³ m.
  Both are the same mixed L^∞–L² argument, applied to different factorizations.
- **Theorem S** (p, q ≤ Kφ log² m). Not found in the literature. The lit notes already list it as a two-line modification of EOS 1987 Cor. 3. Same status as A1: new statement, routine proof.
- **Theorem E at X₁ = X₂ = m** is Banks–Shparlinski Theorem 1.4. The factor (φ/m)² versus φ/m is not an improvement: it is in their proof. The [UNVERIFIED] tag in §0 of the notes can be replaced by this.
- **Theorem B.** Not found. It needs the sieve, so it is the least routine of the four. I did not find it in Banks–Shparlinski.

## 4. Theorem B and Proposition L

**Theorem B — CORRECT** (re-derived; the sieve theorem itself is taken on trust).
- D4(c): Π_{p∣km}(1+1/p) ≤ (m/φ)·σ(k)/k and Σ_{k≤Y} σ(k)/k ≤ ζ(2)Y are right, and the total 2ζ(2)C₅X²/φ follows.
- The range m < X₂ ≤ φL is nonempty only when φ(m) log m > m, which holds for large m. Then log X₂ ≤ 2L and V°(X₂) ≤ (2.78 + C₄)X₂L, as claimed.
- **R4 (citation).** Halberstam–Richert Thm 3.11 is stated with the factor Π_{2<p∣h}(p−1)/(p−2), not Π_{p∣h}(1+1/p), and as an asymptotic inequality in x uniform in h. The form used
  ("all x ≥ 2, absolute C₅, factor Π(1+1/p)") follows, since the two products differ by a bounded factor, but it is not the literal statement. The theorem number is [RECALLED] by the author and by me.
  In Lean this must be its own named hypothesis; the notes say so.
- The closing claim "X₁ ≥ KφL² regardless of X₂ … it must with this method" is a statement about D5 only. Correct in that sense.

**Proposition L — CORRECT WITH FIX** (re-derived).
- The construction is right: A ∩ aA⁻¹ = ∅, total mass X(1 − r/φ), sup norm 2X/φ, and Fourier bound (X/φ)(K₀√φ + r).
- **R5.** r ≤ 2^{ω(m)+2} is true but loose; the number of square roots of a unit is 0 or at most 2^{ω(m)+1}.
- **R6 (gap).** Spencer's theorem in the quoted form needs M ≥ N and gives K√(N log(2M/N)); to get K₀√φ one needs M/N bounded, i.e. N = (φ−r)/2 ≫ φ.
  This holds because r is 0 or the order of the subgroup {x² = 1}, so r divides φ: either r ≤ φ/2, giving N ≥ φ/4 and M/N ≤ 8, or r = φ, where Θ\* = 0 and the statement is empty.
  Also the coefficients have modulus ≤ 2, not ≤ 1; rescale. Add both sentences.
- The "consequently" paragraph is right: (X/φ)K₀√φ ≤ K₀√c √X L for X ≤ cφL², and (X/φ)r = o(√X L) since r = m^{o(1)}.
- The scope disclaimer in the notes (the model does not show that GRH cannot do better) is accurate and should stay.

## 5. Items not checked

- UNCHECKED: §6 (heuristics), the "asymmetric bound and its inputs" paragraph of §5, and the author's table in §7 (I did not rerun `compute/routeC/routeC_check.py`; my composite-m runs give the same sizes, e.g. M/(√X L) between 0.23 and 0.37).
- UNCHECKED: the assertion in §1.5 that `GRHSmoothBound` is not implied by `GRHBounds`. It is plausible and nothing depends on it.
- UNCHECKED: the literal text of Montgomery–Vaughan (13.28), Davenport ch. 12, Halberstam–Richert 3.11, and Spencer's theorem. I relied on the standard statements.

## 6. List of requested changes to the notes

1. R1: delete "decreasing"; give the one-line argument for ≤ 16/9.
2. R2: avoid both γ and −γ when choosing T (or use separate heights).
3. R3: 7/4 in place of 2.
4. Docstring of `GRHSmoothBound`: say that Banks–Shparlinski Lemma 2.5 covers the nonprincipal case only. Record that any valid C is ≥ 1.057.
5. §0: replace "Thm A / Cor A1 … do not appear in the lit notes" by an explicit statement that A1 is the smoothed GRH variance bound plus pigeonhole (§3 above).
6. §0 and §3: Theorem E at (m, m) equals Banks–Shparlinski Thm 1.4 including the factor (φ/m)²; drop the [UNVERIFIED] tag and the suggestion of an improvement.
7. R4: state the sieve bound in the form actually cited, and derive the Π(1+1/p) form from it.
8. R5, R6: tighten r, and add the two sentences that make Spencer's theorem applicable.

## 7. Files

- `compute/verifyC/check_H.py`, `out_check_H.txt` — numerical test of H.
- `compute/verifyC/check_lemmas.py`, `out_check_lemmas.txt` — constants of §1, the R1 counter-check, the ζ explicit formula, identity (1.1) at s = 3/2 for seven primitive characters.
- `compute/verifyC/check_deduction.py`, `out_check_deduction.txt` — D1, Parseval, D4(a), D5, D6 for composite m.
