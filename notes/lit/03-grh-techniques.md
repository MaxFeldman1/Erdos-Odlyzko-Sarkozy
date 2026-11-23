# 03: GRH techniques at the critical scale, and what lies beyond GRH

Strand: what GRH-conditional techniques exist for saving log powers at the critical scale, what extra
inputs are known, and whether EOS under GRH is "binary-hard".

**Provenance tags** (they matter here):
- **[READ]**: I read the statement in the source (the PDF text or the scanned pages).
- **[READ-2nd]**: I read it as quoted in a later paper I read. The paper is cited, but I did not open the original.
- **[ABS]**: from the arXiv abstract or journal landing page only.
- **[RECALLED]**: from memory and not checked this session. Treat as **[UNVERIFIED]**.
- **[DERIVED]**: my own argument in this note. It is short and checkable, but has not been refereed.

**Mapping to the project's proved / sketched / heuristic / [UNVERIFIED] convention (CLAUDE.md):**
- [READ] and [READ-2nd] items are *proved*, in the cited source.
- [ABS] items are *proved* in the source, but I saw only the abstract.
- [DERIVED] means *sketched*, except where it is labelled "heuristic". The Proposition in §0.1 and the
  wall in §0.2 are sketched proofs. §2.2's n-level-density interpretation, the redacted-prime argument
  in §4, and the √m (log m)^{3/2} truth are *heuristic*.
- [RECALLED] means [UNVERIFIED].

Notation follows `00-setup.md`: G = (Z/mZ)^*, φ = φ(m), and characters χ mod m. I use smooth weights
w ∈ C_c^∞((1/2,1)), w ≥ 0, with Mellin transform W(s) = ∫ w(t) t^{s-1} dt, and define

S_w(χ) = S_w(χ; X) = Σ_n Λ(n) χ(n) w(n/X),

N_w(a) = Σ_{n1 n2 ≡ a (m)} Λ(n1)Λ(n2) w(n1/X) w(n2/X) = (1/φ) Σ_χ χ̄(a) S_w(χ)².

Main term: M = S_w(χ0)²/φ ≈ W(1)² X²/φ. Error: E(a) = (1/φ) Σ_{χ≠χ0} χ̄(a) S_w(χ)².

---

## 0. Verdict on the barrier sketch in 00-setup.md

**The sketch is correct in substance.** The precise picture has three layers, and it is sharper than
"a few powers of log".

| Layer | What is needed | Scale X reached for p, q ≤ X | Status |
|---|---|---|---|
| EOS 1987, GRH, sharp cutoff | pointwise bound |ψ(x,χ)| ≪ √x log² x | X ≍ m (log m)^4 (m prime) | **[READ]** EOS87 Cor. 3 |
| GRH, smoothed | pointwise bound |S_w(χ)| ≪ √X log m | **X ≍ φ(m)(log m)²** | **[DERIVED]**, §0.1 |
| GRH + variance asymptotic (Hooley / Friedlander–Goldston type; a single-modulus pair-correlation input) | V(X;m) ~ X log m for X ≈ φ log m | X ≍ φ(m) log m | conditional on more than GRH; §2.2 |
| **Cauchy–Schwarz / variance wall** | any bound of the form |E(a)| ≤ V | X ≥ (1+o(1)) φ(m) log m > m | **unconditional obstruction**; §0.2 |
| EOS | X = m | needs phase information | open, even under GRH |

So GRH loses **two** logs relative to the best L²-type argument, and the L²-type argument itself loses
**one more** log, a factor of (log m)·φ/m, relative to EOS. The last log is the "binary" one, and no
statement about the sizes |S(χ)| can recover it (§0.2, §4).

### What EOS (1987) actually proves [READ]

Source: P. Erdős, A. M. Odlyzko, A. Sárközy, *On the residues of products of prime numbers*, Period.
Math. Hungar. **18** (1987) 229–239, doi:10.1007/BF01848086. I read the scanned pages, static.renyi.hu/~p_erdos/1987-22.pdf.

- The setting is q prime. They assume Hypothesis H(θ_q, x): no zeros of L(s,χ) with Re s > θ_q and |Im s| ≤ x^{1−θ_q}.
  They quote ψ(x,χ) − E_0 x ≪ x^{θ_q} (log x)² (Prachar).
- **Theorem 1 / Corollary 1.** Under H(θ_q, q), Σ_a (G(a,2) − q)² < c q^{1+2θ_q}(log q)^5. Under GRH, therefore,
  **p1 p2 ≡ a with p_i ≤ q holds for all but c3 (log q)^5 residues a.** The method is Parseval plus
  max_{χ≠χ0} |ψ(q,χ)|² · Σ_χ |ψ(q,χ)|² ≤ (√q log² q)² · 2q² log q, which is the L⁴ bound of the setup note.
- **Theorem 2 / Corollary 2.** H(θ_q, q) with θ_q = 1 − (3+ε) log log q / log q gives F(a,3) > 0 for all a.
  So **GRH implies the ternary statement with p1, p2, p3 ≤ q**. In fact F(a,3) ≫ q²(log q)^{−2}.
- **Theorem 3 / Corollary 3.** Under GRH, **f(c16 q (log q)^4, a, 2) > 0 for all a**, i.e. p1, p2 ≤ c q log^4 q.
  The proof bounds (1/(q−1)) Σ_{χ≠χ0} |ψ(x,χ)|² by max ≪ x log^4 x and compares with x²/q.
- They say the binary conjecture is "almost certainly true, but will be hopelessly difficult to prove" (p. 230).

So the item "check whether this is already in EOS (1987)" has a yes answer: the m(log m)^C statement is
there with C = 4, for prime moduli.

### 0.1 GRH gives X ≍ φ(m) log² m [DERIVED]

**Proposition.** Assume GRH. There is an absolute K such that for all large m and all (a,m) = 1 there
are primes p, q ∈ (X/2, X] with pq ≡ a (mod m), where X = K φ(m) (log m)².

*Proof sketch.*
1. Let χ ≠ χ0 be induced by a primitive χ* mod m* | m. The explicit formula gives
   Σ Λ(n)χ*(n) w(n/X) = −Σ_ρ W(ρ) X^ρ + O_w(1).
   Since W decays faster than any power on vertical lines, and #{γ : |γ − t| ≤ 1} ≪ log(m(|t|+2)),
   GRH gives |S_w(χ*)| ≤ √X Σ_ρ |W(ρ)| ≪_w √X log m.
2. Passing from χ* to χ changes the sum by ≪ ω(m) log X.
3. Hence |E(a)| ≤ (1/φ) Σ_{χ≠χ0} |S_w(χ)|² ≤ max_{χ≠χ0} |S_w(χ)|² ≪ X log² m.
4. The main term is ≥ (1/2) W(1)² X²/φ. It wins once X ≥ K φ log² m.
5. The prime-power contribution is ≪ √X log^4 X, which is negligible.

The improvement over EOS87 (log^4 → log²) is the standard smoothing trick. It removes one log from each
of the two factors S, because Σ_ρ |W(ρ)| ≍ log m while Σ_{|γ|≤x} 1/|ρ| ≍ log m · log x. This is the
same mechanism Bach–Sorenson and LLS use for the least prime (§1). I did not find this exact statement
in the literature; I did not search exhaustively. The constant K can be improved with a
Brun–Titchmarsh positivity trick (§1), but the exponent of log cannot.

The same computation, averaged over a, gives Σ_a |E(a)|² = (1/φ) Σ_{χ≠χ0} |S_w|^4 ≤ max|S_w|² · V.
At X = m, V = Σ_{p≤X} w² log² p ≍ X log X exactly. So **all but O((φ/X)² log³ m) = O(log³ m)
classes are represented at X = m**. This matches **Banks–Shparlinski, arXiv:2610.19597, Thm 1.4**
[READ]: under QRH[q, σ0], |G \ EOS2(q)| ≪ φ(q) q^{−2(1−σ0)} (log q)³. For σ0 = 1/2 this is O(log³ q).
Their Thm 1.3 [READ]: under GRH, every a is ℓ1ℓ2ℓ3 with ℓ1, ℓ2 ≤ q and ℓ3 ≪ (log q)^4. This is the EOS
analogue of "Goldbach numbers in short intervals" (§3.2).

### 0.2 The variance (Cauchy–Schwarz) wall [DERIVED; unconditional]

Write D(b) = θ_w(X; m, b) − main. Then E(a) = Σ_b D(b) D(a b̄), so |E(a)| ≤ Σ_b D(b)² = V(X;m).
With two ranges X1 and X2, |E(a)| ≤ (V(X1) V(X2))^{1/2} and the main term is ≈ X1 X2/φ.

- **For X ≤ m, V is known exactly.** Primes ≤ m are distinct residues, so V = Σ_p w² log² p − M ≍ X log X.
  Hence any argument that ends in Cauchy–Schwarz over b needs √(X1 X2) ≳ φ log m.
  That is impossible with X1, X2 ≤ m, since φ(m) log m ≫ m log m / log log m.
- For X slightly larger than m, V(X;m) is conjecturally ~ X log m. This follows heuristically from
  Hardy–Littlewood on average over the shifts km; see Friedlander–Goldston in §2.2. The wall then sits
  at X ≈ (1+o(1)) φ log m. Reaching it needs more than GRH; GRH alone gives only V ≪ X log² m.
- **Even a "perfectly flat" spectrum does not help.** Suppose |S(χ)|² = X log X for every χ ≠ χ0, the
  smallest value Parseval allows. Choosing the phases arg S(χ) = (arg χ(a) + π)/2 makes
  E(a) = −V ≈ −X log X, which exceeds the main term when X ≤ m. (Real characters contribute O(2^{ω(m)}) terms and can be ignored.)
  **No statement about the moduli |S(χ)| (L^∞, L², L⁴, or distribution) can prove EOS.**
  The needed input is about how arg S(χ)² aligns with χ(a). Section 4 gives a concrete set-level version.

**Minor correction to 00-setup.md.** The Type II threshold "UV ≫ m log^4 m" is for prime-indicator
weights with a sharp cutoff. With Λ-weights and smoothing it becomes UV ≫ m log² m. It still fails,
because uv ≤ m. The asymmetric threshold "y ≫ m log^5 m" likewise drops by smoothing. None of this
changes the conclusion.

---

## 1. Least prime in an AP under GRH

### Statements

- **Titchmarsh (1930)**: GRH ⇒ P(q) := max_a P(a,q) ≪ q² (log q)^4. [READ-2nd, via Kandhil–Languasco–Moree, arXiv:2607.14515]
- **Bach–Sorenson**, Math. Comp. 65 (1996) 1717–1735, doi:10.1090/S0025-5718-96-00763-6:
  GRH ⇒ P(a,q) ≤ (1+o(1))(φ(q) log q)², and explicitly P(a,q) ≤ 2(q log q)². [READ-2nd, LLS §1.2]
- **Lamzouri–Li–Soundararajan**, *Conditional bounds for the least quadratic non-residue and related
  problems*, Math. Comp. 84 (2015) 2391–2412, arXiv:1309.3595; corrigendum Math. Comp. 86 (2017) 2551–2554. [READ]
  - Cor. 1.2: GRH ⇒ P(a,q) ≤ (φ(q) log q)² for all q > 3.
  - Thm 1.4 (coset version): the least prime in a coset aH of index h satisfies
    p ≤ ((h−1) log q + 3(h+1) + (5/2)(log log q)²)², unless p ≤ 10^9.
  - They remark that Brun–Titchmarsh gives (1 − δ + o(1))(φ(q) log q)².
- **Carneiro–Milinovich–Quesada-Herrera–Ramos**, *Fourier optimization, the least quadratic
  non-residue, and the least prime in an AP*, arXiv:2404.08380. [READ]
  - Thm 3: GRH ⇒ limsup P(a,q)/(φ(q) log q)² ≤ C(3)^{−2} < 8/9.
  - Thm 5: C(3)^{−2} > 0.8859, so "we have essentially arrived at the limit of this method".
  - Brun–Titchmarsh enters as the parameter A = 3 in their extremal problem. A = ∞, i.e. no Brun–Titchmarsh, is shown to be sharp for Bach–Sorenson's Chebotarev method.
- **Bruna**, arXiv:2603.25612: generalized Lindelöf ⇒ P(a,q) ≪_ε q^{2+ε}. [ABS]
- **Kandhil–Languasco–Moree**, arXiv:2607.14515 (Jul 2026). [READ]
  - Assume GRH and "Hypothesis 2": F_k(x,T;a) ≪ φ(k) T exp(c1 (log x)^{c2}) for
    exp(c1 (log x)^{c2}) ≤ T < x, uniformly for k up to x·exp(−2c1 (log x)^{c2}).
    This is a pair-correlation hypothesis for zeros of different characters, twisted by χ(a); see §2.3.
  - Then (Thm 4) ψ(x;k,a) − x/φ(k) ≪ √(x/φ(k)) exp(c1 (log x)^{c2}), and (Thm 5) **P(k) ≪ φ(k) exp(B (log k)^A)** with A < 1.
  - Remark 2 (verbatim sense): this "does not bring us closer to establishing Heath-Brown's conjectural
    estimate p(k) ≪ k (log k)²". A wider k-range would contradict Friedlander–Granville.
- **"Almost all a"**: Turán, *Über die Primzahlen der arithmetischen Progression*, Acta Sci. Math.
  (Szeged) 8 (1936–37) 226–235. Usually quoted as: GRH ⇒ P(a,q) ≪ φ(q) (log q)^{2+ε} for all but o(φ(q)) classes a.
  **[RECALLED, UNVERIFIED]**: the search found the paper but not the statement.
  The variance argument reproves it [DERIVED]: #{a : θ(X;q,a) = 0} ≤ V/(X/φ)² ≪ φ² log² q / X under GRH,
  which is o(φ) once X = φ log² q · ψ(q) with ψ → ∞.

### How the log savings work, and where they stop

1. **Smoothing / Riesz means.** Weights like (1 − n/x) or log(x/n) turn Σ_ρ x^ρ/ρ into Σ_ρ x^ρ/(ρ(ρ+1)).
   That sum converges absolutely, to √x · O(log q). This is the whole gain from φ² log^4 to (φ log q)².
   What remains is **√x · #(low-lying zeros) ≍ √x log q**: the worst case where all ≍ log q zeros with
   |γ| ≪ 1 add in phase. GRH says nothing about their phases.
2. **Fourier optimization** of the test function, plus **Brun–Titchmarsh positivity**, only changes constants (8/9, essentially sharp).
3. **Averaging over a**, i.e. the variance, gains a factor φ·(log q)^{−2}/... in the count of bad classes, not in the worst case.
4. **Beyond GRH**: pair correlation across characters (KLM) breaks the "all zeros in phase" worst case
   and wins a power. But it only works when x/q ≥ exp((log x)^{c}), far from the critical scale x/q = (log x)^{O(1)} (see below).

### No GRH result reaches φ(q)(log q)^{1+o(1)} for all a, and the conjectured truth is larger

- **Lower bounds.**
  - Pomerance (1980): P(k) ≥ (e^γ + o(1)) φ(k) log k log₂k log₄k/(log₃k)² for k outside a sparse set.
  - Granville–Pomerance (J. London Math. Soc. 1990): infinitely many APs ℓ mod k with
    p(k,ℓ) ≥ (2 + o(1)) k log k log₂k log₄k/(log₃k)².
  - Prachar and Schinzel give a similar bound for p′(k,ℓ).
  - **Li–Pratt–Shakan**, *A lower bound for the least prime in an AP*, arXiv:1607.02543 [READ]:
    for almost every k, P(k) ≫ φ(k) log k log₂k log₄k/log₃k.
    Their coupon-collector heuristic gives **liminf P(k)/(φ(k) log²k) = 1 and limsup = 2**.
- **Heath-Brown (1978) conjecture**: P(k) ≪ k (log k)². [READ-2nd, KLM]
- **Friedlander–Granville**, *Limitations to the equi-distribution of primes I*, Ann. of Math. 129 (1989) 363–382.
  At the critical scale x/k = (log x)^u, ψ(x;k,a) − x/φ(k) can be ≫ u^{−u} x/φ(k) (Maier-matrix type).
  So a Montgomery-type bound √(x/φ)(log x)^A, uniform for k ≤ x/(log x)^B, is **false**.
  [READ-2nd: Granville's remark quoted in KLM 2607.14515 §1.2]
  Their corrected Montgomery conjecture: ψ(x;k,a) − x/φ ≪ √(x/φ) x^ε for k ≤ x^{1−ε}.
- **Takeaway for EOS.**
  - For the least prime, the truth for **all** a is about φ log² q. That is exactly the scale at which
    GRH plus variance gives **almost all** a.
  - For EOS the conjectured truth is far below m. The coupon-collector heuristic needs
    (X/log X)² ≳ φ log φ, i.e. X ≈ √m (log m)^{3/2} [DERIVED heuristic, UNVERIFIED].
  - Banks, arXiv:2609.37434 [READ], proves the EOS analogue in Granville's random model for q^Θ, Θ > 3/4.
    It fails with positive probability in the Banks–Ford–Tao model, because of a local defect.
  - **EOS is not at the limit of the truth. It sits at the limit of L² methods** (§0.2).

---

## 2. Family averages beyond GRH: pair correlation, n-level densities, variance

### 2.1 What is known

- **Özlük** (1982 thesis; "On the q-analogue of the pair correlation conjecture", J. Number Theory 59 (1996) 319–351):
  pair correlation of zeros averaged over χ mod q **and over q ∈ [Q, 2Q]**. Under GRH it gives ≥ 11/12 simple zeros (weighted).
  [READ-2nd, KLM 2411.19762 §1; journal details RECALLED]
- **Yıldırım (1991)** [READ-2nd, KLM 2411.19762 Thm 1 / Conj. 1]. Define
  F_q^+(x,T;a) = Σ_{χ1,χ2} χ̄1(a) χ2(a) Σ_{0≤γ_j≤T} x^{i(γ1−γ2)} W(γ1−γ2), with W(u) = 4/(4+u²).
  - Theorem: under GRH, F^+ ~ (φ(q)/2π) T log x for q ≤ √x/log³x and x/(q log x) ≤ T ≤ exp(x^{1/4}).
  - Conjecture: F^+ ~ (φ/2π) T log(qT) for smaller T, down to x^η.
- **Kandhil–Languasco–Moree**, *Pair correlation of zeros of Dirichlet L-functions: a possible path
  towards the conjectures of Chowla, Elliott–Halberstam and Montgomery*, arXiv:2411.19762, Math. Ann. 394 (2026), art. 43. [READ intro]
  - Key structural fact: F_q(x,T;a) = ∫ |Σ_χ χ(a) Σ_γ x^{iγ} e^{ivγ}|² e^{−2|v|} dv ≥ 0.
    **It is a Hermitian square.** That positivity is what makes Montgomery's method run.
  - Thm 2: GRH ⇒ F_q ≪ φ(q) T log x for q ≤ x^{1−ε} and x ≤ T ≤ exp(√x).
  - Assuming GRH plus Yıldırım-type pair correlation, they derive Montgomery's conjecture (Friedlander–Granville form) and Elliott–Halberstam.
- **Hughes–Rudnick**, *Linear statistics of low-lying zeros of L-functions*, Q. J. Math. 54 (2003), arXiv:math/0208230. [ABS]
  For the family of χ mod prime q, the m-th moment of a linear statistic is Gaussian when supp f̂ ⊆ [−2/m, 2/m]
  ("mock-Gaussian"). Equivalently, the n-level densities are known for total Fourier support < 2.
- **Fiorilli–Miller**, *Surpassing the ratios conjecture in the 1-level density of Dirichlet L-functions*,
  Algebra & Number Theory 9 (2015) 13–52, arXiv:1111.3896. [ABS]
  - Family: all χ mod q, averaged over Q/2 < q ≤ Q.
  - 1-level density for supp f̂ ⊂ (−3/2, 3/2), with a lower-order term the ratios conjecture misses.
  - Montgomery's conjecture for primes in APs ⇒ the ratios prediction for any finite support.
- **Chandee–Lee–Liu–Radziwiłł**, arXiv:1211.6725: asymptotic large sieve, primitive χ, averaged over moduli. [ABS]
  **Quesada-Herrera**, arXiv:2108.10238: Fourier-optimization bounds for the q-analogue of pair correlation, averaged. [search snippet only]
- **Variance of primes in APs for a single modulus.**
  - Prachar: GRH ⇒ I(x,h,q) ≪ h x log²(qx). [READ, Goldston–Yıldırım (1.4)]
  - **Friedlander–Goldston**, Quart. J. Math. 47 (1996): under RH plus a strong twin-prime (HL) hypothesis,
    G(x,q) = Σ_a (ψ(x;q,a) − x/φ)² ~ x log q for x^{1/2+ε} ≤ q ≤ x. [READ-2nd, Goldston–Yıldırım (1.15)]
    This is "Hooley's conjecture".
  - **Goldston–Yıldırım**, *Primes in short segments of arithmetic progressions*, Canad. J. Math. 50 (1998) 563–580,
    doi:10.4153/CJM-1998-031-9. [READ abstract + pp. 1–3] Under GRH the HL-conditional asymptotics hold
    **for almost all q** (averaged over moduli), and lower bounds of the correct order hold for all q.
    **No GRH upper bound V(x;q) ≪ x log q is known for an individual q.**

### 2.2 Can a family statement control E(a) pointwise in a?

**Untwisted family statistics cannot [DERIVED].** This covers 1- and 2-level densities of
{L(s,χ) : χ mod m}, moments Σ_χ |S(χ)|^{2k}, and the distribution of |S(χ)|.

- These statistics are invariant under any relabelling of the family that commutes with χ ↦ χ̄.
  E(a) = (1/φ) Σ χ̄(a) S(χ)² is not invariant.
- What controls E(a) is the **alignment** between the phase of S(χ)² and the value χ(a).
- A **second-moment** statement, i.e. the variance V(X;m), enters only through |E(a)| ≤ V. That is the
  wall of §0.2: at best it gives X ≈ φ log m (assuming the Hooley/Friedlander–Goldston asymptotic at
  X/m ≈ log m) and never X ≤ m.

**Where the variance sits in the n-level-density picture [DERIVED, heuristic but clean].** Write
Z_χ(X) = Σ_γ W(½+iγ) X^{iγ}. In normalized units γ̃ = γ log m/2π, the factor X^{iγ} has Fourier
frequency α = log X/log m. Then:

- (1/φ)Σ_χ |S_w(χ)|² = (X/φ) Σ_χ |Z_χ|² is a 2-level statistic with Fourier support at (α, −α).
- For X ≤ m (α ≤ 1) it is computable. That is the exact diagonal, consistent with Hughes–Rudnick's
  "total support < 2".
- For X = m(log m)^C we have α = 1 + O(log log m/log m), **just past the edge**. This is the family
  analogue of Montgomery's F(α) at α = 1⁺.
- Pair correlation for the single family mod m in that range would recover one log (GRH → variance wall).

**The twisted statistic that is actually needed.** E(a) = (X/φ) Σ_{χ≠χ0} χ̄(a) Z_χ(X)². EOS at scale X
(weighted) is equivalent to

  (★) |Σ_{χ≠χ0} χ̄(a) Z_χ(X)²| ≤ (1 − δ) W(1)² X, uniformly in (a,m) = 1, for some X ≤ m.

- The triangle inequality, which is all GRH or moment information gives, yields
  Σ_χ |Z_χ|² = (φ/X)(V + small) ≍ φ log X.
- So (★) asks for a saving of a factor ≍ log m · (φ/m) in a sum of φ terms with the twist χ̄(a).
- A random-phase model gives a saving of √φ, so (★) should be true with enormous room.
- Z_χ² pairs zeros of L(s,χ) with zeros of L(s,χ) (equivalently, γ with −γ′ for χ̄), so (★) is a
  **twisted 2-level density at Fourier support (1, 1)**.
- Unfolding with the explicit formula gives back Σ_{n1 n2 ≡ a} Λ(n1)Λ(n2) w w. So **(★) is a
  restatement of EOS, not a reduction.** Likewise, a "ratios conjecture" for Σ_χ χ̄(a) (L′/L)(s1,χ)(L′/L)(s2,χ)
  with power-saving error near the critical line would imply EOS. It is the same statement in zero language.

**Contrast with the linear problem.** KLM and Yıldırım's twisted object for ψ(x;q,a) is a Hermitian
square |Σ_χ χ(a)(…)|², so it is non-negative and Montgomery's positivity method applies. The EOS object
Σ_χ χ̄(a) Z_χ² is an **indefinite** quadratic form: one character, squared, not a modulus squared.
There is no positivity, so the Montgomery/Goldston–Montgomery machinery has nothing to grip.
I found no paper treating Σ_χ χ̄(a)(Σ_ρ X^ρ/ρ)² beyond the triangle inequality.

**The KLM-style pointwise-in-class route is worse than GRH for EOS.** Control of every θ(X;m,b) to
relative error o(1) gives N(a) ≈ Σ_b θ(X;b) θ(X;ab̄)/… ≈ X²/φ for all a, so EOS follows with
p, q ≤ m·exp(B(log m)^A). That is worse than m log² m. Friedlander–Granville forbids anything better
by that route, since at X/m = (log m)^C individual classes genuinely fluctuate by constant factors.
EOS has to use the **sum** over b.

---

## 3. Explicit formula for products; binary problems under GRH

### 3.1 Products of zero sums

- **Averaged Goldbach (Fujii 1991; Languasco–Zaccagnini; Goldston–Suriajaya).**
  Languasco–Zaccagnini, *The number of Goldbach representations of an integer*, Proc. AMS 140 (2012) 795–804,
  arXiv:1011.3198 [ABS]: under RH,
  Σ_{n≤N} R(n) = N²/2 − 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) + O(N log³ N).
  Goldston–Suriajaya, *On an average Goldbach representation formula of Fujii*, Nagoya Math. J., arXiv:2110.14250;
  smoothed GRH version arXiv:2306.04807. [ABS / search snippet]
  **Mechanism [DERIVED]:** averaging over the target N turns the zero–zero cross term into
  Σ_{ρ,ρ′} N^{ρ+ρ′} Γ(ρ)Γ(ρ′)/Γ(ρ+ρ′+2). The Beta factor decays, so the double sum converges
  absolutely and RH bounds it trivially. Pointwise in N there is no such decay.
  The EOS analogue is averaging over a, which gives only the O(log³ m) exceptional-set results of §0.1.
- I found **no work** that writes S(χ)² via the explicit formula and handles Σ_χ χ̄(a)(Σ_ρ m^ρ/ρ)²
  using linear independence or other zero heuristics. Searches for "products of two primes in APs under
  RH/GRH" return only the EOS-line papers (§4), and those all use absolute values.

### 3.2 Binary Goldbach under (G)RH

- **Exceptional set.**
  - Hardy–Littlewood (Partitio Numerorum V, 1924): GRH ⇒ E(X) ≪ X^{1/2+ε}.
  - **Goldston**, *On Hardy and Littlewood's contribution to the Goldbach conjecture*, Proc. Amalfi
    Conf. (1989), Univ. Salerno 1992, 115–155: GRH ⇒ E(X) ≪ X^{1/2} log³ X.
    [READ-2nd: Bhowmik–Grimmelt survey arXiv:2607.27282 §1; the log³ form is from a search snippet]
  - Unconditionally, Montgomery–Vaughan (1975) gives X^{1−δ}, and Pintz gives δ = 0.28.
- **GRH plus pair correlation.** Languasco–Perelli, *Pair correlation hypothesis and the exceptional set
  in Goldbach's problem*, Mathematika 43 (1996) 349–361, doi:10.1112/S0025579300011827:
  under GRH plus a pair-correlation hypothesis for Dirichlet L-functions, |E(N,H)| ≪ N^ε for N^ε < H < N
  (the exceptional set in a short interval). [search snippet of a unipd.it survey; UNVERIFIED details]
  **Pair correlation shrinks the exceptional set but still gives nothing pointwise.**
- **Goldbach numbers in short intervals under RH.**
  - Linnik: [N, N + log^{3+ε} N].
  - Kátai and Montgomery–Vaughan: H ≪ log² N.
  - Languasco–Perelli, Ann. Inst. Fourier 44 (1994) 307: C log² N via Selberg's mean-square of primes in short intervals.
  - Chirre–Hagen, arXiv:2512.23534: under RH, (x, x + 123 log² x] contains a Goldbach number for all x ≥ 2,
    and "the order of H hasn't been improved since". [ABS + intro]
  - The EOS analogue is Banks–Shparlinski Thm 1.3: GRH ⇒ ℓ1ℓ2ℓ3 ≡ a with ℓ3 ≪ log^4 q. In other words,
    some class a·r̄ with prime r ≪ log^4 q is EOS-representable.
- **Why GRH fails pointwise for binary Goldbach.** Bhowmik–Grimmelt §3 [READ] says that, even with
  Θ = 1/2, "Parseval implies that the average size of |f(x)| is N^{1/2}(log N)^{1/2}, which is too large
  for the expected main term. Thus, any resolution of the binary Goldbach problem needs to be supplied
  with much sharper information". They refer to Tao.
- **Tao, "Heuristic limitations of the circle method"** (blog, 20 May 2012), terrytao.wordpress.com/2012/05/20/. [READ, via fetch summary]
  1. GRH gives "very precise control on major arc exponential sums, but not on minor arc ones".
  2. With only magnitude bounds one cannot exclude |S|² "oscillat[ing] in sympathetic resonance with the phase". One is forced to use the triangle inequality, and the minor arcs then exceed the main term "by a logarithmic factor".
  3. **Redacted primes**: delete the primes p < x for which x − p is not prime. Every exponential sum changes only by a factor (1 + O(1/log x)), yet x is no longer a sum of two such primes.
  4. Tight minor-arc asymptotics are "basically just a Fourier reformulation of the underlying binary problems".

---

## 4. Is EOS "binary-hard"?

### What authors say explicitly [READ]

- **EOS 1987, p. 230**: "almost certainly true, but will be hopelessly difficult to prove".
- **Szabó**, arXiv:2208.05762 (Bull. LMS 56 (2024) 1227–1243), p. 1: "This is not known how to prove even if one assumes GRH."
- **Matomäki–Teräväinen**, *Products of primes in arithmetic progressions*, J. reine angew. Math. 808
  (2024) 193–240, arXiv:2301.07679, p. 1: "This remains open even under the generalized Riemann hypothesis."
  - Their unconditional results: E3(q) = G for large cube-free q, and |E2(q)| ≥ (2/3 − ε)φ(q).
  - They say their transference methods "are not applicable to" the sieve-type binary problem a = pn with Ω(n) ≤ k.
- **Banks**, arXiv:2609.37434 (Sep 2026), §1.1. This is the most explicit diagnosis I found:
  - Bounding the error terms by absolute values "yields a total that exceeds the main term by the factor φ(q)/π(q) ≫ log q/log log q".
  - "The loss comes from the sum over the characters, not from any single character. The square-root saving in each individual sum, which is all that GRH provides, does not recover this loss."
  - "The EOS conjecture is also resistant to sieve methods … integers with exactly two prime factors are the standard example of the parity problem."
- **Banks–Shparlinski**, arXiv:2610.19597 (Oct 2026). Under GRH: all but O(log³ q) classes, and the
  ternary case with ℓ3 ≪ log^4 q. This is the current state of GRH-conditional EOS.

**No author I found explicitly says "EOS is as hard as binary Goldbach" or "as hard as a binary
problem in short intervals".** The comparison below is mine, but every ingredient is in the sources above.

### The dictionary [DERIVED]

| | Binary Goldbach, r(N) | EOS, N(a) at X = m |
|---|---|---|
| Group | Z/N, additive (circle) | G = (Z/m)^*, multiplicative |
| Pairs / targets | ≈ N²/log² over N targets | ≈ m²/log² over φ targets |
| Expected count | ≈ N/log² N | ≈ (m/φ) · m/log² m |
| Parseval (Λ-weights) | ∫|S|² ≈ N log N vs main N | V ≈ X log X vs main X²/φ ≈ X(m/φ) |
| L² loss | one log | one log (× φ/m) |
| GRH controls | major arcs only | **all** "arcs" (every χ) |
| GRH exceptional set | ≪ N^{1/2} log³ N | ≪ log³ m |
| GRH, short-interval or "third variable" version | H ≍ log² N | ℓ3 ≪ log^4 m |
| Pointwise | open under GRH | open under GRH |

**EOS under GRH is binary Goldbach with GRH-quality control on every arc.** That is strictly more than
anyone has for Goldbach, and it is still provably insufficient for L² methods (§0.2). In that precise
sense EOS is binary-hard: the missing input is phase alignment, exactly Tao's minor-arc conspiracy
transposed to Ĝ.

### Redacted primes for EOS [DERIVED, heuristic like Tao's]

Fix a. Let R_a = {p ≤ m : a p̄ mod m is a prime ≤ m}, so |R_a| = N(a) ≈ |P|·(m/φ)/log m.
Put P′ = P \ R_a. Then:

- |P′| = (1 − O(1/log m))|P|.
- The elements of P′ are still distinct residues, so the exact Parseval identity holds.
- Heuristically R_a is "random", so Σ_{p∈R_a} χ(p) ≈ √m/log m and P′ satisfies every GRH-quality
  bound |S′(χ)| ≪ √m log m that P does.
- But a ∉ P′·P′.

So any proof that uses only (PNT for P) + (GRH-type bounds on character sums over P) + (L² structure)
must fail. A proof has to use some property of the actual primes that P′ lacks. The caveat matches
Tao's: P′ is not proven to satisfy GRH-type bounds, because the character sums over R_a are themselves
binary sums. The argument is heuristic.

### Ways EOS might still be easier than Goldbach (assessment)

1. The problem is multiplicative, so Vaughan or Heath-Brown identities can decompose one prime.
   - Ranges with a smooth variable of length ≥ m^{1/4+ε} get Burgess-type power savings on max_χ |A(χ)|.
     That is how the ternary results (Szabó; Matomäki–Teräväinen) work.
   - The Type II range (two rough variables) is again phase-blind and, by the setup's computation, short by log factors.
   - Parity: sieve weights cannot isolate E2 (Banks).
2. GRH makes the exceptional set tiny, O(log³ m). A structural argument, e.g. that bad classes force
   some large |S(χ)| or are closed under an operation, could in principle finish.
   I found nothing in the literature in this direction **[speculative]**.
3. Over F_ℓ[t] the analogue is a theorem for large ℓ. Sawin, Acta Math. 233 (2024) 285–418, proves
   square-root cancellation for factorization functions in squarefree progressions; Xie, Math. Z. 313 (2026),
   proves the EOS analogue via Katz equidistribution. [READ-2nd, Banks §1.1]
   The input there is **monodromy / independence (Katz–Deligne), not just RH for the individual
   L-functions**. That is the function-field version of the missing phase information.

---

## Honest assessment: what extra input beyond GRH would close the gap

1. **GRH alone is two logs plus one "binary" log short.**
   - GRH gives p, q ≤ K φ(m) log² m (§0.1; EOS87 proved log^4) and all but O(log³ m) classes at X = m (EOS87: log^5; Banks–Shparlinski: log³).
   - I believe the exponent 2 is the limit of GRH-only arguments. The number of low-lying zeros, ≍ log m per character, can add in phase, and GRH cannot exclude that.
   - Fourier optimization and Brun–Titchmarsh positivity improve only constants, as for the least prime (Carneiro et al.: "essentially at the limit").

2. **Statistical or spectral inputs on zeros recover at most one log and cannot reach X ≤ m.**
   - Pair correlation for the family mod m (Yıldırım/KLM-type, a single modulus, at the edge α = 1⁺).
   - Hooley / Friedlander–Goldston variance V(X;m) ~ X log m at X ≈ φ log m.
   - Hardy–Littlewood averaged over the shifts km.
   - Each of these, at best, moves GRH's φ log² m down to the variance wall (1+o(1)) φ log m.
   - That wall is unconditional and exact below m (distinct residues), so **no hypothesis about
     |S(χ)|, |ψ(x,χ)|, or untwisted n-level densities can prove EOS** (§0.2, §2.2).

3. **What would suffice, and is not a mere restatement: genuinely new phase information**, i.e. a log-power saving in

   Σ_{χ≠χ0} χ̄(a) S(χ)² (equivalently (★), a twisted 2-level density at support (1,1)), uniformly in a.

   Candidate hypotheses that imply it:
   - (a) A **twisted ratios conjecture** for {L(s,χ)} mod m with weight χ̄(a), with power-saving error near Re s = 1/2.
     It implies EOS asymptotically, but it is the same statement in zero language. Fiorilli–Miller show
     that even the untwisted ratios predictions encode Montgomery-type prime conjectures.
   - (b) **"Montgomery's conjecture for products at level 1/2"**: Σ_{n ≡ a (m)} (Λ·w * Λ·w)(n) =
     main + O(m^{1/2+ε}·…), pointwise in a. Natural, but it is EOS with an error term.
   - (c) **Quantitative linear independence / random-phase model** for the low-lying zeros of
     {L(s,χ) : χ mod m}, jointly with the values χ(a).
     - Heuristically this gives N(a) ~ main for X down to about √m polylog m.
     - Qualitative LI (Rubinstein–Sarnak) is useless: it is ergodic in log X, and EOS needs one fixed X ≤ m.
     - A quantitative LI (lower bounds for linear forms in the γ's at height O(1), uniformly in m) is far out of reach and has no precedent.
   - (d) A **number-field analogue of the monodromy input** used over F_ℓ[t] (Sawin; Xie). This is the most
     "honest" extra input, since it is what actually closes the function-field case. But no number-field
     framework for it exists.

4. **Bottom line.** Under GRH, EOS is a binary problem in the precise sense of Tao's
   circle-method analysis. It needs one log of phase cancellation beyond the triangle inequality, and a
   redacted-prime set defeats any phase-blind argument. It is not "GRH plus a technical log saving"; the
   last factor of log m is of the same nature as the minor arcs in binary Goldbach. Realistic GRH-conditional
   targets are:
   - (i) improving the constant or exponent in the "all a" statement at X ≍ φ log² m (exponent 2 → 1 needs a single-modulus variance or pair-correlation input);
   - (ii) shrinking the O(log³ m) exceptional set, for example via extra structure of the bad set;
   - (iii) ternary statements with the third prime ≪ log^{O(1)} m.

   A proof of EOS itself would have to go outside L²/GRH technology, for example by exploiting
   specific multiplicative structure of the primes in Type II ranges in a way that breaks parity. No
   current method does that for a binary problem.

---

### Source list (IDs)

EOS87 doi:10.1007/BF01848086 (pdf static.renyi.hu/~p_erdos/1987-22.pdf) · Bach–Sorenson doi:10.1090/S0025-5718-96-00763-6 ·
LLS arXiv:1309.3595 · Carneiro–Milinovich–Quesada-Herrera–Ramos arXiv:2404.08380 · Bruna arXiv:2603.25612 ·
Kandhil–Languasco–Moree arXiv:2411.19762 and arXiv:2607.14515 · Li–Pratt–Shakan arXiv:1607.02543 ·
Friedlander–Granville Ann. Math. 129 (1989) · Goldston–Yıldırım doi:10.4153/CJM-1998-031-9 ·
Fiorilli–Miller arXiv:1111.3896 · Hughes–Rudnick arXiv:math/0208230 · Chandee–Lee–Liu–Radziwiłł arXiv:1211.6725 ·
Quesada-Herrera arXiv:2108.10238 · Languasco–Zaccagnini arXiv:1011.3198 · Goldston–Suriajaya arXiv:2110.14250, arXiv:2306.04807 ·
Languasco–Perelli doi:10.1112/S0025579300011827 · Chirre–Hagen arXiv:2512.23534 · Bhowmik–Grimmelt arXiv:2607.27282 ·
Tao blog 2012-05-20 "Heuristic limitations of the circle method" · Szabó arXiv:2208.05762 · Matomäki–Teräväinen arXiv:2301.07679 ·
Banks arXiv:2609.37434 · Banks–Shparlinski arXiv:2610.19597.
