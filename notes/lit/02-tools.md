# 02 — Analytic tools bearing on the reformulations (lit strand 2)

Scope: Kloosterman sums over primes, multiplicative energy, products/bilinear forms in
APs, additive combinatorics in (Z/m)^*. Goal: find anything that could save the missing
log powers in `00-setup.md`.

**Provenance tags** (each claim carries one):
- **[READ id]**: I read the statement in the paper's PDF or abstract (arXiv id given).
- **[READ-2nd id]**: I read it as quoted or summarised in another paper (that paper's id).
- **[RECALLED]**: from memory, not checked this session. Treat as **[UNVERIFIED]**.
- **[OWN]**: my own derivation in these notes. Not refereed. Check before relying on it.

Mapping to the project convention (proved / sketched / heuristic / [UNVERIFIED]):
- [READ] and [READ-2nd] items are *proved in the cited literature*. The second-hand ones carry a
  transcription risk.
- [RECALLED] items are [UNVERIFIED].
- [OWN] items are **sketched**: §2.2 (the L² obstruction), §4.3(a) (the deletion barrier), and the
  Parseval computation in §1.5 are short and, I believe, complete. The following [OWN] items are
  **heuristic**: §4.3(b) (Bernstein and union-bound details not written out), the Vaughan range
  bookkeeping in §1.5, the "Chen switching ⇒ p·P_2" claim in §1.3, and the zero-statistics remark
  in §5(3).

Notation follows `00-setup.md`: G = (Z/m)^*, P = primes ≤ m coprime to m, S(χ) = Σ_{p≤m} χ(p),
N(a) = #{(p,q) ∈ P²: pq ≡ a}, μ := |P|²/φ(m) ≈ (m/φ)·m/log²m, A_a = {a p̄ mod m : p ∈ P} ⊂ [1,m].

---

## 0. Executive summary

1. **Reformulation 2 is a sieve problem with a known level of distribution, and it is
   parity-blocked.** Kloosterman sums over primes (Garaev; Fouvry–Shparlinski) give
   Σ_{p≤m} e(h p̄/m) ≪ m^{15/16+o(1)}. Hence A_a is equidistributed in intervals and in APs, with
   level of distribution m^{1/16} and power-saving error. Combined with weighted sieves, this
   already gives "a·p̄ mod m is a P_17 for some p ≤ m" (Shparlinski 2013), later
   "a ≡ p·n, n ∈ P_5" (Zhao 2022, as quoted by Matomäki–Teräväinen). Primes need **Type II
   (bilinear) information** about A_a, and none exists.
2. **The log loss is not a weakness of GRH. No information about the *sizes* of character
   sums can close it.** §4.4 gives a random-pairing construction **[OWN]**. It builds a set
   A ⊂ G of density 1/log m with |Â(χ)| ≪ √m for all χ ≠ χ0 (better than GRH), mimicking
   primes in intervals, APs and Kloosterman sums, yet with a ∉ A·A. Also, a fraction of only
   ≈1/log m of the primes (namely N(a) ≈ |P|/log m of them) can be deleted to kill all
   representations of a. So any argument that is robust under deleting o(1) of the primes
   fails. This rules out dense-model or transference methods and all L^r-of-|S| methods.
3. **Energy (L⁴) cannot give pointwise results, even in principle** (§2.3, **[OWN]**). By
   Cauchy–Schwarz, Σ_a (N(a) − μ)² ≥ (1−o(1))|P|², but a pointwise result from L² needs it to be
   < μ² ≈ |P|²/log²m. Higher moments in a are not excluded, but they need phase information.
4. **Where EOS sits in the "level of distribution" landscape** (reformulation 3): X = m²,
   modulus Q = m = X^{1/2}, both factors of length X^{1/2}, pointwise in a, single modulus.
   On average over moduli this is exactly the Bombieri–Vinogradov edge Q = X^{1/2}, which BV
   misses by a (log X)^B factor. That is the same log loss in another guise. All
   "beyond 1/2" results (Fouvry–Radziwiłł, Bettin–Chandee, Wright 2026) average over q. For a
   single modulus, beyond-1/2 results exist only for divisor-type (smooth) sequences.
5. **The function-field analogue is settled** (Sawin, Acta Math 2024, + Xie, Math Z 2026,
   **[READ-2nd 2609.37434]**). There the missing ingredient is square-root cancellation in
   the *family* sum Σ_χ χ̄(a)S(χ)², which comes from cohomology. Over Z that would be a
   Montgomery-type hypothesis for E_2-numbers in APs, beyond GRH.
6. **Most promising concrete target** (§5): a Type II estimate for A_a at UV ≈ m. This is a
   trilinear congruence p·u·v ≡ a (mod m) with arbitrary α_u, β_v. Plain Parseval misses it
   by exactly (log m)^{1/2} (§1.5, **[OWN]**), against a full (log m) for the original binary
   sum. Together with the known Type I level m^{1/16}, such an estimate for
   U ∈ [m^{1/32}, m^{1/2}] would give EOS via Vaughan's identity.

**Corrections and additions to `00-setup.md`:**
- The EOS 1987 GRH result: "under GRH, at most c log⁵ q residues a < q fail" **[READ-2nd
  1505.03328, Walker]**. Banks–Shparlinski (2026) improve this to O((log q)³) exceptional
  classes under GRH, and show that every class is ℓ1ℓ2ℓ3 with ℓ1, ℓ2 ≤ q, ℓ3 ≪ (log q)⁴
  **[READ 2610.19597]**. The conjecture "remains open even under GRH"
  **[READ 2609.37434, 2301.07679]**.
- The setup says Type II via sieve "needs UV ≫ m log⁴ m". **[OWN]** If GRH is used pointwise
  on S, the loss is ≈ log³ m (with |S| ≪ √m log² m). If instead exact Parseval is used on all
  factors (no GRH), the loss is only (log m)^{1/2}. GRH pointwise is the *wrong* tool there;
  see §1.5.
- The upper bound N(a) ≪ μ is known: N(a) ≤ (64+o(1))π(q)²/φ(q) for prime q (Walker)
  **[READ-2nd 2208.05762; READ 1505.03328]**. It also follows from the m^{1/16} level plus an
  upper-bound sieve **[OWN, routine]**. So the problem is purely about the lower bound.

---

## 1. Modular inverses of primes / Kloosterman sums over primes

### 1.1 Bounds for W_m(a;x) := Σ_{p≤x, p∤m} e_m(a p̄), with (a,m) = 1

| Result | Modulus | Range | Bound | Nontrivial for | Source |
|---|---|---|---|---|---|
| Garaev (2010) | prime q | x < q | (x^{15/16} + x^{2/3}q^{1/4}) q^ε | x ≥ q^{3/4+δ} | Math. Notes 88 (2010) 330–337 **[READ-2nd 1301.6372, 1911.09981]** |
| Fouvry–Shparlinski (2011), Thm 3.1 | **any m** | x ≤ m^{4/3} | (x^{15/16} + m^{1/4}x^{2/3}) m^{o(1)} | x ≥ m^{3/4+δ} | Acta Arith 150 (2011) 285–314 **[READ-2nd 1705.06087 eq.(5.1); 1301.6372]** |
| Fouvry–Michel (1998) | prime p | X ≤ p | X (p/X)^{7/32} p^{−η}, any η < 1/32 (general rational f; f = a/x included) | X ≥ p^{1−...} | Ann. Sci. ENS 31 (1998) 93–130 **[READ-2nd 1211.6043]** |
| Bourgain (2005); Baker explicit δ = 0.0005ε⁴ | prime q | X ≥ q^{1/2+ε} | X q^{−δ} (non-homogeneous a p̄ + b p) | X ≥ q^{1/2+ε} | IJNT 1 (2005); Baker Acta Arith 156 (2012) 351–372 **[READ-2nd 1911.09981]** |
| Korolev (2018) | any m | — | X^{32/37} q^{7/74+ε} | X ≥ q^{7/10+ε} | Sb. Math 209 (2018) 652–659 **[READ-2nd 1911.09981]** |
| Korolev (2019) | any m, non-homog. | q^{3/4+ε} ≤ X ≤ (q/2)^{3/2} | X q^ε Δ, Δ = (q^{3/4}/X)^{1/7} or (q^{2/3}/X)^{3/35} | — | arXiv 1911.09981 **[READ]** |
| Fouvry–Shparlinski Thm 5 (avg over q) | q ∼ Q | x ≤ Q^{3/2} | Σ_q max_a \|W\| ≪ (Q^{13/10}x^{3/5} + Q^{13/12}x^{5/6})Q^ε | x ≥ Q^{3/4+δ} | **[READ-2nd 1301.6372]** |
| Baker (2012), avg over q | q ∼ Q | Q^{1/2} ≤ x ≤ 2Q | (Q^{11/10}x^{4/5} + Q x^{11/12})Q^ε | — | **[READ-2nd 1301.6372]** |
| Irving (2013), avg over q | q ∼ Q | Q^{2/3} ≤ x ≤ Q^{3/2} | (Q^{5/4}x^{5/8} + Q x^{9/10} + Q^{7/6}x^{13/18})Q^ε | x ≥ Q^{2/3+δ} | arXiv 1301.6372 **[READ]** |
| Conjecture | — | — | x^{1/2+ε}q^ε | — | **[READ 1301.6372]** ("far out of reach") |

**At the EOS scale x = m:** the best pointwise bound I found is m^{15/16+o(1)} (Garaev / Fouvry–Shparlinski).
Korolev's bound gives m^{71/74} there, which is weaker; Fouvry–Michel gives m^{1−η} with η < 1/32.
I did not find anything better at x = m for a single modulus. **[UNVERIFIED that no better bound exists]**

**Short sums over all integers** (not primes), for context: Bourgain–Garaev,
|Σ_{n≤N} e_p(a n̄)| ≪ (log log p)³ log p/(log N)^{3/2} · N **[READ 1211.4184, Thm 16]**.
For general m, saving (log m)^{-1/2}(log log m)^{O(1)} for N > m^c **[READ 1309.1124, Thm 5]**.
Weil gives m^{1/2+o(1)} for complete and incomplete sums over intervals.

**Does GRH help with W_m(a;m)?** **[OWN]** Not directly. Expanding e(b x̄/m) into multiplicative
characters gives coefficients of size √m/φ, so the expansion yields
|W| ≤ (1/φ)Σ_χ |τ(χ)||S(χ)| ≲ √m·√m log²m. That is trivial. The Kloosterman-over-primes bounds
come from Vaughan's identity plus Weil/bilinear Kloosterman estimates, not from L-functions.

### 1.2 Consequences for A_a = {a p̄ mod m}

**Intervals.** Let T_1(a;x,y) = #{p ≤ x : a p̄ mod m ≤ y}. Then
|T_1 − π(x)y/m| ≤ (x^{15/16} + m^{1/4}x^{2/3})m^{o(1)} for m^{1/2} ≤ x ≤ m and y ≤ m
**[READ 1705.06087, Lemma 5.4]** (Shparlinski 2013, Lemma 2; the proof is Erdős–Turán).
At x = m the discrepancy of A_a in [1,m] is ≪ m^{−1/16+o(1)}, so A_a is equidistributed in all
intervals of length ≥ m^{15/16+ε}.

**APs to moduli d with (d,m) = 1.** **[READ 1705.06087, §7]** The elements of A_a divisible
by d correspond to p·(du) ≡ a with u ≤ m/d, i.e. a d̄ p̄ mod m ∈ [1, m/d]. This is an
interval condition. So |#A_a(d) − π(m)/d| ≤ m^{15/16+o(1)} uniformly in d, and

> **A_a has level of distribution D = m^{1/16−ε} with power-saving remainder**
> (Σ_{d≤D} |r(d)| ≪ |A_a|^{1−κ}). [READ 1705.06087, "D_1 ≥ min{x^{1/16}ym^{-1}, x^{1/3}ym^{-5/4}}" at x = y = m]

**APs to moduli d | m.** Here a p̄ mod d is determined by p mod d, so this is the distribution
of primes ≤ m mod d: Siegel–Walfisz unconditionally, and under GRH for d ≤ m^{1/2}/log². **[OWN, trivial]**
For general d with 1 < (d,m) < d, combine the two cases.

**Answer to the strand question.** Yes: {a p̄ mod m : p ≤ m} is equidistributed in intervals
(down to length m^{15/16+ε}) and in APs to moduli ≤ m^{1/16−ε}, unconditionally, with power saving.

### 1.3 Almost-prime results for reformulation 2 (a·p̄ mod m ∈ P_r)

- **Shparlinski 2013**, Period. Math. Hungar. 67 (2013) 55–61, doi:10.1007/s10998-013-2736-3.
  (17; 0.997, 0.997) is admissible: every reduced a is p·s with p ≤ m^{0.997+ε},
  s ≤ m^{0.997+ε}, s ∈ P_17 **[READ-2nd 1705.06087, eq.(1.4)]**. Since s < m, this says
  exactly that **a p̄ mod m is a P_17 for some prime p ≤ m**. Method: level m^{1/16} above plus
  Greaves' weighted sieve (degree g = log y/log D ≈ 16 < ℓ − δ_ℓ forces ℓ = 17).
- **Shparlinski 2019**, PAMS 147 (2019) 977–986, arXiv 1705.06087 **[READ]**. General
  admissibility criteria for p_1⋯p_k·s, using S_k(a;x) for k = 2, 3, 4 (bilinear Vinogradov
  bound plus the trivial energy bound below). For example, (k_η; 1/2+η) ∈ A_2: every class is a
  product of k_η primes ≤ m^{1/2+η}.
- **Walker 2016**, Bull. LMS 48 (2016) 1018–1028, arXiv 1505.03328 **[READ]**, prime q:
  every residue is a product of ≤ 6 primes < q^{15/16+ε}; P_η^{(48)} = G with η = q^{−1/16+ε}.
  Theorem 1: |E_2(q)| ≥ (1/64 + o(1))φ(q), using an upper-bound sieve majorant with good additive
  Fourier L¹ norm plus Weil.
- **Zhao 2022**, Acta Arith 204 (2022) 253–267, doi:10.4064/aa211215-2-6. Abstract
  **[READ]**: p1 p2 n ≡ a with p_i, n ≤ q and n ∈ P_2. MT 2301.07679 credit Zhao with
  a = p·n, p, n ≤ q, n having ≤ 5 prime factors **[READ-2nd 2301.07679]**. The current record
  for "a p̄ mod m ∈ P_r" is therefore r = 5 **[UNVERIFIED in Zhao itself]**.
- **Squarefree instead of almost-prime (no parity issue).** Yau, arXiv 1907.06016 **[READ]**:
  #{ps ≡ a: p ≤ P, s ≤ S squarefree} = π_q(P)s_q(S)/q + O((PS)^{o(1)}S^{1/2}E). For q ≥ P^{3/4},
  E = P^{31/32}/q^{(1−ε)/2} + P^{5/6}/q^{(3/4−ε)/2}. At P = S = q the error is ≈ q^{31/32} against
  a main term ≈ q/log q, so every class is p·(squarefree) with both ≤ q, asymptotically.
  Friedlander–Kurlberg–Shparlinski, arXiv 0708.1562 **[READ]**: products ps with p, s ≤ m^{1/2+ε}
  represent almost all classes the expected number of times; squarefree × squarefree asymptotic
  for x ≥ m^{3/4+ε}.

**What improving the Kloosterman exponent would buy** **[OWN]**. If
W_m(h;m) ≪ m^{1−θ+ε} uniformly in h, then A_a has level m^{θ}. With θ = 1/2 (square-root
conjecture), Greaves' sieve gives g = 2 < 3 − δ_3, so **a p̄ ∈ P_3**. A Chen-type switching
argument should give **a ≡ p·P_2**: the upper-bound side for #{p q1 q2 ≡ a} only needs constants,
which the sieve supplies. **No level below 1 breaks parity.** Primes need bilinear input (§1.5).

### 1.4 Bilinear and multilinear Kloosterman sums: candidate sources of Type II input

- **Bourgain–Garaev, prime modulus**, arXiv 1211.4184 (Izv. Math 78 (2014) 656–707) **[READ]**.
  - Thm 8 / Cor 2: for arbitrary 1-bounded α, β on [1,N_1], [1,N_2],
    |Σ α_{x1}β_{x2} e_p(a x̄1 x̄2)| < p^{−δ} N_1N_2, unless both N_i are within p^{±ε} of some
    p^{1/(2j)}. In particular this holds when N_1N_2 ≈ p.
  - Thm 13: intervals in arbitrary position with |I_1|⋯|I_n| > p^{1/2+ε} give
    |Σ α_1⋯α_n e_p(a x̄1⋯x̄n)| < p^{−δ}Π|I_i|.
  - Thm 7: |I_1| > p^{1/18}, |I_2| > p^{5/12+ε} gives a power saving.
  - Thm 6: additive energy of reciprocals of **primes**:
    #{x̄1+…+x̄k ≡ x̄_{k+1}+…+x̄_{2k}, x_i ≤ N prime} < (2k)^k (N^{2k−1}/p + 1) N^k.
- **Bourgain–Garaev, general modulus**, arXiv 1309.1124 **[READ]**: the same bilinear results
  (Thm 3, Cor 1) and the reciprocal-energy bound for primes (Thm 2) mod any m. They rely on
  Bourgain's sum-product theorem in Z_q, q arbitrary (J. Anal. Math 106 (2008) 1–93). For
  A_i ⊂ Z_q with |A_i| > q^γ and no concentration on residue classes mod divisors q_1 > q^ε,
  |Σ_{x_i∈A_i} e_q(ξ x1⋯xk)| < q^{−τ}Π|A_i| **[READ 1309.1124, Lemma 1]**. This works for
  **arbitrary sets**, not just intervals.
- **Kerr–Shparlinski–Wu–Xi**, arXiv 2204.05038 **[READ abstract]**: Type I and II bilinear forms
  with complete and incomplete Kloosterman sums, including forms with one variable from an
  arbitrary set (via additive combinatorics). **Shkredov**, arXiv 1905.00291 **[READ abstract]**:
  incidences for modular hyperbolas and a combinatorial nontrivial bound for bilinear
  Kloosterman forms. **Pascadi**, arXiv 2511.08445 **[READ abstract]**: Type II sums of
  Kloosterman sums S(m,n;c) with composite c via non-abelian amplification on SL_2(Z/cZ).
  Saves c^{−1/12} at M ≈ N ≈ √c for products of two equal primes; non-trivial for all c except
  near-primes.

### 1.5 Why these do not yet give Type II for A_a, and the exact size of the gap  **[OWN]**

The Type II sum for A_a, with UV ≤ m and 1-bounded α_u (u ∼ U), β_v (v ∼ V), is
T := Σ_{u,v} α_u β_v #{p ≤ m : p·uv ≡ a (mod m)}. Each (u,v) contributes 0 or 1. We need
T = (main) + o(UV/log m). By orthogonality,
T = (1/φ)Σ_χ χ̄(a) S(χ) B(χ), where B(χ) = Σ α_uβ_v χ(uv).

- *Exact Parseval on both factors* (distinct n ≤ m are distinct mod m):
  |error| ≤ (1/φ)(φ|P|)^{1/2}(φ Σ_n |(α*β)(n)|²)^{1/2} ≈ √(|P|·UV).
  The main term is ≈ UV/log m, so error/main ≈ √(m log m/UV) ≥ **(log m)^{1/2}**.
  For comparison, the binary sum itself is off by a factor log m.
- *GRH on S pointwise* gives error ≤ √m log²m · √(UV), so error/main ≥ log³ m. This is worse.
- *Additive Fourier route.* Write 1[uv ≡ a p̄] = (1/m)Σ_h e(h(uv − a p̄)/m). Then
  T = (1/m)Σ_h B_add(h)·W_m(−ha; m). Here |B_add(h)| ≤ √(UVm) (Vinogradov) and
  W_m ≪ m^{15/16}, but Σ_h|B_add(h)| ≈ m√(UV). The total error is m^{15/16}√(UV) ≫ UV.
  Putting primes on the additive side instead fails because Σ_h|P̂(h)| ≈ m√|P| is huge.
  The bilinear Kloosterman bounds of §1.4 control e(c x̄ ȳ/m) with arbitrary weights, but
  turning the *multiplicative* congruence p·uv ≡ a with the *archimedean* cut uv ≤ m into such
  sums always costs an L¹ norm of a rough Fourier transform.
- *Dispersion* (Cauchy–Schwarz in u, open the square). This leads to counting
  p1 v1 ≡ p2 v2 (mod m) with an interval condition on a·\overline{p1 v1}, which is again
  "primes in a modular-inverse sequence". The problem is self-similar under dispersion: primes
  reappear on the inside. That is a warning sign, but not a proof of impossibility.

**Target statement (Type II for A_a).** For all U ∈ [m^{1/32}, m^{1/2}], V ≤ m/U, and all
divisor-bounded α, β:
 T(α,β) = (m/φ(m))·(1/log m)·Σ_{u,v} α_uβ_v·(1 + o(1)) + O(UV (log m)^{−A}).
Together with the known Type I level m^{1/16} (§1.2), Vaughan's identity with cut parameters
U = V = m^{1/32} would give N(a) ∼ μ. For a lower bound only, Harman's sieve needs a narrower
Type II range. **[OWN; the range bookkeeping is not checked carefully]**

**A warning about the 4-linear form** **[OWN]**. Decomposing *both* primes gives
(u1 v1)(u2 v2) ≡ a (mod m) with u_iv_i ≤ m. For general Siegel–Walfisz coefficients this is
**false** at a single modulus. Take all four coefficient sequences twisted by a quadratic χ mod m
(conductor m, so still Siegel–Walfisz). The count then equals χ(a)·(untwisted count) ± …, while
the predicted main term is ≈ 0. This is the scenario "ψ(p) = −1 for most p" isolated by
Matomäki–Teräväinen. GRH kills it for the primes, but the argument must therefore use that the
coefficients come from μ/Λ and not merely that they are Siegel–Walfisz.

---

## 2. Multiplicative energy and L⁴ control of S(χ)

### 2.1 What is known

- **Energy of primes mod m, trivial bound.** #{p1p2 ≡ q1q2 (mod m), p_i, q_i ≤ x}
  ≤ x^{2+o(1)}(x²/m + 1) **[READ 1705.06087, Lemma 5.1]**. Proof: fix (q1,q2); then
  p1p2 ≤ x² lies in one AP mod m with ≤ x²/m + 1 terms. At x = m this gives m^{3+o(1)}, against
  the truth ≍ m³/log⁴m.
- **Energy up to a constant.** **[OWN; essentially Walker]** E(P) = Σ_a N(a)² ≤ (max_a N(a))·|P|²
  ≪ μ|P|² ≍ |P|⁴/φ, using the upper bound N(a) ≪ μ (Walker, or the m^{1/16} level plus an
  upper-bound sieve). Equivalently Σ_χ|S(χ)|⁴ ≍ |P|⁴. Walker notes the energy bound is
  equivalent to the 4th moment Σ_χ|Σ_{p<q}χ(p)|⁴, and that "applying Lemma 7 with an upper-bound
  sieve weight" (credited to Harper) gives it easily **[READ 1505.03328, §3]**.
- **Under GRH**: Σ_{χ≠χ0}|S|⁴ ≤ max|S|²·φ|P| ≪ m³ log³m = o(|P|⁴), so E(P) = (1+o(1))|P|⁴/φ.
  **[OWN, trivial]**
- **Mixed energy, primes × interval** (Garaev–Karatsuba, arXiv math/0503164) **[READ]**. For
  any set V of primes ≤ m^{1/2} and an interval of length L:
  #{v1y1 ≡ v2y2 (mod m)} = |V|²L²/m + |V|L − |V|L²/m + O(m² log²m/φ(m)).
  This is an *asymptotic* for a mixed 4th moment Σ_χ|V(χ)|²|I(χ)|², but only for primes ≤ √m.
- **Energy of products of intervals.** Garaev, arXiv 0807.4318 (Math Z 272 (2012) 473–482)
  **[READ]**: N1N2N3 > m^{1+ε} implies {x1x2x3 mod m} covers m − O(m^{1−δ}) classes. For
  cube-free m, four intervals with product > m^{1+ε} suffice. Also, for p > N > p^{63/76+ε},
  p1p2(p3+k) ≡ λ has (1+o(1))π(N)³/p solutions. The tools are Burgess plus the Huxley large-values
  estimate R ⪅ N²/V² + pN⁴/V⁶. Garaev–Karatsuba: {x1x2 : x_i ≤ m^{1/2+ε}} covers almost all of
  Z_m **[READ-2nd 0807.4318]**.
- **Concentration on modular hyperbolas.** Cilleruelo–Garaev, arXiv 1007.1526 (GAFA 21 (2011))
  **[READ abstract]**: #{xy ≡ λ (mod p), x, y in boxes of side M} ≤ M^{o(1)} for M < p^{1/4}, and
  ≤ M²/p + O(p^{1/2}log²p) in general (Weil). This is the interval analogue of N(a).
  **For intervals, II = G as soon as |I| ≫ p^{3/4}log²p**, i.e. at density p^{−1/4}. The interval
  case is easy because Weil gives square-root cancellation on the *additive* side, where
  intervals have L¹-bounded Fourier transforms.
- **Reciprocal energies** (Bourgain–Garaev Thm 2/6) **[READ 1211.4184, 1309.1124]**: listed in
  §1.4. At N = m they are trivial.
- Shkredov, arXiv 1802.09066 **[READ abstract]**: asymptotic formulae in sum–product questions over
  F_p, e.g. (a1−a2)(a3−a4) = (a′1−a′2)(a′3−a′4), via Rudnev incidences and Helfgott's SL_2 growth.
  These concern arbitrary sets; I see no direct EOS input.

### 2.2 Can L⁴ control give pointwise EOS?  **No.**  [OWN]

By Parseval in a, Σ_a(N(a) − μ)² = (1/φ)Σ_{χ≠χ0}|S(χ)|⁴. By Cauchy–Schwarz and the exact
identity Σ_{χ≠χ0}|S|² = φ|P| − |P|²,

 Σ_a (N(a) − μ)² ≥ (φ|P| − |P|²)²/(φ(φ−1)) = (1 − o(1))|P|².

Concluding N(a) > 0 for every a from this L² information needs Σ_a(N(a)−μ)² < μ² = |P|⁴/φ², i.e.
|P| > φ. That fails by a factor of ≈ log m. **No energy bound, however sharp, suffices on its own.**

Higher moments. Σ_a (N(a)−μ)^{2k} ≥ φ^{1−k}|P|^{2k} by Hölder, and this is < μ^{2k} for k ≥ 2.
So the 4th central moment in a is *not* excluded in principle. But on the character side it is
 φ^{−3}Σ_{χ1χ2=χ3χ4, all ≠χ0} S(χ1)²S(χ2)²\bar S(χ3)²\bar S(χ4)².
We need it to be < μ⁴ = |P|⁸/φ⁴, i.e. the inner sum over quadruples must be < |P|⁸/φ.
With absolute values and a flat spectrum (|S|² ≈ |P|), the inner sum is ≈ φ³|P|⁴. That exceeds
|P|⁸/φ by (φ/|P|)⁴ ≈ log⁴m, so absolute values fail. With random phases only the diagonal
(χ3,χ4) = (χ1,χ2) or swapped survives, giving ≈ 2φ²|P|⁴ < |P|⁸/φ (since φ³ < |P|⁴), and that works. So **the phases of S(χ)² along multiplicative
relations χ1χ2 = χ3χ4 are exactly the missing information.** On the physical side this is the
count of 8-tuples with p1q1 ≡ p2q2 ≡ p3q3 ≡ p4q4 to relative precision ≈ 1/φ. That is
equivalent in difficulty.

---

## 3. Products, E_2 numbers, and bilinear forms in APs to large moduli

### 3.1 Single modulus, pointwise in a (the EOS setting)

Known exponents θ with Σ_{n≤x, n≡a (q)} f(n) = main + o(x/φ(q)) for each q ≤ x^{θ}:
- d_2: θ = 2/3 (Selberg/Hooley/Heath-Brown). **[RECALLED]**
- d_3: θ = 1/2 + 1/230 (Friedlander–Iwaniec, Annals 1985); 1/2 + 1/82 (Heath-Brown, Acta Arith
  1986) **[RECALLED]**; **1/2 + 1/46 for prime q** (Fouvry–Kowalski–Michel, Mathematika 61 (2015)
  121–144, arXiv 1304.3199) **[READ abstract]**. The last rises to 1/2 + 1/34 on averaging over
  the residue class.
- d_k, k ≥ 4: θ_k = 8/(3k+4) (Friedlander–Iwaniec / Heath-Brown), so θ_4 = 1/2. **[RECALLED]**
- Trace functions over primes: power saving for x ≥ p^{3/4+ε} (FKM, Duke 163 (2014), arXiv
  1211.6043) **[READ-2nd 1804.01337]**. Korolev–Shparlinski reach p^{1/2+ε} for sums twisted by
  Möbius or divisor functions (arXiv 1804.01337) **[READ abstract]**.
- **E_2 numbers / α*β with two rough factors, single modulus at level 1/2: nothing.** All
  beyond-trivial pointwise results use a smooth (divisor-type) factor, i.e. Type I structure.
  EOS (both factors are primes of length X^{1/2}, Q = X^{1/2}) is the unsolved critical case.
  The quadratic-twist example in §1.5 shows a general-coefficient version is false.

### 3.2 Averaged over moduli, fixed residue (dispersion method)

- **BV edge.** Bombieri–Vinogradov for convolutions handles Q ≤ X^{1/2}(log X)^{−B}. EOS
  averaged over m is exactly Q = X^{1/2}, so it misses by the (log X)^B. **[RECALLED; consistent
  with FKS below]** BFI handle Q = x^{1/2} for primes with savings (log x)^{−A}, A < 2 only
  **[READ-2nd 1811.08672]**.
- **Fouvry–Radziwiłł**, arXiv 1811.08672 (Ann. Sci. ENS 55 (2022) 537–568) **[READ]**: weak level
  x^{1/2+1/66−ε} for α*β with β supported on n ≤ exp((log x)^ε) and Siegel–Walfisz, averaged over
  q. Applications include products of exactly two primes in APs to large moduli. Ingredients are
  Bettin–Chandee trilinear Kloosterman fractions and Duke–Friedlander–Iwaniec bilinear forms.
- **Fouvry–Radziwiłł**, arXiv 1812.00562 **[READ]**: "narrow Type II", M = X^{1/2−δ},
  N = X^{1/2+δ}, β Siegel–Walfisz, exponent 1/2 + δ − ε for 0 ≤ δ < δ_0 (averaged over q, fixed a).
- **Wright 2026**, arXiv 2604.25177 and 2608.27732 **[READ abstracts]**: range improvements of FR.
  Unbalanced: N ≤ Q^{−11/12}X^{17/36−ε} with Q ≤ X^{1/2+1/66−δ}, plus wider ranges for
  Q ≤ X^{45/89}. Nearly balanced: 0 < δ < 1/68, improving FR's 1/112. The method is an improved
  Bettin–Chandee bound, B(M,N,A) ≪ ‖α‖‖β‖‖ν‖(1 + |ϑ|A/MN)^{1/2}((AMN)^{7/20+ε}(M+N)^{1/4} + (AMN)^{3/8+ε}(AN+AM)^{1/8}).
- **Relevance to EOS** **[OWN]**: all of these average over the modulus and need one factor to be
  Siegel–Walfisz. EOS has a single modulus, so they do not apply directly. The only EOS
  statements of this flavour are on average over m:
  - **FKS**, arXiv 0708.1562 **[READ]**: Σ_{q∼M prime} Σ_a (P(x;q,a) − π(x)²/φ(q))² ≪ (M^{−1}x⁴ + Mx²)(log x)^{−2}.
    For general m, R(x,M) ≪ x⁴(log x)^{−A} + Mx². They note "in the case of the average over
    prime moduli we can come within a power of a logarithm of the optimal range" and "even ERH
    seems not powerful enough".
- I found no Banks–Shparlinski paper titled "products of primes/integers in APs" specifically.
  The closest is Banks–Shparlinski 2026 (below). **[UNVERIFIED that I have not missed a paper]**

### 3.3 EOS-specific results (for orientation; overlaps strand 1)

Table taken from Banks, arXiv 2609.37434, Table 1 **[READ]**:
- |E_2(q)| ≥ (1/64)φ (Walker, q prime); E_48(q) = G (Walker).
- E_3(q^{3/2+ε}) = G (Balasubramanian–Ramaré–Srivastav; Ramaré–Srivastav–Serra; Ramaré–Walker).
- |E_2(q)| ≥ 3/8 φ (cube-free) and E_6(q) = G (q prime) (Szabó, arXiv 2208.05762, Bull. LMS 56 (2024)).
- E_3(q^{6/5+ε}) = G (Szabó).
- |E_2(q)| ≥ (2/3 − ε)φ and E_3(q) = G for cube-free q (Matomäki–Teräväinen, arXiv 2301.07679,
  Crelle 808 (2024)) **[READ]**. Also 11/16 for cube-free q, and E_3(q^{1+ε}) = G for all large q.
- E_3(q^{2+ε}) = G for smooth or non-exceptional prime q (Klurman–Mangerel–Teräväinen, PLMS 127 (2023)).
- **Banks–Shparlinski 2026**, arXiv 2610.19597 **[READ]**: for q = p^γ, an asymptotic for
  Σ_{ℓ1ℓ2ℓ3≡a} log ℓ1 log ℓ2 log ℓ3 with ℓ1, ℓ2 ≤ q and ℓ3 ≤ q•, log q• ≥ C(log q)^{2/3}(log log q)^{4/3}.
  The binary exceptional set is ≤ φ exp(−c(log q)^{1/3}(log log q)^{−1/3}). Under QRH[q,σ0] the
  binary exceptional set is ≪ φ q^{−2(1−σ0)}(log q)³, so **(log q)³ under GRH**, and the third
  prime satisfies ℓ3 ≪ (log q)^{2/(1−σ0)} = (log q)⁴.
- **Banks 2026, Granville model**, arXiv 2609.37434 **[READ]**: almost surely EOS holds for
  Granville's random primes with g1, g2 ≤ q^Θ for any Θ > 3/4, with the asymptotic count. The
  exponent 3/4 is where Weil–Estermann balances (error q^{1/2+o(1)} vs main N²/q). It fails with
  positive probability in the Banks–Ford–Tao model (local defect at 2, 3). "Any saving on
  incomplete Kloosterman sums would lower the exponent." Note that this random model has
  independence across orbits n ↦ a n̄, which real primes lack. That independence is what the
  proof uses.
- **Function fields**: Sawin, "Square-root cancellation for sums of factorization functions over
  squarefree progressions in F_q[t]", Acta Math 233 (2024) 285–418. As observed by Xie
  (Math Z 313 (2026), no. 64), Sawin's Lemma 9.14 gives EOS for squarefree moduli of large
  degree once ℓ exceeds an absolute constant **[READ-2nd 2609.37434]**.

---

## 4. Covering G by products of a sparse structured set

### 4.1 Classical facts
- If |A| > φ/2 then A·A = G (pigeonhole: aA^{−1} ∩ A ≠ ∅). **[standard]**
- **Kneser**: |AB| ≥ |A| + |B| − |H| with H the stabiliser of AB. MT use a "popular sums"
  version (their Lemma 6.1). **[READ 2301.07679]**
- **Fourier criterion for three factors**: N_3(a) ≥ |A|³/φ − max_{χ≠χ0}|Â(χ)|·|A|, so
  max|Â| < |A|²/φ gives AAA = G. For primes under GRH, √m log²m ≪ |P|²/φ, so **PPP = G under
  GRH** (Walker footnote 2 **[READ 1505.03328]**). For **two** factors the analogous bound is
  only |E(a)| ≤ |A| (Parseval), which is the barrier.
- Garaev / Bourgain–Garaev product-set results for intervals: §2.1. Bourgain's sum-product in
  Z_q for arbitrary q (J. Anal. Math 106 (2008)) controls additive characters of multiplicative
  products of arbitrary sets (§1.4). For EOS, the place where sum-product could enter is the
  interplay between the archimedean cut (P ⊂ [1,m]) and multiplicative structure in G. I found
  no result exploiting this for binary covering. **[UNVERIFIED that none exists]**

### 4.2 Matomäki–Teräväinen dense model, and why binary stalls  [READ 2301.07679 + OWN analysis]
- Prop 4.1 (multiplicative dense model) **[READ]**. Given f ≤ ν on [N]_q with E ν ≈ 1 and
  max_{χ≠χ0}|E νχ| ≪ q^{−ε}, and with at most Cδ^{−r} large-spectrum characters, there is
  g: G → [0, 1+η] with character sums δ-close to those of f.
- Prop 5.2 **[READ]**: a set A ⊂ G with |A| ≥ (θ/2 − ε)φ, where N^θ is the sieve level.
  (1_A*1_A)(a) ≫ φ/(log q)^{1/2−ε} implies a ∈ E_2(N) **only for all but O(φ(log q)^{−ε/5}) values
  of a**. The ternary version holds for all a. With Burgess (cube-free) θ = 3/4, so |A| ≥ 3/8.
- **Why binary is stuck** **[OWN]**:
  1. *Density, a factor-2 parity barrier.* An upper-bound sieve majorant of primes at level
     N^θ has density ≥ (2/θ)× that of the primes. So the dense model set has |A| ≤ (θ/2)φ.
     Under GRH θ → 1, giving |A| → φ/2, but binary covering by pigeonhole or Kneser needs
     |A| > φ/2 strictly (or a non-degenerate Kneser configuration). The binary problem sits
     exactly at Selberg's parity constant 2.
  2. *Transference for 2-fold convolutions is only L² in a.* r-fold transference needs an
     L^{r′} restriction estimate for some r′ < r. For r = 2 that would be an L^{r′}, r′ < 2,
     bound on Σ_χ|S(χ)|^{r′}, which is impossible beyond Parseval. Hence the "all but a few a"
     caveat. This mirrors binary versus ternary Goldbach.
- Under GRH the MT method therefore gives "almost all a", which is already known (EOS 1987;
  Banks–Shparlinski). **[OWN]**

### 4.3 Barrier constructions  [OWN — please scrutinise]

**(a) Deletion barrier.** N(a) ≈ μ ≈ |P|·|P|/φ ≈ |P|/log m. The pairs {p, a p̄} with both entries
prime are disjoint (an involution). Deleting one prime from each such pair, i.e. a proportion
≈ 1/log m of P chosen depending on a, makes a ∉ A·A, where A is the remaining primes.
**Any method whose conclusion is stable under deleting o(1) of the primes cannot prove binary
EOS.** This includes dense-model or transference methods, any argument using only "P has
relative density ≥ c in a pseudorandom majorant", and Shao-type density thresholds.

**(b) Random pairing barrier (Fourier sizes are useless).** Partition G \ {x : x² = a} into orbits
{x, a x̄}. Independently choose each orbit with probability 2δ, then one of its two elements at
random. The resulting A has A ∩ aA^{−1} = ∅, so a ∉ AA. It has density δ, and
E Â(χ) = δ Σ_{x∈G}χ(x) = 0 for χ ≠ χ0. By Bernstein and a union bound,
max_{χ≠χ0}|Â(χ)| ≪ √(δφ log φ). With δ = 1/log m this is ≪ √φ, **stronger than the GRH
bound √m log²m for S(χ)**. Weighting the choice within each orbit by any prescribed density w
(e.g. that of z-rough integers ≤ m, or of primes in intervals and APs) makes A match those
Type I statistics, and its Kloosterman sums Σ_{x∈A} e(h x̄/m) are ≪ √(m log m) as well.
**Conclusion:** no combination of (i) bounds on |S(χ)|, (ii) Kloosterman-over-primes bounds and
(iii) sieve (Type I) axioms implies a ∈ PP. The proof must use bilinear (Type II) structure of
the primes or the *phases* of S(χ)² correlated with χ̄(a). This is the precise sense in which the
"loss comes from the sum over the characters" (Banks **[READ 2609.37434]**).

---

## 5. Which tools could plausibly beat the log loss, and why

Ranked by plausibility, given the barriers in §4.3.

**1. A Type II (bilinear) estimate for A_a, attacking reformulation 2.** *Most plausible route,
but nothing in the literature supplies it yet.*
- *Why:* §4.3 forces bilinear input. A_a already has power-saving Type I level m^{1/16} (§1.2),
  so Type II is the only missing piece, exactly as in Friedlander–Iwaniec-style "primes in sparse
  sequences" theorems.
- *Quantitative input needed:* for U ∈ [m^{1/32}, m^{1/2}] (narrower if using Harman's sieve) and
  divisor-bounded α_u, β_v,
  Σ_{u∼U, v∼V, uv≤m} α_uβ_v (1[a·\overline{uv} mod m ∈ P] − expected) ≪ UV(log m)^{−A}.
  Equivalently, beat Parseval in (1/φ)Σ_χ χ̄(a)S(χ)B(χ) by (log m)^{1/2+ε} (§1.5).
- *Candidate machinery:* bilinear and multilinear Kloosterman sums with arbitrary weights
  (Bourgain–Garaev Thm 8/Cor 1, valid at N1N2 ≈ m; Bourgain's sum-product in Z_q; KSWX; Shkredov
  incidences; Pascadi for composite m). The obstruction to overcome is converting the
  multiplicative condition plus archimedean cut into additive-character sums without paying a
  rough L¹ norm (§1.5). The argument must also use that the coefficients come from μ/Λ, because
  of the quadratic-twist counterexample for general Siegel–Walfisz coefficients.

**2. Better Kloosterman sums over primes, for a level of distribution of A_a near m^{1/2}
(reformulation 2, Chen-type intermediate target).**
- *Why:* this would not give EOS (parity), but θ = 1/2 gives a ≡ p·P_3 (Greaves), and a Chen
  switching argument should give a ≡ p·P_2. That would be the natural "EOS-minus-parity" theorem.
  Even averaged-over-d versions (Σ_{d≤D}|r(d)|) would suffice, and those are bilinear Kloosterman
  sums over primes, where Irving/Baker/FS-type averaging techniques might help.
- *Input needed:* W_m(h;m) ≪ m^{1/2+ε} uniformly in h, or the averaged version over the
  h·d̄ configurations. The current exponent at x = m is 15/16 (§1.1).

**3. Phase or family cancellation in Σ_χ χ̄(a)S(χ)², attacking reformulation 1.** *The "correct"
mechanism, but beyond GRH over Z.*
- *Why:* it is exactly what §2.2 and §4.3 say is missing, and it is what proves the function-field
  analogue (Sawin, via cohomology of the whole family).
- *Input needed:* (1/φ)Σ_{χ≠χ0} χ̄(a)S(χ)² = o(μ) for every a. Under GRH, via the explicit
  formula, this becomes a twisted 2-level correlation of low-lying zeros across all χ mod m,
  with test-function support exactly at the edge (Σ supports = 2) where Hughes–Rudnick-type
  computations stop. **[OWN sketch; RECALLED for Hughes–Rudnick]** Over Z this is a
  Montgomery-type conjecture for E_2 numbers at level 1/2, not a consequence of GRH.

**4. Higher moments in a (4th central moment), attacking reformulation 1.** *Low plausibility,
but not excluded by §2.2.*
- *Why:* unlike L², the 4th moment is not ruled out by Cauchy–Schwarz.
- *Input needed:* Σ_{χ1χ2=χ3χ4, ≠χ0} S1²S2²\bar S3²\bar S4² ≪ |P|⁸/φ. This needs genuine phase
  cancellation and is equivalent to an 8-prime congruence system to relative precision 1/φ. I
  see no way to make it easier than (3).

**5. Dense model plus Kneser (Matomäki–Teräväinen) together with GRH, attacking reformulation 1.**
*Cannot work alone* (§4.2, §4.3(a)).
- *Use:* structure of the exceptional set. Any counterexample class a would force P to be
  "paired-avoiding" for a, and MT-style coset analysis plus the GRH bound O((log q)³) on the
  exceptional set (Banks–Shparlinski) constrains such a.

**Not promising:** pure energy or L⁴ bounds (§2.2); GRH pointwise on S inside Type II sums (§1.5);
"beyond 1/2" dispersion results averaged over q (§3.2), which do not apply to a single m.

---

## 6. Sources (arXiv ids or DOIs)

Read this session (PDF or abstract):
- Bourgain–Garaev, Sumsets of reciprocals in prime fields and multilinear Kloosterman sums, arXiv 1211.4184; Izv. Math 78 (2014).
- Bourgain–Garaev, Kloosterman sums in residue rings, arXiv 1309.1124.
- Irving, Average bounds for Kloosterman sums over primes, arXiv 1301.6372.
- Korolev, Kloosterman sums with primes to composite moduli, arXiv 1911.09981.
- Shparlinski, On short products of primes in arithmetic progressions, arXiv 1705.06087; PAMS 147 (2019).
- Friedlander–Kurlberg–Shparlinski, Products in residue classes, arXiv 0708.1562; MRL 15 (2008).
- Garaev, On multiplicative congruences, arXiv 0807.4318; Math Z 272 (2012).
- Garaev–Karatsuba, On a symmetric congruence and its applications, arXiv math/0503164.
- Cilleruelo–Garaev, Concentration points on two and three dimensional modular hyperbolas, arXiv 1007.1526.
- Walker, A multiplicative analogue of Schnirelmann's theorem, arXiv 1505.03328; Bull. LMS 48 (2016).
- Ramaré–Walker, Products of primes in APs: a footnote in parity breaking, arXiv 1610.05804 (abstract: q ≤ x^{1/16}, three primes ≤ x^{1/3}).
- Szabó, On the existence of products of primes in APs, arXiv 2208.05762.
- Matomäki–Teräväinen, Products of primes in arithmetic progressions, arXiv 2301.07679; doi:10.1515/crelle-2023-0096.
- Yau, On products of primes and square-free integers in APs, arXiv 1907.06016.
- Banks–Shparlinski, On the EOS conjecture for prime-power moduli, arXiv 2610.19597.
- Banks, Products of two elements of Granville's random model in residue classes, arXiv 2609.37434.
- Fouvry–Kowalski–Michel, Algebraic trace functions over the primes, arXiv 1211.6043 (intro).
- Fouvry–Kowalski–Michel, On the exponent of distribution of the ternary divisor function, arXiv 1304.3199 (abstract).
- Korolev–Shparlinski, Sums of algebraic trace functions twisted by arithmetic functions, arXiv 1804.01337 (abstract).
- Fouvry–Radziwiłł, Level of distribution of unbalanced convolutions, arXiv 1811.08672; Another application of Linnik's dispersion method, arXiv 1812.00562.
- Wright, Trilinear Kloosterman fractions I, II, arXiv 2604.25177, 2608.27732.
- Kerr–Shparlinski–Wu–Xi, Bounds on bilinear forms with Kloosterman sums, arXiv 2204.05038 (abstract and contents).
- Shkredov, Modular hyperbolas and bilinear forms of Kloosterman sums, arXiv 1905.00291 (abstract); On asymptotic formulae in some sum–product questions, arXiv 1802.09066 (abstract).
- Pascadi, Non-abelian amplification and bilinear forms with Kloosterman sums, arXiv 2511.08445 (abstract).
- Garaev–Shparlinski, On the distribution of modular inverses from short intervals, arXiv 2304.07953 (abstract; lower bounds, not directly relevant).
- Zhao, On products of primes and almost primes in APs, Acta Arith 204 (2022), doi:10.4064/aa211215-2-6 (abstract only).

Cited secondhand or recalled (not opened): Garaev, Math. Notes 88 (2010); Fouvry–Shparlinski,
Acta Arith 150 (2011); Fouvry–Michel, Ann. Sci. ENS 31 (1998); Bourgain, IJNT 1 (2005); Baker,
Acta Arith 156 (2012); Shparlinski, Period. Math. Hungar. 67 (2013); Bourgain, J. Anal. Math 106
(2008); Friedlander–Iwaniec, Annals 121 (1985); Heath-Brown, Acta Arith 47 (1986); Sawin, Acta
Math 233 (2024); Xie, Math Z 313 (2026); Klurman–Mangerel–Teräväinen, PLMS 127 (2023); EOS,
Period. Math. Hungar. 18 (1987), doi:10.1007/BF01848086; Shparlinski, Modular hyperbolas,
Jpn. J. Math 7 (2012), doi:10.1007/s11537-012-1140-8 (survey, recommended next read).
