# 04: Where has an exact Parseval identity been beaten pointwise in a binary problem?

Written 2026-11-23. Targeted review for the obstruction in `notes/01-parseval-wall.md`.
Scripts and output: `compute/lit04/smooth_toy.py`, `compute/lit04/out_smooth_toy.txt`.
The saved output covers m = 10007, 100003, 1000003. Figures quoted for m = 4000037 come from an earlier run of the
same script with that modulus added to the list; they are not in the saved file.

**Labels.** [READ] = I read the statement in the paper (abstract and introduction, via the arXiv PDF) in this session.
[SNIPPET] = confirmed only through a search-result excerpt. [RECALLED] = from memory, **[UNVERIFIED]**.
[OWN] = derived here; each such claim also carries *proved* / *sketched* / *heuristic* / *computed*.
I did not re-derive anything already in `lit/01`–`03` or routes A–D; where they cover an item I only point to them.

Notation as in `00-setup.md`. "Volume" of a multiplicative congruence means the number of tuples in the box.
"Deficit" means (Parseval bound for the error) / (main term). EOS has volume m²/log² and deficit log m.

---

## 0. Summary

**Answer to the question.** Every pointwise, fixed-target, binary result that beats an L² identity uses one of
five mechanisms. None supplies the missing log for EOS. Three of them are worth building on.

| # | Mechanism | Where | Gain over L² | Needs | Transfers to EOS? |
|---|---|---|---|---|---|
| M1 | Complete algebraic sums (Weil/Deligne) after Poisson in a **smooth** variable | xy ≡ a in boxes; d₂, d₃ in progressions; sieve Type I for A_a | power of m | a smooth variable, or a prime variable with Vaughan plus Kloosterman sums over primes | Only as Type I data (level m^{1/16}). Parity-limited. Already route A. |
| M2 | Factorable modulus (q-van der Corput) | Irving (d₂), Xi (d₃), Zhang/Polymath, Maynard III | power of m | m smooth, and a smooth variable or a moduli average | Sub-problem only (D §4.2). Does **not** solve the smooth toy (§2.3). |
| M3 | Divisor switching plus "few integers have a divisor in the critical window" | Hooley–Linnik n = p + x² + y²; Titchmarsh divisor problem | exactly the critical range, a power of log | one variable is a convolution 1 ∗ χ; the other has Type I level 1/2 | The multiplicative analogue needs Type I level 1/2 for A_a. We have 1/16. GRH gives nothing (§2.1). |
| M4 | Weighted L² identity whose physical side an upper-bound sieve controls | Goldbach–Linnik (p₁ + p₂ + K powers of 2), Chen | constant factors only | an auxiliary set, or switching | Already in r3 §4 item 2. The removal of the auxiliary set is the parity constant. |
| M5 | Positive-characteristic identity for μ (Pellet / Sawin–Shusterman) | twin primes and Goldbach over F_q[T], q > 685090 p², p odd | parity barrier removed | char p, q large in terms of p | No integer shadow. Nothing for F_2[t], F_3[t]. |
| — | Inverse theorems (large sieve, Parseval saturation) | Green–Harper, Walsh, Helfgott–Venkatesh | — | many moduli | No. The barrier sets of `lit/02` §4.3 are counterexamples to any single-modulus inverse theorem (§1). |
| — | Stepanov / polynomial method | sums in multiplicative subgroups | pointwise *upper* bounds beyond Weil | the set is cut out by a low-degree equation | No. P is not algebraic. |

**New facts found on the way** (all [OWN]; details in §2.3):

1. The smooth toy D₄(a) at prime modulus is **open** as far as I can find. Its hyperbolic version is "d₄ in progressions at level exactly 1/2". Linnik's exponent 1/2 means q ≤ x^{1/2−ε}. No individual-modulus result reaches x^{1/2}, for prime or for smooth q [READ: Parry 2404.04749 table; Wei–Xue–Zhang 1512.01470].
2. The **conjugate** toy n₁n₂ ≡ a n₃n₄ is trivially solvable for prime m (Thue plus pigeonhole; *proved* up to one elementary solvability check). So the toy is conjugation-asymmetric in the opposite direction to EOS, and a proof of the toy may be conjugation-blind.
3. For *existence* in the toy the true deficit is not log m but m/|M| = (log m)^{δ+o(1)}, δ = 0.0860…, where M is the √m-multiplication table (*sketched*, from Ford's theorem). The toy is "M·M = G for a set of density (log m)^{−δ}".
4. *Computed:* the toy holds with room for prime m ≤ 4·10⁶ (min D₄/mean = 0.42, 0.64, 0.80, 0.86 at m ≈ 10⁴, 10⁵, 10⁶, 4·10⁶). The conjugate count has an O(1) singular series, with minimum 0.217·mean at a = −1, stable in m.
5. GRH for Dirichlet L-functions gives **no** Type I information on A_a = {a p̄ mod m} at any level above (log m)^{−1}; all of it comes from Kloosterman sums over primes (*proved* as a statement about the Parseval bound, §2.1). This sharpens Cor G2.

---

## 1. Inverse theorems for the large sieve and Parseval saturation

### 1.1 What the literature proves

- **Green–Harper**, *Inverse questions for the large sieve*, GAFA 24 (2014), arXiv:1311.6176 [READ, introduction].
  Setting: A ⊂ [X] with A mod p ⊂ S_p, |S_p| = (p+1)/2 for all primes p ≤ X^{1/2}. The large sieve gives |A| ≪ X^{1/2}.
  - Thm 1.1: if each S_p has at least (1/16 + δ)p³ additive quadruples, then |A| ≪ X^{1/2 − cδ²}.
  - Thm 1.2: if each S_p is an interval of length ≤ (1 − ε)p for a proportion ε of p, then |A| ≪ (log log X)^{C log(1/ε)}.
  - Thm 1.3: S_p an arithmetic progression of length (1 − ε)p gives |A| ≪ X^{1/2 − ε′}.
  - Thm 1.4, 1.6 ("robustness"): if A is at all close to a rational quadratic then it is very close to one. The inverse conjecture itself (Conj 1.5, 1.7) is open: "Unfortunately we cannot solve the problem itself."
  - Mechanism: Gallagher's larger sieve and additive energy of S_p; for robustness, a comparison with a quadratic.
- **Helfgott–Venkatesh**, *How small must ill-distributed sets be?* (2009), and **Walsh**, *The inverse sieve problem in high dimensions* (Duke 2012) and *The algebraicity of ill-distributed sets* (GAFA 2014) [RECALLED, UNVERIFIED]: a set in [N]^d occupying ≪ p^{κ} classes mod p for all p, of nearly maximal size, lies mostly on an algebraic variety of bounded degree. Mechanism: Bombieri–Pila determinant method.
- **Elsholtz**, *The inverse Goldbach problem*, Mathematika 48 (2001) [RECALLED, UNVERIFIED]: if A + B agrees with the primes from some point on, then A(N), B(N) = N^{1/2+o(1)}. Mechanism: A + B ⊂ primes forces A and B to avoid many residue classes mod many p; then Montgomery's large sieve plus Gallagher's larger sieve. Elsholtz–Harper (Trans. AMS 2015) refine this [RECALLED, UNVERIFIED].
- **Hanson–Petridis** (PLMS 2020, arXiv:1905.09134) [SNIPPET]: if A + B ⊂ H ∪ {0} for a multiplicative subgroup H ≤ F_p^×, then |A||B| ≤ |H| + |(−A) ∩ B|. Mechanism: Stepanov's method. Later work settles when a subgroup is a sumset [SNIPPET: arXiv:2607.24270, 2504.10202].

### 1.2 Could an inverse theorem contradict E(a) ≈ −μ? No.

- *Proved (trivial).* E(a) ≤ −(1 − ε)μ is equivalent to N(a) ≤ εμ, i.e. |P ∩ ι_a(P)| ≤ εμ. Equality in Cauchy–Schwarz carries no further information: "P is nearly anti-symmetric under ι_a" is the negation of EOS, restated.
- *Proved (by the existing barrier sets).* A single-modulus inverse theorem would have to say: a set B ⊂ G with |B| = |P| and B ∩ ι_a(B) = ∅ has structure that primes lack. But:
  - the random pairing-avoiding set (`lit/02` §4.3(b)) has no structure beyond the pairing;
  - the deleted set P \ R_a (deletion barrier) differs from P in o(|P|) elements;
  - A\* (route A, Theorem B) shares all Type I data and sizes with P.
  So the conclusion "structured" must be drawn from Type II information about P, and then the "inverse theorem" is a Type II estimate for A_a under another name.
- *Why the multi-modulus theorems do not apply.* All results in §1.1 use the reductions of one integer set modulo **many** primes, and their conclusion is algebraicity in Z. EOS failure at a says A_a ⊂ {n ≤ m : n has a prime factor ≤ √m or n | …}, i.e. A_a is **covered** by the classes 0 mod ℓ. A covering condition is not a sieve condition; the larger sieve says nothing about it (sketched).
- The Elsholtz / Hanson–Petridis family ("C is not a sumset/product set") is the closest in shape: EOS failure is the containment a·P^{−1} ⊂ G \ P. Their tools need either many moduli (Elsholtz) or that the target set is a subgroup, hence the zero set of x^t − 1 (Stepanov). G \ P is neither.

**Verdict: dead for EOS and for the toy.** Label: the reduction is proved; the survey of statements is as labelled.

---

## 2. Binary problems with a fixed target

### 2.1 Additive problems with one prime and one structured variable

| Problem | Status at fixed N | Mechanism | Label |
|---|---|---|---|
| N = p + s, s squarefree | every large N, asymptotic (Estermann 1931; Page, Mirsky) | μ² = Σ_{d²∣n} μ(d): Siegel–Walfisz for d ≤ log^A, trivial tail Σ_{d>D} N/d² | RECALLED, UNVERIFIED |
| N = p + x² + y² | every large N, asymptotic. Hooley 1957 under GRH (Acta Math. 97, 189–210); Linnik 1960 unconditionally by the dispersion method; Bredikhin–Linnik for other forms; Blomer–Grimmelt–Li–Rydin Myerson with x, y almost primes (GAFA 2023, arXiv:2111.01601) | r₂ = 4(1 ∗ χ₄). Divisor switching d ↔ (N − p)/d reduces to moduli d ≤ √N. GRH or Bombieri–Vinogradov handles d ≤ √N/log^A. The window √N/log^A < d < √N log^A is handled by Brun–Titchmarsh plus the fact that few integers have a divisor in a window of bounded logarithmic length (Erdős's multiplication-table estimate) | statements SNIPPET; the description of Hooley's treatment of the window is RECALLED, UNVERIFIED |
| N = p + P₂ (Chen) | every large even N, lower bound | weighted sieve plus switching; a sieve upper bound for the switched problem loses only a constant | RECALLED |
| N = p₁ + p₂ + 2^{k₁} + … + 2^{k_K} | every large even N; K = 8 (Pintz–Ruzsa), K = 7 under GRH | Gallagher: \|G(α)\| < (1 − c)L outside a tiny set. Minor arcs are bounded by sup\|G\|^{K−2}·∫\|S\|²\|G\|², and ∫\|S\|²\|G\|² counts p₁ − p₂ = 2^i − 2^j, which the upper-bound sieve bounds with the right order | RECALLED, UNVERIFIED |
| N = p + 2^k (Romanoff) | positive lower density of N only; nothing at fixed N | second moment | RECALLED |
| N = p + n² (Hardy–Littlewood Conj. H) | almost all N only, power-saving exceptional set | circle method L² | RECALLED |
| binary Goldbach under GRH | almost all; see `lit/03` §3.2 | — | covered there |

What the solved cases have in common (heuristic, but uniform across the table): **one of the two variables carries a
divisor-type (dimension-zero or 1 ∗ χ) structure, and the other variable has Type I level 1/2, which in the additive
world is free from GRH/Bombieri–Vinogradov.** Nothing in the table beats L² for two variables that are both primes.

**Multiplicative analogues** [OWN].

- *Estermann analogue (sketched).* #{p ∈ P : a p̄ mod m squarefree} ~ c_m·|P| for every a, unconditionally.
  Proof sketch: for d ≤ D use Type I data for A_a at moduli d² ≤ m^{1/16−ε} (Fouvry–Shparlinski, `lit/02` §1.2). For d > D the
  count of p with d² | (a p̄ mod m) is ≤ m/d², since n = d²k ≤ m determines p ≡ a n̄. The tail is ≤ m/D, so D = log² m suffices.
  Only Type I data to moduli ≤ log⁴ m are used. I have not checked whether this is in the literature.
- *Hooley–Linnik analogue (open; deficit computed).* "Every a is p·n with p ≤ m prime and n = x² + y² ≤ m."
  Existence deficit m/√(|P||B|) = (log m)^{3/4}; weighted by r₂ the deficit is log m. It needs Type I data for A_a at level
  m^{1/2}/log^A plus the window argument. So the mechanism M3 transfers **formally**, and the missing input is exactly
  "level of distribution 1/2 for A_a".
- *GRH gives no Type I data for A_a (proved, as a statement about the bound).* For d ≥ 1,
  #{p ∈ P : d | (a p̄ mod m)} = #{(p, k) : k ≤ m/d, p·dk ≡ a} = (1/φ)Σ_χ χ̄(a) χ(d) S(χ) T_{m/d}(χ).
  With |S(χ)| ≤ √m log m and (1/φ)Σ|T_K|² = K, the error bound is ≥ √(|P|·m/d) in the Parseval version and
  √m log m·√(m/d) in the sup version, against a main term |P|/d. Both fail for every d ≥ 1 in the range d ≪ m/log m.
  In the additive problem the same count is "primes in a progression mod d", which GRH evaluates for d ≤ √N/log².
  The difference: multiplicative characters do not detect the inverse of an interval; additive characters applied to p̄ do,
  and those are Kloosterman sums over primes, on which GRH for Dirichlet L-functions is silent.

**Verdict.** M3 is the only mechanism in this section with a formal multiplicative analogue. It would prove a
*weaker* binary statement than EOS (one prime, one sum of two squares), and it is blocked at one clearly named
parameter: the Type I level of A_a (have 1/16, need 1/2).

### 2.2 The modular hyperbola and the multiplication table mod m

- **xy ≡ a, x, y ≤ N.** Solvable for all a once N ≥ C m^{3/4}; the log factors of the completion method can be removed
  (Garaev; quoted in a 2026 ERA paper as "H_N(p) contains all nonzero residues when N is a large constant multiple of p^{3/4}") [SNIPPET].
  Volume m^{3/2}, far below the Parseval volume m². Mechanism M1: Poisson in a smooth variable, then Weil for Kl₂.
  Getting below 3/4 for all a is a well-known open problem [RECALLED].
- **Almost all a.** Garaev, *On multiplicative congruences*, Math. Z. 272 (2012), arXiv:0807.4318 [READ]:
  - Thm 1: N₁N₂N₃ > m^{1+ε} implies #{x₁x₂x₃ mod m} = m + O(m^{1−δ}), any m. The condition cannot be relaxed to N₁N₂N₃ > Cm.
  - Thm 2: the same for four variables, m cubefree, N₁N₂N₃N₄ > m^{1+ε}.
  - Corollary: every invertible λ is x₁…x₆ with x_i ≤ m^{1/3+ε} (volume m^{2+6ε}).
  - Quoted there: {x₁x₂ : x_i ≤ m^{1/2+ε}} contains almost all residues (Garaev–Karatsuba, Proc. Edinburgh Math. Soc. 50 (2007) 363–375, DOI 10.1017/S0013091505000969 [SNIPPET]).
  - Thm 3 (prime modulus): p₁p₂(p₃ + k) ≡ λ has (1+o(1))π(N)³/p solutions in primes ≤ N for N > p^{63/76+ε}.
  - Mechanism: large-value estimates for character sums; "almost all" by second moments.
- **Cilleruelo–Garaev**, arXiv:1404.5070, Math. Proc. Cambridge Philos. Soc. [READ, abstract]: almost all residues are x g^y with x < p^{5/8+ε}, y < p^{3/8}; almost all are x y z g^t with x, y, z, t < p^{1/4+ε}. Mechanism: bounds for x ≡ y r with r in a set of small doubling (Bourgain–Konyagin–Shparlinski geometry of numbers).
- **Pattern.** Every "all a" result I found has volume ≥ m^{2+ε} unless a smooth variable is long enough for M1
  (then m^{3/2}). Every result below volume m² is "almost all a". Nothing sits at volume exactly m².
- Bilinear forms with Kloosterman sums below the Pólya–Vinogradov range: Kowalski–Michel–Sawin, Annals 186 (2017), arXiv:1511.01636 [READ abstract; exact ranges RECALLED, UNVERIFIED];
  Kerr–Shparlinski–Wu–Xi and later work reach both variables of length ≥ q^{3/8+δ} [SNIPPET]. Mechanism: the "+ab" shift of
  Vinogradov–Karatsuba–Friedlander–Iwaniec, Hölder, and Deligne-type bounds for sums of products of Kloosterman sheaves.
  This **does** beat the Fourier-critical range by a power, pointwise, with arbitrary coefficients, at prime modulus.
  It needs a kernel K(xy) that is a trace function. In EOS the kernel is 1[xy ≡ a]; after Fourier inversion in the
  additive variable it becomes e(h a x̄ ȳ/m)-type only if one variable is smooth. `lit/02` §1.4–1.5 already records that
  this does not give Type II for A_a, and I found nothing newer that changes this.

### 2.3 The smooth toy D₄(a) = #{n_i ≤ √m : n₁n₂n₃n₄ ≡ a (mod m)}

**Is it known? No, as far as I can find.**

- Hyperbolic version: Σ_{n ≤ x, n ≡ a (q)} d₄(n) at q = x^{1/2}. Known exponents of distribution for an individual modulus:
  θ₂ = 2/3 (Selberg, Hooley), θ₃ = 1/2 + 1/46 for prime q (Fouvry–Kowalski–Michel, arXiv:1304.3199; 1/2 + 1/230 for general q, Friedlander–Iwaniec),
  **θ₄ = 1/2 (Linnik), meaning q ≤ x^{1/2−ε}**, θ₅ = 9/20, θ₆ = 5/12 [READ: Wei–Xue–Zhang 1512.01470 p. 1; Parry 2404.04749 table].
  Parry: "For k ≥ 4 we don't know if we can take q past √x."
- Linnik's proof of θ₄ = 1/2 is the fourth-moment (Parseval) argument, so it stops exactly where the toy starts [RECALLED].
- Smooth moduli: Irving (IMRN 2015, arXiv:1403.8031) passes 2/3 for d₂ by q-van der Corput [SNIPPET]; Xi (Mathematika 2018) gets 1/2 + 1/34 for d₃, squarefree smooth q [SNIPPET]; Khan (arXiv:1510.03377) passes 2/3 for d₂ modulo p^k, k ≥ 7 [SNIPPET].
  For d₄ the only results past 1/2 are **averaged**:
  - Wei–Xue–Zhang (arXiv:1512.01470) [READ]: Σ over smooth squarefree d < x^{293/584}, fixed a, of |Δ_{τ_k}(x; d, a)| ≪ x exp(−(log x)^{1/2}), k ≥ 4. Zhang's method; the moduli average is used in the Type I/II steps. Nguyen (arXiv:2308.06839) sharpens it [READ abstract].
  - Parry (arXiv:2404.04749) [READ]: Σ_a |Δ(a/q)|² ≪ x^{3/2+ε} q^{7/8} for prime q ≤ x^{4/7}, an average over a, from Petrow–Young subconvexity.
  The balanced shape n_i ≈ x^{1/4} of the toy is the Type II shape (ν₁ + ν₂ = 1/2) in Wei–Xue–Zhang's Lemma 3, the one that needs the moduli average.
- Twisted moments: Σ_χ χ(ℓ₁)χ̄(ℓ₂)|L(1/2, χ)|⁴ is known with power saving for prime q and small ℓ_i (Young, Annals 2011; Blomer–Fouvry–Kowalski–Michel–Milićević; Zacharias arXiv:1611.09582) [SNIPPET].
  That is the **conjugate** toy near a = ±1. I found no result on Σ_χ χ̄(a) L(1/2, χ)⁴ (no absolute values), which is the toy.

**Why q-van der Corput does not settle the toy for smooth m** [OWN, heuristic]. After Poisson in all four variables the
error is m^{−1/2} Σ_{h_i ≤ √m} K̃l₄(a h₁h₂h₃h₄; m), with m² terms; the target is a saving of m^{1/2} over the trivial bound.
Grouping (h₁h₂)(h₃h₄) and completing gives exactly m^{1/2}/log^{O(1)} (unitarity; self-dual, as in D §4.3). q-van der Corput
improves an *incomplete* sum in one smooth variable of length √m by a small power (m^{1/12} for the simplest exponent pair),
not by m^{1/2}; it cannot improve the completed bilinear step. So even for smooth m the toy is at the wall.

**New structural facts about the toy** [OWN].

1. *The conjugate toy is trivial (proved for prime m, modulo the check below).* Let B = ⌊√m⌋ and
   U = {h n̄ mod m : 1 ≤ h, n ≤ B}. By Thue's lemma every u ≠ 0 is ±h/n with 1 ≤ h, n ≤ B, so U ∪ (−U) = G and
   |U| ≥ (m − 1)/2. Also U = U^{−1}. If U ∩ aU = ∅ for some a, then |U| = (m−1)/2, U ∩ (−U) = ∅ and aU = −U.
   Now U ∩ (−U) ≠ ∅ exactly when m = h n′ + h′ n has a solution with all four ≤ B, which is an elementary additive
   statement (true for all m tested; a written proof for all large m is routine but not done here: *sketched*).
   Hence for every a there are h, h′, n, n′ ≤ √m with h h′ ≡ a n n′.
   *Computed:* |U|/(m − 1) = 0.6083, 0.6081, 0.6084, 0.6083 at m = 10007, 100003, 1000003, 4000037 (6/π² = 0.6079; heuristic identification).
2. *The toy and EOS are asymmetric in opposite directions.* In EOS the quotient problem is false at a = −1 (Theorem G).
   In the toy the quotient problem is trivially true. *Computed:* the quotient count has a singular series: its minimum is at
   a = −1 and equals 0.217·mean for all three m (second smallest 0.28·mean), while D₄(−1)/mean = 1.05, 1.00, 0.99.
   Consequence for calibration: **a proof of the toy is not forced to pass Theorem G**, so a toy proof may be conjugation-blind and fail to transfer.
   This adds a seventh caveat to D §4.3 and r3 §4 item 9.
3. *The existence deficit is (log m)^δ, not log m (sketched).* D₄(a) = Σ_{xy ≡ a} r(x) r(y), r(x) = #{n₁n₂ = x}, supported on the
   multiplication table M ⊂ [1, m]. For any 0 ≤ w ≤ r, D₄(a) ≥ Σ_{xy≡a} w(x)w(y) ≥ (Σw)²/φ − Σw². By Cauchy–Schwarz
   (Σw)² ≤ |M| Σw², with equality for w = 1_M. So the best Parseval-type lower bound has deficit φ/|M|, and
   |M| ≍ m (log m)^{−δ} (log log m)^{−3/2}, δ = 1 − (1 + log log 2)/log 2 = 0.08607 (Ford, Annals 168 (2008)) [RECALLED, UNVERIFIED].
   The full deficit log m of D §4.3 comes from Σ r² ≍ m log m, which is carried by integers with many divisors and is irrelevant for existence.
   *Computed:* |M|/m = 0.290, 0.266, 0.248, 0.240; Σr²/(m log m) = 0.566–0.575; min over a of (1_M ∗ 1_M)(a)/expected = 0.69, 0.85, 0.95, 0.97.
   So the toy is the statement M·M = G for a set of density (log m)^{−δ}: the same shape as EOS, with exponent 0.086 in place of 1.
4. *A 1 + 3 form (proved reduction).* The toy at a holds iff a·{n̄ : n ≤ √m} ⊄ Exc₃, where Exc₃ = G \ {n₂n₃n₄ mod m}.
   Garaev's Thm 1 gives |Exc₃| ≪ m^{1−δ′}; GRH gives |Exc₃| ≪ m^{1/2+ε} by the sixth moment (sketched). The toy needs √m. Critical again.
5. *Computed size of the truth.* std(D₄)/mean = 0.220, 0.125, 0.067, 0.044 at the four moduli, roughly m^{−1/2}(log m)^{3}:
   the error is of square-root size, as for EOS.

**Verdict on the toy.** Open. Best known: all a at volume m^{2+ε} (fourth moment); almost all a at volume m^{1+ε} (Garaev);
averaged results past level 1/2 (Wei–Xue–Zhang over smooth moduli, Parry over a). It is a fair model of the Parseval
deficit (log^δ for existence, log for the asymptotic), but **not** of the conjugation barrier.

---

## 3. Pointwise convolution estimates in groups

- **Kneser, Kemperman, Pollard, popular sums.** Pollard's theorem bounds Σ_c min(t, 1_A ∗ 1_B(c)) from below in Z/p, i.e. the
  number of t-popular sums. It is a statement about *many* c, and it is symmetric under A ↦ A^{−1}. Dead by Theorem G (D §1.3). [RECALLED]
- **Quasirandom groups (Gowers; Babai–Nikolov–Pyber).** |A||B||C| > |G|³/d_min gives ABC = G. For two sets one needs |A| + |B| > |G| in general. G = (Z/m)^× is abelian, d_min = 1. No content. [RECALLED]
- **Bourgain–Gamburd, Helfgott.** Growth and spectral gap in SL₂(F_p). The pointwise statement there is flattening of the
  measure after ≍ log p convolutions, not two. [RECALLED]
- **Multiplicative subgroups H ≤ F_p^×, additive binary problem h₁ + h₂ = a.**
  - Fourier (Gauss sums, the analogue of M1): every a ≠ 0 is a sum of two elements once |H| > p^{3/4}. [RECALLED]
  - Bourgain–Glibichuk–Konyagin: sup_ξ |Σ_{h∈H} e(ξh/p)| ≤ |H| p^{−δ} for |H| > p^ε. This is a *sup* bound from sum-product; it gives kH = F_p for k ≥ k(ε), never k = 2. It is the analogue of GRH's role in the ternary problem. [RECALLED]
  - Heath-Brown–Konyagin (2000), Shkredov–Vyugin: #{(x, y) ∈ H² : x + y = a} ≪ |H|^{2/3} for small H, by Stepanov's method. A pointwise *upper* bound that Fourier analysis cannot give. It uses that H is the zero set of x^t − 1. [RECALLED, UNVERIFIED]
  - Hanson–Petridis and successors (§1.1): sumsets inside subgroups, same method.
- **Transference to density 1/log.** Green; Shao (Duke 2014, density version of Vinogradov); Matomäki–Maynard–Shao; Matomäki–Teräväinen for products of three primes (`lit/02` §4.2). The dense model controls the L^∞ norm of the Fourier transform, which bounds ternary forms pointwise and binary forms only on average. Binary results for subsets of primes are of the type "A + B has positive density" (Ramaré–Ruzsa, Matomäki), never a fixed target. [RECALLED]

**Verdict.** No pointwise two-fold convolution lower bound for sparse sets exists in this literature without
(i) density above 1/2, (ii) an algebraic definition of the set, or (iii) a third variable. All three are already
excluded for EOS (pigeonhole fails at density 1/log; P is not algebraic; three primes is known).

---

## 4. Exact identities that bypass Parseval

### 4.1 What each method averages over

| Method | Fixed | Averaged | Why the average is essential |
|---|---|---|---|
| Linnik dispersion (Titchmarsh, Hooley–Linnik) | target N | the divisor d of N − p, which acts as a modulus | opening the square produces n₁ ≡ n₂ (mod d) for varying d; then divisor switching |
| Bombieri–Friedlander–Iwaniec; Fouvry; Fouvry–Iwaniec | residue a, \|a\| ≪ x^ε | moduli q ≤ x^{1/2+δ} | after switching, a becomes part of the modulus of a Kloosterman sum; spectral theory (Deshouillers–Iwaniec) sums over the level |
| Zhang; Polymath8; Wei–Xue–Zhang | a (or a root of a polynomial) | smooth moduli d = qr | dispersion over r; Weil/Deligne mod q with q of convenient size |
| Maynard I, II (arXiv:2006.06572, 2006.07088) | a | moduli, with (triply) well-factorable weights | as BFI, with better Kloosterman-sum estimates [RECALLED, UNVERIFIED] |
| Maynard III (arXiv:2006.08250) [READ abstract and introduction] | nothing: uniform in residue classes | moduli of size x^{1/2+δ} with a conveniently sized divisor | "Any method exploiting bounds for sums of Kloosterman sums via the spectral theory of automorphic forms necessarily introduces a dependence on the residue class"; uniformity is recovered from factorable moduli, still with a moduli sum |
| Heath-Brown square sieve; large sieve for square moduli | — | a family of quadratic characters | detects squares by an average over auxiliary primes [RECALLED] |
| Duke–Friedlander–Iwaniec, Kloosterman fractions | — | both entries of the fraction a d̄/c, bilinearly | amplification over the modulus c [RECALLED]; D §4.9 |
| Friedlander–Iwaniec, FKM, Xi, Irving (d₂, d₃) | **single modulus, every a** | nothing | all variables smooth: M1, plus M2 for smooth q |

So the only **single-modulus, every-a** results past the L² range are those in the last row, and they need all
variables smooth and at most three of them.

### 4.2 Can averaging over the residue side replace averaging over moduli? No (sketched).

- An average over a ∈ W of N(a) is Σ_{p,q} 1_W(pq mod m). For W a coset this restricts the character sum to H^⊥
  (r3 §4 item 2: cosets need ≥ L′ classes). For W an interval it is a bilinear exponential sum, giving intervals of
  length √m log^C. For general W, Cauchy–Schwarz against the variance gives |W| ≥ log⁵ m (route C). All of these are in the repo.
- The structural reason: in the dispersion method the sum over moduli q creates **new equations** n₁ ≡ n₂ (mod q) with q
  variable, and divisor switching replaces q by the complementary divisor, which lowers the conductor. An average over
  residues of a *fixed* modulus is a unitary change of basis on the fixed group G; it permutes the Parseval mass and cannot lower it.
- For EOS specifically there is no hidden modulus to average over: pq = a + km with p as modulus forces
  k ≡ −a m̄ (mod p), and then q = (a + km)/p runs over one residue class mod m with q ≤ m, i.e. one value (proved; this is D §4.9 in other words).
- Fibre averaging for factorable m (m = m₁m₂, split p by its class mod m₁) is the same unitary operation (proved for the square case in D §2.2).
- The fixed residue of BFI/Zhang/Maynard is a fixed **integer** a of small height seen by many moduli. For a single m, a
  residue a of small height (a = ±1, 2, …) gets no help: the product side has no singular series at small heights (r3 §4 item 3).

**Verdict.** Dead as a route. The one transferable piece is M2 for the Type I and Type II levels of A_a when m is smooth (D §4.2), which is parity-limited.

---

## 5. The function-field small-q regime

- **Sawin–Shusterman**, *On the Chowla and twin primes conjectures over F_q[T]*, Annals 196 (2022), arXiv:1808.04001 [READ, introduction].
  - Thm 1.1: p odd, q a power of p, **q > 685090 p²**: #{f : |f| = X, f and f + h prime} ~ S_q(h) X/log_q²X as X → ∞, with a power saving. Remark 1.2: the proof also gives the Goldbach analogue.
  - Thm 1.3: Chowla for k shifts when q > p²k²e². Examples: F_{3^6}, F_{5^5}, F_{7^4}, F_{31^3}.
  - Mechanism (their words, paraphrased): for fixed r, μ(r + s^p) "essentially equals" χ_{D_r}(s + c_r) for a quadratic character χ_{D_r}.
    Reason: μ(f) is the sign of Frobenius on the roots, hence the quadratic character of disc(f) = Res(f, f′), and (r + s^p)′ = r′.
    Then a Burgess-type bound for short character sums, improved geometrically, and a Fouvry–Michel-type estimate give level of distribution beyond 1/2 for primes.
  - Fixed q, degree → ∞, binary, fixed target. This is the only complete solution of a binary prime problem I know in any setting.
  - Why q must be large: the short character sums have conductor growing with deg r; the Burgess-type saving is a power of q that must beat p. Not available for q = p.
- **Sawin–Shusterman**, quadratic Bateman–Horn over F_q[T] (Inventiones 2022) [RECALLED, UNVERIFIED]: same trick.
- **Large q, fixed degree:** Bender; Pollack; Bary-Soroker; Bank–Bary-Soroker–Rosenzweig; Entin; Carmon (characteristic 2, large q). Bender's Goldbach needs q > 8(n+6)^{2n²} [SNIPPET]. These are Chebotarev/monodromy statements and say nothing as n → ∞.
- **Small fixed q.** Cherly: for q > 2 fixed, every polynomial of large degree is a sum of two almost-irreducibles (sieve) [SNIPPET]. Hall, Pollack: infinitely many twin prime pairs for q > 3 from explicit families (x^{ℓ^k} − β) [RECALLED, UNVERIFIED]; these are constructions, useless at a fixed target. Effinger–Hayes: ternary Goldbach for all q [RECALLED].
  **I found no result for a binary multiplicative or additive prime problem over F_2[t] or F_3[t] at large degree.** A search for 2023–2026 work returned nothing.
- Sawin (arXiv:2102.09730) and Xie (arXiv:2510.17612) on EOS over F_q[t] are in route B; both need q large.

**Verdict.** M5 is a genuine removal of parity, but its engine is that f ↦ f′ kills p-th powers. r3 §4 item 4 already
records that characteristic-p parity structure has no integer shadow. The useful negative information: even with every
geometric tool, nobody has a binary result at q = 2, 3, which is the regime where Deligne alone loses, as over Z.
For EOS over F_q[t] with q > C p² and n → ∞, Sawin–Shusterman's level of distribution beyond 1/2 for primes might give a
second, non-monodromy proof (heuristic; not checked, and Sawin's theorem already covers fixed large q).

---

## 6. Why each mechanism does or does not transfer (one line each)

1. **M1 (smooth variable plus Weil).** Transfers as Type I data for A_a through Kloosterman sums over primes. It is the only source of such data (§2.1). Ceiling: parity.
2. **M2 (factorable modulus).** Raises the levels in M1 for smooth m. Does not touch the bilinear, completed step, so it solves neither the toy nor EOS.
3. **M3 (divisor switching plus sparse critical window).** Transfers formally to "prime times sum of two squares". Blocked at Type I level 1/2 for A_a.
4. **M4 (weighted L² with a sieve-bounded physical side).** Already used (r3). Costs an auxiliary set; removing it is the parity constant.
5. **M5 (characteristic p).** No transfer.
6. **KMS "+ab" shift.** Beats the Fourier range by a power for trace-function kernels. EOS has no such kernel unless a variable is smooth.
7. **Stepanov.** Needs an algebraic set. No transfer.
8. **Inverse theorems.** Vacuous at a single modulus.
9. **Harper's "better than squareroot cancellation"** (arXiv:2301.04390; survey arXiv:2512.23681) [SNIPPET]: (1/φ)Σ_χ |Σ_{n≤x} χ(n)| = o(√x). The L² mass of T(χ) sits on a sparse set of χ, the Fourier-side mirror of fact 3 in §2.3. It is a statement about low moments, hence about typical χ, and gives no pointwise information in a (heuristic). D §4.6 stands.

---

## 7. Machinery worth building (ranked)

1. **The Type I level of A_a as an explicit parameter θ, with its corollaries.**
   - Lean: a named `Prop` for "A_a is equidistributed mod d for d ≤ (log m)^C, uniformly in a" (cited: Fouvry–Shparlinski), and from it the
     Estermann analogue "every a is p·s, s squarefree, p, s ≤ m". It is the first fixed-target binary theorem in the repo that beats Parseval, and it is cheap.
   - Mathematics: write the multiplicative Hooley–Linnik reduction: θ = 1/2 − ε plus the sparse-window lemma ⇒ every a is p·(x² + y²). This makes "θ = 1/2" a hypothesis with a concrete binary corollary, weaker than H4 in kind (it is Type I only).
   - Numerics: measure the discrepancy of a p̄ mod m in classes mod d for d up to √m (is level 1/2 true with a power saving, as expected?).
   - Mathematics: for smooth m, push 1/16 up by q-van der Corput on Kloosterman sums over primes (D §4.2).
2. **A toy kit that is honest about what the toy models.**
   - Prove and record: conjugate toy by Thue plus pigeonhole (finish the m = hn′ + h′n check); existence deficit = φ/|M|; the 1 + 3 reduction.
   - Replace the calibration target "asymptotic for D₄" by **"M·M = G"**, deficit (log m)^{0.086}. It is the mildest known instance of the wall.
   - First lemma to try: a lower bound (1_M ∗ 1_M)(a) ≥ c|M|²/m for prime m, using that M has Type I structure in both factors (n₁n₂ with n₁ smooth of length √m) and the KMS bilinear bounds below the Pólya–Vinogradov range. My estimate of success: 10–15%. A failure would say that even a (log m)^{0.086} deficit cannot be beaten with complete algebraic information.
   - Script: `compute/lit04/smooth_toy.py` (extend to composite and smooth m, and to Exc₃).
3. **The sparse-critical-window lemma (Hooley, Erdős–Ford) as a reusable tool.** Statement to isolate: if the L² mass of a
   weight sits on integers with a divisor in a window of bounded logarithmic length, that part can be bounded by an
   upper-bound sieve at the cost of a constant, because such integers have density (log)^{−δ+o(1)}. Test it on the block
   decomposition of the Buchstab sum (Lemma N loses L^{3/2} per block): can the number of critical blocks be cut by a Ford-type bound? (heuristic; I have not checked it against r3 §3.)
4. **A calibration table of barriers for every toy.** Each proposed calibration problem should be run through the conjugate
   problem numerically first (as in `smooth_toy.py`): if the conjugate problem is true, the toy does not test Theorem G. Cheap, and it would have flagged the D₄ toy.
5. **(Low priority) F_2[t] and F_3[t].** No literature to build on. The only concrete item is to test numerically whether the
   Sawin–Shusterman quasi-periodicity of μ(r + s^p) has a usable form at q = p = 3 for the EOS count (the Burgess step fails there, so the saving would have to come from elsewhere).

---

## 8. Not checked

- The exact ranges in Kowalski–Michel–Sawin, Young's and BFKMM's exponents, Maynard I–II, Helfgott–Venkatesh, Walsh, Elsholtz, Heath-Brown–Konyagin, Ford's exponent of log log: all RECALLED.
- Hooley's handling of the critical window (the Project Euclid PDF was not retrievable). The mechanism M3 as described is from memory of Hooley's monograph.
- Whether the Estermann analogue or the multiplicative Hooley–Linnik problem appears in the literature (one search, nothing found).
- Whether "M·M = G" for the multiplication table mod p is stated anywhere as a problem. Garaev–Karatsuba treat the exceptional set of the table itself; I did not read the paper.
- MathSciNet was not available; searches were arXiv and general web only.
- The identification |U|/(m−1) → 6/π² is numerical only.

## 9. Sources

Read in this session (arXiv PDF, abstract and introduction): 1311.6176 (Green–Harper); 0807.4318 (Garaev); 1404.5070 (Cilleruelo–Garaev);
1512.01470 (Wei–Xue–Zhang); 2404.04749 (Parry); 2308.06839 (Nguyen, abstract); 1808.04001 (Sawin–Shusterman); 2006.08250 (Maynard III); 1511.01636 (Kowalski–Michel–Sawin, abstract).

Snippet only: 1304.3199 (Fouvry–Kowalski–Michel); 1403.8031 (Irving); Xi, Mathematika 2018 (d₃, smooth moduli); 1510.03377 (Khan); 1611.09582 (Zacharias);
2301.04390, 2512.23681, 2607.01184 (Harper); 2405.04094 (Wang–Xu); 1905.09134 (Hanson–Petridis); 2607.24270, 2504.10202 (subgroups are not sumsets);
2111.01601 (Blomer–Grimmelt–Li–Rydin Myerson); 0912.1702, 0809.4381 (Goldbach over F_q[t]); Garaev–Karatsuba, DOI 10.1017/S0013091505000969;
Hooley, Acta Math. 97 (1957) 189–210, DOI 10.1007/BF02392397.

Recalled: Linnik (dispersion method, 1960); Estermann (1931); Chen; Pintz–Ruzsa; Gallagher (1975); Ford, Annals 168 (2008); Young, Annals 173 (2011);
BFKMM (twisted moments); Bombieri–Friedlander–Iwaniec I–III; Maynard 2006.06572, 2006.07088; Helfgott–Venkatesh (2009); Walsh (2012, 2014);
Elsholtz (2001); Elsholtz–Harper (2015); Heath-Brown–Konyagin (2000); Bourgain–Glibichuk–Konyagin (2006); Shao (2014); Sawin 2102.09730; Xie 2510.17612.
