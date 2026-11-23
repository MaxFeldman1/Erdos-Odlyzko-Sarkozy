# Literature strand 01: direct literature on EOS and products of primes in residue classes

Compiled 2026-11-22. Conventions: q or m is the modulus, a ∈ (Z/qZ)^*.
E_k(N) = {a : a ≡ p_1⋯p_k (mod q), p_i ≤ N} (the Matomäki–Teräväinen notation; Banks–Shparlinski write EOS_k(q;x)).
EOS is the statement E_2(q) = (Z/qZ)^* for all large q.

**Provenance tags.**
- **[READ]**: I read the statement in the source PDF or abstract this session. arXiv PDFs were downloaded and text-extracted, and the 1987 paper was read as an OCR scan from the Rényi Institute's Erdős archive.
- **[SECONDARY]**: the statement is as quoted by a later paper I read. I did not read the primary source.
- **[RECALL]**: from memory.
- **[UNVERIFIED]**: not checked.
- **[MINE]**: my own derivation or computation. It does not appear in any source I found. Each [MINE] claim also carries the project status tag: proved, sketched or heuristic.
- Every literature statement tagged [READ] is a *proved* result in a published or arXiv source. Correctness is the source's; I did not re-check the proofs.

---

## 0. One-paragraph summary

EOS is open, even under GRH. Every source I read says so explicitly: FKS 2008, Walker 2016, Shparlinski 2019, Szabó 2024, Matomäki–Teräväinen 2024, Banks 2026, and Banks–Shparlinski 2026.

**Under GRH, the known results are these.**
- EOS 1987, for q prime:
  - every a is p_1p_2 with p_i ≤ C q (log q)^4;
  - all but O((log q)^5) classes a are p_1p_2 with p_i ≤ q;
  - every a is p_1p_2p_3 with p_i ≤ q. This needs only a very weak quasi-RH, not full GRH.
- Banks–Shparlinski (Oct 2026), for arbitrary q, conditional on GRH:
  - all but O((log q)^3) classes are p_1p_2 with p_i ≤ q;
  - every a is ℓ_1ℓ_2ℓ_3 with ℓ_1, ℓ_2 ≤ q and ℓ_3 ≪ (log q)^4.

**Unconditionally, the best results are Matomäki–Teräväinen (Crelle 2024).**
- |E_2(q)| ≥ (2/3 − ε)φ(q) for all large q.
- |E_2(q)| ≥ (11/16 − ε)φ(q) for cube-free q.
- E_3(q) is everything for large cube-free q.
- E_3(q^{1+ε}) is everything for all large q.

**The barrier.** Everyone describes it the same way. The character-sum expansion loses a factor of about φ(q)/π(q) ≍ log q through Parseval. GRH gives square-root cancellation inside each χ, but nothing about the phases across χ.

**Small moduli.** My computation shows that the conjecture genuinely needs "m large". It fails for exactly 48 moduli m ≤ 2·10^5, the largest being m = 401 (§7).

---

## 1. Erdős–Odlyzko–Sárközy (1987): the source paper

**Citation.** P. Erdős, A. M. Odlyzko, A. Sárközy, *On the residues of products of prime numbers*, Period. Math. Hungar. 18 (1987), no. 3, 229–239. DOI 10.1007/BF01848086. zbMATH 0625.10035. The PDF is at https://static.renyi.hu/~p_erdos/1987-22.pdf.

**[READ]**, from the OCR scan of the full paper. It is 11 pages and was received 6 Aug 1985.

**Setting.** Throughout, **q is a large prime**. The paper uses weighted counts:
- G(a,k) = Σ_{p_i ≤ q, p_1⋯p_k ≡ a} log p_1⋯log p_k;
- F(a,k) = the number of solutions;
- f(x,a,k) is the same count with p_i ≤ x.

The paper says that Erdős conjectured F(a,2) > 0 for q > q_0. The authors write that it is "almost certainly true, but will be hopelessly difficult to prove".

**Hypothesis H(θ_q, x).** Here 1/2 < θ_q < 1. The hypothesis says that no L(s,χ) mod q vanishes in Re s > θ_q, |Im s| < x^{1−θ_q}.
- Lemma 1: under H(θ_q, x), |ψ(x,χ) − E_0 x| < c x^{θ_q}(log x)^2. This is quoted from Prachar.
- Lemma 3 (Parseval): Σ_χ |ψ(q,χ)|^2 < 2q^2 log q.

**Theorem 1 and Corollary 1 (almost all a).** Under H(θ_q, q):

Σ_{a=1}^{q−1} (G(a,2) − q)^2 < c q^{1+2θ_q}(log q)^5.

Hence F(a,2) > 0 for all but c q^{2θ_q−1}(log q)^5 residues a. **Under GRH, this leaves at most c(log q)^5 exceptional a.**
- Method: a variance computation. Expand in characters, then bound by max_{χ≠χ_0}|ψ(q,χ)|^2 · Σ_χ|ψ(q,χ)|^2. The first factor is GRH and the second is Parseval. Lemma 4 removes the prime powers.

**Theorem 2 and Corollary 2 (ternary, all a).** Suppose H(θ_q, q) holds with θ_q ≤ 1 − 3 log log q / log q. Then

|G(a,3) − q^2| < c q^{1+θ_q}(log q)^3 for all a.

So if θ_q = 1 − (3+ε) log log q / log q, then **F(a,3) > 0 for every a**: every class is p_1p_2p_3 with p_i ≤ q. This needs only a zero-free strip of width ≍ (log log q)/log q, far weaker than GRH.
- Method: the third moment is bounded by max|ψ| times the L^2 norm.

**Theorem 3 and Corollary 3 (binary, all a, longer range).** There is an absolute constant c_15 with the following property. Suppose 1/2 ≤ θ_q < 1 − q^{−1/10} and H(θ_q, x) holds with

x = (c_15 q)^{1/(2(1−θ_q))} · (log q/(1−θ_q))^{2/(1−θ_q)}.

Then f(x,a,2) > 0 for all a.
- **Corollary 3 (GRH):** f(c_16 q (log q)^4, a, 2) > 0 for all a. So under GRH, every a ≡ p_1p_2 with **p_1, p_2 ≤ C q (log q)^4**, giving **C = 4**.
- Method: purely pointwise. The main term is x^2/q. The error is (1/q)Σ_{χ≠χ_0}|ψ(x,χ)|^2 ≤ max|ψ(x,χ)|^2 ≪ x(log x)^4, using GRH with (log x)^2 per sum. Orthogonality is not used.
- They also show f(x,a,2) ≫ x^2/(q(log x)^2).

**What they did not do.**
- Nothing for composite q.
- Nothing for almost all m.
- No unconditional results. The paper says "Part II will be devoted to weaker but unconditional results." I found no trace that Part II ever appeared [UNVERIFIED].

**Effectivity.** All the constants c_i are absolute. The conditional results are effective given the hypothesis. This is my reading; the paper does not discuss it.

**Answers to the orchestrator's questions.**
- Yes: GRH gives p, q ≤ m (log m)^C with **C = 4**, for prime m. The setup sketch's "expected consequence" is already in EOS 1987.
- The almost-all-a result is in the paper: at most O(log^5 q) exceptions under GRH.
- There is no almost-all-m result in EOS 1987.

---

## 2. Friedlander–Kurlberg–Shparlinski (2008): averages over moduli

**Citation.** J. B. Friedlander, P. Kurlberg, I. E. Shparlinski, *Products in residue classes*, Math. Res. Lett. 15 (2008), 1133–1147. DOI 10.4310/MRL.2008.v15.n6.a6. arXiv:0708.1562. **[READ]**

**Statement.** Write P(x;m,a) for the number of pairs of primes p_1, p_2 ≤ x with p_1p_2 ≡ a (mod m), and let 𝒫(x,m) = Σ_a (P(x;m,a) − π(x)^2/φ(m))^2. Theorem 1:
- Σ_{M<m≤2M} 𝒫(x,m) ≪_A x^4(log x)^{−A} + Mx^2;
- Σ_{M<q≤2M, q prime} 𝒫(x,q) ≪ (M^{−1}x^4 + Mx^2)(log x)^{−2}.

Corollaries:
- W(M,x) = #{(q,a) : q prime in (M,2M], P(x;q,a) = 0} is o(Mπ(M)) once x M^{−1/2}(log M)^{−3/2} → ∞. So for almost all prime q and almost all a there are solutions with **p_1, p_2 ≈ q^{1/2}(log q)^{3/2+o(1)}**, which is optimal up to logarithms.
- **W(M,M) ≪ M(log M)^2.** Unconditionally, on average over primes q ~ M, there are only ≪ (log M)^3 bad classes a per modulus with p_i ≤ q. This matches the GRH bound of §1, but only on average over q.

**Other results in the paper.**
- Squarefree analogue: an asymptotic for S(x;m,a) nontrivial for x ≥ m^{3/4+ε}. It rests on the Weil bound for Kloosterman sums.
- Prime × squarefree with both ≤ m^{1/2+ε} represents almost all classes, for every m.
- Ternary congruences: p_1(p_2+p_3) ≡ a and p_1p_2(p_3+h) ≡ a.

**Method.** Bound 𝒫 by (1/φ)Σ_{χ≠χ_0}|T_χ(x)|^4, where T_χ(x) = Σ_{p≤x} χ(p). Write T_χ^2 as one Dirichlet polynomial of length x^2, then apply the multiplicative large sieve over moduli. For general m, use Siegel–Walfisz for small conductors.

FKS also note the following. Heath-Brown's Linnik exponent gives P(x;m,a) > 0 for x ≥ c m^{11/2}. Under ERH, 11/2 can be replaced by any exponent > 2 via the greedy choice q ≡ a p̄. The x ≥ m^{1+ε} bound for individual a is "expected but ideas lacking".

---

## 3. Garaev: multiplicative congruences

**Citation 1.** M. Z. Garaev, *On multiplicative congruences*, Math. Z. 272 (2012), 473–482. DOI 10.1007/s00209-011-0944-1. arXiv:0807.4318. **[READ]**, abstract and introduction.
- If N_1N_2N_3 > m^{1+ε}, then #{x_1x_2x_3 mod m : x_j ≤ N_j} = m + O(m^{1−δ}). These are integers, not primes.
- The condition m^{1+ε} cannot be relaxed to Cm.
- For cube-free m, the same holds with 4 variables.
- Primes, prime modulus p, with p > N > p^{63/76+ε}: the congruence p_1p_2(p_3 + k) ≡ λ (mod p) has (1+o(1))π(N)^3/p solutions in primes ≤ N.
- Method: large-value estimates for character sums.

**Citation 2.** M. Z. Garaev, *An estimate of Kloosterman sums with prime numbers and an application*, Mat. Zametki 88 (2010), 365–373. **[SECONDARY]**, via Shparlinski 2019 and Yau. It gives bounds for Kloosterman sums over primes, Σ_{p≤N} e_m(a p̄ + bp), and improves the FKS ternary results. Fouvry–Shparlinski later extended these bounds.

**Relevance.** Garaev's results concern the shifted or ternary relaxations. There is nothing on p_1p_2 ≡ a itself. Bounds for Kloosterman sums over primes are the natural tool for the "primes in the sequence a p̄ mod m" reformulation (setup, item 2). Those bounds are nontrivial only for p up to a power of m somewhat above m^{1/2}, nowhere near what is needed.

---

## 4. Shparlinski: products of primes and almost primes

**Citation 1.** I. E. Shparlinski, *On products of primes and almost primes in arithmetic progressions*, Period. Math. Hungar. 67 (2013), 55–61. DOI 10.1007/s10998-013-2736-3. **[SECONDARY]**, via Shparlinski 2019 and Walker.
- ps ≡ a (mod m), with p prime ≤ m^{α+ε} and s ∈ P_ℓ (at most ℓ prime factors) with s ≤ m^{β+ε}.
- Example: (ℓ;α,β) = (17; 0.997, 0.997) is admissible. Consequently every class is a product of at most 18 primes below m^{0.997}.

**Citation 2.** I. E. Shparlinski, *On short products of primes in arithmetic progressions*, Proc. Amer. Math. Soc. 147 (2019), 977–986. DOI 10.1090/proc/14289. arXiv:1705.06087. **[READ]**
- Families of admissible (k, ℓ; α, β): products p_1⋯p_k s with p_i ≤ m^α and s ∈ P_ℓ, s ≤ m^β, cover all reduced classes for all large m. Composite m are allowed.
- Examples: (5; 0.905), (6; 0.864), (7; 0.760), (8; 0.673) for products of at most k primes ≤ m^α.
- For every η > 0 there is k_η with (k_η; 1/2+η) admissible.
- Method: bounds for exponential sums with reciprocals of primes (Kloosterman-type sums over primes), fed into Greaves' weighted sieve. This is a level-of-distribution argument, applied to the sequence of a·(p_1⋯p_k)^{−1} mod m in [1, m^β].
- The paper says explicitly that (1;1,1) ∈ A_3, which is essentially EOS, "seems to be out of reach nowadays". It also says that "even the Extended Riemann Hypothesis is not powerful enough to answer the original question".

---

## 5. Walker, Ramaré–Walker, and the ternary and k-ary line

### 5.1 Walker (2016)

**Citation.** A. Walker, *A multiplicative analogue of Schnirelmann's theorem*, Bull. LMS 48 (2016), 1018–1028. DOI 10.1112/blms/bdw062. arXiv:1505.03328. **[READ]** Throughout, q is prime.
- Thm 1: with primes < q^{3/4+ε}, |E_2| ≥ c(ε)q, where c(ε) = (2ε/(3+4ε))^2(1+o(1)). With η = 1 (primes ≤ q), |E_2(q)| ≥ (1/64 + o(1))q.
  - Method: upper-bound sieve weights majorise the primes. Then the pointwise upper bound #{p_1p_2 ≡ a} ≤ (64+o(1))π(q)^2/φ(q) holds, and pigeonhole gives the density.
- Thm 2: every nonzero residue is a product of at most 6 primes < q^{15/16+ε}. Also of at most k(ε) primes < q^{3/4+ε}.
- Thm 3: every residue is a product of exactly 48 primes < q^{15/16+ε}.
- Lemma 9 (key structural input): for primes < q^{1/4+ε}, P is not contained in any proper coset of (Z/qZ)^*.
- Section 4 explains why the method cannot show genuine cancellation in Σ_{p<q} χ(p) unconditionally. The zero-free-region bound ≪ √q x (log x)^{−A} is worse than trivial for x ≤ q.
- Footnote 2: "on GRH, an easy Fourier-analytic method shows that P^{(3)}_1 = (Z/qZ)^×". That is E_3(q) under GRH, consistent with EOS Cor. 2.
- Walker's thesis improves the 48 to E_20(q) = all [SECONDARY, via Szabó].

### 5.2 Ramaré–Walker (2018)

**Citation.** O. Ramaré, A. Walker, *Products of primes in arithmetic progressions: a footnote in parity breaking*, J. Théor. Nombres Bordeaux 30 (2018), 219–225. DOI 10.5802/jtnb.1024. arXiv:1610.05804. **[READ]**, arXiv v2.
- Thm 1.1: if q ≤ x^{1/16}, every invertible class mod q contains a product of three primes, each below x^{1/3}. So the primes are below q^{16/3}, the product is ≤ q^{16}, and everything is fully explicit.
- Note: the orchestrator's brief says "three primes each ≤ q". That is **not** what Ramaré–Walker prove.
  - Szabó and Klurman–Mangerel–Teräväinen both cite the result as E_3(q^{16/3}).
  - Shparlinski 2019 cites it as "p_1, p_2, p_3 ≤ m^4". I could not reconcile this from the arXiv version; perhaps the journal version differs [UNVERIFIED].
- Method:
  - Brun–Titchmarsh-type upper sieve bounds plus additive combinatorics (Kneser-type expansion in (Z/qZ)^*).
  - A weak lower bound for L(1,χ) that does not use Siegel.
  - Lemma 2.5: for a nonprincipal quadratic χ, some prime p ≤ q^4 has χ(p) = 1.
- It is "not blocked by parity" because products of three primes, not primes, are counted.

### 5.3 Explicit and near-explicit ternary results

- Ramaré–Srivastav–Serra, *Product of primes in arithmetic progressions*, IJNT 16 (2020), 747–766. DOI 10.1142/S1793042120500384. [SECONDARY]
  - E_3((650q)^3) = all, for all q ≥ 2 (Szabó's reading).
  - Matomäki–Teräväinen write it as 650q^3.
- Balasubramanian–Ramaré–Srivastav, *Product of three primes in large arithmetic progressions*, IJNT 19 (2023), 843–857. arXiv:2208.04031. [READ, abstract]
  - E_3(q^{3/2+ε}) for large q.
  - q^{11/8+ε} for odd q with no prime factor ≡ 1 (mod 4).
  - q^{6/5+ε} for primes q with (q−1, 4·7·11·17·23·29) = 2.
  - Every class is a product of exactly four primes below q(log q)^6.

### 5.4 Szabó (2024)

**Citation.** B. Szabó, *On the existence of products of primes in arithmetic progressions*, Bull. LMS 56 (2024), 1227–1243. DOI 10.1112/blms.12990. arXiv:2208.05762. **[READ]**
- Thm 1: for cube-free q, |E_2(q)| ≥ (3/8 + o(1))φ(q). For general q, the method gives 1/3 − ε, per Matomäki–Teräväinen.
  - Method:
    - It suffices to bound #{p_1p_2 ≡ a} from above for almost all a, so averaging is allowed.
    - Use multiplicative rather than additive Fourier analysis.
    - Convolve a sieve majorant with the actual primes.
    - Burgess bounds the multiplicative Fourier coefficients of the sieve.
  - If Σ_{n ≤ q^{α+o(1)}} χ(n) had substantial cancellation for all nontrivial χ, the constant would be (1−α)/2. Burgess gives α = 1/4, hence 3/8.
- Thm 2: E_6(q) = all, for large prime q. Uses Kneser plus a "real part trick" built on Heath-Brown's Linnik lemma, to exclude primes concentrated on two cosets of an index-8 subgroup.
- Thm 3: E_3(q^{6/5+ε}) = all, for all large q. Uses Iwaniec's average Brun–Titchmarsh, which gives |E_1(q^{6/5+ε})| > (11/32)φ(q), and Kneser.
- Independently, Lilu Zhao obtained E_6(q) for all large q [SECONDARY, via MT].

### 5.5 Lilu Zhao (2022)

**Citation.** L. Zhao, *On products of primes and almost primes in arithmetic progressions*, Acta Arith. 204 (2022), 253–267. DOI 10.4064/aa211215-2-6. [READ, abstract]
- Every a ≡ p_1p_2n (mod q) with p_1, p_2, n ≤ q and Ω(n) ≤ 2.
- Per Matomäki–Teräväinen: also a = pn with p, n ≤ q and Ω(n) ≤ 5, the best "prime × almost-prime ≤ q" result. And E_6(q) for all large q.
- Method: sieve on the n variable.

### 5.6 Klurman–Mangerel–Teräväinen (2023)

**Citation.** O. Klurman, A. P. Mangerel, J. Teräväinen, *Multiplicative functions in short arithmetic progressions*, Proc. LMS (3) 127 (2023), 366–446. DOI 10.1112/plms.12546. arXiv:1909.12280. **[READ]**, Section 2.
- Thm 2.1:
  - For q^{ε'}-smooth q, every a contains a q-smooth E_3 number n ≪ q^{2+ε}.
  - For all but O_ε(1) primes q ∈ [Q^{1/2}, Q], the same holds.
- Corollary: E_3(q) = all for such q. The primes p_j < q, and can even be taken < q^{1−η}.
- Under GRH they note that L_3(q) ≪ q^{2+o(1)}, where L_3 is the least E_3 number in the class.
- Method: Matomäki–Radziwiłł-type variance estimates for multiplicative functions in progressions, and zero-density / zero-free-region input. This is why it needs smooth or prime-non-exceptional q.

### 5.7 Matomäki–Teräväinen (2024): the unconditional state of the art

**Citation.** K. Matomäki, J. Teräväinen, *Products of primes in arithmetic progressions*, J. Reine Angew. Math. 808 (2024), 193–240. DOI 10.1515/crelle-2023-0096. arXiv:2301.07679. **[READ]**, Sections 1–1.1.
- Thm 1.1:
  - (i) E_3(q) = (Z/qZ)^* for all large cube-free q.
  - (ii) E_3(q^{1+ε}) = all, for all q large in terms of ε.
  - Remark 1.2: "cube-free" can be weakened to "cube-full part ≤ q^{1/9−ε}".
  - The authors say the method would give E_3(q^{1−α}) for some small α > 0 when q is cube-free.
- Thm 1.3:
  - (i) |E_2(q)| ≥ (2/3 − ε)φ(q) for all large q.
  - (ii) |E_2(q)| ≥ (11/16 − ε)φ(q) for cube-free q.
  - Consequence: E_4(q) = all.
- They state explicitly: "This remains open even under the generalized Riemann hypothesis."
- **Method: a multiplicative dense model (transference) theorem.**
  1. Using Burgess and a linear-sieve majorant, construct g : (Z/qZ)^* → [0, 8/3+ε] with max_χ |Σ_{n≤q} 1_P(n) log n · χ(n) − (q/φ)Σ_a g(a)χ(a)| = o(φ(q)).
  2. Halász–Montgomery large-value estimates control L^r norms for r ∈ (2,3).
  3. Pass to the product-set problem for A = {g ≥ ε/10}, which has density ≥ 3/8 − ε.
  4. Kneser's theorem reduces to "primes stuck in a few cosets of a small-index subgroup" scenarios.
  5. These are killed by sieve lower bounds on primes in cosets and by Heath-Brown's lemma. The quadratic case ψ(p) = −1 for most p ≤ q (the Siegel-zero scenario) needs a special pseudorandom majorant.
- For the binary problem, the dense model gives the density statement but not every a. Kneser cannot force A·A to be everything at density 2/3.

### 5.8 Matomäki–Teräväinen (2026), Linnik's problem for multiplicative functions

arXiv:2605.27833. [READ, abstract only] Square-free integers up to q^{2+o(1)} in a class on which a multiplicative h takes opposite signs. Tangential to EOS.

---

## 6. 2023–2026 activity directly on EOS

I searched arXiv and the web for "Erdős–Odlyzko–Sárközy" and "products of two primes in arithmetic progressions". **I found no claimed proof of EOS, conditional or unconditional.** I found the following.

### 6.1 Banks–Shparlinski (Oct 2026)

**Citation.** W. Banks, I. E. Shparlinski, *On the Erdős–Odlyzko–Sárközy conjecture for prime-power moduli*, arXiv:2610.19597, v1 14 Oct 2026. **[READ]**, full text.

**Unconditional results, q = p^γ with p fixed and γ large.**
- Thm 1.1: an asymptotic for Σ_{ℓ_1,ℓ_2≤q, ℓ_3≤q_•, ℓ_1ℓ_2ℓ_3≡a} log ℓ_1 log ℓ_2 log ℓ_3, valid when log q_• ≥ C(log q)^{2/3}(log log q)^{4/3}. So the third prime is q^{o(1)}.
- Thm 1.2 (binary, almost all a): |(Z/qZ)^* \ EOS_2(q)| ≤ φ(q) exp(−C(log q)^{1/3}(log log q)^{−1/3}).
- Input: the authors' Postnikov–Korobov zero-free region σ > 1 − A/((log q)^{2/3}(log log q)^{1/3}), with no exceptional zeros, for characters to prime-power moduli.

**Conditional results, under QRH[q, σ_0]** (no zeros of L(s,χ), χ mod q nonprincipal, in σ > σ_0), for arbitrary q.
- Thm 1.3: every a = ℓ_1ℓ_2ℓ_3 with ℓ_1, ℓ_2 ≤ q and ℓ_3 ≤ C(log q)^{2/(1−σ_0)}. **Under GRH, ℓ_3 ≪ (log q)^4.**
- Thm 1.4: |(Z/qZ)^* \ EOS_2(q)| ≪ φ(q) q^{−2(1−σ_0)}(log q)^3. **Under GRH, all but O((log q)^3) classes are products of two primes ≤ q.** This improves EOS's (log q)^5 and extends it from prime to composite q.

**Method.** Exactly the EOS character-sum method, with two refinements.
1. Fejér weights (1 − ℓ/x), which give the explicit-formula bound θ̃(x,χ) ≪ x^{σ_0} log q (Lemma 2.5, from Montgomery–Vaughan (13.28)). This saves one log over the sharp cut-off.
2. For the exceptional set E, use the dual identity Σ_χ θ̃(q,χ)^2 S_E(χ) = 0, where S_E(χ) = Σ_{a∈E} χ(a). Cauchy–Schwarz with Parseval on both θ̃ and S_E then gives q^2|E| ≪ max|θ̃| · φ(q)(q log q)^{1/2}|E|^{1/2}.

The acknowledgments disclose use of Claude for exposition, literature search and proof checking.

### 6.2 Banks (Sep 2026), random model

**Citation.** W. D. Banks, *Products of two elements of Granville's random model in residue classes*, arXiv:2609.37434, v1 29 Sep 2026. **[READ]**, introduction.
- Thm 1.1: in Granville's random model 𝒢, the following holds almost surely, for any fixed Θ ∈ (3/4, 1]. Every a mod every large q is g_1g_2 with g_i ∈ 𝒢 ∩ (X_q, 2X_q] and X_q ≍ q^Θ. The count is asymptotic to the expected c_q X_q^2/(q log^2 X_q).
- 3/4 is the Weil/Kloosterman completion barrier for the hyperbola n_1n_2 ≡ a in boxes. The statement fails below Θ = 1/2.
- In the Banks–Ford–Tao sieve model, the analogue fails with positive probability. This is a local defect at 2 and 3.
- **Useful for us:**
  - The introduction states the barrier precisely. "Bounding the error terms by absolute values yields a total that exceeds the main term by the factor φ(q)/π(q) ≫ log q/log log q. The loss comes from the sum over the characters, not from any single character. The square-root saving in each individual sum, which is all that GRH provides, does not recover this loss."
  - It also notes that sieves fail by parity.
  - Table 1 is a good current summary of the k-prime results.

### 6.3 Function fields and number fields

- Xie, *On a conjecture of Erdős over function fields*, Math. Z. 313 (2026), Paper 64. DOI 10.1007/s00209-026-04077-6. arXiv:2510.17612. [READ, abstract]
  - For squarefree f ∈ F_q[t] of degree n ≥ 2, every residue class mod f is a product of two monic irreducibles of degree ≤ n, provided q is large in terms of n.
  - Uses Katz equidistribution, a one-dimensional sheaf argument, and gives a q^{−1/2} saving.
- Sawin, Acta Math. 233 (2024), 285–418, Lemma 9.14: square-root cancellation for factorisation functions in squarefree progressions. As Xie observes, this gives the function-field EOS for large degree once the field size exceeds an absolute constant. [SECONDARY]
- **This is the analogue of "GRH + cancellation across the family of characters".** The geometric input gives equidistribution of the whole family of Frobenius conjugacy classes, more than RH for each L-function. It is a strong hint at which hypothesis is needed in the integer case.
- Xie, *Products of prime ideals in ray class groups*, arXiv:2606.30567. [READ, abstract] The Matomäki–Teräväinen transference extended to narrow ray class groups. It gives three prime ideals of norm ≤ (N𝔮)^{103/64+κ}, and a positive proportion of classes represented by two prime ideals.
- Deshouillers–Gun–Ramaré–Sivaraman, arXiv:2210.11051: three prime ideals of norm O((N𝔮)^3). [SECONDARY]

### 6.4 Tangential

- Yau, *On products of primes and square-free integers in arithmetic progressions*, arXiv:1907.06016. [READ] An asymptotic for ps ≡ a with s squarefree, via Kloosterman sums over primes (Fouvry–Shparlinski).
- Pandey, arXiv:2307.14890. [READ, abstract] Almost all (a, x) have a P_2 number in [x, x+L] in the class a mod q, once L/(φ(q) log X) → ∞. It concerns large X, not factors ≤ q.

---

## 7. Small exceptional moduli: the conjecture does need "m large"

**[MINE, proved by exhaustive computation]**, using a short C program: exhaustive coverage of (Z/mZ)^* by {pq mod m : p ≤ q ≤ m prime, p, q ∤ m}, with early stopping. Primes dividing m are automatically useless.

**p = q allowed.** For m ≤ 200 000, the conjecture fails for exactly **48** moduli:

2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 15, 17, 19, 23, 25, 27, 29, 31, 33, 35, 37, 41, 43, 47, 53, 55, 57, 59, 61, 67, 69, 71, 73, 83, 89, 91, 97, 101, 103, 121, 127, 137, 169, 173, 179, 191, **397, 401**.

- The largest is **m = 401**, where only a = 385 is missed. At m = 397, only a = 308 is missed.
- No failures occur for 402 ≤ m ≤ 200 000.
- Examples:
  - m = 5: primes {2,3} give products {1,4}, so 2 and 3 are missed. Walker uses this example.
  - m = 11: three classes, {1,7,8}, are missed.
  - m = 17: four classes, {3,11,12,13}, are missed. This is the most of any m.

**p ≠ q required.** Checked to m ≤ 40 000: there are 62 exceptional moduli, the largest being **m = 431**, where only a = 169 is missed.

So EOS as literally stated ("all sufficiently large m") is consistent with the data. The threshold is small, and the margin grows quickly: once m is in the thousands, the expected count π(m)^2/φ(m) is ≳ 70. The verification does not use the theory, but it matters for any effective version. A proof with explicit q_0 would need to close the gap to 401.

I did not find this computation in the literature [UNVERIFIED that it is absent]. EOS 1987 only says q > q_0.

---

## 8. Other relevant baselines

- **Linnik-type, every a, unconditional.** Take p_1 = the least prime not dividing m (O(log m)). Then p_2 ≡ a p̄_1 is ≪ m^5 by Xylouris (Chebyshevskii Sb. 19 (2018)) [SECONDARY]. So p_1p_2 ≪ m^{5+o(1)}. I know of nothing better for the least E_2 number in every class unconditionally [UNVERIFIED]. Sieve methods give P_2 numbers (Ω ≤ 2) but cannot isolate exactly two primes, because of parity.
- **Under GRH, every a.**
  - EOS gives p_1, p_2 ≤ C m (log m)^4, so the product is ≤ m^2 (log m)^{8+o(1)}.
  - The greedy route (p_1 = 2, least prime p_2 ≡ a/2) gives p_2 ≪ (φ(m) log m)^2 [RECALL: Bach–Sorenson / Lamzouri–Li–Soundararajan form of GRH-Linnik]. So the product is also ≪ m^{2+o(1)}, but with unbalanced factors.
  - The conjecture asks for **balanced factors ≤ m**, so product ≤ m^2. In terms of the size of the product alone, GRH already gives m^{2+o(1)}. The content of EOS is the factor balance, exactly at the threshold.
- **Lower-order sharpening under GRH, C = 2 [MINE, sketched; not stated in any source I read].** Rerun EOS Theorem 3 with Banks–Shparlinski's Fejér weights. Under GRH, θ̃(x,χ) ≪ √x log q for every nonprincipal χ mod q (their Lemma 2.5, σ_0 = 1/2). Then

  Σ_{p_1,p_2 ≤ x, p_1p_2 ≡ a} (1−p_1/x)(1−p_2/x) log p_1 log p_2 = x^2/(4φ(q)) (1+o(1)) + O(x log^2 q).

  This is positive once x ≥ C φ(q) log^2 q. So **under GRH, every a ≡ p_1p_2 with p_1, p_2 ≤ C q (log q)^2**. This needs checking, but it is a two-line modification.
  - GRH alone cannot do better pointwise. The bound √x log q is sharp in the explicit formula: about log q zeros with |γ| ≤ 1 could all align. So any argument that bounds Σ_{χ≠χ_0} χ̄(a) θ̃(x,χ)^2 by absolute values stops at x ≍ q log^2 q.

---

## 9. Where exactly the frontier is under GRH

**Strongest known GRH-conditional statements toward EOS:**
1. Every a is p_1p_2 with p_1, p_2 ≤ C q (log q)^4 (EOS 1987, Cor. 3, q prime; the proof extends verbatim to all q). My derivation (§8) improves this to C q (log q)^2 using smoothed weights. That derivation is not in the literature as far as I found.
2. All but O((log q)^3) classes a are p_1p_2 with p_1, p_2 ≤ q, for arbitrary q (Banks–Shparlinski 2026, Thm 1.4). EOS 1987 had O((log q)^5), for q prime.
3. Every a is ℓ_1ℓ_2ℓ_3 with ℓ_1, ℓ_2 ≤ q and ℓ_3 ≪ (log q)^4 (Banks–Shparlinski 2026, Thm 1.3). Ternary EOS with all three primes ≤ q needs only a log log q / log q-wide zero-free strip (EOS 1987, Cor. 2), and is unconditional for cube-free q (Matomäki–Teräväinen).

So under GRH we are short of EOS in three ways:
- by a factor (log q)^2 in the range, for every a;
- by an exceptional set of O(log^3 q) classes at the exact range;
- by a third prime of size polylog(q).

**What blocks going further.** Write N(a) = (1/φ)Σ_χ χ̄(a) θ(q,χ)^2. The main term is ≍ q (or q^2/φ). Parseval is exact at x = q, because distinct primes ≤ q lie in distinct classes: Σ_χ |θ(q,χ)|^2 = φ(q) Σ_{p≤q} log^2 p ≍ φ q log q. So the error has trivial size ≍ q log q, a factor ≍ log q (more precisely φ(q)/π(q)) above the main term. The setup sketch's "basic barrier" agrees with the sources on this point.

The specific obstructions:
- **(a) Magnitude information is exhausted.** GRH bounds each |θ(q,χ)| by √q log q. The L^2 average is already √(q log q), so GRH is within √log q of the RMS, and no magnitude bound (L^∞, L^2 or mixed) closes the gap. Hölder and the large sieve are similarly stuck, since Σ_χ |θ|^4 ≈ φ · (q log q)^2 · (energy factor) does not help pointwise. What is needed is **cancellation in the phases of χ̄(a) θ(q,χ)^2 across the family of φ(q) characters**, for each fixed a. Equivalently, the zeros of the different L(s,χ) mod q must not conspire. This is a statement about the joint distribution of zeros in the family, of linear-independence or pair-correlation type. GRH says nothing about it.
  - All sources make this point: Banks 2026, introduction; FKS; Shparlinski; Matomäki–Teräväinen. In Banks's words, the loss "comes from the sum over the characters, not from any single character".
  - The function-field proofs (Sawin; Xie) succeed precisely because Deligne/Katz equidistribution supplies this family-level cancellation, which RH for individual L-functions does not.
- **(b) The exceptional-set method also stops at polylog.** The duality argument (Banks–Shparlinski) gives |E| ≪ max|θ̃|^2 · log q / q ≍ log^3 q. Making E empty needs max_{χ≠χ_0} |θ̃(q,χ)| = o(√q / log q · …). That is, it needs more than square-root cancellation in individual character sums over primes up to the conductor, which is false for some χ.
- **(c) Sieve and Kloosterman routes are blocked by different barriers.**
  - Parity: products of exactly two primes are the standard parity example, and this is why Zhao, Shparlinski and Walker get P_ℓ, not P_1.
  - Level of distribution: Kloosterman sums over primes are nontrivial only well beyond m^{1/2}; Weil completion stops at m^{3/4} even for integers (Banks's 3/4).
  - GRH does not help with either.
- **(d) The unconditional transference route** (Matomäki–Teräväinen) gives a positive-density dense model. It reaches every class only with three primes, or with two primes for 2/3 of the classes. Even with GRH plugged into the dense model, Kneser-type combinatorics cannot turn "density > 1/2" into "A·A = G" for k = 2. The binary case needs pointwise asymptotics, not density.

**What would suffice (conditional targets suggested by the literature).**
- Any hypothesis implying (1/φ)Σ_{χ≠χ_0} χ̄(a) θ(q,χ)^2 = o(q/(log q)^{…}) pointwise in a. For example:
  - a "random phases" or linear-independence-type hypothesis for the zeros of the family {L(s,χ) : χ mod q}, made quantitative;
  - or a fourth-moment / multiplicative-energy bound for primes ≤ q mod q, strong enough to feed a pointwise argument. As the setup notes say, L^4 alone controls only the variance over a.
- Under such a hypothesis, the natural intermediate goal is p_1, p_2 ≤ q (log q)^{o(1)} for all a, or EOS for all but O(1) classes.
- An easier stepping stone, also not in the literature as far as I found: x ≍ q log q for every a under GRH plus a Montgomery–Hooley-type variance asymptotic Σ_b (θ̃(x;q,b) − θ̃(x)/φ)^2 ~ c x log q for the single modulus q at x = q log^{O(1)} q. **[MINE, heuristic: |E(a)| ≤ variance, and the variance asymptotic is an unproved hypothesis.]**

---

## 10. Reference list (with ids)

1. Erdős, Odlyzko, Sárközy, Period. Math. Hungar. 18 (1987) 229–239. DOI 10.1007/BF01848086. PDF: static.renyi.hu/~p_erdos/1987-22.pdf.
2. Friedlander, Kurlberg, Shparlinski, Math. Res. Lett. 15 (2008) 1133–1147. DOI 10.4310/MRL.2008.v15.n6.a6. arXiv:0708.1562.
3. Garaev, Math. Z. 272 (2012) 473–482. DOI 10.1007/s00209-011-0944-1. arXiv:0807.4318.
4. Garaev, Mat. Zametki 88 (2010) 365–373 (Kloosterman sums with primes).
5. Shparlinski, Period. Math. Hungar. 67 (2013) 55–61. DOI 10.1007/s10998-013-2736-3.
6. Shparlinski, Proc. AMS 147 (2019) 977–986. DOI 10.1090/proc/14289. arXiv:1705.06087.
7. Walker, Bull. LMS 48 (2016) 1018–1028. DOI 10.1112/blms/bdw062. arXiv:1505.03328.
8. Ramaré, Walker, JTNB 30 (2018) 219–225. DOI 10.5802/jtnb.1024. arXiv:1610.05804.
9. Ramaré, Srivastav, Serra, IJNT 16 (2020) 747–766. DOI 10.1142/S1793042120500384.
10. Balasubramanian, Ramaré, Srivastav, IJNT 19 (2023) 843–857. DOI 10.1142/S1793042123500422. arXiv:2208.04031.
11. Zhao, Acta Arith. 204 (2022) 253–267. DOI 10.4064/aa211215-2-6.
12. Szabó, Bull. LMS 56 (2024) 1227–1243. DOI 10.1112/blms.12990. arXiv:2208.05762.
13. Klurman, Mangerel, Teräväinen, Proc. LMS 127 (2023) 366–446. DOI 10.1112/plms.12546. arXiv:1909.12280.
14. Matomäki, Teräväinen, J. reine angew. Math. 808 (2024) 193–240. DOI 10.1515/crelle-2023-0096. arXiv:2301.07679.
15. Banks, Shparlinski, arXiv:2610.19597 (Oct 2026), EOS for prime-power moduli, plus the GRH results.
16. Banks, arXiv:2609.37434 (Sep 2026), EOS in Granville's random model.
17. Xie, Math. Z. 313 (2026) no. 64. DOI 10.1007/s00209-026-04077-6. arXiv:2510.17612 (function fields).
18. Xie, arXiv:2606.30567 (ray class groups).
19. Sawin, Acta Math. 233 (2024) 285–418. DOI 10.4310/ACTA.2024.v233.n2.a3.
20. Yau, arXiv:1907.06016. Pandey, arXiv:2307.14890. Matomäki–Teräväinen, arXiv:2605.27833 (tangential).
