# Referee report on Theorem W (three primes, third prime ≪ (log m)²(log log m)²)

Written 2026-11-23. Subject: `notes/brainstorm/r1-wildcard.md` §1 (Lemma M, Lemma S, Theorem W) and the lemmas
D0, D2, D3, D4(a) of `notes/routes/C-log-exponent.md` §2 on which it rests. Standing hypothesis: GRH, used only
through route C's bound H (`GRHSmoothBound`).

Status tags: *proved* = I re-derived it here line by line. *sketched* = steps indicated, bookkeeping not written.
[READ] = source text read this session. [SECONDARY] = quoted from a source that quotes it. [UNVERIFIED] = not checked.

## 0. Verdict

| Question | Verdict |
|---|---|
| Is Theorem W correct? | **Yes** (proved, §2). I rechecked every step, including D0, D2, D3, D4(a), which no round-2 reviewer had rechecked. I found no error. The only remaining dependence is route C's Theorem 1 (bound H), which I did not re-derive; it is also Banks–Shparlinski's Lemma 2.5 at σ₀ = 1/2 [READ]. |
| Is it new? | **It improves the only GRH statement of this kind in the literature I could find**, Banks–Shparlinski Thm 1.3, which gives ℓ₃ ≪ (log q)⁴ under GRH [READ, full text]. Their paper has no (log q)² variant, no remark that the exponent can be lowered, and no moment or energy argument. I found no other source with a small third prime. The method (Hölder against a high moment of a short prime character sum, which is diagonal when y^k < m) is a standard device, so the result is an easy refinement, not a new idea. Novelty is "not found in a targeted search", not "certified absent". |
| By-product | The same argument under a zero-free half-plane σ > σ₀ gives ℓ₃ ≪ (log q)^{3/(2−2σ₀)}, against Banks–Shparlinski's (log q)^{2/(1−σ₀)} = (log q)^{4/(2−2σ₀)} (sketched, §3). |

## 1. Literature

### 1.1 What was read

- **Banks–Shparlinski, arXiv:2610.19597v1 (14 Oct 2026)** [READ: full text, extracted from the PDF].
  - Thm 1.3: under QRH[q, σ₀] every unit a is ℓ₁ℓ₂ℓ₃ with ℓ₁, ℓ₂ ≤ q and ℓ₃ ≤ C(log q)^{2/(1−σ₀)}. The paragraph
    after Thm 1.4 states the GRH case as ℓ₃ ≪ (log q)⁴.
  - Proof (§4.1): orthogonality, then the non-principal characters are bounded by
    (1/φ) Σ_χ |ϑ(q,χ)|² · max_{χ≠χ0} |ϑ̃(q_•,χ)| ≪ q log q · q_•^{σ₀} log q (their (2.3) and Lemma 2.5). So the third
    prime enters through a **sup bound**, and positivity needs q_•^{1−σ₀} ≫ (log q)². That is where the 4 comes from.
  - There is no variant with a smaller exponent, no use of moments of ϑ̃(q_•,χ), and no remark on optimality.
  - Thm 1.4 (all but O((log q)³) classes under GRH) plus pigeonhole already gives ℓ₃ ≪ (log q)³ log log q. This is
    route D's Remark 5.1. The authors do not state it. So the exponent 4 in Thm 1.3 is not their best implicit bound.
  - Thm 1.1 (prime-power moduli, unconditional) has ℓ₃ ≤ exp(C(log q)^{2/3}(log log q)^{4/3}); not comparable.
- **Shparlinski, arXiv:1705.06087** [READ: §5–§7]. Products p₁⋯p_k·(almost prime) with power-size ranges. No GRH
  statement and no small third prime.
- **Hughes, arXiv:2610.04678** [READ: abstract only]. Subset products of about (1/log 2) log Q small primes cover
  (Z/qZ)^* for almost all q ≤ Q. Different problem (subset products, almost all moduli, no large primes).
- From `notes/lit/01-eos-direct.md` (read there, not re-read): Ramaré–Walker (three primes ≤ q^{16/3}),
  Ramaré–Srivastav–Serra, Balasubramanian–Ramaré–Srivastav, Szabó (three primes ≤ q^{6/5+ε}), Klurman–Mangerel–
  Teräväinen, Matomäki–Teräväinen. All are unconditional and have three primes of power size. None has a third
  prime of polylogarithmic size, and none is conditional on GRH.

### 1.2 Searches

Web searches (extended mode) for: the EOS conjecture with a small third prime under GRH; "(log q)^2"; high moments /
multiplicative energy / Sidon arguments for products of primes mod q; arXiv listings after October 2026 citing
Banks–Shparlinski. No result states Theorem W or anything between (log q)² and (log q)⁴ for the third prime.
The searches are not exhaustive: I could not query MathSciNet or zbMATH, and a paper posted in the last few weeks
could be missed.

### 1.3 What is standard in the method

- Σ_χ |Σ_{s≤y} χ(s)|^{2k} = φ·#{s₁⋯s_k ≡ s′₁⋯s′_k}, diagonal when y^k < m. This is the classical moment computation
  for short character sums over primes (it is behind the Gaussian law of short prime character sums and many
  "almost all characters" arguments). Not new.
- Bounding a trilinear character sum by sup^{1/k} × Parseval × energy^{1/2k} is the usual multiplicative-energy
  form of Hölder (Garaev, Bourgain–Garaev–Konyagin–Shparlinski and others use it for products of sets mod p).
- What is specific here: the two long variables are at the exact range m, where Parseval is exact, and the GRH sup
  bound is needed only to the power 1/k, so with k ≈ log log m it costs a constant. I did not find this
  combination applied to EOS.

**Recommendation.** State Theorem W as "an improvement of Banks–Shparlinski Thm 1.3 under GRH from (log q)⁴ to
(log q)²(log log q)²", cite their Lemma 2.5 and (2.3) for the inputs, and describe the method as a standard moment
refinement. Do not claim a new technique.

## 2. Proof check (proved)

Notation of route C §2 with X₁ = X₂ = X = m: Θ(b) = Σ_{p ≤ m, p ≡ b} log p·(1 − p/m), ϑ̃(χ) = Σ_b Θ(b)χ(b),
T = ϑ̃(χ0), M = max_{χ≠χ0}|ϑ̃(χ)|, V° = (1/φ)Σ_{χ≠χ0}|ϑ̃(χ)|², R(c) = Σ_b Θ(b)Θ(c b̄) = T²/φ + E(c),
E(c) = (1/φ)Σ_{χ≠χ0} χ̄(c)ϑ̃(χ)². L = log m.

### 2.1 Route C's lemmas

- **D0** (prime powers). |ψ̃(x,χ) − ϑ̃(x,χ)| ≤ Σ_{p^k ≤ x, k ≥ 2} log p ≤ Σ_{k=2}^{⌊log₂x⌋} θ(x^{1/k}) ≤ (log 4)√x·log₂x = 2√x log x.
  Checked: the weights (1 − n/x) lie in [0,1], |χ| ≤ 1, there are at most log₂x values of k, and (log 4)/(log 2) = 2.
  Uses Chebyshev θ(y) ≤ y log 4. **Correct.**
- **D2** (T ≥ X/8 for X ≥ max(X₀, 8L)). T(X) differs from ϑ̃(X, 1) by the primes dividing m, at most Σ_{p|m} log p ≤ L.
  H at q = 1 and D0 give ϑ̃(X,1) ≥ X/2 − C_H(log 2)√X − 2√X log X ≥ X/4 for X ≥ X₀. **Correct.** At X = m the
  condition m ≥ 8L holds for m ≥ 27. Only a Chebyshev-type lower bound is really used.
- **D3** (M(X) ≤ C₃√X·L for X ≤ m³, C₃ = C_H(1 + log 2) + 6). H at modulus m gives |ψ̃(X,χ)| ≤ C_H√X log(2m), and
  log(2m) ≤ (1 + log 2)L because L ≥ 1 for m ≥ 3; D0 adds 2√X log X ≤ 6√X·L. **Correct.** H is applied to an
  arbitrary non-principal character mod m, primitive or not, which is how Theorem 1 of route C is stated.
- **D4(a)** (V°(X) ≤ (log 4)·X log X for X ≤ m). Primes p ≤ X ≤ m with p ∤ m lie in [1, m−1], so they are distinct
  mod m and each Θ(b) has at most one term. Hence Σ_bΘ(b)² = Σ_p log²p·(1−p/X)² ≤ log X·θ(X), and
  V° = Σ_bΘ² − T²/φ ≤ Σ_bΘ². **Correct.** This is Banks–Shparlinski's (2.3).
- **D1** (R(c) = T²/φ + E(c)) is orthogonality. R(c) > 0 iff c ≡ pq with primes p, q < m: the weight vanishes
  only at p = m, and p ∤ m is automatic because c is a unit. **Correct.**

### 2.2 Lemma M

Claim: for a finite multiset 𝒮 ⊂ G and k ≥ 1, |Σ_{c∈𝒮} E(c)| ≤ M^{1/k}·V°^{1−1/2k}·E_k(𝒮)^{1/2k}, with
E_k(𝒮) = (1/φ)Σ_χ|1̂_𝒮(χ)|^{2k}.

Check. Σ_{c∈𝒮}E(c) = (1/φ)Σ_{χ≠χ0} ϑ̃(χ)²·conj(1̂_𝒮(χ)). Hölder with exponents r = 2k/(2k−1) and 2k:
Σ_{χ≠χ0}|ϑ̃|²|1̂_𝒮| ≤ (Σ_{χ≠χ0}|ϑ̃|^{2r})^{1/r}(Σ_χ|1̂_𝒮|^{2k})^{1/2k}. Since 2r − 2 = 2/(2k−1),
Σ_{χ≠χ0}|ϑ̃|^{2r} ≤ M^{2/(2k−1)}·φV°, and raising to 1/r = (2k−1)/2k gives M^{1/k}(φV°)^{1−1/2k}. The second factor is
(φE_k)^{1/2k}. Powers of φ: −1 + (1 − 1/2k) + 1/2k = 0. **Correct.** The right side is increasing in M, V° and E_k,
so upper bounds may be inserted. No hypothesis is used.

### 2.3 Lemma S

Claim: if 𝒲 is a set of primes not dividing m, all < m^{1/k}, then for 𝒮 = {a·s̄ : s ∈ 𝒲}: E_k(𝒮) = E_k(𝒲) ≤ k!·|𝒲|^k.

Check. 1̂_𝒮(χ) = χ(a)·conj(1̂_𝒲(χ)), so the moduli agree and E_k(𝒮) = E_k(𝒲). E_k(𝒲) counts
(s, s′) ∈ 𝒲^k × 𝒲^k with s₁⋯s_k ≡ s′₁⋯s′_k (mod m). Both products are integers in [1, m), so the congruence is an
equality, and by unique factorisation s′ is a permutation of s: at most k! choices of s′ for each s. **Correct.**
The elements of 𝒲 are distinct mod m (they are distinct integers below m), so 𝒮 is a set of |𝒲| classes.

### 2.4 Theorem W with explicit constants

**Theorem W (proved; GRH through H only).** Let C₃ be as in D3, C₄ = e^{1/2}·max(1, C₃/√(log 4)) and
K₀ = (64·log 4·C₄)². Let m ≥ max(X₀, 27), L = log m, k = ⌈log L⌉, and let 𝒲 be a set of primes not dividing m,
all < m^{1/k}, with

  |𝒲| > K₀·(φ/m)²·L²·⌈log L⌉.

Then for every unit a there are primes p, q < m and s ∈ 𝒲 with pqs ≡ a (mod m). Consequently there are absolute
K′, m₀ such that for m ≥ m₀ one may take s ≤ K′(φ/m)²(log m)²(log log m)².

*Proof.* Suppose R(a s̄) = 0 for every s ∈ 𝒲. Then Σ_{c∈𝒮}E(c) = −|𝒲|T²/φ, so by D2, Lemma M, D3, D4(a), Lemma S:

  |𝒲|·m²/(64φ) ≤ |𝒲|T²/φ ≤ M^{1/k}V°^{1−1/2k}(k!)^{1/2k}|𝒲|^{1/2}
   ≤ (log 4)·mL·(C₃²L/log 4)^{1/2k}·k^{1/2}·|𝒲|^{1/2}.

Here I used M^{1/k}V°^{1−1/2k} ≤ V̄·(M̄²/V̄)^{1/2k} with V̄ = (log 4)mL, M̄ = C₃√m·L, and (k!)^{1/2k} ≤ k^{1/2}.
Since k ≥ log L, L^{1/2k} ≤ e^{1/2}, and (C₃²/log 4)^{1/2k} ≤ max(1, C₃/√(log 4)). So
|𝒲|^{1/2} ≤ 64(log 4)C₄(φ/m)L·k^{1/2}, i.e. |𝒲| ≤ K₀(φ/m)²L²k, a contradiction.

For the last sentence take 𝒲 = primes ≤ y not dividing m with y = K′(φ/m)²L²(log L)². Then y ≤ K′L²(log L)², so
log y ≤ 3 log L for large m, and y^k ≤ exp(3 log L·(log L + 1)) < m. Also π(y) ≥ y/(2 log y) ≥ (K′/6)(φ/m)²L² log L,
and ω(m) ≤ 2L/log L is smaller than (φ/m)²L² log L ≫ L²/log L (Mertens: φ/m ≫ 1/log L). Take K′ = 13K₀. ∎

Points I looked at specifically and found in order:
- the direction of every inequality when upper bounds for M and V° are substituted into Lemma M;
- that the factor (φ/m)² is on the right side (it comes from T²/φ ≥ m²/(64φ) against V̄ ∝ m);
- that 𝒲 need not consist of all small primes: any set of primes below m^{1/k} of the stated size works, which is
  what Corollary W1 (rays) uses;
- that k = ⌈log L⌉ ≥ 1 and m^{1/k} > 2 for large m;
- Corollary W2 needs y^{2k} < m (as the technical skeptic noted), because 1̂_𝒮 = χ̄(a)·conj(1̂_𝒲)² and the 2k-th
  moment of 1̂_𝒲² is E_{2k}(𝒲).

**Why the log log factors are not removable by this argument (heuristic).** The condition is
|𝒲| ≫ L²·k·(C L)^{1/k}, minimised at k ≍ log L. The factor k comes from k! in the energy of a set with no
multiplicative relations; it is the 2k-th moment of a Gaussian. A second log log comes from π(y) ≈ y/log y.

### 2.5 Dependencies not re-derived

- Route C Theorem 1 (H) itself: |ψ̃(x,χ) − [χ=χ0]x/2| ≤ C_H√x log(2q). Refereed in `C-referee.md`; independently it
  is Banks–Shparlinski Lemma 2.5 with σ₀ = 1/2 (they derive it from Montgomery–Vaughan (13.28)). I did not redo
  the contour argument.
- The absolute constant X₀ in D2 and the value of C_H are not computed.

## 3. Variant under a zero-free half-plane (sketched)

Assume QRH[m, σ₀] with 1/2 < σ₀ < 1, so M ≤ C·m^{σ₀}L (Banks–Shparlinski Lemma 2.5 [READ]) and V° ≤ (log 4)mL as before.
Take 𝒲 = primes ≤ y not dividing m and k = ⌈L/log y⌉ − 1, so y^k < m and m^{1/k} = y^{1+o(1)} when log y = o(L^{1/2}).
Then (M²/V°)^{1/2k} ≤ (C m^{2σ₀−1}L)^{1/2k} = y^{σ₀−1/2+o(1)} and (k!)^{1/2k} ≤ (L/log y)^{1/2}. The condition of §2.4 becomes

  y/log y ≫ (φ/m)²·L²·(L/log y)·y^{2σ₀−1+o(1)}, i.e. y^{2−2σ₀−o(1)} ≫ L³.

So every a is ℓ₁ℓ₂ℓ₃ with ℓ₁, ℓ₂ ≤ m and **ℓ₃ ≪ (log m)^{3/(2−2σ₀)+o(1)}**, against (log m)^{4/(2−2σ₀)} in Thm 1.3.
At σ₀ = 1/2 the choice k ≈ log L is better and gives the exponent 2 of Theorem W; the exponent as a function of σ₀
is discontinuous at 1/2 because for σ₀ > 1/2 the factor m^{(2σ₀−1)/2k} forces k as large as possible.
Status: sketched; the o(1) and the uniformity in σ₀ were not written out.

## 4. Not checked

- No MathSciNet or zbMATH search; papers from the last few weeks may be missing.
- Banks–Shparlinski is a v1 preprint; a later version could add a remark on the exponent.
- Theorem W-Linnik and the F_q[t] transcription (wildcard §2.2, §3) are outside this report.
- Numerical confirmation is the existing `compute/brainstorm/wildcard/multiplier_cert.py` only; I did not rerun it.
