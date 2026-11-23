# Round 3: moderator's synthesis of the brainstorm

Written 2026-11-23. Standing hypothesis: GRH for Dirichlet L-functions. Anything more is flagged **[EXTRA]**.
Sources: `r1-*.md` (five personas, fifteen proposals), `r2-skeptic-barriers.md`, `r2-skeptic-technical.md`,
`r2-builder.md`. Status tags as in the project rules: proved / sketched / heuristic / computed / [UNVERIFIED].
"Verified by X" means X re-derived the statement in round 2; I did not re-derive anything except where §2.3 says so.

Notation: G = (Z/mZ)^*, φ = φ(m), L = log m, P = primes ≤ m not dividing m, ρ = |P|/φ, λ = μ = |P|²/φ,
L′ = φ/|P|, N(a) = #{pq ≡ a}, N⁻(b) = #{p ≡ bq}, A_a = {a·p̄ mod m : p ∈ P}.

## 0. Verdict

**No proposal reaches EOS, and none has a probability above 1% of doing so.** All three reviewers agree on this.
What the brainstorm produced is:

1. one new rigorous GRH theorem toward EOS (Theorem W: every a is p·q·s with s ≪ (log m)²(log log m)²), which
   improves the (log m)³ log log m recorded in route D and is Lean-formalizable from what the repo already has;
2. one conditional reduction that survives all six barrier objects (Theorem BH: Buchstab instead of Vaughan, with
   the gap isolated in an a-independent fourth-moment hypothesis H4(η) or its weak-type form LD(η));
3. a sharper map of the obstruction: every method tried lands on the same conservation law (volume m², one log
   short of Parseval), and the conjugation barrier is now quantified on both sides.

I recommend funding three items (§3): the Theorem W package, the Buchstab certificate with H4/LD as the named gap,
and a small gated calibration ladder. The Lean recommendation (§5) is H4/LD, entered through an exact finite
certificate lemma that needs no asymptotics.

---

## 1. Scoreboard

Final status is for the proposal as a contribution to the project. The column "EOS reach" is separate, because
several live items have none.

| # | Proposal | Final status | EOS reach | Reason (who killed or saved it) |
|---|---|---|---|---|
| A1 | Analytic 1: Buchstab + Hölder, H4(η) | **alive** (as a reduction) | only through H4 **[EXTRA]** | Technical skeptic re-derived Thm BH, Cor H4, Cor LD, Prop S; barrier skeptic could not break the implication with any of the six objects. Barrier skeptic's objection upheld in part: H4 is not provable from sizes + Type I (A\* violates it), so entries (3), (4) are "transferred to H4", not passed. Builder's attempts to lower the price all end at Lemma N. |
| A2 | Analytic 2: shrinking box a = q·x | wounded | none | Proposer: not EOS. Technical skeptic: novelty risk high (Kloosterman sums over primes are standard; guess 10–15% new). Barrier skeptic: never exercises barrier 6, so it tests bookkeeping only. Kept as a debugging model for Lemma 2.2 (builder). |
| A3 | Analytic 3: special moduli for Type I level | wounded | none | No exponent computed; proposer's own balanced estimate m^{−1/24} is below the known 1/16; D §4.2 caps the level at 1/4. Changes the constant in H4, not the need for it. Folded into A1 as a remark. |
| K | Automorphic K: Kloosterman-dual expansion | **dead** as a route; lemmas kept | none | Proposer's own verdict (fails barriers 1–5); both skeptics agree. Lemmas H and K verified by both skeptics; the correction to D §4.1(iii) stands. |
| TD | Automorphic TD: prime × GL₂ coefficient | alive (side result) | none | A\* satisfies TD at every level below 1/2 (barrier skeptic), so it cannot imply EOS. Saved by technical skeptic and builder as a rung of the calibration ladder and as the source of a higher Type I level. |
| FE | Automorphic FE: smooth toy D₄ | alive (calibration only), gated | none | Barrier skeptic and builder keep it as rung 1. Technical skeptic's caveats stand: the kernel is Kl₂(a·s·r̄), a ratio, so the quoted bilinear bounds do not apply directly; sup-norm steps lose m^{o(1)}, not logs (geometer C1). Literature check before any work. |
| G1 | Geometer G1: Schur–Mellin pieces, q₀ | wounded for this project | none over Z | No transfer mechanism (all three reviewers). Barrier skeptic: barrier 6 is vacuous in F_q[t], so even success is not evidence. Technical skeptic corrected two statements (rank 4 with O(4) in odd characteristic; the m = 2 formula is not uniform in a). Alive only as function-field arithmetic. |
| G2 | Geometer G2: characteristic-2 structure | **dead** for EOS over Z | none, by design | Proposer: no transfer. Technical skeptic: the only supporting observation is a collapse 4 → 2, a factor 2. Caution C2 kept. |
| G3 | Geometer G3: geometry over Z | **dead** | none | Proposer's own verdict, agreed by all. Caution C1 kept. |
| R1 | Combinatorial R1: symmetry space, WL, rigidity | wounded | none | Lemmas correct (technical skeptic). But K6 is a tautology, and **EOS does not imply WL** (technical skeptic), and WL is trivial for the half of classes with λ(a₀) = −1 (builder, Lemma B3). So "cannot do WL ⇒ cannot do EOS" is a heuristic. The barrier skeptic's proposal to use WL as a gate is overruled. |
| R2 | Combinatorial R2: entropy decrement | **dead** | none | Proposer's autopsy (no class-preserving dilation of height ≤ √m), accepted by all. |
| R3 | Combinatorial R3: coset certificate | **dead** for EOS; results merged into W2 | none | Coset statements are deletion-stable (both skeptics, proposer). Prop M1 correct; Hypothesis V is "pair constant < 2" and the Hooley attribution is wrong (technical skeptic). Builder's Mersenne computation is kept under W2. |
| W1 | Wildcard W1: Theorem W | **promising** (as a theorem) | none, provably | Both skeptics re-derived Lemma M, Lemma S, Theorem W and failed to break them; builder rates it the one proved advance. Conjugation-blind, so by Theorem G it cannot be refined to one class. |
| W2 | Wildcard W2: Linnik format, exceptional-set structure | alive, one lemma unwritten | none, provably | Chain verified by both skeptics given the constant C_s. Open: the lattice sieve lemma, the coset fallback when ord(g) is small, the interval-energy citation. |
| W3 | Wildcard W3: relaxed theorems in F_q[t] | alive, low priority | none | Routine transcription (both skeptics). Diagnostic value only. |

### Disagreements I had to settle

- **A1: "wounded" (barrier skeptic) or "alive" (technical skeptic, builder).** Both are right about different
  things. The implication H4 ⇒ EOS is sound and survives every barrier object: alive as a reduction. As a route to a
  proof it has no mechanism: H4 is an 8-prime modular count with relative error 1/M, it implies N(a) ≥ 0.4μ, and any
  proof must use Type II information for A_a. I record it as alive with EOS reach "only through H4".
- **Is H4 in F_q[t] a decision experiment?** The barrier and technical skeptics say yes, the builder says no. I side
  with the builder for the question as posed: for q → ∞ at fixed degree Sawin's pointwise bound already gives H4 and
  powers of the degree are free, and at fixed q the log structure is that of Z. The technical skeptic's sharper form
  (count the pieces of type (d,d,d,d) and their ranks) is well posed but measures the q-threshold of one method, not
  the difficulty of H4. Not funded. The cheap F_2[t] test of the Gaussian law of δ_I at large relative block size
  (builder) goes into the barrier harness instead.
- **WL as a gate.** Overruled, see R1. The replacement that EOS does imply is the P_r ladder of §3.3.
- **"Five logs" for H4.** The technical skeptic's accounting is the correct one: measured from GRH-provable bounds
  the gaps are 5 + 3/k logs (H4) and 3 + 3/k logs (LD), k = ⌊log m/log M⌋ (Prop R1). The builder's remark gives the
  other true number: as one binary problem P × (rough composites) the distance is one log.

---

## 2. New rigorous results from the brainstorm

### 2.1 Proved and independently re-derived in round 2

| Result | Statement | Hypotheses | Verification |
|---|---|---|---|
| **Lemma M** (wildcard) | For finite S ⊂ G and k ≥ 1: \|Σ_{c∈S} E(c)\| ≤ V°·(M²·E_k(S)/V°)^{1/2k}, M = sup of non-principal prime character sums, V° their mean square, E_k the k-fold multiplicative energy. | none | re-derived by both skeptics |
| **Lemma S** (wildcard) | For a set W of primes ≤ y with y^k < m: E_k(W) ≤ k!·\|W\|^k. | none | re-derived by both skeptics |
| **Theorem W** (wildcard) | Every unit a is p·q·s with p, q ≤ m prime and s prime, s ≪ (log m)²(log log m)². Threshold \|W\| ≥ K(φ/m)²L² log L. | GRH (route C's bound H) | re-derived by both skeptics, given route C's lemmas, which were not rechecked this round |
| Cor W1, W2 (wildcard) | For every a, all but K L² log L primes s < m^{1/log log m} have a/s ∈ P·P; every a is n₁n₂ with n_i = prime × prime ≤ K m L (log L)². | GRH | technical skeptic (W2 needs y^{2k} < m) |
| **Prop R1** (technical skeptic) | For a block I of primes in (M, M′] with M′^k < m: Σ_c δ_I(c)² ≤ (k!)^{1/k}(C₁²L³)^{1/k}\|P\|\|I\|. Unconditional weak-type companion: #{c : δ_I(c) > T} ≤ (k\|P\|\|I\|/T²)^{k/(k−1)}. | GRH for the first, none for the second | proved in the referee note; not re-derived by a second reviewer |
| **Theorem BH** (analytic) | For 0 < η ≤ η₀, m ≥ m₀(η): B(a) ≤ (1+η)ρB₀ implies N(a) ≥ 0.4μ. | none beyond the quoted inputs (T1) Fouvry–Shparlinski Type I for A_a and (FL) the fundamental lemma | re-derived by technical skeptic; (T1) quoted correctly from lit/02 §1.2; (FL) numbering [RECALLED] |
| **Cor H4, Cor LD** (analytic) | H4(η), or LD(η), implies B(a) ≤ (1+η)ρB₀ for every a. GRH not used. | **Lemma 2.2 is only sketched** | re-derived by technical skeptic given Lemma 2.2 |
| **Prop S** (analytic) | Any P\* with the Type I data of A_a and no primes in a·P\*⁻¹ violates H4 with η replaced by 1.7η. | none | technical skeptic; it is the contrapositive of the reduction (barrier skeptic), and the same fact as automorphic §1.6 |
| **Prop Q** (analytic) | The conjugate fourth moment is ≥ (m/M)(ρ\|I\|)⁴, above the H4 threshold. | none | technical skeptic for prime m; **the "− ω(m)" count is wrong for composite m** and must be repaired |
| **Lemma H** (automorphic) | The closed horocycle of height 1/m on Y₀(m) self-intersects exactly at z_x = x/m + i/m, paired x ↔ −x̄; a fixed point-pair kernel needs about m forms. Corrects D §4.1(iii). | none | re-derived by both skeptics |
| **Lemma K** (automorphic) | m prime: N(a) = (m+1)\|P\|²/m² + m⁻² Σ_c Π(c)S(1,ac;m), Π = P̂ ∗ P̂. | none | re-derived by technical skeptic; reconstructs N(a) to 10⁻¹¹ at three moduli (computed) |
| Lemmas K0–K4, Thm K5, Cor K6 (combinatorial) | Dictionary for the involution ι_a; corank = dim W_a + number of root-free components. | none | technical skeptic; K6 is a tautology |
| Lemma E1 and class-stabiliser lemma (combinatorial) | Dilation identity; (x,y) ↦ (sx,ty) preserves the class iff st ≡ 1, so max(s,t) > √m. | none | technical skeptic |
| **Prop M1** (combinatorial) | N(aH) ≥ 2\|H\|λ − Σ_{h∈H} N⁻(h) for every subgroup H. | none | technical skeptic, threshold arithmetic exact |
| Energy inequality, 1/(89L) bias, Lemma B (wildcard W2) | Structure of subsets of the exceptional set; Bohr-mass bound through a Fejér majorant and N⁻. | GRH where route C enters | both skeptics |
| **Lemma N** (builder) | Any sup × Parseval bound for one Buchstab block is short by L^{3/2}/√λ even with ideal sup norms. | none | proved in the builder note; the barrier skeptic reached the same wall independently (deficit L³/η² for the arc form) |
| **Lemma B3** (builder) | WL(a) fails iff λ(N) = +1 for every N ≡ a in the m × m multiplication table; WL(a) holds when λ(a₀) = −1. | none | one-line proof; not re-derived |
| Square-modulus identity (builder) | S(1,c;ℓ²) = ℓ Σ_{w² ≡ c} e(2w/ℓ²). | none | classical; checked numerically for ℓ = 7, 11, 13 |
| Schur–Mellin identity, X_a/(S_m × S_m) = T, χ(T∖D) (geometer) | Function-field statements. | none | L1, L2 checked by technical skeptic |

### 2.2 Stated as proved in round 1 and corrected in round 2

- Geometer, m = 2: "rank ≥ 3 in odd characteristic" is **rank exactly 4 with monodromy O(4)** (computed on every
  class for p = 101, 211, 401, 1009; moments 1, 3, 15, 105). "N(a) = const + D₄′/4 + O(√Q)" is **not uniform in a**.
- Analytic: "five logs" and "three logs" are measured from an unproved variance; see §1.
- Combinatorial: "if the team cannot do WL it cannot do EOS" is not an implication. Hypothesis V is not implied by
  Hooley's conjecture in the range where it is used.
- Barrier checklist of A1: (3), (4) and (5) should read "transferred to H4".

### 2.3 Moderator's addition: the finite Buchstab certificate (proved; computed)

Reading Thm BH for the Lean question, I separated its exact part from its asymptotic part.

**Lemma C (exact identity).** For every m, every unit a, and every 2 ≤ z ≤ √m:

  #{primes n ≥ √m in A_a} = S(A_a, z) − B(a) − [1 ∈ A_a],

with S(A_a, z) = #{n ∈ A_a : n = 1 or P⁻(n) ≥ z} and B(a) = Σ_{z ≤ p₁ < √m} #{n = p₁k ∈ A_a : k = 1 or P⁻(k) ≥ p₁}.

*Proof.* Buchstab's identity, and an n < m coprime to m with all prime factors ≥ √m is 1 or a prime. ∎

**Lemma C′ (finite certificate).** Let the half-open blocks I_j = [M_j, M_{j+1}) cover the primes in [z, √m), let
𝒦_j = {units k ≤ m/M_j : k = 1 or P⁻(k) ≥ M_j}, δ_j(c) = #{p₁ ∈ I_j : c·p̄₁ ∈ P} − ρ|I_j|, and Y_j ≥ Σ_{c∈G} δ_j(c)⁴. If

  S(A_a, z) − 1 − Σ_j (ρ|I_j||𝒦_j| + |𝒦_j|^{3/4} Y_j^{1/4}) > 0,

then a ∈ P·P.

*Proof.* Lemma C, the inclusion (2.1) of the analytic note (positivity of 1_P), and Hölder (2.2). ∎

Status: proved (elementary; it is Thm BH and Cor H4 with all asymptotics removed). Computed
(`scratchpad/moderator/cert.py`, full path
`/private/tmp/claude-501/-Users-maxfeldman-Desktop-maths-research/9e4c9912-0c7a-4fa9-a228-3de7c709a385/scratchpad/moderator/cert.py`):
for m = 2003, 2311, 3003, 2401, 10007 and every unit a, the identity of Lemma C holds with zero failures and the
block inequality B(a) ≤ Σ_j(…) holds with zero failures. **The certificate itself never fires at these sizes**
(the left side is between −270 and −1900 against μ between 46 and 151), which agrees with the analytic persona's
statement that H4 has content only once M exceeds roughly (log m)⁵. So Lemma C′ is a sound but numerically vacuous
statement for every m we can compute; its use is as the exact interface between the sieve side and the hypothesis.

### 2.4 Heuristic or computed only (not results)

- **Quotient atlas** (builder): N⁻(u/v)/λ ≈ Σ_j w_j 𝔖_j over the lines vp − uq = jm; computed to 0.5–1%; explains
  the 4% variance deficit, max N⁻(b)/λ = 1.29 at b = 2/3, 3/2, and 0.88–0.95 for even-order subgroups. Heuristic.
- **Kloosterman singular series** (automorphic): secondary terms κ(u/v)(√m/log² m)Kl₂(ac;m) in N(a), κ stable in m;
  the formula for κ is heuristic; the θ′² law is empirical.
- **Barrier 6 is vacuous in F_q[t]** (barrier skeptic): computed for F_2[t], n = 9..17; the local explanation is
  sketched. The script is still in the session scratchpad and has to be copied into `compute/` by its owner.
- **Variance deficit** c(λ)ρ with c(1) ≈ 0.56 (technical skeptic, computed); **Mersenne certificate** for
  m = 2ⁿ ± 1, n = 13..24 (builder, computed); **rigidity** for primes 113 ≤ m < 620 and four larger m (computed).

---

## 3. What to fund next

### 3.1 Fund first: the Theorem W package (a GRH theorem and a Lean deliverable)

**Goal.** Under GRH (in the repo's form `GRHSmoothBound` / `GRHBounds`): there are K, m₀ such that for every m ≥ m₀
and every unit a mod m there are primes p, q ≤ m and a prime s ≤ K(log m)²(log log m)² with p·q·s ≡ a (mod m).
Supporting unconditional statements: Lemma M, Lemma S, and the weak-type half of Prop R1. Secondary: Theorem
W-Linnik (a = p·q·gʲ·s, j < K L log L) once the lattice sieve lemma for C_s is written.

**Barriers.** The statement is weaker than EOS, so the test is that no barrier object contradicts it. (1) Random
pairing-avoiding set: only one class is avoided, the target has ≫ L² classes. (2) Deletion: emptying every class
a/s would need deleting more than all the primes. (3) Parity: three primes, no sieve. (4) A\*: no Type I data
used. (5) Prop L: consistent, L′² is the variance wall for Sidon-type targets. (6) Theorem G: the proof sees only
|S(χ)|², so it proves the same for P·P⁻¹, which is true there. **By the same token it provably cannot reach a single
class.** This item is funded as a theorem, not as progress toward EOS.

**First two tasks.**
1. Literature check against Banks–Shparlinski (Thm 1.3 and any (log q)² variant) and the ternary literature; then
   write Theorem W with explicit constants on top of route C's lemmas D2, D3, D4(a), rechecking those lemmas, since
   no round-2 reviewer did.
2. Lean: state and prove Lemma M (finite Fourier analysis on (Z/mZ)^* and Hölder) and Lemma S (unique
   factorisation), then `coveredBy_three_primes` from the existing `GRHSmoothBound`. Numerical companion already
   exists (`compute/brainstorm/wildcard/multiplier_cert.py`: the certificate drops below 1 at 64–256 small primes).

**Lean form.** Lemma M, Lemma S: unconditional. Theorem W: GRH only (existing named hypothesis). Theorem W-Linnik:
GRH plus an unconditional sieve lemma that would have to be a cited named `Prop`.

**Probability.** Theorem W correct: 90%. New in the literature: unverified, my guess 50%. Lean formalization
completed with moderate effort: 70%. Reaches EOS: 0.

### 3.2 Fund second: the Buchstab certificate with H4/LD as the named gap

**Goal.** (a) A complete proof of: there are η₀ > 0 and m₀(η) such that for η ≤ η₀ and m ≥ m₀(η),

  H4(η): Σ_{c∈G} δ_j(c)⁴ ≤ (η/2)⁴ρ⁴|I_j|′⁴|𝒦_j| for every block I_j ⊂ [m^η, (1+λ)√m], λ = η/(4C₁),

implies N(a) ≥ 0.4μ for every unit a; the same with LD(η) (E_j(T) ≤ ¼|𝒦_j|(T_j/T)² for T ≥ T_j = ηρ|I_j|′/4) in
place of H4. (b) The barrier table for H4 and LD on all six objects, for prime and composite m. (c) The builder's
open question, stated as a research problem: B(a) = #{(p,n) ∈ P × R : pn ≡ a}, R the z-rough composites ≤ m, needs a
one-sided bound with relative precision η, and Parseval misses by one log; R has bilinear structure and Type I data
to level 1, P has neither. Find a formulation that uses the structure of R without the L^{3/2} of Lemma N.

**Barriers.** (1) Random avoiding set R: the argument uses P in two roles, so for R it proves a ∈ R·P, which is
true. (2) Deletion: |A_a| = |P| exactly; P ∖ R_a breaks Type I at d = 1, and the sifted count drops by exactly N(a).
(3) Parity and (4) A\*: **not passed, transferred**: Prop S shows every parity object with the Type I data violates
H4(1.7η), and A\* violates H4, so no proof of H4 from sizes plus Type I exists. (5) Prop L: transferred likewise;
H4 is a four-point phase-sensitive statement, and any sup + Parseval proof of it is blocked (Lemma N). (6) Theorem
G: passed twice, Type I of {−p} fails at d = 2 and Prop Q puts the conjugate fourth moment above the threshold
(prime m; composite m to be repaired). D's four requirements are met by the reduction: joint (P, a) Type I data,
the fragile identity |A_a| = |P|, bilinear input beyond Type I, and separation of one prime from two through the
sieve weights.

**First two tasks.**
1. Mathematics: write Lemma 2.2 in full (top blocks near √m included), repair Prop Q for composite m, and state
   the theorem with H4 and with LD. Use the shrinking-box model (A2) only as a check of the block bookkeeping.
2. Numerics: the barrier harness proposed by the barrier skeptic. One script evaluating the block statistics
   (variance, fourth moment, one-sided tail at T_j) on P, P⁻¹, P ∖ R_a, A\*_a, a random pairing-avoiding set and a
   Spencer-type signed set, at m ≈ 10⁶–10⁷, for prime m, m = r², and highly composite m, plus the F_2[t] version of
   the δ_I law at large relative block size. The P-versus-A\* gap at finite m is the real size of the target.

**Lean form.** GRH is not used. The theorem is "cited unconditional Type I input + H4(η) ⇒ `Conjecture`", i.e.
GRH-free plus a named hypothesis; see §5 for the layering. The exact core (Lemmas C, C′ of §2.3) is unconditional
and formalizable now.

**Probability.** Reduction correct after Lemma 2.2 is written: 85%. H4 or LD from GRH: about 1%. Any saving at all
over the Prop R1 bound for the fourth moment: 5%. EOS: under 1%.

### 3.3 Fund third, small and gated: the parity-free calibration ladder

**Goal.** Determine the least r for which the following is provable (unconditionally or under GRH) for prime m:
for every unit a there is n < m with Ω(n) + Ω(ι_a(n)) ≤ r, where ι_a(n) = a·n̄ mod m. EOS is r = 2 and is implied
by nothing weaker on this ladder; unlike WL, each rung is implied by EOS. Rung 0, to be done first or found in the
literature: the unbalanced smooth toy, #{n₁n₂n₃n₄ ≡ a : n₁, n₂ ≤ m^{3/4}, n₃, n₄ ≤ m^{1/4}} ~ m²/φ for every a,
which sits exactly at the Weil threshold.

**Barriers.** No barrier object applies to the smooth toy (complete Type I data, no deletion), and barrier 5 is
the point of it: nobody has beaten a one-log Parseval deficit pointwise in a anywhere. For the P_r ladder: (1), (2)
not applicable for r ≥ 3 (deletion of R_a does not affect almost-primes); (3) parity is not crossed, by design;
(4) A\* satisfies every rung with r ≥ 3, which is why the ladder measures distance and proves nothing about EOS;
(6) passed, the Kloosterman sums over primes are the product-specific input. **This item cannot yield EOS.**

**First two tasks.**
1. Literature check: the unbalanced toy against the level-2/3 results for d(n) and d₄-type sums in progressions;
   the P_r record for a·p̄ mod m (lit/02 tags r = 5 as unverified in the source). Resolve the kernel issue (ratio
   Kl₂(a·s·r̄) versus product) before attempting the toy.
2. If the toy is open: the first lemma of TD, a trilinear Kloosterman bound with well-factorable weights beating
   Fouvry–Shparlinski's m^{15/16}, stated in the form Thm BH wants (sieve remainder for A_a at level above 1/16).
   This is the one place where the third item feeds the second: level 1/4 would allow η ≈ 1/20 (analytic's
   constant, not recomputed).

**Lean form.** Nothing soon. A final statement would be unconditional or GRH-only, but depends on deep external
bilinear Kloosterman bounds.

**Probability.** Toy already known: 40%. New almost-prime result for prime m: 15%. A mechanism transferable to two
primes: under 0.5%.

### Not funded

- G1 (ranks of Schur pieces, the sharp bound |D₄′(a) − Q²| ≤ 4Q): a legitimate function-field project with about
  30% chance of a lower q-threshold, but with no transfer and, after the barrier skeptic's computation, no
  evidential value for barrier 6. Hand it off as a separate note if someone wants it.
- H4 in F_q[t] as a decision experiment (§1), special moduli (A3), the shrinking-box theorem (A2) as a goal in
  itself, exceptional set ≪ L^{2+ε} (needs an inverse theorem with polynomial losses that does not exist).

---

## 4. What we learned

1. **One conservation law, seen five times.** Every route lands at volume exactly m² with a one-log Parseval
   deficit: EOS itself (Prop L), the Buchstab sum as a binary problem P × R (builder), the sum over all blocks
   (barrier skeptic), WL (technical skeptic), and the analogy with the least prime ≤ q² (automorphic). Block
   decompositions make it worse (Lemma N: L^{3/2} per block), which is where the three and five logs of LD and H4
   come from.
2. **Conjugation-blind methods have a sharp ceiling, and the wildcard found it.** Size methods need a target of
   at least L′ classes (deletion) and reach L′²·(log L) for Sidon-type targets, L′ log for progressions, L′ for
   cosets (Wiener-norm hierarchy, heuristic as a lower bound). Removing the auxiliary set is, in every version
   (W2, R3, route C §6.1, the Mersenne certificate), the single statement "prime-pair upper bound with constant
   below 2": the parity constant. Theorem G forbids a single class.
3. **Barrier 6 is quantified, on both sides.** Quotient side: an O(1) singular series on small heights (atlas,
   0.44λ to 1.32λ, zero at b = −1). Product side: a singular series only at relative size m^{−1/2}, in the
   Kloosterman-dual variable (automorphic). So a conjugation-blind method cannot prove N(a) ≥ cλ with c above about
   0.5 (heuristic); the barrier is not confined to a = −1. This refines D §1.2.
4. **The F_q[t] test bed is faithful for barriers 1–5 only.** With P = irreducibles of degree exactly n the
   quotient problem has no obstructed class (computed for F_2[t]), so a function-field proof may be
   conjugation-blind and correct. Also, characteristic 2 has parity-breaking structure (Berlekamp) with no integer
   shadow. D §3's sentence about a q = 2 proof needs both caveats.
5. **The level-m trace formula costs m terms, not m².** Lemma H corrects D §4.1(iii); the verdict there is
   unchanged because the expansion is still a unitary change of basis.
6. **Buchstab beats Vaughan for this problem.** One-sided, constant relative precision, rough k only, M ≤ √m, no
   sup bound, against route A's two-sided precision ε/log m on all k up to m^{1−η}. H4 supersedes M4.
7. **"Passes all six barriers conditional on H" means the barriers have been moved into H.** A\* violates H4
   although H4 is a-independent, because each a gives its own P\*_a. Future checklists should distinguish "passed"
   from "transferred to the hypothesis".
8. **GRH now controls second moments of Type II block counts** up to k(CL³)^{1/k} (Prop R1). The fourth moment
   is untouched: it is a four-fold convolution on the character side and no Hölder step against |U| applies.
9. **Calibration problems must be implied by EOS.** WL is not; the P_r ladder is. The smooth toy is not "logs
   only": sup-norm steps for smooth sums of length √m lose m^{o(1)}.
10. **Recorded failed combinations** (do not repeat): Lemma M on the Buchstab arc; averaging the Buchstab sum over
    Sidon multipliers; Chen switching; Theorem W witnesses for WL (they leave the table by exactly L²).

Open questions carried forward: a product-side analogue of Lemma B (a positive-definite majorant in the
Kloosterman-dual variable with a sieve-bounded physical side; expected not to exist, since Π is not positive); and
the builder's one-log question of §3.2(c).

---

## 5. Recommendation for the Lean deliverable

**Recommendation: isolate the gap as H4(η) (or its weak-type form LD(η)), entered through the finite certificate
of §2.3. Keep TwistedRatios as the documented alternative. Retire M4.**

Comparison of the candidates:

| Hypothesis | Mentions a? | Relation to EOS | Deduction status | Lean cost of the deduction |
|---|---|---|---|---|
| **TR(δ)** (route B) | yes, for every a | essentially "E(a) has a power saving in every box": a restatement in ratios-conjecture language, stronger than EOS, false for δ > 2/3 | proved modulo standard GRH facts | high: Mellin inversion, contour shifts, bounds for L′/L |
| **M4** (route A) | no | a-independent fourth moment, ten logs below trivial, for M up to m^{1−η} | Prop E only sketched; needs a sup bound not available for M < √m | not ready |
| **H4(η)** (analytic) | no | a-independent fourth moment for M ≤ √m; implies N(a) ≥ 0.4μ; GRH not used | proved given Lemma 2.2 (sketched) and two quoted unconditional inputs | exact core is elementary; asymptotic layer needs sieve inputs |
| **LD(η)** | no | weak-type form, weaker than a fourth-moment bound of the same strength | proved given Lemma 2.2 | same as H4 |
| "C_s < 2" / Hypothesis V | no | gives coset and Linnik-format statements only; **cannot** give EOS (deletion-stable, Theorem G) | n/a | n/a |

Why H4/LD is the most natural and least circular:

1. **It does not mention the target class.** TR(δ) and the hypothesis of Thm BH itself ("B(a) ≤ (1+η)ρB₀ for all a")
   are statements about every a and are EOS with a different name. H4 is a single statistic of the pair (P, I_j)
   over all of G.
2. **It separates products from quotients inside the hypothesis.** Prop Q: the conjugate statement is false. No
   other candidate has a proved statement of this kind; TR's conjugate is simply a different conjecture.
3. **It is falsifiable and has been tested against the barrier objects**: A\* and every parity object violate it
   (Prop S), the random avoiding set is consistent with it, and δ_I is Gaussian in the computed range (kurtosis
   3.02–3.29). The barrier harness (§3.2) will give the full table.
4. **The deduction has an exact, elementary core.** Lemma C′ needs only Buchstab's identity, positivity and
   Hölder. It can be formalized now and is unconditional.

What has to be said honestly in the Lean file and in the notes:

- **The theorem is not of the form "GRH + H ⇒ EOS"; GRH is not used.** The correct shape is

  `theorem eos_of_H4 (hT : TypeISifted) (hH : H4 η) : Conjecture`

  where `TypeISifted` is a named `Prop` for Lemma 2.1 (S(A_a, z) ≥ ρΦ_m(m,z)(1 − Ce^{−s}) − m^{1−c}), an
  **unconditional** theorem cited from Fouvry–Shparlinski plus the fundamental lemma. The project rule asks for
  named hypotheses with a citation showing they follow from GRH; a cited unconditional theorem satisfies that
  a fortiori, but it is a second named input and should be listed as such. If the deliverable must literally
  contain `GRHBounds`, add it as an unused hypothesis only with a comment saying so; I would not.
- **H4 is beyond GRH and stronger than EOS** (it gives N(a) ≥ 0.4μ, and is an 8-prime modular count with relative
  error 1/M). It isolates the gap; it does not shrink it. Measured from GRH-provable bounds it asks for 5 + 3/k logs.
- **The constants are bad.** With Type I level m^{1/16}, η is about 1/100–1/150, so the constant in H4 is about
  10⁻⁹ and m₀(η) is astronomically large. The Lean statement should quantify "∃ η₀, ∀ η ≤ η₀, ∃ m₀".
- **The asymptotic layer is not cheap in Lean**: Mertens' product with the constant e^{−γ}, π(m) ~ m/L, counts
  of rough numbers in intervals (Lemma 2.2). Suggested layering:
  1. `buchstab_certificate` (Lemma C′): unconditional, finite, formalize now.
  2. `eos_of_H4` assuming `TypeISifted`, `H4 η`, and one more cited named `Prop` for the rough-number counts
     (Lemma 2.2 with the Mertens constant), each with its citation. Formalize after Lemma 2.2 is written on paper.
  3. Discharging the cited inputs: deferred, like the derivation of `GRHBounds` from literal GRH.

Independently of the gap theorem, the strongest Lean target from this brainstorm that needs no extra hypothesis
is Theorem W (§3.1): it needs only the GRH hypothesis already in the repo and would sit next to `coveredBy_log_sq`
and `coveredByAsym_m_log_cube` as a third rigorous approximation to EOS.

---

## 6. Not checked by the moderator

- I did not re-derive any round-1 or round-2 proof except Lemma C and C′ of §2.3; the verification column of §2.1
  reports what the round-2 reviewers say they did.
- Route C's lemmas D2, D3, D4(a), on which Theorem W rests, were not rechecked by anyone in this brainstorm.
- The literature status of Theorem W, the unbalanced D₄ toy, WL, and the shrinking-box theorem is unverified.
- The certificate computation of §2.3 covers m ≤ 10007 only and tests soundness, not strength.
- Several round-2 scripts (`ff2_conjugate.py`, the builder's `atlas.py`, `var2.py`, `mers.py`, and my `cert.py`)
  live in the session scratchpad, which is not durable; they should be copied into `compute/brainstorm/` by whoever
  owns that directory.
