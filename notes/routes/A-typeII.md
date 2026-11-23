# Route A: sieve over A_a = {a·p̄ mod m} with an arithmetic Type II estimate

Written 2026-11-22. Scripts and outputs: `compute/routeA/` (`typeII_vaughan.py`, `dispersion_arc.py`, `out_*.txt`).

Status tags, as in CLAUDE.md: **proved** / **sketched** / **heuristic** / **[UNVERIFIED]**.
"Proved (GRH)" means proved assuming GRH for Dirichlet L-functions (including ζ).
Results quoted from `notes/lit/` keep the provenance given there; I did not re-read the sources.

---

## 0. Verdict

**Verdict (b): the route does not work under GRH as it stands. The Type II estimate it needs is equivalent
to quantitative EOS, and every available way of proving it stops at the same log-power wall.**

In one paragraph. Vaughan's identity applied to the sifted variable gives the exact relation
Ψ(a) = ρm + II(a) + O(m^{1−κ}) (Theorem A). The Type II sum II(a) is therefore not an auxiliary quantity:
bounding it *is* EOS. Opening the Möbius structure of its coefficients is exactly circular (Proposition D).
Treating the coefficients as generic gives Parseval, which is short by (log m)² per block, and every use of GRH
sup-bounds is worse (§3). A set-level barrier (Theorem B, proved under GRH) shows that no argument can succeed
if all it uses about the outer primes P is their size, GRH-quality character sums, exact orthogonality and the
Type I data of A_a to any level D < √m, even with the genuine μ/Λ coefficients on the sifted side. The
"redacted primes" barrier is, by contrast, *vacuous* against this route (Proposition C): redaction leaves every
Type II sum unchanged and shows up only in the cardinality |A|.

What the route does give:

1. An exact reduction with explicit log accounting (§1, §3).
2. A correct barrier replacing the redacted-prime one for this route (§4).
3. Two clean sufficient hypotheses, both **beyond GRH** (flagged): a bilinear Kloosterman bound over
   primes × primes with a saving equal to the full length of the short variable (K-II, §5), and an
   a-independent fourth-moment / exceptional-set bound for the ternary-type count ν_M(c) (M4, §6).
   M4 needs only a (log m)^{10} saving over the trivial bound, has a factor M/(log m)^{O(1)} of room, and is
   numerically true with Gaussian size. I could not derive either from GRH.
4. No new partial result. The Type II estimate holds for all but (log m)^{O(1)} classes a (Proposition 3.2),
   which re-proves a weaker form of the known almost-all statement.

---

## 1. The reduction

### 1.1 Notation

- m large, (a,m) = 1, G = (Z/mZ)^*, φ = φ(m). P = {p ≤ m prime, p ∤ m}, ρ = |P|/φ.
- A = A_a = {a·p̄ mod m : p ∈ P} ⊂ [1,m], F = F_a its indicator, F(n) = 1_P(a·n̄ mod m) for (n,m) = 1.
- A_d = {n ∈ A : d | n}. Since A ⊂ units, A_d = ∅ unless (d,m) = 1.
- Ψ(a) = Σ_{n≤m} Λ(n)F(n). Prime powers contribute O(√m), so
  Ψ(a) = Σ_{q ∈ P, a q̄ ∈ P} log q + O(√m) and N(a) ≥ Ψ(a)/log m − O(√m).
  The expected value is ρm, and ρm/log m ≍ μ = |P|²/φ.
- S(χ) = Σ_{p∈P} χ(p). Under GRH, |S(χ)| ≪ √m log m for χ ≠ χ0 (prime-count normalisation, sharp cutoff).

### 1.2 Vaughan's identity on the sifted variable

Fix U, V ≥ 1. For every n ≥ 1,

  Λ(n)·1[n > U] = Σ_{d|n, d≤V} μ(d) log(n/d) − Σ_{dc|n, d≤V, c≤U} μ(d)Λ(c) + Σ_{dc|n, d>V, c>U} μ(d)Λ(c).

Hence, exactly,

  Ψ(a) = Σ_{n≤U} Λ(n)F(n) + I₁ − I₂ + II,

- I₁ = Σ_{d≤V} μ(d) Σ_{n∈A_d} log(n/d),
- I₂ = Σ_{e≤UV} c_e |A_e|, with c_e = Σ_{dc=e, d≤V, c≤U} μ(d)Λ(c), |c_e| ≤ log e,
- II = Σ_{U<u≤m/V} Λ(u) Σ_{V<k≤m/u} b_k F(uk), with **b_k = Σ_{d|k, d>V} μ(d) = [k=1] − Σ_{d|k, d≤V} μ(d)**.
  So b_k = 0 for k ≤ V, and b_k = −1 for every V-rough k > 1.

The identity was checked numerically to rounding error for every sequence tested (`typeII_vaughan.py`).

### 1.3 Type I input

**Lemma 1.1 (quoted; `lit/02-tools.md` §1.2, [READ 1705.06087, Lemma 5.4], Fouvry–Shparlinski).**
For (d,m) = 1 and y ≤ m: #{n ∈ A_d : n ≤ y} = |P|·y/(dm) + O(m^{15/16+o(1)}), uniformly in a, d, y.

**Lemma 1.2 (sketched, under RH).** Put Z_V = Σ_{d≤V,(d,m)=1} μ(d)/d and Z′_V = −Σ_{d≤V,(d,m)=1} μ(d) log d/d.
Then Z_V ≪ V^{−1/2+ε} m^{o(1)} and Z′_V = m/φ(m) + O(V^{−1/2+ε} m^{o(1)}).
*Sketch.* Σ_{d≤x,(d,m)=1} μ(d) = Σ_{k | m^∞} M(x/k) ≪ x^{1/2+ε} ∏_{p|m}(1 − p^{−1/2−ε})^{−1} = x^{1/2+ε} m^{o(1)} under RH.
Partial summation, with Σ_{(d,m)=1} μ(d)d^{−s} = (ζ(s)∏_{p|m}(1−p^{−s}))^{−1}, gives both claims.
Without RH the uniformity in m of Z_V → 0 for V = m^η is a nuisance I did not resolve.

### 1.4 The exact reduction

**Theorem A (proved (GRH), given Lemma 1.1; Lemma 1.2 is sketched).** Let U = V = m^η with 0 < η < 1/32.
There is κ = κ(η) > 0 such that for all large m and all (a,m) = 1,

  **Ψ(a) = ρm + II(a) + O(m^{1−κ}).**

Consequently:
- N(a) ~ μ in the Λ-weighted sense ⟺ II(a) = o(ρm);
- Ψ(a) ≥ δρm ⟺ II(a) ≥ −(1−δ)ρm + O(m^{1−κ}).

*Proof.* Σ_{n≤U}ΛF ≤ ψ(U). By Lemma 1.1 and partial summation, I₁ − I₂ equals
(|P|/m)·m·[Z_V(log m − 1 − Σ_{c≤U,(c,m)=1} Λ(c)/c) + Z′_V] + O(UV·m^{15/16+o(1)}).
By Lemma 1.2 the bracket is m/φ + O(m^{−κ}), and |P|·m/φ = ρm. ∎

Remarks.
- **The Type I range suffices, in the bookkeeping sense.** Level UV ≤ m^{1/16−ε} is all that Vaughan needs.
  The price is the Type II range: u runs over the whole of (m^η, m^{1−η}]. No sub-range can be dropped, and
  no Harman-type argument is available because there is no range at all in which Type II information for A_a
  is known.
- **Theorem A is an identity, so the Type II statement with the genuine coefficients is *equivalent* to
  quantitative EOS, not a reduction of it.** The only question is whether II(a) can be bounded by a route
  that does not pass back through Ψ(a). Sections 2–6 examine every such route I could find.
- The same holds for Heath-Brown's identity and for iterated Vaughan: any identity
  Λ = (Type I of level ≤ D) + (multilinear terms supported on n with a factorisation into parts > 1)
  gives Ψ(a) = ρm + (multilinear part) + O(m^{1−κ}) for D ≤ m^{1/16−ε}.
- Numerically (m ≈ 10⁶, 4·10⁶, U = V = m^{1/6}): the centred II(a)/(ρm) has mean ≈ 0 and standard deviation
  0.018, 0.016 over random a. The random-model prediction (ρ Σ c_II(n)²)^{1/2}/(ρm) is 0.014 at m = 4·10⁶.
  So II(a) is of square-root size in truth; the estimate is true with enormous room and unprovable.
  (At these m the truncation Z_V is not small, so the scripts centre with the integer model, II − ρ·II(integers).)

### 1.5 Is parity evaded?

Only by the Type II hypothesis itself.
- Type I data alone cannot detect primes in A_a: Theorem B below constructs a sequence with the same Type I
  data to any level D < √m (with square-root error, better than Lemma 1.1) and no primes above D.
- A Type II bound for A_a with general bounded coefficients would break parity. For instance it implies
  Σ_{n∈A_a} μ(n) = o(|A_a|) by the analogous identity for μ (**sketched**). That Möbius-randomness statement
  for A_a is itself open.

---

## 2. Structure of the Type II sum: opening the Möbius coefficient is circular

Split u into blocks u ∼ M (M < u ≤ 2M) and write
Ψ_M(a) = Σ_{u∼M} Λ(u)F(u), G(M) = Σ_{u∼M} Λ(u) Σ_{k≤m/u} b_k F(uk), so II = Σ_M G(M).

**Proposition D (proved; an identity).** For every block,

  **Ψ_M(a) = G(M) + L(M),  L(M) := Σ_{d≤V} μ(d) Σ_{u∼M} Λ(u) |A_{ud}|.**

Moreover Σ_{all u>U} of the L-terms equals I₁ − I₂.

*Proof.* Σ_{d≤V}μ(d)|A_{ud}| = Σ_k (Σ_{d|k,d≤V}μ(d)) F(uk) = Σ_k ([k=1] − b_k)F(uk). For the last claim use
Σ_{u | n/d} Λ(u) = log(n/d). ∎

Consequences.
- L(M) is a pure level-of-distribution sum for A_a, with moduli ud ≈ M that have a large prime factor. It is
  not parity-sensitive. It is known only for MV ≤ m^{1/16−ε}.
- Using b = −μ_{≤V} * 1 inside G(M) returns Ψ_M(a) − L(M): **the μ-structure of the Type II coefficient,
  once opened, hands back the unknown.** The only non-circular uses of G(M) treat b_k as an opaque
  coefficient (§3), or open it and prove a new estimate for sums over the smooth variable restricted to
  e > V/d (§5).
- A blockwise Type II estimate asserts strictly more than blockwise EOS: it asserts
  Ψ_M(a) − ρ·Σ_{u∼M}Λ(u) = L(M) − (main) + o(ρm/log m), with L(M) unknown for M > m^{1/16}.
- Concretely, since b_k = −1 on V-rough k, G(M) is essentially −Σ_{k rough} (Σ_{u∼M}Λ(u)F(uk) − mean) plus a
  bounded-coefficient remainder. **EOS has been traded for the ternary count p·u·k ≡ a with p ≤ m prime,
  u ∼ M prime, k ≤ m/M rough, at relative precision o(1/log m).** That is a three-"prime" problem at the same
  critical volume m², and Parseval fails for it by (log m)^{3/2} (§3.1, "three primes at critical volume").

---

## 3. Log accounting for phase-blind arguments

Centre everything: G_c(M) = G(M) − ρ Σ_{(n,m)=1} c_M(n), where c_M(n) = Σ_{u|n, u∼M} Λ(u) b_{n/u}.
Then G_c(M) = (1/φ) Σ_{χ≠χ0} χ̄(a)·S̃(χ)·C_M(χ), with |S̃(χ)| = |S(χ)| and C_M(χ) = Σ_n c_M(n)χ(n).

**Target.** There are ≍ log m blocks, so the route needs |G_c(M)| ≤ ε·ρm/log m ≍ ε·m/log² m for each block
(absent a proof of cancellation between blocks).

### 3.1 What each tool gives

- **Size of the coefficients.** Σ_{n≤m} c_M(n)² ≍ m log m. The upper bound is **sketched**: the diagonal is
  Σ_u Λ(u)² Σ_{k≤m/u} b_k² ≪ m log M using Σ_{k≤x} b_k² ≪ x (Dress–Iwaniec–Tenenbaum, [RECALLED]).
  Numerically Σ c_M²/(m log m) ∈ [0.05, 0.23] in every block, at all three m tested.
- **Exact Parseval** (distinct integers ≤ m are distinct mod m, both for P and for the support of c_M):
  |G_c(M)| ≤ (|P| · Σ c_M²)^{1/2} ≍ m. **Deficit: (log m)².** (Numerically the bound is 3–7 times ρm per block,
  against a target of 0.07·ρm.)
- **GRH sup-bound on S:** |G_c(M)| ≤ max|S| · (Σ c_M²)^{1/2} ≪ √m log m · √(m log m) = m (log m)^{3/2}.
  Deficit (log m)^{7/2}. Worse than Parseval.
- **GRH sup-bound on the short polynomial** U_M(χ) = Σ_{u∼M}Λ(u)χ(u) ≪ √M log² m:
  ≤ max|U_M| · (|P|·m/M)^{1/2} ≍ m (log m)^{3/2}. Deficit (log m)^{7/2}.
- **GRH for Möbius-weighted short polynomials** Σ_{d≤V} μ(d)χ(d): the available GRH bound is
  V^{1/2} exp(O(log m/log log m)) [RECALLED: it comes from 1/L(s,χ) near the half-line], which loses more than
  any power of log. So "GRH for M(χ), N(χ)" is quantitatively the weakest input of all.
- **Hölder mixtures.** The L² norms of S and C_M are exact and the sup norms are within log powers of the
  RMS, so no Hölder combination beats Parseval. The numbers are as in `lit/03` §0.2.
- **Three primes at critical volume.** For a ≡ p·q₁·q₂ with q₁ ∼ M, q₂ ∼ m/M: main term ≍ m/log³ m,
  Parseval error (|P|·#{q₁q₂})^{1/2} ≍ m/(log m)^{3/2}. Deficit (log m)^{3/2}.
- **Baseline.** With 1-bounded coefficients and target o(main), the deficit is (log m)^{1/2} (`lit/02` §1.5).
  The extra (log m)^{3/2} above comes from Λ being sparse (1/2) and from the log m blocks (1).
  A cleverer identity could reduce 2 towards 1/2 but not below.

**Conclusion (proved).** Every bound of the form (1/φ)Σ|S||C_M|, however the factors are grouped, is at least
a power of log too large. What is needed is cancellation in Σ_χ χ̄(a) S̃(χ) C_M(χ) across χ.

### 3.2 What survives: almost all a

**Proposition 3.2 (proved (GRH)).** For each block, Σ_a |G_c(M)|² = (1/φ)Σ_{χ≠χ0}|S|²|C_M|² ≤ max|S|²·Σc_M²
≪ m² (log m)³. Hence the Type II estimate |G_c(M)| ≤ ερm/log m holds for all but O(ε^{−2}(log m)^7) classes a,
and for all blocks simultaneously outside O(ε^{−2}(log m)^8) classes.

This is weaker than Banks–Shparlinski's O((log m)³) and gives nothing new. It shows that the Type II estimate
has the same almost-all status as EOS itself.

---

## 4. The barriers, made precise for this route

### 4.1 The redacted-primes barrier is vacuous here

Let R_a = {p ∈ P : a p̄ ∈ P} and P′ = P ∖ R_a, as in `lit/03` §4. The corresponding sequence is A′ = A ∖ P.

**Proposition C (proved; an identity).**
1. II(A′) = II(A) exactly, block by block. The Type II coefficient c_II(n) vanishes at primes (a prime n has
   no factorisation n = uk with u > U, k > V), so removing primes from A changes nothing.
2. For 1 < d ≤ D, |A′_d| = |A_d| − #(A ∩ {primes dividing d}) ; so Type I data differ by O(1) per modulus.
3. The only change is at d = 1: Σ_{n∈A′} log n = Σ_{n∈A} log n − Σ_{q∈A∩P} log q. That is, I₁ drops by exactly
   Ψ(a) (up to O(√m)).

So Vaughan's identity "holds" for the redacted set, as it does for every sequence. Redaction is not seen by
Type II sums at all; it is seen as a relative defect ≈ ρ·(m/φ) in the *cardinality* |A′| = |P| − N(a),
compared with the density |P| read off from the moduli d > 1. In formula form (**sketched**, same proof as
Theorem A): for any sequence 𝒜 ⊂ [1,m] ∩ units with #{n ∈ 𝒜_d, n ≤ y} = X_∞·y/(dm) + O(m^{1−κ}) for
1 < d ≤ m^{2η}, and |𝒜| = X₁ with the d = 1 distribution uniform to o(X₁/log m),

  Σ_{n∈𝒜} Λ(n) = (m/φ)·X_∞ + (X₁ − X_∞)(log m − 1) + II(𝒜) + o(m/log m).

For A_a, X₁ = X_∞ = |P|. For A′, X₁ − X_∞ = −N(a), the left side is ≈ 0, and II is unchanged: consistent,
and no information.

**Answers to the brief's questions.** A redacted prime set does satisfy the Vaughan identity. The Type II
statement with genuine μ-coefficients does *not* fail for it; it is literally the same number. The redacted
set is therefore neither an obstruction to proving the Type II estimate nor a test of what extra structure
the route uses. A proof of II(a) = o(ρm) from GRH-quality bounds on S′(χ) would be no contradiction: it
would prove EOS for P and say nothing false about P′, because for P′ the missing mass sits in X₁.
(Caveat inherited from `lit/03`: that P′ satisfies GRH-quality bounds is itself heuristic.)

### 4.2 The correct barrier: boosted rough composites

The right adversary keeps X₁ = X_∞ and still has no primes. It must move the mass of the primes onto
composites that Type I moduli d ≤ D cannot see.

**Theorem B (proved (GRH); the smoothed prime-sum bound is quoted from `lit/03` §0.1, where it is sketched).**
Fix 0 < θ < 1/2 and put D = m^θ. For every large m and every (a,m) = 1 there is a set A* ⊂ [1,m] of integers
coprime to m, equivalently a set P* = a·(A*)^{−1} ⊂ G of distinct residues, such that:

1. |P*| = |P| + O(√(m log m)).
2. max_{χ≠χ0} |Σ_{x∈P*} χ(x)| ≪_θ √m. (For P itself GRH gives √m log m.)
3. For every 1 < d ≤ D with (d,m) = 1 and every y ≤ m:
   #{n ∈ A*_d : n ≤ y} = ρ·#{n ≤ y : d | n, (n,m) = 1} + O(√(m log m)).
   For d = 1: |A*| = |P| + O(√(m log m)) and Σ_{n∈A*} log n = |P| log m·(1 + O(1/log m)).
4. A* contains no prime in (D, m], and Σ_{n∈A*} Λ(n) ≪ D + √m.
5. Hence, for any identity as in Theorem A with Type I level ≤ D (Vaughan with UV ≤ D, Heath-Brown, iterated
   Vaughan), the multilinear part satisfies **II(A*) = −ρm(1 + O(1/log m))**.

*Construction.* Let w ∈ C_c^∞((1/2,1)), w ≥ 0. For dyadic X_i ∈ [2D, √m/2] let
g_i(n) = Σ_{q₁q₂=n} w(q₁/X_i) w(q₂X_i/m) log q₁ log q₂ over primes q_j ∤ m, and g = s·Σ_i g_i, with s ≍ (log m)^{−3}
chosen so that Σ_n g(n) = ρ·#{p ∈ P : p > D}. Then 0 ≤ g ≪ 1/log m, and g is supported on products n ≤ m of
two primes > D. Include each n ≤ m, (n,m) = 1, in A* independently with probability

  π(n) = ρ·(1 − 1[n prime, n > D]) + g(n).

*Proof.* (4) is immediate (prime powers contribute ≪ √m). (3): a multiple of d ∈ (1, D] is neither a prime
> D nor in supp g, so π = ρ there; E|A*| = ρφ = |P| by the choice of s; Bernstein's inequality and a union
bound over (d, y) give the errors. The log-weighted d = 1 statement holds because the mass ρ|P| ≍ m/log² m is
moved by a bounded factor in n. (2): for χ ≠ χ0,
E Σ_{n∈A*} χ(n) = ρ Σ_{n≤m} χ(n) − ρ Σ_{D<p≤m} χ(p) + s Σ_i Q_{i,1}(χ) Q_{i,2}(χ).
The three terms are ≪ ρ√m log m (Pólya–Vinogradov), ≪ ρ√m log m (GRH), and
≪ (log m)^{−3}·log m·(√X_i log m)(√(m/X_i) log m) = √m (GRH, smoothed explicit formula). The fluctuation is
≪ √(|P| log m) ≪ √m for all χ simultaneously, by Bernstein and a union bound. (5) follows from (3), (4) and
the proof of Theorem A. ∎

**Numerical check** (`typeII_vaughan.py`, simplified version boosting all D-rough composites uniformly;
m ≈ 10⁶ and 4·10⁶, D = m^{1/3}): centred II(A*)/(ρm) = −1.02, Ψ(A*)/(ρm) = 0.002, max_χ|S*(χ)|/√m ≤ 1.13
(primes: 0.79–0.81), Type I discrepancies max_{d≤D} of the same size as those of A_a.

**What Theorem B rules out.** Any proof of the Type II estimate whose only inputs about the outer primes are:
(i) P ⊂ [1,m], distinct residues, exact Parseval; (ii) |P|; (iii) bounds |S(χ)| ≤ √m (log m)^C for all
χ ≠ χ0; (iv) the full Type I data of A_a to level D < √m. This holds *with the genuine coefficients on the
sifted side*. In particular:

- **Character expansion with GRH for the short polynomials cannot supply the phase cancellation.** In
  (1/φ)Σ_χ χ̄(a) S̃(χ) C_M(χ) the factor C_M(χ) is the same for P and P*, with all its GRH properties. With S̃
  replaced by S̃* the sum is ≍ −ρm/(number of active blocks) per block. So the cancellation is a property of
  the relative phases of S(χ) and C_M(χ), which nothing about C_M alone controls.
- **Iterating Vaughan, or Heath-Brown's identity,** on the sifted variable changes nothing: Theorem B(5)
  covers every such identity.
- Kloosterman sums over P enter the route only through the Type I data, so they are covered by (iv).
  (I do not claim a power saving for Σ_{x∈P*} e(h x̄/m); only (iv), which is what the route uses.)

**What it does not rule out.** P* is not a set of primes. An argument that also decomposes the outer prime p
escapes Theorem B. That is the four-variable form of §5.3.

**A deterministic variant supported on primes (heuristic).** Let w(p) = 1 − 1[a p̄ prime > z] + κ_a·1[a p̄ is a
z-rough composite], z = m^c with c small, κ_a = O(1) chosen so that Σ w(p) = |P| (possible by the upper-bound
sieve N(a) ≪ μ and the fundamental lemma). The weighted sequence has the Type I data of A_a for 1 ≤ d ≤ z
and no primes above z. If, as randomness suggests, Σ_p w(p)χ(p) ≪ √m log m, then even "the weight lives on
primes and is within a bounded factor of 1" is not enough: a proof must use joint information about p and
a p̄, which is EOS-type information. This is heuristic for the same reason as Tao's redaction.

---

## 5. Additive (Kloosterman) and four-variable formulations

### 5.1 A sufficient bilinear Kloosterman hypothesis

Open b_k = −Σ_{d|k,d≤V}μ(d) for k > V. The inner variable e = k/d then runs over the *interval*
(V/d, m/(ud)], whose additive Fourier transform has L¹ norm ≪ log m. With W(c) = Σ_{p∈P} e(c p̄/m),

  G_c(M) = −Σ_{d≤V} μ(d) Σ_{u∼M} Λ(u) Σ_{h≠0} Î_{u,d}(h) W(h a \overline{ud}) + (terms with (h,m) > 1).

**Hypothesis K-II (extra hypothesis, beyond GRH).** For some A > 4, all M ∈ [m^η, m^{1−η}] and all c ≢ 0 (mod m)
with (c,m) = 1:

  Σ_{p∈P} Σ_{u∼M} Λ(u) e(c·p̄·ū/m) ≪ m (log m)^{−A}.

**Proposition 5.1 (sketched).** GRH + K-II (with the analogous statement for (c,m) > 1, where GRH handles
small quotient moduli) implies N(a) ~ μ for all a. The steps are: separate the u-dependence of the interval
by cutting u into ranges (M, M(1+λ)], λ = (log m)^{−B}; sum |Î(h)| over h; apply K-II. The frequencies
(h,m) > 1 produce the coprimality correction to the main term.

How strong is K-II?
- Trivial bound: |P|·M. **Required saving: M (log m)^{A−1}, the full length of the short variable.**
- Mean-square size over c: (m·Σ_c δ_M(c)²)^{1/2}/√m ≍ √(mM). So K-II asks for a pointwise bound within
  m^{η/2} of the RMS when M = m^{1−η}. It is a square-root-cancellation conjecture, uniform in c.
- Known: W(c) ≪ m^{15/16+o(1)} gives K-II only for M ≤ m^{1/16−ε}, which is the Type I range again. Even the
  conjecture W(c) ≪ m^{1/2+ε} gives only M ≤ m^{1/2−ε}.
- GRH: expanding e(c x̄/m) in characters gives |sum| ≤ √m·(1/φ)Σ|S||U_M| ≤ m√M·(log m)^{O(1)}, a saving of √M.

**Lemma 5.2 (proved).** For any kernel K with |K(x,y)| = 1 on X × Y,
sup_{|α|,|β|≤1} |Σ α_x β_y K(x,y)| ≥ |X|·(|Y|/2)^{1/2}. (Khintchine: average over β ∈ {±1}^Y.)

So a bilinear estimate that treats the coefficients of *either* variable as arbitrary saves at most √(2M).
K-II needs M(log m)^{A−1}. **Bourgain–Garaev-type bounds (arbitrary coefficients, saving m^{−δ}), the
classical Cauchy–Schwarz + Weil bound (saving √M), and Vaughan applied to p inside W (which produces
arbitrary-coefficient bilinear forms) are all excluded, in every range of M.** K-II needs the
arithmetic of both p and u at once; Σ_{p,u} e(c·\overline{pu}/m) = Σ_r ν_M(r) e(c r̄/m) is a statement about the
distribution of the E₂-type counts ν_M(r) (§6), i.e. about the problem itself.

### 5.2 Why the additive route fails when both variables are rough

Recorded in `lit/02` §1.5: with rough coefficients on both u and v the L¹ norm of the additive transform is
≈ m√(UV), and the saving m^{−1/16} in W is far too small. §5.1 is the only arrangement in which the L¹ norm
is logarithmic, and it costs the full-length saving.

### 5.3 Decomposing both primes

Applying an identity to p as well gives a purely arithmetic four-variable form on the modular hyperbola
n₁n₂ ≡ a, n_i ≤ m, with coefficients among μ, Λ, 1, log. No set P remains, so Theorem B does not apply.
- Again the statement is an identity-level restatement of EOS.
- Evaluable pieces (**sketched**): (smooth × smooth) with cofactors d₁d₂ ≤ m^{1/2−ε}, by Weil for points on
  the hyperbola in a box (error m^{1/2+o(1)}); and (smooth) × (prime) to level m^{1/16} (Lemma 1.1).
- All other pieces have total length m², and Parseval over χ is again short by log powers.
- With general Siegel–Walfisz coefficients the four-variable statement is false at a single modulus
  (quadratic twist, `lit/02` §1.5). GRH removes that example, but only through the sizes of
  Σ μ(n)χ(n), Σ Λ(n)χ(n), which §3 shows are insufficient.

I found no mechanism here that §3 does not already cover.

---

## 6. The dispersion method: an a-independent sufficient condition

Define, for c ∈ G,

  ν_M(c) = Σ_{u∼M} Λ(u) 1_P(c ū), δ_M(c) = ν_M(c) − ρ Σ_{u∼M,(u,m)=1} Λ(u).

Since F(uk) = 1_P(a·\overline{uk}), G_c(M) = Σ_k b_k δ_M(a k̄) up to the cutoff uk ≤ m. Cauchy–Schwarz in k
(K = m/M, Σ_{k≤K} b_k² ≪ K) gives

  |G_c(M)|² ≪ K · Σ_{k≤K} δ_M(a k̄)².

**Requirement.** Σ_{k≤K} δ_M(a k̄)² ≤ ε² K (ρM)² / (C log² m).

The dispersion is thus *not* self-similar in the bad sense feared in `lit/02` §1.5: it leads to the
second moment of δ_M over the K classes {a k̄ : k ≤ K}, the "arc" of a.

What is known and what is needed:

- **Global variance (proved (GRH)).** Σ_{c∈G} δ_M(c)² = (1/φ)Σ_{χ≠χ0}|S|²|U_M|² ≪ m·M (log m)^{O(1)}.
  The truth is ≍ mM log M (diagonal p₁ = p₂, u₁ = u₂).
- **Typical arc value.** If the arc carries its share K/m of the variance, the left side is ≍ m log m, and
  the requirement holds with room M/(log m)^5. Numerically (m ≈ 10⁶, M from m^{0.3} to m^{0.7}, five values
  of a; `dispersion_arc.py`) the normalised arc sum equals the random prediction log M/(ρM) to within 15%,
  e.g. 0.0248 against 0.0265 at M = m^{0.6}, and decays like 1/M.
- **Trivial completion.** Bounding the arc sum by the global variance loses the factor M and leaves a
  deficit of (log m)^{O(1)}. This is the Parseval deficit of §3 again.
- **Exceptional-set form.** Let 𝔈_M(ε) = {c : |δ_M(c)| > ερM/log m}. From the variance,
  |𝔈_M(ε)| ≪ ε^{−2} (m/M) (log m)^{O(1)} (the exponent is ≥ 4 even with the true variance). The arc has m/M
  points. So L² information allows every point of the arc to be exceptional. This is the exact analogue of
  the Banks–Shparlinski O((log m)³) exceptional set, one level up: there, O(log³) possibly bad classes
  against 1 class of interest; here, K·(log m)^{O(1)} possibly bad classes against K classes of interest.
- **The barrier sequence A* fails exactly here.** For k rough, the numbers uk are boosted, so
  δ*_M(a k̄) ≈ κρM. The arc sum for A* is ≍ K(ρM)²/log m, above the requirement by only (log m)^{1+o(1)}.
  Numerically the normalised arc sum for A* is 0.2–1.1 (for K > D) against a threshold 1/log² m = 0.005.

**Hypothesis M4 (extra hypothesis, beyond GRH; a-independent).** For all M ∈ [m^η, m^{1−η}],

  Σ_{c∈G} δ_M(c)⁴ ≪ m M³ (log m)^{−12}.

**Proposition E (sketched).** GRH + M4 + a sup bound ν_{M}(c) ≪ ρM·(m/φ) on short blocks implies N(a) ~ μ for
every a.
*Sketch.* Take T = ερM/(C log m). Arc points with |δ_M| ≤ T contribute ≤ KT², as required. The number of
c ∈ G with |δ_M(c)| > T is ≤ T^{−4} Σδ⁴ ≪ ε^{−4}(m/M)(log m)^{−4}; each contributes ≤ (CρM)² by the sup bound;
the total is ≪ ε^{−4} K(ρM)²(log m)^{−4}. The cutoff uk ≤ m is handled with blocks (M, M(1+λ)].
The sup bound is a two-dimensional upper-bound sieve; its level comes from Weil for the hyperbola
u′w ≡ c′ in a box M/d₁ × m/d₂, which works for M ≥ m^{1/2+ε} (**sketched**). For M ≤ m^{1/2+ε} one uses the
trivial bound ν ≤ CM instead, which costs (log m)² in the bad-point contribution; M4 with the exponent 12
is then borderline and a slightly larger exponent is needed. I did not check the edge terms in detail.

Assessment of M4.
- Trivial bound: sup² × variance ≍ (ρM)²·mM = mM³/log² m. **M4 asks for a saving of (log m)^{10}.**
- Truth: Gaussian, ≍ m M² log² m. Numerically Σδ⁴/(mM²) ∈ [0.25, 1.5] for M = m^{0.3},…,m^{0.7} at m ≈ 10⁶.
  So there is a factor M/(log m)^{14} of room.
- M4 is a-independent, so neither the redacted set nor A* (both depend on a and alter only the arc)
  contradicts it. It is the ternary analogue of the fourth-central-moment remark in `lit/02` §2.2.
- On the character side, Σ_c δ⁴ = (1/φ)Σ_ψ |V(ψ)|² with V(ψ) = Σ_c δ_M(c)² ψ(c)
  = (1/φ)Σ_χ (SU_M)(χ)·\overline{(SU_M)(χψ)}. M4 says that the correlation of S·U_M with its shift by ψ is, in
  mean square over ψ, smaller than the unshifted second moment by √(M/m)·(log m)^{−6}. GRH bounds each
  factor in size and says nothing about this correlation. Physically V(ψ) is a ψ-twisted count of
  p₁u₁ ≡ p₂u₂ (mod m), a family of twin-prime-type equations p₁u₁ − p₂u₂ = jm.
- **I cannot prove M4 under GRH**, and I do not know a standard hypothesis (GRH for other L-functions,
  pair correlation) that implies it. It should be regarded as a restatement of the phase problem in an
  a-independent, moment form with a large margin.

---

## 7. Failure points, in one table

| Step | Statement needed | Best available (GRH) | Deficit |
|---|---|---|---|
| Type I for A_a | level m^{2η} | m^{1/16−ε}, power saving (unconditional) | none |
| II(a), genuine coefficients | o(ρm) | equivalent to EOS (Thm A) | — |
| G_c(M), b opened | Ψ_M − L(M) | circular (Prop D) | — |
| G_c(M), b opaque, Parseval | ε m/log² m | ≍ m | (log m)² |
| same, GRH sup on S or U_M | ε m/log² m | m (log m)^{3/2} | (log m)^{7/2} |
| same, GRH on Möbius polynomials | — | loses exp(c log m/log log m) | worse |
| Almost all a | all a | all but (log m)^{O(1)} (Prop 3.2) | the exceptional set |
| K-II (additive) | save M(log m)^{A−1} | save √M; general coefficients cap at √(2M) (Lemma 5.2) | √M (log m)^{A−1} |
| Dispersion, arc variance | ≤ ε²K(ρM)²/log² m | global variance only | (log m)^{O(1)}, or M4 |
| M4 | mM³/(log m)^{12} | mM³/log² m (trivial) | (log m)^{10} |

---

## 8. Verdict and what would change it

1. **(b), rigorous part.** Theorem A: the Type II estimate with arithmetic coefficients is equivalent to
   Ψ(a) = (1+o(1))ρm, and its one-sided form to N(a) ≫ μ. Proposition D: the Möbius structure of the
   coefficient is circular. §3: every phase-blind bound is short by a power of log, with Parseval the best at
   (log m)². Theorem B: no proof can rest on sizes of S(χ), orthogonality and Type I data, even with genuine
   coefficients. Lemma 5.2: no general-coefficient bilinear Kloosterman bound reaches K-II.
2. **Correction to the project's barrier picture.** For Route A the redacted-prime set is not a barrier
   (Proposition C). The operative barrier is the boosted-rough-composite sequence A*, a parity-type example
   that additionally has GRH-quality character sums.
3. **Not achieved.** No proof of EOS, no new partial result (no a ≡ p·P₂, no smaller exceptional set, no
   special moduli). GRH does not improve the level of distribution of A_a: with multiplicative characters
   the Type I remainder is itself at the Parseval threshold, since the total length is again m².
4. **What would change the verdict.** A proof, from GRH or otherwise, of any of:
   - M4, or the weaker statement |𝔈_M(ε) ∩ {a k̄ : k ≤ m/M}| ≤ ε²(m/M)(log m)^{−4} for all a;
   - K-II;
   - cancellation across χ in Σ_χ χ̄(a)S̃(χ)C_M(χ) by a factor (log m)^{2+ε}.
   All three are phase statements. M4 is the most promising target because it is a-independent, has a
   power of room, and requires only a log-power saving. It is the single place where I see the problem
   reformulated without merely restating it for the same a.

## 9. Things not checked

- Lemma 1.1 and the smoothed GRH bound are quoted from the lit notes, not re-read.
- Lemma 1.2 and the Dress–Iwaniec–Tenenbaum input are standard but written from memory.
- Propositions 5.1 and E are sketches; the edge terms from the cutoff uk ≤ m and the frequencies with
  (h,m) > 1 were not written out.
- Numerics are for prime m ≤ 4·10⁶ with U = V = m^{1/6}, far from the asymptotic regime U = V = m^η, η < 1/32.
  They test the identities and the random-model sizes, nothing more.
