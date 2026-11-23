# Round 1, combinatorial / ergodic persona

Written 2026-11-22. Standing hypothesis: GRH for Dirichlet L-functions. Anything more is flagged as an extra hypothesis.
Scripts and outputs: `compute/brainstorm/combinatorial/` (`hyperbola_rank.py`, `hyperbola_graph.py`, `rigidity_scan.py`,
`coset_certificate.py`, `liouville_hyperbola.py`, `out_*.txt`).

**Status tags.** *proved* = complete argument written here. *sketched* = believed complete, steps only indicated.
*heuristic* = not a proof. *computed* = exact output of a script. [UNVERIFIED] / [RECALLED] = not checked against a source.

Notation as in `00-setup.md`: G = (Z/mZ)^*, φ = φ(m), L = log m, P = {p ≤ m prime, p ∤ m}, π = |P|, λ_m = π²/φ (the mean of N; written λ_m
here because λ(n) is the Liouville function), S(χ) = Σ_{p∈P} χ(p), N(a) = #{(p,q) ∈ P² : pq ≡ a}, N⁻(a) = #{(p,q) : p ≡ aq}.
New notation: U = {1 ≤ n < m : (n,m) = 1} and **ι_a : U → U, ι_a(n) = [a n̄]_m**, the hyperbola involution. EOS at a says ι_a(P) ∩ P ≠ ∅.

---

## 0. Summary

**Verdict.** No route to EOS. Three routes were examined; one produced new verified structure, one died with a precise
autopsy, one reduces to a statement already on record.

| Route | What it is | Outcome | Chance of EOS |
|---|---|---|---|
| **R1 Symmetry space of ι_a** (best; §1) | Replace "is there a prime pair" by "which completely multiplicative functions f satisfy f∘ι_a = f". Linear algebra over F_2 and Q on the exponent matrix of the numbers n·ι_a(n) = a₀ + km. | An exact structure theorem for the kernel (proved), the implication *dyadic EOS at a ⇒ a non-character multiplicative symmetry exists* (proved), and a rigidity statement (computed: no exception for prime 113 ≤ m < 620, all classes; sampled to m = 30011). It is a reformulation plus a parity-only test problem. It contains no mechanism for producing the symmetry. | ≤ 1% |
| **R2 Entropy decrement on the hyperbola** (§2) | Tao's dilation trick λ(n)λ(n+1) = λ(pn)λ(pn+p), transplanted to (n, ι_a(n)). | Dead. The exact dilation identity exists (proved), but the dilations that fix a class a have height > √m (proved), so there is no stationary multi-scale system at fixed a. The scale budget fails as well (heuristic). | < 0.5% |
| **R3 Coset certificate** (§3) | N(aH) ≥ 2\|H\|λ_m − Σ_{h∈H} N⁻(h) for every subgroup H. | Proved inequality; computed threshold \|H\| ≈ φ/π ≈ log m. Proving it needs a prime-pair upper bound with constant < 2, which is route C §6.1 in group language. Not new in substance. | 0 (coset statements are deletion-stable); about 2% for a GRH-only improvement of \|H\| ≥ C log² m |

**What I would hand to round 2.**
1. The *weak Liouville problem* (§1.2): show under GRH that ι_a does not preserve λ, i.e. some n ≤ m has λ(n) ≠ λ([a n̄]_m).
   It has no deletion barrier, no A\*, no log-power deficit (the Parseval bound fails by exactly the equality case), and it is
   still open as far as I can tell. If the team cannot do this, it cannot do EOS.
2. The *rigidity conjecture* (§1.5), which would settle item 1 and is numerically clean.
3. The observation that every root-free component of the large-prime graph Γ_a is a certificate of rank deficiency, and that
   dyadic EOS pairs are exactly the size-2 ones on primes > m/2 (§1.4).

---

## 1. Route R1 (best route): the symmetry space of the hyperbola involution

### 1.1 Mechanism

A prime p > m/2 has no multiple other than itself in [1, m]. So in any linear system whose unknowns are indexed by primes and whose
equations are indexed by integers n ≤ m, the column of p is supported on the single equation n = p. This is the only place in this
note where "p is prime, so it has no factors" is used in a way that is not a sieve, and it is the whole mechanism.

For n ∈ U write M(n) = n·ι_a(n) = a₀ + k_n m, where a₀ is the least positive residue of a. Let P_m = P be the set of columns and

  𝐌_a = ( v_p(M(n)) )_{n ∈ U/ι_a, p ∈ P}   (an integer matrix with ≈ φ/2 rows and π columns).

All prime factors of n and of ι_a(n) are ≤ m and coprime to m, so the matrix records the full factorisation of every M(n).

**Lemma K0 (dictionary, proved).**
- x ∈ ker_{F_2} 𝐌_a ⟺ the completely multiplicative f : U → {±1} with f(p) = (−1)^{x_p} satisfies f(n) = f(ι_a(n)) for all n ∈ U.
- x ∈ ker_Q 𝐌_a ⟺ the completely additive g with g(p) = x_p satisfies g(n) + g(ι_a(n)) = 0 for all n ∈ U.

*Proof.* f(n)f(ι_a(n)) = f(M(n)) = (−1)^{⟨v(M(n)), x⟩}. Same for g. ∎

**Lemma K1 (characters, proved).** If χ is a real character mod m with χ(a) = 1 then χ|_U is in the F_2-kernel. If χ(a) = −1 then χ∘ι_a = −χ.
*Proof.* χ(n)χ(ι_a(n)) = χ(a). ∎

**Lemma K2 (Fourier form; equality case of Parseval, proved).** For real f on U with |f| = 1 put S_f(χ) = Σ_{n∈U} f(n)χ(n) and
C_f(a) = Σ_{n∈U} f(n) f(ι_a(n)) = (1/φ) Σ_χ χ̄(a) S_f(χ)². Then for ε = ±1:

  f∘ι_a = εf ⟺ S_f(χ) = ε χ(a) \overline{S_f(χ)} for all χ ⟺ χ̄(a) S_f(χ)² = ε|S_f(χ)|² for all χ ⟺ C_f(a) = εφ.

*Proof.* Σ_n f(ι_a n)χ(n) = Σ_y f(y)χ(a ȳ) = χ(a) S_f(χ̄) = χ(a)\overline{S_f(χ)}. The last equivalence is (1/φ)Σ_χ|S_f|² = φ. ∎

So a multiplicative symmetry of ι_a is exactly an extremiser of the Parseval bound |C_f(a)| ≤ φ. The phases of S_f(χ)² are then
*equal* to χ(a), which is the adversarial alignment of `lit/03` §0.2 realised at 100% strength.

**Lemma K3 (antisymmetric case, proved, trivial).** If f∘ι_a = −f then Σ_{n∈U} f(n) = 0, because ι_a is a permutation.
In particular, whenever Σ_{n∈U} λ(n) ≠ 0 there is n with λ(n) = λ(ι_a(n)).

**Lemma K4 (wrap-around multiplicativity, proved).** Let f be completely multiplicative with values ±1 and f∘ι_a = f.
Then for every n ∈ U and every divisor d of ι_a(n): f([nd]_m) = f(n)f(d).
*Proof.* [nd]_m · (ι_a(n)/d) ≡ a and ι_a(n)/d ∈ U, so ι_a([nd]_m) = ι_a(n)/d. Hence f([nd]_m) = f(ι_a(n)/d) = f(ι_a(n))f(d) = f(n)f(d). ∎

Lemma K4 says a symmetric f is multiplicative *modulo m* (not only on integers) along the pairs (n, d) with d | ι_a(n). A real
character is multiplicative mod m along all pairs. Rigidity (§1.5) is the statement that the first forces the second on the small primes.

### 1.2 The weak Liouville problem

**Problem WL.** For all large m and all a ∈ G, show that there is n ∈ U with λ(n) ≠ λ(ι_a(n)). Equivalently C_λ(a) < φ.
(The other sign pattern is Lemma K3.)

Why it is the right minimal test (all *proved* as statements about inputs unless tagged):
- λ(n)λ(ι_a(n)) = λ(a₀ + k_n m). So WL asks for one integer N ≡ a (mod m), N ≤ m², with a divisor in [N/m, m] and Ω(N) odd. If
  λ(a₀) = −1, take n = 1. Otherwise it is a pure parity question in a single progression at level 1/2.
- **No log deficit.** Parseval gives |C_λ(a)| ≤ φ and the claim is C_λ(a) ≠ φ. The gap to Parseval is the equality case, not a power of log.
- **No deletion barrier, no A\*, no Type I ambiguity.** There is no set to delete from. λ is canonical.
- **The random-pairing barrier still applies to size-only arguments.** A uniformly random ι_a-invariant sign function has
  GRH-quality character sums and C = φ (heuristic for the sizes; the invariance is exact). So any proof must use multiplicativity of λ.
- **Multiplicativity alone is not enough.** The numbers M(n) all lie in the class a, and no two elements of a class below m² are
  related by a factor ≡ 1 (mod m). So no formal identity between rows gives a contradiction; this is why the kernel of 𝐌_a is the right object.
- **Under GRH I could not prove WL.** Every decomposition I tried (Σ_p λ(ι_a(p)); n = 2n′; dilation by s, §2; variance of λ on the
  segments c, c+m, …, c+(H−1)m over the density-1/H set {c : ι_a(c) < m/H}) lands exactly on the Parseval equality case. The last one
  is instructive: the hypothesis λ∘ι_a = λ forces λ(c + jm) = λ(c) for every j < H such that c + jm has a divisor in (j, H], on a
  set of c of density 1/H. Cauchy–Schwarz against the (expected) variance H of segment sums gives a contradiction iff the number
  of forced coincidences exceeds H, and it is at most H. Whether WL is in the literature is [UNVERIFIED].

**Computed** (`liouville_hyperbola.py`, prime m, all a by FFT): max_a |C_λ(a)|/φ = 0.108 (m = 10007), 0.049 (100003), 0.019 (1000003).
The RMS of C_λ(a) is 3.1√φ, 4.0√φ, 4.0√φ. This matches (12/π²·log m)^{1/2}√φ, the contribution of the integer solutions of n₁n₂ = n₃n₄
(heuristic). So the fourth moment of S_λ has the same single-log excess as the d₄ toy problem of `D` §4.3.

### 1.3 Structure theorem for the kernel

Call a prime r ∈ P **large** if r² > m, **small** otherwise. Every n ∈ U has at most one large prime factor, with multiplicity one;
call it ℓ(n) (or ∅ if there is none). Define the **large-prime graph Γ_a**: vertices are the large primes and a root ∅; for each n ∈ U
with ℓ(n) ≠ ℓ(ι_a(n)) join ℓ(n) and ℓ(ι_a(n)). A component is *root-free* if it does not contain ∅. Let
W_a ⊂ F_2^{small primes} be the projection of ker_{F_2} 𝐌_a to the small coordinates.

**Theorem K5 (proved).**
1. ker_{F_2} 𝐌_a ∩ {x_small = 0} has basis {1_C : C a root-free component of Γ_a}. Hence
   **corank_{F_2} 𝐌_a = dim W_a + c₂(Γ_a)**, where c₂ is the number of root-free components.
2. Over Q the same holds with c₂ replaced by the number c_Q of root-free components that are bipartite and contain no r with
   ℓ(n) = ℓ(ι_a(n)) = r for some n; the kernel vector is ±1 on the two sides.
3. W_a contains the restrictions to small primes of the real characters χ with χ(a) = 1 (dimension d′_a).

*Proof.* With x_small = 0 the equation of row n reads x_{ℓ(n)} + x_{ℓ(ι_a n)} = 0, with x_∅ := 0. Over F_2 this says x is constant on
components and zero on the root component. Over Q it says x changes sign along edges and 2x_r = 0 on a doubled row. Rank–nullity for
the projection gives the formula. (3) is Lemma K1. ∎

**Corollary K6 (dyadic EOS ⇒ rank deficiency, proved).** Let r ≠ r′ be primes in (m/2, m], coprime to m, with rr′ ≡ a (mod m).
Then {r, r′} is a root-free component of Γ_a. Consequently:
- corank_{F_2} 𝐌_a ≥ dim W_a + #{unordered such pairs} and corank_Q 𝐌_a ≥ #{unordered such pairs};
- the function f = −1 on {r, r′}, +1 on all other primes, is completely multiplicative, satisfies f∘ι_a = f, and is not the
  restriction of a character once φ > 4;
- g = e_r − e_{r′} is a completely additive function with g(n) + g(ι_a(n)) = 0 on U.

*Proof.* The only multiple of r in [1, m] is r, so the only row meeting column r is n = r, and ι_a(r) = r′. Same for r′. ∎

So: **if a ≡ pq with primes m/2 < p < q ≤ m, then the relation matrix of the hyperbola is rank-deficient over Q, and ι_a has a
multiplicative symmetry that is not a character.** In Fourier terms (Lemma K2) the prime pair is detected by a function f with
χ̄(a)S_f(χ)² ≥ 0 for every χ.

### 1.4 What the root-free components are (computed)

`rigidity_scan.py`, `hyperbola_graph.py`. "pairs" counts unordered {r, ι_a(r)} with both prime and > m/2 (r = ι_a(r) allowed over F_2).

| m (prime) | classes | mean c₂ | mean pairs | mean non-pair components | min over classes of c₂ |
|---|---|---|---|---|---|
| 1009 | all 1008 | 3.32 | 2.61 | 0.71 | 0 |
| 2003 | all 2002 | 5.52 | 4.59 | 0.93 | 0 |
| 5003 | 40 sampled | 10.97 | 9.28 | 1.70 | 4 |
| 10007 | 40 sampled | 18.32 | 15.10 | 3.23 | 12 |
| 30011 | 40 sampled | 43.00 | 36.00 | 7.00 | 30 |

- Between 79% and 84% of root-free components are dyadic EOS pairs; the ratio is stable from 10³ to 3·10⁴.
- The others are small clusters of large primes linked through cofactors: every root-free component yields large primes r, r′ and
  integers j, j′ < √m with (jr)(j′r′) ≡ a and jr, j′r′ ≤ m (proved, from the definition of an edge). So "Γ_a has a root-free component"
  is a relaxation of dyadic EOS to *a ≡ (jp)(j′q) with j, j′ < √m such that the component closes up*. I did not classify them.
- For composite m with small prime factors there are many more (m = 30030: mean c₂ = 786 against 193.5 pairs), because a prime
  r ≤ m/2 is already pendant when all of 2r, 3r, … ≤ m share a factor with m.
- For m ≤ 2003 there are classes with c₂ = 0, i.e. no symmetry beyond characters. These are classes with no dyadic pair, which is
  consistent with `RESULTS.md` (the dyadic count has mean ≈ λ_m/4 and is Poisson-like at this size).

### 1.5 Rigidity (computed; conjecture)

**Rigidity conjecture.** For all large m and all a ∈ G: W_a is exactly the space of real characters with χ(a) = 1, restricted to
small primes. Over Q: the projection of ker_Q 𝐌_a to the small primes is 0. Equivalently,

  corank_{F_2} 𝐌_a = d′_a + c₂(Γ_a),  corank_Q 𝐌_a = c_Q(Γ_a).

In words: **the only completely multiplicative symmetries of the modular hyperbola are real characters, up to local modifications on
root-free clusters of large primes.**

**Computed.** exc₂ := corank_{F_2} − d′_a − c₂ ≥ 0 and exc_Q := corank_Q − c_Q ≥ 0 (both ≥ 0 by Theorem K5; the scripts report zero
violations in 20 594 pairs (m, a)).
- *Prime m, every class.* For all primes 5 ≤ m < 620: the last prime with exc₂ > 0 in some class is m = 109, and the last with
  exc_Q > 0 is m = 97 (`out_prime_exceptions.txt`). For m = 809, 1009, 1511, 2003 (all classes, both fields): no excess.
- *Prime m, sampled.* m = 3001, 5003, 10007, 20011, 30011, 40–60 classes each, F_2 only: no excess.
- *Prime powers.* 512, 1024, 2048, 729, 2187, 961, 1849 (all classes, both fields), 4096, 6561, 10201 (60 classes): no excess. m = 256: 12 classes with excess.
- *Composite m with several small prime factors* fail at small size and recover: 2310 has F_2-excess in 444 of 480 classes (max 6),
  4620 in 8 of 60, while 9240, 6006, 10010, 30030 (60 classes each) have none. The cause is the shortage of small primes coprime to m
  and of smooth rows (heuristic).

**Consequence (proved, conditional on rigidity for the pair (m, a)).** WL holds at (m, a) as soon as no real character χ mod m has
χ(p) = −1 for every small prime p ∤ m. For prime m this is the statement that the least prime quadratic residue is ≤ √m, which is
known for large m (Linnik–Vinogradov, ≪ m^{1/4+ε}) [RECALLED] and trivial under GRH.
*Proof.* λ corresponds to x = (1, …, 1). If it is in the kernel, its small part is in W_a, hence equals a character on small primes. ∎

**Why rigidity is not easy (sketched).** The constraints on x_small come from the *smooth rows*, those n with n and ι_a(n) both
√m-smooth. The expected number is ρ(2)²φ/2 ≈ 0.047φ, far more than the π(√m) unknowns, which is why the numerics are clean. But
even the existence of smooth rows for every a is the problem a ≡ n₁n₂ with n_i ≤ m smooth: a product of ≥ 4 free variables of
total length m², which is the d₄-type toy of `D` §4.3 and sits at the same Parseval threshold (logs only, no parity). So:

  **rigidity ⇐ (a quantitative d₄-type toy) + (an index-calculus full-rank statement)**, neither of which I can prove.

Lemma K4 is the only handle I found on the second: it upgrades f to a partial homomorphism of G on the set
{(n, d) : d | ι_a(n)}, which for a fixed small prime d = s has density ≈ 2/s − 1/s² in n (the no-wrap set [n] < m/s together with
{n : s | ι_a(n)}). A 99%-to-100% argument would need density close to 1.

### 1.6 Barrier checklist for R1

The route is a reformulation, so "pass" means "the object is not fooled", not "the barrier is beaten".

1. **Random pairing-avoiding set.** *Pass, vacuously.* No subset of G enters. 𝐌_a is built from the factorisations of the integers
   a₀ + km. A random set has no such matrix. For size-only arguments about f the barrier applies in full (§1.2).
2. **Deletion of 1/log m of the primes.** *Pass for the statement, and the identity is fragile in the right way.* Deleting a prime r
   from the column set removes the kernel vector 1_{{r,r′}}. corank is an exact invariant that changes by exactly one per deleted pair.
   There is no approximate version of rank.
3. **Parity.** *Not beaten; isolated.* WL and rigidity are parity statements with every other difficulty removed. Corollary K6 shows
   where one prime differs from two: a row of weight 2 on pendant columns creates a kernel vector, a row of weight 3 does not.
4. **A\*.** *Not applicable to the reformulation; fatal to any sieve attempt at proving rank deficiency.* A\* lives on the sifted
   sequence. Here both coordinates of the row are factored completely, so Type I data are not the input.
5. **Proposition L / variance wall.** *Not beaten.* By Lemma K2 a symmetry is the equality case of Parseval. Any attempt to prove or
   refute a symmetry by bounding |S_f(χ)| is subject to the wall. The route offers no way around it; it offers a problem (WL) in
   which the wall is the only obstruction.
6. **Theorem G.** *Pass.* For the quotient map κ_a(n) = [an]_m the same construction gives a matrix whose pendant pairs are the
   solutions of r′ ≡ ar. At a = −1, m odd, m − 2 composite, there are none. The object computes N⁻ correctly and is different from 𝐌_a.

D's four requirements: joint (P, a) information (yes: the rows are the pairs (n, ι_a(n))); exact identity fragile under deletion (yes:
rank); more than Type I plus sizes (yes: full factorisations); separates one prime from two (yes, K6). **What is missing is any
mechanism that produces a kernel vector without exhibiting the prime pair.** I looked for one in three places and found nothing:
- counting: #{f : f∘ι_a = f} = 2^{corank}, and for a Rademacher random multiplicative f one has
  E_f[C_f(a)^k] = #{(n₁,…,n_k) ∈ U^k : Π n_i ι_a(n_i) is a square} (proved), but the event C_f = φ has probability 2^{−rank} and is
  visible only in moments of order k ≫ φ;
- Gram determinant: EOS-type deficiency ⟺ det(𝐌_aᵀ𝐌_a) = 0, but the null vector is supported on two columns whose Gram entries are a 2×2 block of ones;
- averaging over a: {a : f∘ι_a = f} is empty or a coset of the period group of n ↦ f([n]_m) (proved), which is trivial for the pair functions.

**Extra hypotheses.** None for the proved statements. The rigidity conjecture is new and is not a consequence of GRH as far as I can see.

**First concrete lemma.** WL under GRH for prime m and a = 1: some n < m has λ(n) ≠ λ(n̄). **First experiment.** Done (§1.4, §1.5).

**Probability.** EOS by this route: ≤ 1%. WL under GRH by any method within the project's reach: about 5%. Rigidity proved for all
large prime m: about 2%. Usefulness as a calibration problem for other personas' mechanisms: high, because a mechanism that cannot
decide WL cannot prove EOS.

---

## 2. Route R2: entropy decrement / dilation covariance — dead, with autopsy

### 2.1 Mechanism

Tao's two-point Chowla argument uses λ(n)λ(n+1) = λ(pn)λ(pn+p), then shows by an entropy pigeonhole over scales that the event
p | n′ is independent of the sign pattern, then applies a bilinear estimate. The analogue here:

**Lemma E1 (dilation identity, proved).** For a prime s ∤ m,

  C_λ(a) = −Σ_{n ≤ m} Σ_{N ≤ sm, nN ≡ sa (m)} λ(n)λ(N) 1_{s | N}.

*Proof.* N ≤ sm, s | N, nN ≡ sa force N = s·ι_a(n). ∎

Put D_s(a) = −(1/s) Σ_{n ≤ m} Σ_{N ≤ sm, nN ≡ sa} λ(n)λ(N), the same sum with 1_{s|N} replaced by its density.

**Proposition E2 (GRH; sketched).** For H ≥ m^{5ε}, the average of D_s(a) over primes s ∼ H is ≪ m^{1−ε/2}, uniformly in a.
*Sketch.* The average is (1/φ)Σ_χ χ̄(a) S_λ(χ; m)·T(χ) with T(χ) = π(H)^{−1}Σ_s χ̄(s) s^{−1} S_λ(χ; sm). GRH gives
|S_λ(χ; x)| ≪ x^{1/2}(mx)^{ε}, so |T(χ)| ≪ (Hm)^{1/2+ε}/H. Parseval on S_λ(χ; m) gives the bound m^{1+2ε}H^{−1/2+ε}. ∎

So "Chowla on the hyperbola" would follow from the **independence statement**: C_λ(a) − D_s(a) is small on average over s ∼ H.

### 2.2 Why it fails

1. **The independence statement is the original problem (proved).** Expanding 1_{s|N} − 1/s in characters mod s turns the difference
   into sums of S_λ(χψ; sm) over characters of conductor ms and length sm. Parseval is again exact and tight. Lemma E1 is an identity,
   so no information was created.
2. **No class-preserving small dilations (proved).** (x, y) ↦ (sx, ty) maps the hyperbola xy ≡ a to xy ≡ sta. It preserves the class
   iff st ≡ 1 (mod m), hence st ≥ m + 1 and max(s, t) > √m. Tao's argument needs, at every scale H in a long range, ≫ H/log H primes
   p ∼ H acting on one stationary process. At fixed a the only dilations available have height > √m, where divisibility by s is a
   condition of modulus ≍ length. Using small s moves the class: the conclusion concerns the classes a s̄, s ∼ H.
3. **No stationarity (proved as a statement about the construction).** The natural process is j ↦ λ(y + jm) with the frozen factor
   λ([b ȳ]_m). Dilation by s sends the frozen factor of class b to that of class b s̄, so the "sign pattern" variable is different for
   every s. The joint pattern over all s ∼ H has ≍ H²/log H bits and the entropy budget is H.
4. **Scale budget (heuristic).** Entropy decrement gains ε/log H per scale, so it needs scales up to exp exp(c/ε). To reach the box
   [1, m]² from a box where GRH applies one must cross a factor J in one variable: J ≍ (log m)³ for primes (route C) and J = m^{o(1)}
   for λ. Crossing in one step needs H ≥ J with window length comparable to the whole range, so there is no room for stationarity.
   Crossing in k ≍ log J / log H steps needs ε ≪ 1/k, hence scales beyond exp exp(log m), which exceed m.
5. **For primes there is nothing to dilate.** Λ(sn) = 0. The identity exists only for completely multiplicative weights, so the output
   could at best be C_λ(a) = o(m), not EOS (parity is not crossed in the prime-producing direction).

### 2.3 Barrier checklist for R2

1. Random pairing set: *not beaten.* A random ι_a-invariant sign function is not multiplicative, so Lemma E1 does not apply to it and
   nothing false is proved. But the only property of λ that the entropy step would use is multiplicativity at s, and item 1 of §2.2
   shows that this alone returns the original problem.
2. Deletion: *not applicable* (λ target); for primes the route does not start.
3. Parity: *fails* for EOS (item 5).
4. A\*: *not applicable.*
5. Proposition L: *fails.* The independence statement is at the Parseval equality case.
6. Theorem G: *pass in principle.* Lemma E1 holds for [an]_m as well, and the λ-analogue of the conjugate problem (Σλ(n)λ(m−n)) is
   expected to cancel, so nothing false would be proved.

**What survives.** Only an orbit-averaged, logarithmically box-averaged statement about the classes {a s̄ : s ∼ H}. For primes the
exceptional-set bound O(log³ m) of route C already gives more. I did not establish any such theorem.
**Extra hypotheses.** None stated; the route does not reach a hypothesis worth naming.
**First lemma.** Lemma E1 and item 2, both proved here. **Probability of EOS:** < 0.5%.

---

## 3. Route R3: the coset certificate (Matomäki–Radziwiłł-style restriction of the family)

### 3.1 Mechanism

Matomäki–Radziwiłł gain over Parseval because the family (|t| ≤ X/h) is shorter than the Dirichlet polynomial. In G the family can be
shortened only by passing to H^⊥ for a subgroup H, which averages a over the coset aH.

**Proposition M1 (proved).** For every subgroup H ≤ G and every a ∈ G, with T(H) := Σ_{h∈H} N⁻(h) = Σ_{cosets c of H} |P ∩ c|²:

  N(aH) := Σ_{h∈H} N(ah) ≥ 2|H|λ_m − T(H).

*Proof.* N(aH) = (|H|/φ)Σ_{χ∈H^⊥} χ̄(a)S(χ)² ≥ (|H|/φ)(2π² − Σ_{χ∈H^⊥}|S(χ)|²), and (|H|/φ)Σ_{χ∈H^⊥}|S(χ)|² = T(H). ∎

So the symmetric data certify that *every* coset of H meets P·P as soon as the mean of N⁻ over H is below 2λ_m. Since N⁻(1) = π, the
heuristic threshold is |H| > φ/π ≈ log m, against |H| ≥ C log² m from GRH (`B` §5.2).

**Computed** (`coset_certificate.py`, prime m with smooth m − 1, all subgroups):

| m | φ/π | smallest \|H\| with certificate | largest \|H\| without | mean_{h≠1} N⁻(h)/λ_m at \|H\| = 20, 22 (even order) |
|---|---|---|---|---|
| 110881 | 10.54 | 10 | 9 | 0.95 |
| 1108801 | 12.84 | 12 | 11 | 0.95 |
| 4324321 | 14.21 | 14 | 13 | 0.95 |

Two details. (i) Subgroups of even order contain −1, and N⁻(−1) ∈ {0, 2} (Theorem G), so their off-diagonal mean is below λ_m (0.88–0.95)
and the certificate starts slightly earlier; subgroups of odd order have mean 1.00 ± 0.02. Theorem G *helps* here. (ii) The threshold is
exactly where the diagonal π equals |H|λ_m; there is no hidden loss.

### 3.2 What a proof needs

T(H) < 2|H|λ_m ⟺ the off-diagonal prime-pair count Σ_{h∈H∖1} N⁻(h) is below (2 − φ/(π|H|))·(|H| − 1)λ_m·(1 + o(1)). An upper-bound sieve gives this with a
constant ≥ 2 (parity) in place of < 2. For m = m₁m₂ and H = ker(G → (Z/m₁)^*), T(H) = Σ_{c mod m₁} π(m; m₁, c)², the variance of
primes up to x = m in progressions to the single modulus m₁ = x/m₂. This is route C §6.1 ("prime pairs p, p + km₁ on average over
k ≤ m₂ with constant < 2") and the Goldston–Montgomery / Hooley circle of problems. Not new in substance.

**Extra hypothesis (flagged, beyond GRH).** *Hypothesis V*: for q ≤ x with x/q ≥ (1 + ε) log x,
Σ_{c mod q}^* (π(x; q, c) − π(x)/φ(q))² ≤ (1 − ε/2)·π(x)²/φ(q). It is implied by Hooley's conjectured asymptotic x log q for the
variance at a single modulus [RECALLED], which is known only on average over q or under Hardy–Littlewood with a uniform error.
**Conditional statement (proved from M1).** GRH is not needed: Hypothesis V for (x, q) = (m₁m₂, m₁) implies that every class mod m₁
is pq with p, q ≤ m₁m₂, i.e. EOS for the modulus m₁ with range (1 + ε) m₁ log m₁ in place of Theorem S's K φ log² m.

### 3.3 Barrier checklist for R3

1. Random pairing set: *defeated for EOS.* A set avoiding one class a still meets every coset aH with |H| ≥ 2.
2. Deletion: *defeated for EOS.* Removing R_a changes N(aH) by O(N(a)); coset statements are stable. This is why the route cannot reach a single class.
3. Parity: *defeated*, in the precise form "constant < 2".
4. A\*: *not applicable* (no sieve on A_a).
5. Proposition L: *consistent.* The certificate lives at |H| ≈ log m, the coset analogue of X ≈ φ log m; Proposition L's model has V° equal to the main term, i.e. T(H) = 2|H|λ_m.
6. Theorem G: *pass.* The inequality is symmetric and the conclusion is true for (P, P⁻¹) as well (it is a coset statement).

**First lemma.** M1 (proved). **First experiment.** Done. **Probability.** A GRH-only proof of the certificate for |H| = o(log² m): about 2%.
EOS: 0.

---

## 4. Ideas considered and dropped (one line each)

- *Transference (Green–Tao) on the hyperbola with a Selberg majorant ν⊗ν.* The majorant is pseudorandom on {xy ≡ a} to level
  m^{1/2−ε} (Weil), but the dense model problem "A×A meets the hyperbola" is false for dense A. Barriers 1 and 2. Dead.
- *Moments in a.* Σ_a E(a)⁴ < λ_m⁴ gives EOS and needs only a log-power saving over GRH-trivial, but one bad class already contributes λ_m⁴; `B` §4.6 has this.
- *Higher convolutions.* N∗N = N₄ is flat to relative precision L⁵/m under GRH, but one bad class moves N∗N by O(λ_m) out of λ_m²φ. No information.
- *Large values of S(χ) (Halász–Montgomery with a sieve majorant).* The off-diagonal terms are complete sums of size √m, so the
  method is vacuous at length = conductor.
- *Ternary with a tiny third prime s ≤ H.* The L^∞·L² split needs π(H) ≫ L², and the true energy would not help: Cauchy–Schwarz with
  Σ|S|⁴ = 2π²φ gives the same threshold.
- *Square moduli, fibre sums (`D` §2).* Fibre Fourier coefficients are averages of S(χ) over r characters; the slice Σ_b|Û_b(ξ a₀ b̄)|²
  is a diagonal slice of an exact Parseval identity. Same wall.

---

## 5. What was actually established

| Item | Status |
|---|---|
| Lemmas K0–K4, Theorem K5, Corollary K6 (dyadic EOS at a ⇒ rank deficiency of 𝐌_a over Q and a non-character multiplicative symmetry of ι_a) | proved |
| Lemma K2: symmetries are the equality case of Parseval for C_f(a) | proved |
| Rigidity (kernel = characters ⊕ root-free components): every class for all primes 113 ≤ m < 620 and m = 809, 1009, 1511, 2003; sampled classes to m = 30011; prime powers; composites ≥ 6006 sampled | computed |
| 79–84% of root-free components are dyadic EOS pairs (prime m, 10³–3·10⁴) | computed |
| Rigidity ⇒ WL (given least prime quadratic residue ≤ √m) | proved (conditional) |
| WL under GRH | not obtained; reduced to the Parseval equality case in four ways |
| max_a \|C_λ(a)\|/φ ≤ 0.019 at m = 10⁶+3; RMS ≈ (12/π²·log m)^{1/2}√φ | computed; the RMS formula is heuristic |
| Lemma E1, class-stabiliser obstruction for dilations | proved |
| Proposition E2 | sketched (GRH) |
| Scale-budget obstruction for entropy decrement | heuristic |
| Proposition M1 and the certificate threshold \|H\| ≈ φ/π | proved; computed |
| Hypothesis V ⇒ EOS for m₁ at range (1+ε)m₁ log m₁ | proved from M1; Hypothesis V is beyond GRH |

## 6. Not checked

- Whether WL, or the rank of relation matrices of this shape, appears in the literature.
- The Linnik–Vinogradov bound for the least prime quadratic residue is recalled, not re-read; for composite m the needed statement
  (no real character equal to −1 on all small primes) was not examined.
- The non-pair root-free components were counted, not classified.
- Rigidity over Q was computed modulo the prime 2147483629, which can only overestimate the corank; since the reported excess is 0 this does not affect the conclusion.
- Rigidity for m > 30011, and for every class when m > 2003, was not run.
- Proposition E2's exponent bookkeeping and the form of Hooley's conjecture used in Hypothesis V.
- Probabilities are opinions.
