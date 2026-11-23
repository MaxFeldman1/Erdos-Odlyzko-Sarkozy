# Route D: new connections, stress-tested against the barriers

Written 2026-11-22. Standing hypothesis: GRH for Dirichlet L-functions; anything more is flagged.
Scripts and outputs: `compute/routeD/` (`conj_barrier.py`, `square_fibers.py`, `ff2_eos.py`, `out_*.txt`).

**Status tags.** *proved* = complete argument written here. *sketched* = believed complete, steps only indicated.
*heuristic* = not a proof. *computed* = exact output of a script. [UNVERIFIED] = recalled or not checked.
Results quoted from `notes/lit/` and routes A–C keep the status they have there; I did not re-read sources.

Notation as in `00-setup.md`: G = (Z/mZ)^*, φ = φ(m), L = log m, P = {p ≤ m prime, p ∤ m},
S(χ) = Σ_{p∈P} χ(p), N(a) = #{(p,q) ∈ P² : pq ≡ a}, λ = |P|²/φ.

---

## 0. Summary

**Verdict.** I found no route to EOS under GRH. What this note adds:

| # | Item | Status |
|---|---|---|
| Thm G (§1) | **Conjugation barrier.** For odd m with m − 2 composite, −1 is not of the form p·q^{-1} (mod m) with p, q ∈ P. The pair (P, P^{-1}) has the same \|S(χ)\| at every truncation, the same exact Parseval identity, the same energies and the same GRH bounds as (P, P). So no argument that is blind to replacing S(χ)² by \|S(χ)\|² can prove EOS. Unconditional, and the set is the primes themselves. | proved |
| Cor G1 | Exact size bias: Σ_{χ odd} \|S(χ)\|² = (φ/2)(\|P\| − N⁻(−1)). For such m the odd characters carry mean \|S\|² = \|P\| exactly and the even non-principal ones \|P\|(1 − 2\|P\|/φ + …). A "conspiracy" of the critical relative strength ≍ 1/log m between \|S(χ)\|² and χ(−1) exists for the true primes. | proved; computed |
| Cor G2 | Any proof of EOS must use, at least implicitly, the distribution of a·p̄ mod m in residue classes to small moduli coprime to m (already d = 2), i.e. Kloosterman sums over primes. The threshold X = m is sharp for the quotient problem: at range (1+ε)m the obstruction disappears. | proved (as a statement about inputs) |
| Prop P (§2) | **Linearisation.** If h² \| m, then on each fibre p ≡ b, q ≡ c (mod m/h) the congruence pq ≡ a (mod m) is a *linear* congruence mod h in the top digits. EOS for such m is a sum over φ(m/h) fibres of binary Goldbach-type problems in Z/h. | proved; computed |
| §2.3 | A single fibre is not enough: single-fibre counts vanish for structured (c, e), concentrated at c ∈ {±1, ±3, ±1/3}. These are Thm G-type local–archimedean obstructions. | computed; explanation heuristic |
| §3 | **F_2[t] test bed.** For f primitive of degree n ≤ 23 over F_2, the EOS analogue (irreducibles of degree exactly n) holds for all sampled f with n ≥ 11, and the statistics match the integers (for n ≥ 17: minimum 0.84–0.95 of the random depth, energy excess 0.95–0.97 of random). Nothing distinguishes q = 2 from large q numerically. | computed |
| Rem 5.1 | Under GRH every a is p·q·s with p, q ≤ m and s ≪ (log m)³ log log m (pigeonhole on the exceptional set). Lit note 01 records (log m)⁴ from Banks–Shparlinski. | proved from Thm E of route C; novelty [UNVERIFIED] |
| §4 | Twelve candidate routes with barrier checklists. Nine are dead; three are live only as sub-problems (none reaches EOS). | mixed, tagged per item |

**Ranking of the routes** (details in §4, probabilities are my honest guesses):

1. **D-G, the conjugation barrier** (§1). Done. It is a filter, not a route: it kills every approach that is symmetric under inversion of one factor (Kneser/Kemperman, Gowers norms on G, expanders, all size/moment/zero-statistics inputs).
2. **D-P, moduli with a square factor** (§2). Exact linearisation; no proof of EOS follows. Chance of EOS for prime powers under GRH by this route: about 1%. Value: a concrete additive model of the problem, and a second place where Thm G-type obstructions are visible.
3. **D-F, F_2[t] / F_3[t] large degree** (§3). Well-posed test problem with no large-q crutch. Chance that a proof for q = 2 is found by known methods: under 5%. Chance that it yields a transferable idea if found: decent.
4. **D-S, special (smooth or prime-power) moduli for "EOS minus parity"** (§4.2). Improve the Type I level of {a p̄ mod m} by q-van der Corput and get a ≡ p·P_r with smaller r. Parity-blocked for EOS by design. Chance of a publishable improvement of r for special moduli: about 30%. Chance of EOS: 0.
5. **D-4, the smooth toy problem** (§4.3): d_4 in a residue class at exact level 1/2. Same Parseval log-deficit, no parity, no deletion barrier. A calibration problem. Whether it is open is [UNVERIFIED].
6. Dead on arrival (§4.4–4.12): Kuznetsov at a fixed modulus; additive combinatorics and higher-order Fourier analysis on G; expanders/mixing; multiplicative chaos (heuristic only); Maynard–Tao/GPY; Bombieri's asymptotic sieve; Duke–Friedlander–Iwaniec; arithmetic geometry over Z; the remark.pdf ideas.

---

## 1. The conjugation barrier

### 1.1 The quotient problem

Define N⁻(a) = #{(p,q) ∈ P² : p ≡ a q (mod m)}. With Q := P^{-1} = {p̄ : p ∈ P} ⊂ G,

  N⁻(a) = #{(p, y) ∈ P × Q : p y ≡ a} = (1/φ) Σ_χ χ̄(a) S(χ) \overline{S(χ)} = (1/φ) Σ_χ χ̄(a) |S(χ)|²,

against N(a) = (1/φ) Σ_χ χ̄(a) S(χ)². (Orthogonality; the Fourier transform of 1_Q is \overline{S(χ)}.)

**Theorem G (proved, unconditional).** Let m ≥ 3 be odd.
1. N⁻(−1) = #{(p,q) ∈ P² : p + q = m} = 2·[m − 2 is prime]. In particular N⁻(−1) = 0 whenever m − 2 is composite: −1 ∉ P·P^{-1}.
2. The pair (Θ₁, Θ₂) = (1_P, 1_Q) shares the following with (1_P, 1_P):
   - (a) nonnegativity and total masses |P|;
   - (b) |Θ̂₂(χ)| = |S(χ)| for every χ, and the same at every truncation: Σ_{p ≤ x} χ(p̄) = \overline{Σ_{p≤x} χ(p)}. So every bound on character sums over primes, at every scale and for every weight, in particular every consequence of GRH for the L(s,χ) and the hypothesis H of route C, holds verbatim;
   - (c) Q consists of |P| distinct residues, so Parseval is exact: Σ_χ |Θ̂₂|² = φ|P|;
   - (d) all moments Σ_χ |Θ̂₂(χ)|^{2k}, the multiplicative energy, and every statistic of the multiset {|S(χ)|}, also jointly with χ ↦ χ(a) for any fixed a;
   - (e) every statement about the zeros of the individual L(s,χ) that is invariant under χ ↦ χ̄ on one factor (GRH, simplicity, spacing statistics inside one L-function);
   - (f) each set separately is equidistributed in residue classes to small moduli d coprime to m: P by the prime number theorem in progressions, Q = A_1 by the Kloosterman-sum bound of Fouvry–Shparlinski (level m^{1/16}, `lit/02` §1.2).
3. Consequently no set of hypotheses satisfied by both pairs implies a ∈ A·B for all a. Every proof of EOS must use an input that fails for (P, P^{-1}).

*Proof.* (1) If p ≡ −q (mod m) with 1 ≤ p, q ≤ m − 1 then m | p + q and 2 ≤ p + q ≤ 2m − 2, so p + q = m. As m is odd, one of p, q is 2 and the other is m − 2. Conversely if m − 2 is prime then 2 ∤ m and gcd(m − 2, m) | 2, so both lie in P. (2) is immediate from Θ̂₂ = \overline{S}. (3) follows. ∎

Remarks.
- For even m, N⁻(−1) is the Goldbach count of m. So in general: **an argument that proves a ∈ P·P for all a from inputs invariant under conjugating one factor would prove a false statement for odd m and binary Goldbach for even m.**
- This is stronger, as a statement about inputs, than the three barriers on record for "size" methods. The redacted-prime set is heuristic (its GRH-quality bounds are unproved, `lit/03` §4). The random-pairing set (`lit/02` §4.3(b)) and Proposition L (route C §5) are not the primes, and Proposition L lives at X ≥ φ log m. Here the set is P itself, the range is exactly X = m, and nothing is assumed.
- It is weaker in one respect: it says nothing against arguments that use the joint structure of P and a·P^{-1} (route A does; see §1.4).

### 1.2 The size bias is real (Corollary G1)

Since χ(−1) = ±1, for every m ≥ 3:

  Σ_{χ even} |S(χ)|² − Σ_{χ odd} |S(χ)|² = φ N⁻(−1), Σ_χ |S(χ)|² = φ|P|,

hence **Σ_{χ odd} |S(χ)|² = (φ/2)(|P| − N⁻(−1))** (proved). For odd m with m − 2 composite the odd characters have mean |S|² equal to |P| exactly, and the even non-principal ones have mean |P|(φ/2 − |P|)/(φ/2 − 1), smaller by the relative amount 2|P|/φ ≈ 2(m/φ)/log m.

So the primes do exhibit a correlation between |S(χ)|² and a character value χ(a), of exactly the critical relative strength 1/log m that `B` §4.4 identified as sufficient to kill a class. In the product problem the same class a = −1 survives only because the *arguments* of S(χ)² are spread out: writing S(χ) = |S(χ)| e^{iθ_χ},

  EOS at a = −1 ⟺ Σ_{χ≠χ0} χ(−1) |S(χ)|² cos 2θ_χ > −|P|², while Σ_{χ≠χ0} χ(−1) |S(χ)|² = −|P|² exactly.

This replaces the hypothetical adversarial-phase example of `lit/03` §0.2 by an actual one.

**Computed** (`conj_barrier.py`, prime m, all characters by FFT; `out_conj_barrier.txt`):

| m | N⁻(−1) | mean \|S\|² odd / even | (odd − even)/(2\|P\|²/φ) | Σ_{χ≠χ0} χ(−1)\|S\|² / \|P\|² | Σ_{χ≠χ0} χ(−1) Re S² / \|P\|² | N(−1)/λ |
|---|---|---|---|---|---|---|
| 10007 | 0 | 1229.00 / 927.28 | 0.9994 | −1.0000 | +0.0069 | 1.007 |
| 100003 | 0 | 9592.00 / 7752.06 | 0.9999 | −1.0000 | +0.0347 | 1.035 |
| 1000003 | 0 | 78498.00 / 66174.28 | 1.0000 | −1.0000 | +0.0036 | 1.004 |
| 3000017 | 0 | 216816.00 / 185476.84 | 1.0000 | −1.0000 | −0.0085 | 0.992 |

The identity Σ χ(−1)|S|² = φN⁻(−1) − |P|² holds to the last digit in each case.

The quotient problem also has singular-series structure at every a of small height, which the product problem lacks (computed, same script; values of N⁻(a)/λ, stable across the four moduli; N(a)/λ at the same a is 1.00 ± 0.03 for m ≥ 10⁶):

| a | 2 | −2 | 3 | −3 | 1/2 | 3/2 | −3/2 | 6 | −6 |
|---|---|---|---|---|---|---|---|---|---|
| N⁻(a)/λ, m = 3000017 | 0.62 | 0.69 | 0.83 | 0.85 | 0.62 | 1.30 | 0.50 | 1.00 | 1.05 |

(heuristic reading: p = uq/v − km/v is a linear equation with small coefficients, so a Hardy–Littlewood singular series and a count of admissible wraps k appear. I did not derive the constants.)

### 1.3 What the barrier kills

An approach is dead if its inputs about the two factors are invariant under replacing one factor A by ι(A) = A^{-1}. Inversion is an automorphism of the abelian group G, so this covers every method that works "in the category of finite abelian groups with a subset":

- Kneser, Kemperman, Plünnecke, and any product-set theorem for pairs (A, B) stated in terms of sizes, doubling, or stabilisers;
- Gowers norms and higher-order Fourier analysis on G: ‖1_B‖_{U^k(G)} = ‖1_{ι(B)}‖_{U^k(G)}, and a generalised von Neumann theorem for the form Σ_{xy=a} f(x)g(y) cannot see the difference;
- Cayley graphs and expander mixing for the generating set P (the spectrum is {S(χ)} for the directed graph; any bound through |S(χ)|, i.e. the mixing lemma, is symmetric);
- transference with a pseudorandom majorant, in which the majorant conditions are imposed on each factor separately;
- L^∞/L²/L⁴ and all mixed-norm bounds on S, the variance wall, energy methods, large sieve inequalities;
- zero statistics of the individual L(s,χ), and "random phase" models that are equally plausible for Z_χ² and |Z_χ|².

*Status:* proved, in the sense that each listed input holds for both pairs.

### 1.4 What it does not kill, and what it shows is necessary (Corollary G2)

The quotient problem at a = −1 fails for a *local* reason interacting with the archimedean cut: the sequence {−p mod m} = {m − p} lies in the even numbers. In the language of route A, the sifted sequence a·ι(Q) has Type I data with singular series 0 at d = 2. For the product problem the sifted sequence A_a = {a p̄ mod m} is equidistributed mod every small d coprime to m (Fouvry–Shparlinski). So:

- Route A (sieve on A_a with Type I input) is not touched by Thm G. Its own barrier is A\* (Theorem B of route A).
- **Any proof of EOS must use the equidistribution of a p̄ mod m (as an integer in [1,m]) modulo small d, at least d = 2.** A proof that never invokes Kloosterman sums over primes, or an equivalent, cannot be correct, because it would apply to the quotient problem. (proved as a statement about inputs: without this, the inputs are the same for both pairs.)
- **The threshold X = m is sharp for the quotient problem.** With p, q ≤ (1+ε)m the equation p + q = 2m becomes available and the obstruction disappears (computed: 754 solutions at m = 3000017, ε = 0.02). The character-sum theorems of route C at X ≥ Kφ log² m are therefore consistent with Thm G, and Thm G gives a structural reason, independent of Parseval, why symmetric methods cannot be pushed down to X = m.
- Combined with the other barriers the necessary inputs are now: (i) joint Type I information about (P, a) [Thm G]; (ii) an exact identity that fails after deleting o(1) of the primes [deletion]; (iii) more than Type I data plus sizes [A\*]; (iv) something that separates one prime from two [parity]. Only a Type II estimate for A_a, or a second spectral expansion of the function a ↦ N(a) as in the function-field proofs, meets all four. I found no third kind of object.

---

## 2. Moduli with a square factor: the problem becomes linear on fibres

### 2.1 The identity

**Proposition P (proved).** Let m = M′h with h | M′ (so h² | m; e.g. m = r², h = M′ = r, or m = ℓ^k, h = ℓ^j, j ≤ k/2).
For b ∈ [0, M′) coprime to m put U_b = {0 ≤ u < h : b + M′u ∈ P}. For (a,m) = 1 and b, c with bc ≡ a (mod M′) put
d(b,c) = ((a − bc)/M′) mod h. Then for p = b + M′u, q = c + M′v:

  pq ≡ a (mod m) ⟺ b v + c u ≡ d(b,c) (mod h),

and therefore N(a) = Σ_{b mod M′} #{(u,v) ∈ U_b × U_{c(b)} : b v + c(b) u ≡ d(b, c(b)) (mod h)}, c(b) = a b̄ mod M′.

*Proof.* pq = bc + M′(bv + cu) + M′²uv and M′² = m·(M′/h) ≡ 0 (mod m). ∎

This is Postnikov's phenomenon: the characters that are trivial on 1 + M′Z are the characters mod M′, and the others restrict to additive characters of Z/h on each coset. In the coset decomposition of `B` §5.2 with H = 1 + M′Z/m, the frequency ξ = 0 term is N_{M′}(a)/h (pairs with pq ≡ a mod M′), which GRH evaluates asymptotically once h ≥ K(log m)⁴ (sketched: error ≤ max|S|² ≪ m log² m against |P|²/φ(M′)). The frequencies ξ ≠ 0 are

  T_ξ = Σ_b Û_b(ξ c) Û_c(ξ b) e(−ξ d(b,c)/h), Û_b(η) = Σ_{u ∈ U_b} e(ηu/h).

Computed check (`square_fibers.py`): the identity holds for 20 random a at r = 101 and r = 211.

### 2.2 What it gives and does not give

- EOS for m with h² | m is a sum over φ(M′) fibres of **binary linear problems in Z/h**, each with sets of density ≈ 1/log m. With h ≈ (log m)⁴ each fibre has ≈ (log m)² expected solutions and there are ≈ m/(log m)⁴ fibres; a class a fails only if every fibre fails.
- Nothing is gained analytically (proved): Cauchy–Schwarz over b and Parseval in ξ give Σ_ξ |T_ξ| ≤ h|P|, the same bound |E(a)| ≤ |P| as before. Each fibre is a short-segment problem (h terms of a progression mod M′), where even GRH gives only the mean square over b.
- **Barrier checklist.** Random-set: defeated (the identity holds for any set; no property of primes is used). Deletion: defeated (delete R_a). Parity: each fibre is a binary Goldbach-type problem. A\*: not applicable (no sieve). Proposition L: applies to every bound through |Û_b|. Thm G: see §2.3; individual fibres do have local obstructions. **Verdict: a reformulation, not a route.** I see no property of ℓ^k beyond this identity that GRH can use. Probability of EOS for prime powers under GRH this way: about 1%.
- What it is good for: an explicit additive model in which to test any proposed mechanism for cross-character cancellation, since for m = r² the 'phases' are literally e(ξ·(bv + cu)/r).

### 2.3 A single fibre does not suffice (computed)

For m = r², r prime, take the fibre b = 1: p ≡ 1, q ≡ c (mod r). Every a ≡ c (mod r) corresponds to one e mod r and the fibre equation is v + c u ≡ e (mod r) with u ∈ U_1, v ∈ U_c. The expected count is ≈ r/(4 log² r)·(r/φ(r))².

| r | \|U_1\| | mean count | (c, e) with no solution | Poisson guess |
|---|---|---|---|---|
| 1009 | 80 | 6.28 | 1685 of 1 017 072 | 1907 |
| 2003 | 144 | 10.20 | 574 of 4 010 006 | 150 |
| 4001 | 265 | 17.08 | 488 of 16 004 000 | 0.6 |

At r = 4001 the 488 empty pairs lie on only 8 values of c: c = 1 (172), −1 (93), 1/3 (86), −3 (51), −1/3 (50), 3 (33), and three isolated ones (`out_square_fibers_zeros.txt`). For c = 1 the empty e are small even numbers 0, 2, 4, …
(heuristic explanation: u and v have fixed parity, so v + u = e + jr determines j, and for small e the equation v + u = e has few solutions. This is the same interaction of a small modulus with the archimedean cut as in Thm G.) So the "one fibre" strengthening of EOS for square moduli is false for small-height c, and only the sum over all b removes the singular series.

---

## 3. Function-field test bed with a small field (computed)

Route B notes that the faithful analogue of the integer problem is F_q[t] with q small and fixed, deg f → ∞, and that Sawin's theorem needs q > 7567. `ff2_eos.py` tests q = 2.

Setup: f ∈ F_2[t] irreducible of degree n with t a generator of (F_2[t]/f)^* (primitive f; 2–3 random such f per degree). P = irreducibles of degree exactly n other than f, as residues (the analogue of primes in (m/2, m]). N(a) for all 2^n − 1 classes by FFT.

| n | \|P\| | λ | classes with N = 0 | min N/λ | random-model R_rand | depth (1−R)/(1−R_rand) | max\|S\|/√\|P\| | energy excess / random |
|---|---|---|---|---|---|---|---|---|
| 8 | 29 | 3.3 | 30–34 | 0 | — | — | 1.8 | 0.82–0.85 |
| 10 | 98 | 9.4 | 4–7 | 0 | — | — | 2.0–2.2 | 0.87–0.91 |
| 11 | 185 | 16.7 | 0 | 0.06–0.24 | — | — | 2.2–2.4 | 0.90–0.92 |
| 14 | 1160 | 82 | 0 | 0.48–0.51 | 0.36 | 0.76–0.82 | 2.6–2.7 | 0.94–0.95 |
| 17 | 7709 | 453 | 0 | 0.74 | 0.70 | 0.84–0.87 | 2.9 | 0.95 |
| 20 | 52376 | 2616 | 0 | 0.88 | 0.86 | 0.87 | 3.1–3.3 | 0.96 |
| 23 | 364721 | 15857 | 0 | 0.94–0.95 | 0.94 | 0.88–0.95 | 3.4–3.5 | 0.97 |

- Failures occur for every sampled f with n ≤ 10 and for none with 11 ≤ n ≤ 23 (sampled moduli only; not exhaustive over f, and non-primitive f were not tested).
- The minimum is 0.84–0.95 of the Gaussian depth, the energy excess is 0.95–0.97 of the fixed-size random-set value, and max|S|² ≈ (0.70–0.75)·|P| log φ. The integer numbers in `compute/RESULTS.md` are 0.87–0.91, 0.91–0.94 and 0.6·π log φ: the same picture, with slightly larger sup norm here.
- Reading (heuristic): nothing in the statistics distinguishes q = 2 from the integers or from large q. The large-q hypothesis in Sawin and Xie is a limitation of the proofs (Betti numbers against √q), not of the truth. A proof for q = 2 would have to control the cohomology of the fibres X_a much more precisely than by counting Betti numbers, or use a different mechanism; either would be the first mechanism not obviously unavailable over Z.

**As a route.** Mechanism: none proposed here. Barrier checklist: the geometric proofs evade all five barriers for the reasons in `B` §6 (they bound the bilinear object itself); Thm G is evaded as well, since the fibre variety X_a for the product map is not the variety for the quotient problem. First lemma: sharpen Sawin's bound in the binary case n₁ = n₂ = deg f, where the count is governed by only two cohomology groups; determine the true threshold for q. First experiment: done above. Probability of a proof at q = 2: under 5%.

---

## 4. The candidate routes, with barrier checklists

Barrier abbreviations: **RS** random-set (pairing-avoiding set with perfect statistics), **DEL** deletion of ≈ 1/log m of the primes, **PAR** parity, **A\*** route A's sequence, **L** Proposition L and the variance wall, **G** Thm G above. "Defeated" means the barrier object satisfies everything the route uses, so the route cannot work.

### 4.1 Kuznetsov / Petersson as a second spectral expansion — dead

- *Mechanism.* N(a) = m^{-2} Σ_{h,l mod m} P̂(h)P̂(l) S(h, al; m) with P̂(h) = Σ_p e(hp/m) and S the Kloosterman sum (proved, completion on the hyperbola xy ≡ a). Hope: expand S spectrally so that a enters only through Hecke eigenvalues.
- *Why it fails.* (i) Kuznetsov sums over the modulus c; here c = m is fixed. The matrix (S(h, al; m))_{h,l} has multiplicative Fourier transform τ(χ)², of constant modulus, so the expansion is a unitary change of basis from the character expansion (proved). (ii) Embedding c = m into Γ_0(m) with c ∈ {m, 2m, …} gives ≍ m forms of level m and bounded spectral parameter; the spectral large sieve at length N ≍ level is Parseval-sharp, exactly like characters (sketched). (iii) Isolating the single value c = m needs a test function of width 1/m in 4π√(hl)/c, i.e. spectral length ≍ m, hence ≍ m² forms (heuristic, uncertainty principle).
- *Checklist.* RS: defeated (only orthogonality is used). DEL: defeated. L: defeated (a new orthonormal basis gives the same L² wall). G: not obviously, since the Kloosterman form is specific to products, but nothing is extracted from that.
- *First lemma, were one to try.* Sign or positivity information for Σ_f λ_f(a) A_f B_f. I know of none. Probability: under 1%.

### 4.2 Special moduli for "EOS minus parity" — alive as a sub-problem only

- *Mechanism.* The Type I level of A_a = {a p̄ mod m} is m^{1/16}, from Σ_p e(h p̄/m) ≪ m^{15/16+o(1)} (`lit/02` §1.2). After Vaughan's identity the bottleneck is the balanced Type II Kloosterman sum, treated by Cauchy–Schwarz and Weil for incomplete sums of length > m^{1/2+ε}. For smooth m, or m = ℓ^k, q-van der Corput (Heath-Brown, Irving) or Postnikov–Korobov handles much shorter incomplete Kloosterman sums, so the exponent 15/16 should drop [UNVERIFIED: I did not compute the new exponent; the Cauchy–Schwarz diagonal caps the method at 3/4, i.e. level m^{1/4}]. A weighted sieve then gives a ≡ p·n with p, n ≤ m and Ω(n) ≤ r for smaller r than the r = 5 recorded in `lit/02` §1.3.
- *Checklist.* PAR: defeated for EOS; the output is an almost-prime statement by design. A\*: defeated for EOS (Type I data only). G: passed (uses the joint Type I data). DEL, RS: passed for the almost-prime statement.
- *First lemma.* For m = ℓ^k or m^ε-smooth: Σ_{u∼U, v∼V} α_u β_v e(h ū v̄/m) ≪ UV m^{−δ} for U ≈ V ≈ m^{1/2} with an explicit δ > 1/16.
- *Probability.* About 30% for an improvement of r on special moduli; 0 for EOS.

### 4.3 The smooth toy problem — a calibration target

- *Statement.* D₄(a) := #{(n₁,…,n₄) : n_i ≤ √m, n₁n₂n₃n₄ ≡ a (mod m)} ~ (√m)⁴/φ, uniformly in a. This is d₄ in a residue class at exact level 1/2 (x = m²).
- *Why it is the right toy.* With T(χ) = Σ_{n≤√m} χ(n): D₄(a) = (1/φ)Σ_χ χ̄(a)T(χ)⁴, and (1/φ)Σ_{χ≠χ0}|T(χ)|⁴ ≈ #{n₁n₂ = n₃n₄} ≍ m log m against a main term ≍ m (sketched: n₁n₂ < m, so the congruence is an equality). **The Parseval deficit is exactly one log, as in EOS**, and GRH/Lindelöf sup bounds are worse. But the variables are smooth: no parity, no deletion barrier, Type I data are complete, and Deligne's bounds for hyper-Kloosterman sums are available. Poisson summation in all four variables is self-dual (error m^{-1/2}Σ_{h_i ≲ √m} Kl₄(a h₁h₂h₃h₄; m), trivial bound m^{3/2}) (sketched).
- *Checklist.* PAR, DEL, A\*: not applicable. L: defeated for size-only methods. G: the conjugate problem n₁n₂ ≡ a n₃n₄ is the twisted fourth moment of Dirichlet L-functions, which is known by spectral methods (Young; Blomer–Fouvry–Kowalski–Michel–Milićević) [UNVERIFIED]; the holomorphic form T⁴ is not a shifted-convolution problem.
- *Use.* If the one-log deficit cannot be beaten here, with every algebraic tool available, there is no hope for Type II on A_a. If it can, the mechanism is the first candidate for a second expansion over Z. Whether this asymptotic is known is [UNVERIFIED]; the classical exponent of distribution θ₄ = 1/2 stops just short of it.
- *First lemma.* The asymptotic for prime m with a (log m)^{-δ} saving. Probability that it is provable with current technology: perhaps 25%.

### 4.4 Additive combinatorics, Gowers norms, ergodic methods on G — dead (proved)

- Kneser/Kemperman, U^k(G) norms, nilsequences on G, transference. G: defeated, §1.3 (inversion is an automorphism of G). DEL: defeated (all are stable under removing o(1) of P). Under GRH, f = 1_P − ρ already has ‖f‖_{U²(G)}⁴ ≪ (log m)^{O(1)}/m, a power saving over ρ⁴ = (log m)^{-4}, and this gives exactly the almost-all statement and nothing pointwise (proved: Σ_a E(a)² = φ³‖f‖⁴_{U²}).
- The Green–Tao viewpoint for the quotient problem (two linear forms in two lattice coordinates) is circular: the coefficients are of size √m, which is the congruence condition again (sketched).

### 4.5 Expanders, Cayley graphs, mixing of x ↦ a x̄ — dead (proved)

- a ∈ P·P is a path of length 2 in Cay(G, P). For two-step walks ending at a single vertex the spectral bound is |N(a) − λ| ≤ max_{χ≠χ0}|S(χ)|², which is ≈ m up to logs against λ ≈ m/log² m. The mixing lemma proper (max|S| < |P|²/φ) is the three-factor criterion of `lit/02` §4.1 and gives P·P·P = G only. RS, L, G: all defeated. The map x ↦ a x̄ is an involution; there is no dynamics to mix.

### 4.6 Multiplicative chaos, random multiplicative functions — heuristic only

- Modelling {S(χ)} by a random family predicts |E(a)| ≈ √(λ log φ), which the numerics confirm. A model is not an input. Any model symmetric under conjugation predicts the same for N⁻, which is wrong at a = −1 by Thm G; so even as a heuristic it must be conditioned on the Type I data. Not a proof route.

### 4.7 Maynard–Tao / GPY weights — dead (parity)

- A GPY argument for the 2-tuple (n, a n̄ mod m) needs each component prime with weighted probability > 1/2. For k = 2 this is unattainable at any level of distribution (parity), and the level here is m^{1/16}. Enlarging the tuple to (n, a s̄ n̄)_{s ≤ z} proves a ternary statement, which is already known with s ≪ (log m)^{3+o(1)} (Remark 5.1).

### 4.8 Bombieri's asymptotic sieve, Selberg's formula — dead (level)

- Λ₂ = Λ·log + Λ∗Λ, and the sequence {n ≤ x : n ≡ a (m)} has Type I level x/m. At x = m² that is level 1/2. Bombieri's sieve needs level 1 − ε for an asymptotic; with level 1/2 one gets P₂ numbers below m^{2−δ} (known), unbalanced, with primes not separated from products. The GRH route for each of Λ·log and Λ∗Λ separately stalls at x ≈ m²(log m)^{O(1)}. PAR: defeated.

### 4.9 Duke–Friedlander–Iwaniec, Kloosterman fractions — dead (single modulus)

- pq − km = a gives k ≡ −a m̄ (mod p) and q ≈ m·{−a m̄/p}: Kloosterman fractions with prime modulus p and fixed numerator. The DFI and Bettin–Chandee bounds for Σ α_m β_n e(a m̄/n) need both m and n to vary; here m is one number. Reciprocity returns e(a p̄/m). The spectral structure behind roots of quadratic congruences (binary forms of a fixed discriminant) has no linear analogue. Averaged over m this is Friedlander–Kurlberg–Shparlinski.

### 4.10 A variety or motive encoding N(a) — dead over Z (as in route B)

- For m = ℓ^k the residues are Witt vectors and [1, m] is everything, but primality of the integer with given digits is not a constructible condition in Witt coordinates, unlike irreducibility in F_ℓ[t]. Nothing beyond `B` §6.3.

### 4.11 Ideas from sources/remark.pdf — nothing usable

- The file is a four-page unverified announcement with no statement or proof that can be checked. The two ideas named (Stepanov's method with multiplicity; chains of theta lifts) concern single L-functions. EOS under GRH needs cancellation *across* the family, which RH-type statements do not address. Stepanov's method counts points on a curve; N(a) is not a point count over Z. [UNVERIFIED; used only as a prompt.]

### 4.12 Changing the problem

- **p, q ≤ (1+ε)m.** Thm G no longer applies (§1.4), but DEL, RS, L do, and route C shows the methods stop at Kφ log² m. No gain.
- **One small prime** (p ≤ (log m)^{2+ε}, q ≤ m; numerically true, `RESULTS.md` Task 3b). Needs a prime below m in one of ≈ (log m)² prescribed classes; GRH needs X₁X₂ ≥ Kφ² L² log X₂. Dead by L.
- **F_2[t], F_3[t].** §3.
- **Weighted versions.** Any nonnegative weights on primes ≤ m obey exact Parseval; flat weights are optimal (route C §6.3).

---

## 5. Two small remarks

**Remark 5.1 (proved from route C Theorem E; novelty [UNVERIFIED]).** Assume GRH. There is K such that for all large m every a coprime to m is p·q·s with primes p, q ≤ m and s ≤ K (log m)³ log log m.
*Proof.* Let 𝓔 be the set of classes not of the form pq with p, q ≤ m; |𝓔| ≤ K₁(φ/m)²(log m)³ by Theorem E. The classes a s̄, s ≤ z prime, s ∤ m, are distinct, and there are at least π(z) − ω(m) ≥ π(z) − 2 log m of them. If π(z) > K₁(log m)³ + 2 log m, one of them is outside 𝓔. ∎
Lit note 01 records s ≪ (log m)⁴ under GRH (Banks–Shparlinski Thm 1.3); their theorem is stated for a general zero-free strip and is much stronger than pigeonhole when σ₀ > 1/2. At σ₀ = 1/2 the pigeonhole bound is smaller by (log m)/log log m. This is a triviality and should be checked against their text before it is quoted.

**Remark 5.2 (proved).** In the Kloosterman form of §4.1, and in every other change of basis, the a-dependence sits in a unimodular or Hecke factor and the two prime sums in a product of two coefficients. Every such expansion with ≍ m orthogonal terms has the same L² wall. A useful second expansion must have far fewer than m terms (as in Sawin: C^n against q^n), or a sign.

---

## 6. Not checked

- The Fouvry–Shparlinski level m^{1/16} for P^{-1} and A_a is quoted from `lit/02`.
- §4.2: no exponent was computed. §4.3: I did not search the literature for the d₄ statement.
- §3: 2–3 primitive moduli per degree; P is "degree exactly n". The variant "degree ≤ n − 1" was not run, nor F_3[t].
- §2.3: the explanation of the empty fibres is heuristic; only c = 1 was examined by hand.
- The singular-series values of N⁻(a)/λ in §1.2 are computed, not derived.
- Probabilities are opinions.
