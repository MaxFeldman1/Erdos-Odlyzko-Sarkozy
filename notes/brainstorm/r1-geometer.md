# Round 1, arithmetic geometer: what the second expansion really is, and what it costs at small q

Written 2026-11-22. Standing hypothesis for anything over Z: GRH for Dirichlet L-functions. Nothing in this
note proves anything about the integer problem; it is about the function-field mechanism, its true size, and
its integer shadow.

Scripts and outputs: `compute/brainstorm/geometer/`
(`schur_count.py`, `rho_count.py`, `tower_eos.py`, `m2_oddchar.py`, `m2_identify.py`, `ff2_pieces.py`, `out_*.txt`).

Status tags: **proved** (complete argument here, or a one-line consequence of a quoted theorem),
**sketched**, **heuristic**, **computed** (exact script output), **[UNVERIFIED]** (recalled, not checked).
Statements about Sawin and Xie are taken from `notes/routes/B-function-field.md` (tagged READ there); I did not
re-open the papers. I could not retrieve the explicit constants C_1(ρ), C_2(ρ) of Sawin's theorem this session.

Notation. k = F_Q, f ∈ k[t] squarefree of degree m, B = k[t]/f, T = Res_{B/k} G_m (the torus of residue classes,
dim m, T(k) = B^×), φ = |B^×|. For χ ≠ χ0 primitive, L(u,χ) = det(1 − u√Q θ_χ), θ_χ ∈ U(m−1).
p_m, e_k, h_k, s_ν are power-sum, elementary, complete and Schur functions of the eigenvalues of θ_χ.

---

## 0. Summary

**Verdict.** No route to EOS over Z. The round produced a sharper picture of the one mechanism that is known to
work (Sawin/Xie), three pieces of which are new to the notes and change how the F_2[t] test bed should be read.

| # | Item | Status |
|---|---|---|
| L1 | **Schur–Mellin form of the EOS error.** Λ-weighted error = (Q^m/φ) Σ_χ χ̄(a) p_m(θ_χ)², and on U(m−1) p_m² = Σ_ν χ^ν(m,m) s_ν with **exactly C(m,2) partitions ν**, coefficients in {±1, ±2}, Σ\|χ^ν\| = (m−1)², Σ(χ^ν)² = (m−1)(2m−3). So the second expansion is a signed sum of only C(m,2) irreducible Tannakian pieces; all the exponential growth is in their ranks r_ν. | identity proved; the closed-form counts computed for m ≤ 14 |
| L2 | **X_a / (S_m × S_m) ≅ T for every a**, and N(a) = Σ_{y ∈ T(k)} 1_irr(y) 1_irr(a/y). The coefficient system is lisse on T ∖ (D ∪ aD^{-1}), D the discriminant hypersurface. χ(T∖D) = (−1)^m binom(2m−2, m). The conjugate (Theorem G) problem is T ∖ (D ∪ aD), which degenerates exactly at a ∈ k^×, where it is binary Goldbach. | proved (Euler characteristic: standard) |
| L3 | Lefschetz number of an (m,m)-cycle on X_a is 0 for generic a, m ≥ 3, p ∤ m ("the q = 1 count vanishes"); for σ with exactly m cycles of lengths n_j it is m!·Πn_j. | sketched (tame case) |
| E1 | **Tower experiment** (f over F_2 fixed, constant field F_{2^r}, all classes a by FFT): Var_a(m²(N−λ)/Q^{m/2}) = 5.996, 14.94, 27.90, 65.75 for m = 3, 4, 5, 7 against (m−1)(2m−3) = 6, 15, 28, 66. Moments 4, 6, 8 Gaussian. No heavy tail: no weight-(m+1) contribution on a divisor of classes. | computed |
| E2 | **m = 2, characteristic 2: the second expansion has exactly two terms.** Moments of the normalised error over a: 1.001, 2.003, 5.03, 14.15 (Sato–Tate for SU(2): 1, 2, 5, 14), and \|D₄′(a) − Q²\| ≤ 2Q for every a at Q = 8, 32, 128. It is an elliptic-curve family. In odd characteristic (p = 101, 211, 401) the fourth moment is 2.96–3.07: not SU(2). Sawin-type bookkeeping gives a bound in the hundreds for the same object. | computed; "elliptic curve" is heuristic |
| E3 | Regular-representation heuristic: keeping signs between hook pairs does not lower the exponential base coming from coefficient ranks (ρ(m+1)/ρ(m) → ≈ 3.7–4). | computed + heuristic |
| E4 | F_2[t], m ≤ 20: Möbius-EOS piece max_a\|M(a)\|/2^m falls from 0.16 to 0.0044; smooth toy D₄ has min/mean 0.33 → 0.88, no empty class for m ≥ 8. | computed |
| C1 | **Caution for the test bed.** For q ≤ 16 Weil's RH gives no pointwise bound at all for the smooth sums Σ_{deg e = m/2} χ(e) (the bound binom(m−1, m/2) q^{m/4} exceeds the trivial q^{m/2}). In F_2[t] smooth pieces are *worse* controlled than prime sums. | proved (trivial) |
| C2 | **Caution for the test bed.** F_q[t] has parity-breaking structures with no integer shadow (Möbius is a character of the discriminant; in characteristic 2 an Artin–Schreier phase of Berlekamp's invariant; the derivative trick). A proof of F_2[t]-EOS through them would not be evidence of a transferable mechanism. | proved as a statement about inputs |

**Routes, ranked.**

1. **G1. Second expansion with the signs kept; true ranks; the honest threshold q₀.** Best route; worked on below.
   Chance of a substantially lower threshold than 7567 in tame characteristic: about 30%. Chance of F_2[t]-EOS: about 1%.
   Chance of EOS over Z: below 0.5% (no transfer mechanism).
2. **G2. Characteristic-2 structure (Berlekamp/Swan, wild collapse).** Chance of F_2[t] Möbius-EOS: about 3%.
   Chance of F_2[t]-EOS: about 1%. EOS over Z: 0 by design. Listed mainly because of C2 and E2.
3. **G3. Geometry over Z.** Three concrete candidates for a second parameter, each fails. Below 1%.

---

## 1. The three routes

Barrier abbreviations as in route D: **RS** random pairing-avoiding set, **DEL** deletion of ≈ 1/log m of the primes,
**PAR** parity, **A\*** route A's sequence, **L** Proposition L, **G** Theorem G. "Pass" means the barrier object
does not satisfy what the route uses.

### G1. The second expansion with signs kept: Schur–Mellin pieces and their true ranks

**Mechanism.** Sawin bounds Σ_{g ≡ a} F_ρ(g) for each factorization function F_ρ by (Betti number) × Q^{(n−m)/2}.
For EOS (n = 2m) the notes record this as O((32e√Q)^m): hook-pair pieces (∧^i ⊠ ∧^j induced to S_{2m}) are bounded
one at a time and their signs are discarded. L1 says the Λ*Λ error is a signed combination of only C(m,2) *irreducible*
pieces t_ν(a) = (Q^m/φ) Σ_χ χ̄(a) s_ν(θ_χ), each of which is Sawin's error term for the irreducible representation
attached to ν. So

  |Λ-error(a)| ≤ Q^{m/2} · B(m), B(m) := Σ_ν |χ^ν(m,m)| · r_ν,

where r_ν bounds the normalised trace of the ν-piece (its rank, when it is pure of weight m). F_Q[t]-EOS at degree m
follows when B(m) < Q^{m/2}(1 − o(1)). The route is: compute, or bound sharply, r_ν for the C(m,2) partitions with
m-quotient of size 2 and at most m−1 rows; the exponential rate C_true = limsup B(m)^{1/m} gives the exact reach
q₀ = C_true² of the method.

**What the experiments say.** (i) For m = 2 in characteristic 2, B = 2 exactly (E2), against bounds in the hundreds.
(ii) The rank depends on the characteristic (E2). (iii) In the tame case the heuristic count is
r_ν ≈ |χ(T∖(D∪aD^{-1}))| · f^ν / binom(2m,m), which gives B(m) between 4^m and 16^m up to polynomial factors (E3, L2),
i.e. q₀ between 16 and 256 rather than 7567 (heuristic). (iv) For q = 2 one would need C_true < √2; the only evidence
that this is not absurd is the m = 2 collapse. I do not believe it.

**Barrier checklist** (for the function-field analogues of the six objects; over Z the route produces nothing, so no
barrier is engaged there).
1. RS: pass. The bound is on the bilinear object as a Frobenius trace; a random set has no L-function and no sheaf.
2. DEL: pass. L1 needs Ψ(d,χ) = −Q^{d/2} Tr θ_χ^d for one unitary θ_χ of size m−1; deletion destroys rationality (`B` §6.1).
3. PAR: pass. The sgn ⊠ sgn piece is the Möbius-EOS sum and is bounded directly like every other piece.
4. A\*: pass. Not a sieve; no Type I data are used.
5. L: pass in form, **fail in substance at small q.** No sup-norm or Parseval step occurs, but the termwise Deligne
   bound is the same kind of loss: it replaces "sum of φ unit phases" by "sum of B(m) unit phases". For Q < C_true²
   the second expansion has *more* terms than the first and is void. This is Remark 5.2 of route D made quantitative.
6. G: pass. The product problem lives on T∖(D∪aD^{-1}), the quotient problem on T∖(D∪aD); at a ∈ k^× the latter is
   degenerate (g₁ − a g₂ = (1 − a) f, a Goldbach equation). The geometry distinguishes them (L2).

**Extra hypotheses.** None. Unconditional over F_Q[t].

**First lemma.** For ν = the three partitions at m = 3 and the six at m = 4, compute the generic rank of the ν-isotypic
part of the varying cohomology of X_a (tame characteristic), and compare Σ|χ^ν| r_ν with Sawin's constants. Then the
general statement: r_ν ≤ binom(2m−2, m)·f^ν/binom(2m, m)·m^{O(1)}.
**First experiment.** Done: §3.

**Probability.** Lower q₀ substantially in tame characteristic: 30%. F_2[t]-EOS by this route: 1%. EOS over Z: < 0.5%.

### G2. Characteristic 2: Möbius as an Artin–Schreier phase, and wild collapse of ranks

**Mechanism.** Over F_{2^r}, for squarefree g of degree n, μ(g) = (−1)^n ψ(β(g)), ψ = (−1)^{Tr}, where
β(g) = Σ_{i<j} α_iα_j/(α_i+α_j)² is Berlekamp's invariant (Stickelberger–Swan; for a quadratic t² + bt + c it is c/b²)
[UNVERIFIED in this generality; the quadratic case is elementary and is what §3.3 uses]. So the Möbius-EOS sum is a
pure Artin–Schreier sum on the torus,

  M(a) = Σ_{y ∈ T(k) ∖ (D ∪ aD^{-1})} ψ(β(y) + β(a/y)),

with a rank-one coefficient sheaf wildly ramified along D ∪ aD^{-1}. Its number of Frobenius eigenvalues is
−χ_c(T∖(D∪aD^{-1}), L_ψ(β + β∘ι_a)), which is the tame Euler characteristic corrected by Swan conductors. E2 shows that
at m = 2 this number is 2, where the tame count is larger. If the collapse persists (rank growth below √2 per degree,
or below √q for q = 4, 8), the μ-piece of F_q[t]-EOS follows for those q; the remaining hook pairs would need the same
analysis with coefficients of rank binom(m−1,i)binom(m−1,j).

A second characteristic-p tool is the derivative trick of Sawin–Shusterman (μ(r + s^p) is a short product of
characters of linear forms in s, because the derivative does not see s^p), which gives Möbius cancellation and a level
of distribution beyond 1/2 for fixed q large in terms of p [UNVERIFIED: recalled thresholds q > p²k²e² for k-point
Chowla, q > 685090 for twin primes]. For p = 2 and deg n = 2m against a modulus of degree m the free family s has no
room (deg s ≤ m, s fixed mod f): exactly level 1/2 again. I see no way to make the inversion g ↦ a/g mod f compatible
with it.

**Barrier checklist.**
1. RS: pass (an exact algebraic identity for μ).
2. DEL: pass (deletion is not algebraic).
3. PAR: pass, and this is the point: parity is broken by a structure special to characteristic p.
4. A\*: pass (no sieve).
5. L: same as G1.5: fails in substance unless the wild ranks are small.
6. G: pass, as in G1.6.
**Transfer.** None. The integer μ is not a character of anything algebraic. **A proof of F_2[t]-EOS by G2 would be
evidence about characteristic 2, not about Z.** The test bed is faithful only for proofs that avoid these structures.

**Extra hypotheses.** None.
**First lemma.** Identify the rank-2 object at m = 2 (explicit elliptic curve E_a over F_{Q²} with
D₄′(a) = Q² − Tr(Frob | H¹(E_a)) + bounded), then compute the Swan-corrected Euler characteristic at m = 3.
**First experiment.** Done for m = 2 (§3.3) and for the size of M(a) over F_2 (§3.5).
**Probability.** μ-EOS over F_2[t]: 3%. F_2[t]-EOS: 1%. Z: 0.

### G3. Geometry over Z: three candidates for a second parameter

A second expansion needs a parameter that varies with (m, a) fixed and in which the count is a trace. In F_Q[t]
it is r in F_{Q^r}. L2 isolates what is used: **1_irr is a trace function on the algebraic group T**, lisse off a
divisor, so 1_irr * 1_irr is computed by cohomology of T∖(D∪aD^{-1}). Candidates over Z:

- **(a) Base change K/Q.** There is no unramified tower; in a cyclic K/Q the analogue of "monic of degree m" (a
  canonical representative of each class mod m among integers of bounded size) does not exist. Dead (`B` §3).
- **(b) Fixed-level trace formulas.** pq − km = a is det (p, k; m, q) = a with lower-left entry m: one Bruhat cell of
  level m. For a = ±1 it is: the reversed continued fraction of p/m has prime numerator. Kuznetsov, Eichler–Selberg on
  Γ_1(m) and Kloosterman sheaves mod a prime m all give unitary changes of basis with ≍ m terms (route D §4.1,
  Remark 5.2). The hyperbolic terms of Eichler–Selberg for T_n⟨a⟩ detect d ≡ a (mod m) for d | n, which is linear in
  the primes, not pq ≡ a. Dead.
- **(c) Special moduli.** m = ℓ^k (Witt coordinates), m smooth (CRT coordinates), m = value of a cyclotomic polynomial:
  in each case (Z/m)^× is the points of an algebraic group, but 1_P is not a trace function on it, because [1, m] is
  not constructible (route D §4.10). The close-fields trick (Z/ℓ^k versus F_ℓ[t]/t^k via Q(ℓ^{1/k})) moves the
  problem to a field where the size condition is again not algebraic. Dead.

**Barrier checklist.** RS: fail. DEL: fail. PAR: fail. A\*: not engaged. L: fail. G: (b) passes in form only.
All three candidates end in an orthonormal expansion with ≍ m terms and use nothing a random set lacks.
**Extra hypotheses.** None proposed; the integer analogue of Sawin's bound is TR(δ) of `B` §5.1 and I have nothing weaker.
**First lemma.** None worth stating. **Probability.** Below 1%.

What L1–L3 add to the diagnosis in `B` §6.3: (i) the second expansion is a statement about C(m,2) objects, not m²
hook pairs and not C^m partitions; an integer hypothesis modelled on it should be about the class function of type
(m,m), i.e. about Z_χ(X)² only, which is what TR(δ) already is; (ii) L3: at "q = 1" the signed number of terms is 0,
so no Euler-characteristic or F_1 heuristic can replace absolute Betti bounds (heuristic remark).

---

## 2. Lemmas

### L1. Schur–Mellin form (proved; closed-form counts computed)

Let χ ≠ χ0 mod f. Σ_{deg g = d} χ(g) = 0 for d ≥ m, so L(u,χ) is a polynomial of degree ≤ m−1, and
Ψ(d,χ) := Σ_{deg g = d} Λ(g)χ(g) = −Q^{d/2} p_d(θ_χ) (with the usual modification for the O(Q^{m−1}) characters
that are imprimitive or trivial on k^×). Hence

  Σ_{g₁g₂ ≡ a, deg g_i = m} Λ(g₁)Λ(g₂) = Ψ(m,χ0)²/φ + (Q^m/φ) Σ_{χ≠χ0} χ̄(a) p_m(θ_χ)².

By Frobenius' formula p_m² = p_{(m,m)} = Σ_{ν ⊢ 2m} χ^ν(m,m) s_ν, and s_ν(θ) = 0 for θ ∈ U(m−1) when ν has more than
m−1 rows. By Murnaghan–Nakayama χ^ν(m,m) ≠ 0 only if ν has empty m-core, i.e. m-quotient of total size 2;
there are C(m,2) + 2m such ν, with values ±2 (two runners) or ±1 (one runner), and Σ_ν χ^ν(m,m)² = 2m².

`schur_count.py` (beta-set Murnaghan–Nakayama, checked against Σχ² = 2m²):

| m | #ν, all | #ν with ≤ m−1 rows | V(m) = Σχ² | Σ\|χ\| | max\|χ\| |
|---|---|---|---|---|---|
| 2 | 5 | 1 | 1 | 1 | 1 |
| 3 | 9 | 3 | 6 | 4 | 2 |
| 4 | 14 | 6 | 15 | 9 | 2 |
| 5 | 20 | 10 | 28 | 16 | 2 |
| 7 | 35 | 21 | 66 | 36 | 2 |
| 10 | 65 | 45 | 153 | 81 | 2 |
| 14 | 119 | 91 | 325 | 169 | 2 |

For 2 ≤ m ≤ 14 the restricted counts are C(m,2), (m−1)(2m−3) and (m−1)² (computed; not proved in general).
V(m) = ∫_{U(m−1)} |p_m|⁴ is the large-Q variance of m²(N(a) − λ)/Q^{m/2} if the θ_χ are equidistributed. V(m)/m² → 2,
the factor 2 of the random model (`RESULTS.md`: variance 2λ).

Each t_ν(a) = (Q^m/φ) Σ_χ χ̄(a) s_ν(θ_χ) is the error term of the factorization function of an irreducible
representation of S_{2m}, so Sawin's theorem applies to it: |t_ν(a)| ≤ 2(C₁ + C₂√Q) Q^{m/2} with constants depending
on ν only (quoted via `B` §1.2). **The Λ*Λ error is Σ_ν χ^ν(m,m) t_ν(a), a sum of C(m,2) terms.**

### L2. The quotient X_a/(S_m × S_m) is the torus, for every a (proved)

X_a = {(x, x′) ∈ (A¹∖Z(f))^{2m} : Π(t − x_i)Π(t − x′_j) ≡ a (f)}. The quotient by S_m × S_m is
{(g₁, g₂) monic of degree m, g₁g₂ ≡ a}. Reduction mod f is a bijection from monic polynomials of degree m to B
(Lagrange interpolation at the roots of f), and g₂ is determined by g₁. So the quotient is T, with g₁ ↦ y = g₁ mod f
and g₂ ↔ a/y. Therefore

  N(a) = Σ_{y ∈ T(k)} 1_irr(y) · 1_irr(a y^{-1}),

and 1_irr is the trace function of a virtual sheaf on T, lisse on T∖D, D = {y : g_y has a repeated root}. The sheaf
for the pair is lisse on U_a = T∖(D ∪ aD^{-1}).

- T∖D is the space of unordered m-point configurations on C = P¹ ∖ (Z(f) ∪ ∞), χ(C) = 1 − m, so
  χ(T∖D) = binom(1−m, m) = (−1)^m binom(2m−2, m). Since χ(T) = 0:
  χ(U_a) = 2(−1)^m binom(2m−2, m) + χ(D ∩ aD^{-1}) (tame Euler characteristics).
- **Theorem G in this language.** The quotient problem g₁ ≡ a g₂ lives on T∖(D ∪ aD). For a ∈ k^×, a ≠ 1, the
  equation is g₁ − a g₂ = (1 − a) f, binary Goldbach for f; for a = 1 it is g₁ = g₂. So the classes where the
  conjugate problem is linear are the constants k^×, the analogue of the small-height classes of route D §1.2. The
  product problem has no such classes. Both problems have the same |S(χ)| data; the arrangements differ.

### L3. Lefschetz numbers on X_a (sketched; tame case p > 2m)

For σ ∈ S_{2m} of order prime to p, Σ(−1)^i Tr(σ | H^i_c(X_a)) = χ_c(X_a^σ). If σ has l cycles of lengths n_j,
X_a^σ = {z ∈ C^l : Π_j (c − z_j)^{n_j} = a(c) for the m roots c of f}.
- l < m: empty for generic a (m equations, l unknowns). In particular for cycle type (m,m), m ≥ 3: Lefschetz number 0.
- l = m: m divisors of multidegree (n_1,…,n_m) in (P¹)^m, with no common point on the boundary (a point with some
  z_j = ∞ would need the other m−1 coordinates to hit all m roots of f). The count is m!·Πn_j (intersection number;
  transversality for generic a not written out).
So the full cohomology of X_a is at least of size m!·2^m, but the (m,m)-class function that EOS uses has signed
dimension 0: all cancellation between the C(m,2) pieces is in signs that a termwise bound cannot see.

### C1. Smooth sums at small q (proved, trivial)

T_k(χ) = Σ_{deg e = k} χ(e) = (−1)^k Q^{k/2} e_k(θ_χ). Weil gives |T_k(χ)| ≤ binom(m−1,k) Q^{k/2}. At k = m/2 this is
≈ 4^k Q^{k/2}/√k against the trivial Q^k, so it is void for Q ≤ 16. The integer counterpart is that GRH gives
Σ_{n ≤ √m} χ(n) ≪ m^{1/4} exp(C log m/log log m), not m^{1/4}(log m)^{O(1)}. For the d₄ toy of route D §4.3 this
means: the exact fourth-moment count is fine, but any step that uses sup bounds for the smooth polynomials loses
m^{o(1)}, not a power of log. In F_2[t] even the "all but (log)^{O(1)} classes" statement for the toy is not available
by the argument that gives it for primes (the eighth moment of T_k is a congruence count, not an equality count).

---

## 3. Experiments

### 3.1 Tower experiment (E1) — `tower_eos.py`, `out_tower.txt`, `out_tower_moments.txt`

f ∈ F_2[t] irreducible of degree m (0x7, 0xB, 0x13, 0x25, 0x83), Q = 2^r with gcd(r, m) = 1, so
B_r = F_Q[t]/f = F_{2^{rm}} and g ↦ g(τ) is a bijection from monic degree-m polynomials over F_Q to the field.
P_r = irreducibles of degree m other than f (count checked against the necklace formula). N_r(a) for all a by FFT.
e(a) = m²(N_r(a) − λ)/Q^{m/2}. By Lefschetz, for fixed a this is a signed sum of r-th powers of Frobenius eigenvalues.

| m | r | Q | \|K^×\| | min N/λ | Var e | V(m) | m4 | m6 | m8 | max\|e\| | max/√(2 Var log φ) | max/√Q |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 3 | 4 | 16 | 4095 | 0.896 | 5.982 | 6 | 2.93 | | | 8.58 | 0.86 | 2.14 |
| 3 | 5 | 32 | 32767 | 0.948 | 5.990 | 6 | 2.975 | 14.89 | 103.5 | 9.31 | 0.83 | 1.65 |
| 3 | 7 | 128 | 2097151 | 0.991 | 5.996 | 6 | 2.995 | 14.91 | 103.8 | 12.53 | 0.95 | 1.11 |
| 4 | 3 | 8 | 4095 | 0.775 | 14.43 | 15 | 3.19 | | | 13.91 | 0.90 | 4.92 |
| 4 | 5 | 32 | 1048575 | 0.985 | 14.94 | 15 | 3.006 | 15.04 | 103.9 | 15.99 | 0.79 | 2.83 |
| 5 | 3 | 8 | 32767 | 0.877 | 27.90 | 28 | 2.97 | | | 25.59 | 1.06 | 9.05 |
| 5 | 4 | 16 | 1048575 | 0.977 | 27.90 | 28 | 3.006 | 15.12 | 106.7 | 24.53 | 0.88 | 6.13 |
| 7 | 2 | 4 | 16383 | 0.773 | 66.16 | 66 | 3.04 | | | 34.86 | 0.97 | 17.4 |
| 7 | 3 | 8 | 2097151 | 0.971 | 65.75 | 66 | 2.990 | 14.84 | 102.5 | 41.43 | 0.95 | 14.6 |

(m4, m6, m8 are normalised even moments; Gaussian values 3, 15, 105.)

Readings.
- **Var e = V(m) to three digits already at Q = 8–32** (computed). This confirms L1 and the equidistribution of θ_χ in
  U(m−1) at the level of ∫|p_m|⁴, in the q-aspect.
- **Gaussian through the eighth moment, extremes at 0.8–1.06 of the Gaussian extreme** (computed). The same
  shape as the integer data. In the q-aspect this is forced by Deligne equidistribution if the pieces have large
  monodromy (heuristic).
- **No class a has an error of larger order.** A weight-(m+1) contribution on a divisor of classes (allowed by the
  C₂√Q term in Sawin's bound, and compatible with the variance) would give kurtosis ≍ Q and max|e| ≍ √Q. Observed:
  kurtosis 3.00, and max|e|/√Q decreasing in r (computed). So for these f the error is of size Q^{m/2} for every a.
- Lower bounds for the number of terms: B(3) ≥ 12.5, B(4) ≥ 16, B(5) ≥ 25.6, B(7) ≥ 41.4 (computed: sup over the
  classes seen). These are Gaussian extremes, growing like m^{3/2}√(r); **the experiment cannot see exponential rank
  growth**, because traces of high-rank pieces are Gaussian until the number of points exceeds exp(rank²).
  For comparison, F_2[t]-EOS by a termwise bound needs B(m) < 2^{m/2}: 2.8, 4, 5.7, 11.3. It already fails at m ≤ 7,
  which says nothing about large m.

### 3.2 m = 2 in characteristic 2: two eigenvalues (E2) — `out_tower_m2.txt`, `out_tower_moments.txt`

| r | Q | Var e | m4 | m6 | m8 | generic max\|e\| | largest \|e\| (at a = 1) |
|---|---|---|---|---|---|---|---|
| 7 | 128 | 1.023 | 2.075 | 5.65 | 19.5 | 2.27 | 3.92 |
| 9 | 512 | 1.006 | 2.012 | 5.11 | 14.65 | 2.12 | (r divisible by 3, a = 1 not extremal) |
| 11 | 2048 | 1.0015 | 2.003 | 5.03 | 14.15 | 2.08 | 2.71 |

The moments of the trace of SU(2) are 1, 2, 5, 14 (Catalan numbers). The data converge to them with corrections
O(Q^{-1/2}). A single irreducible piece (V(2) = 1) whose trace has the Sato–Tate law has rank 2.

### 3.3 Why, and the exact form — `m2_identify.py`, `out_m2_identify.txt`

For m = 2 the reducible monic quadratics are the products (t+α)(t+β), so with U = τ + F_Q ⊂ F_{Q²}
(τ² + τ + 1 = 0) and r₂(x) = #{(α,β) : (τ+α)(τ+β) = x}: 1_red = (r₂ + 1_{U²})/2, and (proved, elementary)

  N(a) = const + ¼ D₄′(a) + O(√Q), D₄′(a) = #{(α₁,…,α₄) ∈ F_Q⁴ : Π(τ + α_i) = a}.

So at m = 2 the EOS error *is* the smooth toy with k = 1: products of four points of a line in F_{Q²}.
Computed, for every a ∈ F_{Q²}^×:

| Q | range of D₄′(a) − Q² | 2Q |
|---|---|---|
| 8 | [−10, 16] | 16 |
| 32 | [−58, 62] | 64 |
| 128 | [−250, 256] | 256 |

A Hasse bound |D₄′(a) − Q²| ≤ 2Q for all a, with the Sato–Tate law: D₄′(a) = Q² − (trace of Frobenius of F_{Q²} on a
rank-2 weight-1 object), i.e. an elliptic curve E_a/F_{Q²} (heuristic identification; the curve was not found, and
the trace is not a function of N(a), Tr(a) alone). The values are not Kloosterman sums of F_Q.

**Odd characteristic** (`m2_oddchar.py`, f = t² − d over F_p, random a): Var 1.01–1.04, m4 = 2.96, 2.96, 3.07, m6 =
14.3–15.9 for p = 101, 211, 401. Fourth moment 3, not 2: the piece is irreducible but not of rank 2 with SU(2)
monodromy (rank ≥ 3). The same decomposition N = const + ¼D₄′ + O(√Q) holds, so the surface is "the same" and its
cohomology is smaller in characteristic 2.

For scale: the formula recorded in `B` §1.2 gives at m = 2 (n = 4) the bound 432 Q + 60 Q^{3/2} for the Λ-weighted error
(my evaluation of that formula: binom(4,2)·(2·binom(9,7) Q + binom(5,2) Q^{3/2}); [UNVERIFIED] against the paper);
the truth in characteristic 2 is 2Q·(1 + o(1)) in the same normalisation, with no Q^{3/2} term.

### 3.4 Do the signs help with the exponential rate? (E3) — `rho_count.py`

If the varying cohomology of X_a is close to a multiple of the regular representation of S_{2m} (free-quotient
heuristic), then r_ν ≈ |χ_orb|·f^ν and the number of terms is |χ_orb|·W(m), W(m) = Σ_ν |χ^ν(m,m)| f^ν, against
|χ_orb|·binom(2m,m)(2^{m−1}−1)² when hook pairs are bounded separately.

| m | W(m)/binom(2m,m) | ratio to previous | (2^{m−1}−1)² |
|---|---|---|---|
| 4 | 4.01 | 5.02 | 49 |
| 8 | 1003 | 3.71 | 16129 |
| 12 | 1.81·10⁵ | 3.68 | 4.19·10⁶ |
| 16 | 3.46·10⁷ | 3.74 | 1.07·10⁹ |

The saving over hook-pair bookkeeping is a factor ≈ 30 at m = 16 and the growth ratio drifts back towards 4
(computed). **Keeping the signs gains a polynomial factor, not a smaller base** (heuristic: rests on the
regular-representation assumption). With χ(T∖D) ≈ 4^m from L2, the tame count is between 4^m and 16^m, so
q₀ ∈ [16, 256] (heuristic). Either way the tame second expansion has more terms than the first for q ≤ 16.

### 3.5 Pieces over F_2 itself (E4) — `ff2_pieces.py`, `out_ff2_pieces.txt`

f primitive of degree m over F_2, all classes by FFT. M(a) = Σ_{g₁g₂ ≡ a} μ(g₁)μ(g₂) over monic g_i of degree m;
D₄(a) = #{e₁e₂e₃e₄ ≡ a, e_i monic of degree m/2}.

| m | max\|M\|/2^m | Var M/2^m | max/Gaussian extreme | D₄ min/mean | D₄ max/mean | Σ d_kk²/2^m |
|---|---|---|---|---|---|---|
| 8 | 0.164 | 0.59 | 1.02 | 0.33 | 1.85 | 3.0 |
| 12 | 0.050 | 0.63 | 0.98 | 0.59 | 1.89 | 4.0 |
| 16 | 0.0135 | 0.74 | 0.86 | 0.76 | 1.46 | 5.0 |
| 20 | 0.0044 | 0.80 | 0.96 | 0.88 | 1.29 | 6.0 |

- Möbius-EOS: square-root cancellation in every class, extremes Gaussian. Nothing special happens at q = 2.
- **A prediction of mine was wrong.** I expected Var M/2^m ≈ ∫_{U(m−1)}|h_m|⁴ = m+1. The measured value is 0.6–0.8,
  growing slowly. The large-Q value m+1 comes from equal products g₁g₂ = g₃g₄; at q = 2 it is multiplied by a small
  arithmetic factor (heuristic; not derived). For the smooth toy the energy is exactly (k+2)/2 instead of k+1.
  The lesson: **at q = 2 the θ_χ are far from Haar for statistics outside the stable range**, although for the
  prime piece p_m the Haar value V(m) was accurate at Q = 4 already.
- Smooth toy: every class is hit for m ≥ 8 and D₄(a)/mean → 1. True, and (by C1) not provable by the methods that
  handle the prime case.

---

## 4. What this means for the team

1. **The test bed needs a faithfulness rule.** F_2[t]-EOS could fall to characteristic-p structure (G2, C2). Only a
   proof that would also work for a "generic" multiplicative family is evidence for Z. Conversely E2 shows that
   characteristic 2 is geometrically atypical already at m = 2, so numerical agreement between F_2[t] and Z
   (route D §3) is agreement of random-model statistics, not of mechanisms.
2. **Remark 5.2 of route D is now quantitative** on the function-field side: the second expansion has
   B(m) = Σ_ν|χ^ν(m,m)| r_ν terms; it beats the first only for Q > C_true². Tame heuristic: C_true ∈ [4, 16]. The
   normalisation "q ↔ e" for Z puts the integers far on the wrong side, as `B` §3 argued with Sawin's constant.
3. **The integer shadow of the mechanism is not a bound, it is a constructibility statement**: 1_irr is a trace
   function on the group of residue classes (L2). Every input demanded by route D's synthesis (joint (P,a)
   information, exact identity fragile under deletion, more than Type I plus sizes, separation of one prime from two)
   is supplied at once by that single fact, and by nothing weaker that I can find.
4. **Route D §4.3 (d₄ toy):** by §3.3 the toy with k = 1 is literally EOS at m = 2, and is an elliptic curve. But C1
   says the toy is not the easy case under GRH-type inputs: smooth polynomials have the worse sup norm.
5. For the analysts: Theorem G's function-field avatar (L2) suggests testing any proposed joint (P,a) input on the
   pair of arrangements D ∪ aD^{-1} versus D ∪ aD; an input that does not change when a·y^{-1} is replaced by a·y is
   blind in the sense of Theorem G.

## 5. Not checked

- Sawin's constants C₁(ρ), C₂(ρ) and whether his theorem is stated for irreducible ρ in the form used in L1 (it is
  stated for arbitrary ρ in `B` §1.2); the evaluation 432 Q + 60 Q^{3/2} in §3.3.
- The closed forms C(m,2), (m−1)², (m−1)(2m−3) beyond m = 14.
- L3: transversality; the wild case. The general Berlekamp/Swan formula in G2. Sawin–Shusterman thresholds.
- The identification of the m = 2 object as an elliptic curve, and the rank in odd characteristic (only "not SU(2)").
- The tower experiment used one f per degree, irreducible over F_2, and r coprime to m. Split f was not tested.
- E3 rests on the regular-representation heuristic; no Betti number was computed for m ≥ 3.
