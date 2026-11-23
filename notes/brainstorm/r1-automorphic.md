# Round 1 — automorphic / spectral persona

Written 2026-11-22. Standing hypothesis: GRH for Dirichlet L-functions; anything more is flagged.
Scripts and outputs: `compute/brainstorm/automorphic/` (`kl_dual.py`, `kl_model.py`, `out_*.txt`).

**Status tags.** *proved* = complete argument here. *sketched* = steps indicated, believed complete.
*heuristic* = not a proof. *computed* = exact output of a script. [RECALLED] = literature statement from memory, not re-read.

Notation as in `00-setup.md`. For prime m: P̂(h) = Σ_{p∈P} e(hp/m), S(u,v;m) the Kloosterman sum,
K(t) = S(1,t;m), Kl₂(t) = K(t)/√m ∈ [−2,2], τ(χ) the Gauss sum, ε_χ = τ(χ)/√m, L = log m, λ = |P|²/φ,
E(a) = N(a) − λ, N⁻(c) = #{(p,q) ∈ P² : p ≡ cq}.

---

## 0. Summary

**Verdict.** I found no automorphic route to EOS. I did find what route D §4.1 missed, and it is a structural fact rather than a proof strategy.

| # | Item | Status |
|---|---|---|
| Lemma H (§1.1) | The closed horocycle of height 1/m on Y₀(m) meets itself exactly at the points z_x = x/m + i/m, paired by x ↔ −x̄. Hence, with a *fixed* point-pair kernel, the pre-trace formula of Γ₀(m) gives the exact identity Σ_{p,q} K_Γ(z_p, z_{−āq}) = N(a) + N⁻(−ā). D §4.1(iii) ("isolating c = m needs spectral length m, hence m² forms") is wrong: ≍ m forms of bounded spectral parameter suffice. D §4.1(ii) (no gain over characters in L²) stands. | proved |
| Lemma K (§1.2) | For prime m: N(a) = (m+1)\|P\|²/m² + m⁻² Σ_{c≠0} Π(c) K(ac), with Π = P̂ ⋆ P̂ (multiplicative convolution of the additive transform) and Π(c) = Σ_{p,q} S(1,cpq;m) up to an explicit constant. | proved; computed (error 10⁻¹¹) |
| §1.3 | **Kloosterman singular series.** Π is far from flat. It has peaks at c of small height u/v, of size κ(u/v)·(m/L)² with κ stable in m: κ(−1/6) ≈ +1.45, κ(1/6) ≈ −1.29, κ(−1/30) ≈ −1.27, κ(−1/12) ≈ −1.07. These are 31, 78 and 138 standard deviations of Π at m ≈ 10⁵, 10⁶, 4·10⁶. Equivalently N(a) has explicit secondary terms κ(c)·(√m/L²)·Kl₂(ac): corr_a(E(a), Kl₂(a/6)) = −0.083, −0.069, −0.062. The peaks are produced by the major arcs of P̂. | computed; derivation heuristic |
| §1.4 | **No few-term expansion.** The major-arc part of level R explains the share θ′² of Var_a E(a), where θ′ ≈ log R/log m is the share of ‖P̂‖² on the major arcs (checked to 2–3 digits). A fixed number of Kloosterman terms explains O(1/L²). Even R = √m gives at most about 1/4, and the Parseval bound for the remainder is still ≥ (1/2)\|P\|. | computed; heuristic law |
| §1.5 | Theorem G in dual form: among the bases obtained by twisting with ε_χ^k, S(χ)² is structured only for k = ∓2 and \|S(χ)\|² only for k = 0. The product and quotient problems differ exactly by the squared root number. | computed |
| §1.6 | Symmetric parity statement: for any Type I weight ν of level R ≤ m^{1/16−ε} and f = ν − 1_P, the counts 1_P⋆1_P(a) and f⋆f(a) differ by computable terms. | sketched |
| §2, §3 | Two further routes (parity-free "Titchmarsh" ladder; functional-equation bridge for the smooth toy D₄). Both stop at a required saving of √m in multilinear Kloosterman forms. | sketched / heuristic |

**Proposed routes and honest probabilities.**

1. **Route K — Kloosterman-dual expansion at level m.** EOS: under 1%. Delivered: Lemmas H, K and the singular series.
2. **Route TD — parity-free ladder (prime × GL₂ coefficient).** EOS: 0 (parity-blocked by design). A new almost-prime result for prime moduli: about 15%. The asymptotic TD conjecture under GRH: about 2%.
3. **Route FE — product = Kloosterman transform of quotient, for sequences with a functional equation.** The smooth toy D₄ of D §4.3: about 3–5% (D guessed 25%). EOS: under 0.5%.

---

## 1. Route K: the Kloosterman-dual expansion (best route; worked)

### 1.1 Lemma H: the self-dual horocycle

Let Γ = Γ₀(m) acting on the upper half-plane, and z_x = x/m + i/m for an integer x coprime to m.

**Lemma H (proved).** Let k(z,w) = k₀(cosh d(z,w)) with k₀ smooth, supported in [1, 5/4), k₀(1) = 1, and K_Γ(z,w) = Σ_{γ∈Γ} k(z,γw) (γ in PSL₂). Then for units x, y mod m

  K_Γ(z_y, z_x) = 1[y ≡ x] + 1[y ≡ −x̄ (mod m)].

Consequently, for every (a,m) = 1,

  **Σ_{p,q∈P} K_Γ(z_p, z_{−āq}) = N(a) + N⁻(−ā).**

*Proof.* Write γ = ±(A B; C D) with m | C. Use cosh d(z,w) = 1 + |z−w|²/(2 Im z Im w).
- C = 0: γ is an integer translation, γz_x = z_{x+nm}. Two distinct points z_y, z_{y′} have cosh d = 1 + (y−y′)²/2 ≥ 3/2.
- |C| = m (say C = m): |Cz_x + D|² = (x+D)² + 1. If D = −x then γz_x = A/m + i/m with A ≡ −x̄ (from AD − BC = 1). If D ≠ −x then Im γz_x ≤ 1/(2m) and cosh d(z_y, γz_x) ≥ 1 + (1/2m)²/(2·(1/m)·(1/2m)) = 5/4.
- |C| ≥ 2m: |Cz_x + D|² ≥ 4, Im γz_x ≤ 1/(4m), cosh d ≥ 1 + (3/4m)²/(2·(1/m)(1/4m)) = 17/8.
So only γ with γz_x ∈ {z_x + n, z_{−x̄} + n} contribute, each with k = 1. For the second statement take x = −āq: then −x̄ ≡ a q̄. ∎

Remarks.
- Geometrically: the closed horocycle of height 1/m in Y₀(m) has length m and exactly the double points z_x ∼ z_{−x̄}. EOS at a = −1 says that some double point has both parameters prime. For general a one pairs the prime-sampled horocycle with its Galois translate x ↦ −āx.
- Spectral side (Selberg): K_Γ(z,w) = Σ_j h(t_j) u_j(z) ū_j(w) + Eisenstein, with h the Selberg transform of k₀, a fixed rapidly decaying function. So N(a) + N⁻(−ā) = Σ_j h(t_j) A_j \overline{B_j(a)} + Eis, A_j = Σ_p u_j(z_p), B_j(a) = Σ_q u_j(z_{−āq}). By Weyl's law the effective number of terms is ≍ vol(Γ₀(m)\H) ≍ m.
- **Correction to D §4.1(iii).** The moduli of Γ₀(m) are multiples of m and the relevant frequencies are ≍ m, so c = m is separated from c ≥ 2m by a test function of width O(1). The count is ≍ m forms, not m². D's point (ii) is the real obstruction: this is a basis of the same size as the characters, and the spectral large sieve at length ≍ level is Parseval-sharp.
- The pre-trace kernel cannot see N(a) without N⁻(−ā) (the identity term of Kuznetsov). At a = −1 this is ⟨1_P, (I + J)1_P⟩ ≥ 0 with J the involution x ↦ −x̄, i.e. the useless bound N(−1) ≥ −|P|. Positivity of h does not help.
- The a-dependence is a Galois action on horocycle points, not a Hecke eigenvalue. It becomes λ_j(a) only for an integer representative of bounded size; for a of height ≍ m the Hecke relation has ≍ m terms. So there is no "a enters through few eigenvalues" at fixed modulus. The level-1 oldforms contribute Σ_p u(p/m + i/m), sums over primes on a low horocycle (the Sarnak–Ubis setting), but they are O(1) of the ≍ m forms.

### 1.2 Lemma K: the exact Kloosterman-dual identity (m prime)

**Lemma K (proved).** Let m be prime, Π(c) = Σ_{h,l≠0, hl≡c} P̂(h)P̂(l). Then Π is real,

  **N(a) = (m+1)|P|²/m² + m⁻² Σ_{c≠0} Π(c) K(ac),**

and conversely Π(c) = Σ_b N(b) K(bc) + |P|² = Σ_{p,q∈P} S(1, cpq; m) + |P|².

*Proof.* 1_P(x) = m⁻¹ Σ_h P̂(h) e(−hx/m), so N(a) = m⁻² Σ_{h,l} P̂(h)P̂(l) S(h, al; m). For h, l ≠ 0, S(h,al;m) = S(1, ahl; m). The terms with exactly one of h, l zero have S = −1 and Σ_{l≠0} P̂(l) = −|P| (since 0 ∉ P); h = l = 0 gives (m−1)|P|². Reality: P̂(−h) = conj P̂(h) and (−h)(−l) = hl. The converse follows from Σ_c K(ac)K(cb) = m(m·1[a=b] − 1). ∎

*Computed:* max_a |N(a) − reconstruction| = 2·10⁻¹², 1·10⁻¹¹, 5·10⁻¹¹ at m = 100003, 1000003, 4000037.

In Mellin terms: S(χ) = (τ(χ)/m)·Σ_{h≠0} P̂(h) χ̄(−h), so S(χ)² = ε_χ²·(Mellin transform of Π)/m, and |S(χ)|² involves no root number. **The Kloosterman kernel is exactly the squared root number that separates S² from |S|².** Lemma K is a unitary change of basis; its content is that Π is a much more structured function than N.

### 1.3 The Kloosterman singular series (computed; derivation heuristic)

**Heuristic derivation.** If rh = j + bm with r squarefree and small, (j,r) = 1 and |j| ≲ r, then h/m = b/r + j/(rm) and the prime number theorem in progressions gives

  P̂(h) ≈ (μ(r)/φ(r))·I(j/r), I(β) = Σ_{p≤m} e(βp/m) ≈ (m/L)·ι(β), ι(β) = (e(β) − 1)/(2πiβ).

Here h ≡ j r̄ (mod m). Inserting into Π(c) = Σ_h P̂(h)P̂(c h̄):

  Π(c) ≈ Π♯(c) := Σ_{j₁j₂ \overline{r₁r₂} ≡ c} (μ(r₁)μ(r₂)/(φ(r₁)φ(r₂)))·I(j₁/r₁) I(j₂/r₂),

so Π is large at c ≡ u v̄ of small height, with Π(u v̄) ≈ κ(u/v)(m/L)². Example: for c = ±1/6 the four terms (r₁,r₂) ∈ {(2,3),(3,2)}, (j₁,j₂) = ±(1,±1) give κ ≈ 2 Re(ι(1/2)ι(±1/3)) = ∓0.912, times (|P|L/m)² ≈ 1.18 gives ∓1.08; the remaining terms move this to the computed values below.

**Computed** (`kl_dual.py`, `kl_model.py`; Π/(m/L)² at three prime moduli, and the major-arc model Π♯ with r ≤ 300, |t| ≤ 3 at m = 1000003):

| c = u/v | m = 100003 | m = 1000003 | m = 4000037 | model Π♯ (10⁶) | Π/rms(Π) at 4·10⁶ |
|---|---|---|---|---|---|
| −1/6 | +1.500 | +1.450 | +1.420 | +1.500 | +137.5 |
| 1/6 | −1.276 | −1.286 | −1.276 | −1.314 | −123.5 |
| −1/30 | −1.354 | −1.274 | −1.266 | −1.133 | −122.6 |
| −1/12 | −1.150 | −1.075 | −1.054 | −1.118 | −102.0 |
| 1/4 | −0.766 | −0.752 | −0.723 | −0.752 | −70.0 |
| 1/3 | −0.587 | −0.594 | −0.569 | −0.587 | −55.1 |
| 1 | −0.335 | −0.306 | −0.310 | −0.273 | −30.0 |
| −1 | +0.364 | +0.337 | +0.357 | +0.287 | +34.6 |

- rms(Π) = 0.86–0.89 × √(2m)|P|, the value predicted by the multiplicative energy of the primes.
- The kurtosis of Π is 39, 155, 384 at the three moduli; that of E(a) is 2.98–3.01.
- 85–110% of each of the top peaks comes from major × major pairs with r ≤ 40.
- The model P̂♯ has cosine 0.995–1.000 with P̂ on the major arcs r ≤ 100, and 0.955 for r ≤ 300 at m = 10⁶.

**Consequence (heuristic, with computed support).**

  **N(a) = λ + (√m/L²)·Σ_{c small height} κ(c)·Kl₂(ac; m) + (rest).**

- One Kloosterman sum, Kl₂(a/6; m), has correlation −0.083, −0.069, −0.062 with E(a) at the three moduli, against a noise level 1/√φ = 0.003, 0.001, 0.0005. The predicted value is κ√m/(L²·std E), which matches to three digits.
- D §1.2 says the product problem lacks the singular-series structure that N⁻ shows at small heights. That is true of N(a)/λ, where the effect is of relative size m^{−1/2}. In the Kloosterman-dual variable the structure is there and is as sharp as for N⁻.
- By Katz's theorem [RECALLED] the sheaves [×c]^*Kl₂ for distinct c are geometrically non-isomorphic, so the values (Kl₂(ac₁),…,Kl₂(ac_k)) are jointly Sato–Tate equidistributed in a. So the arithmetic part of N(a) is a sum of independent Sato–Tate variables with explicit coefficients, not a deterministic local factor. This is why the product problem has no local obstruction of the Theorem G kind: no a aligns all the Kloosterman terms. (heuristic as a statement about N; the equidistribution is a theorem for fixed k.)
- Proving even one peak, e.g. Σ_{p,q≤m} S(1, pq·6̄; m) ~ κ(m/L)², needs cancellation of full square-root strength in a sum of Kloosterman sums over products of two primes. The trivial bound is m^{5/2}/L² and Cauchy–Schwarz gives m²/L. I see no proof under GRH.

### 1.4 No few-term expansion (computed)

Share of Σ_c (Π(c) − mean)² carried by the K largest entries, i.e. the share of Var_a E(a) explained by the best K Kloosterman terms, against the same statistic in the delta basis (E(a) itself), the character basis (|S(χ)|⁴) and a real Gaussian vector:

| m | K | Kloosterman basis | delta basis | character basis | Gaussian |
|---|---|---|---|---|---|
| 100003 | 10 / 10³ / 10⁴ | 0.047 / 0.228 / 0.544 | 0.002 / 0.083 / 0.438 | 0.003 / 0.116 / 0.523 | 0.002 / 0.084 / 0.439 |
| 1000003 | 10 / 10³ / 10⁴ | 0.030 / 0.136 / 0.232 | 0.0002 / 0.013 / 0.085 | 0.0004 / 0.021 / 0.123 | 0.0002 / 0.013 / 0.084 |
| 4000037 | 10 / 10³ / 10⁴ | 0.024 / 0.107 / 0.168 | 0.0001 / 0.004 / 0.027 | 0.0001 / 0.007 / 0.044 | 0.0001 / 0.004 / 0.027 |

- The Kloosterman basis compresses E(a) far better than the other two (10³ terms carry 11% at m = 4·10⁶, against 0.4–0.7%).
- The share at fixed K decays like C_K/L²: the top term carries 1.26/L², 1.15/L², 1.09/L².

Decomposition by major arcs (`kl_model.py`). Write P̂ = P̂♯ + P̂♭ with P̂♯ the model on the arcs r ≤ R, and correspondingly E = E♯♯ + E♯♭ + E♭♭. Let θ′ = ‖P̂♯‖²/‖P̂‖².

| m | R | θ′ | log R/L | Var share ♯♯ | θ′² | ♯♭ | ♭♭ | corr(E, E♯♯) | Parseval bound for ♭♭, in units of λ |
|---|---|---|---|---|---|---|---|---|---|
| 100003 | 10 | 0.270 | 0.200 | 0.073 | 0.073 | 0.439 | 0.558 | 0.31 | 6.9 |
| 100003 | 100 | 0.501 | 0.400 | 0.249 | 0.251 | 0.604 | 0.321 | 0.53 | 4.7 |
| 1000003 | 10 | 0.217 | 0.167 | 0.047 | 0.047 | 0.370 | 0.623 | 0.25 | 9.2 |
| 1000003 | 40 | 0.331 | 0.267 | 0.104 | 0.109 | 0.500 | 0.478 | 0.36 | 7.9 |
| 1000003 | 100 | 0.402 | 0.333 | 0.158 | 0.162 | 0.554 | 0.404 | 0.44 | 7.0 |
| 1000003 | 300 | 0.495 | 0.413 | 0.246 | 0.245 | 0.603 | 0.321 | 0.53 | 5.9 |

- The law Var(E♯♯)/Var(E) = θ′² holds to 2–3 digits. θ′ grows like log R/log m (the Selberg-sieve sum Σ_{r≤R} μ²(r)/φ(r)), and cannot exceed about 1/2 before the arcs overlap at R ≈ √m.
- All three pieces are Gaussian in a (kurtosis 2.98–3.01). The full Parseval bound is 12.7λ at m = 10⁶ and the ♭♭ bound stays at 5.9λ. Subtracting everything Type I can see saves a constant, never a logarithm.
- So the "second expansion with few terms" asked for in B §6.3 is not hiding in Γ₀(m): with m^{4θ} Kloosterman terms one explains θ² of the variance. Route K cannot prove EOS.

### 1.5 Theorem G in dual form (computed)

For each k, form Ξ_k = inverse Mellin transform of S(χ)²·ε_χ^k (conjugate for k < 0) and record max|Ξ_k|/rms:

| data | k = 0 | k = ±1 | k = 2 (one sign) | other sign | k = ±3 | k = ±4 |
|---|---|---|---|---|---|---|
| S(χ)² at m = 4000037 | 5.1 | 4.0–4.2 | **137.5** | 5.3 | 9.8 / 4.2 | 5.0–5.5 |
| \|S(χ)\|² at m = 4000037 (class a = 1 removed) | **165.6** | 3.2 | 4.4 | 4.4 | — | — |

- The quotient data |S|² are structured in the physical variable (the singular series of N⁻, D §1.2). The product data S² are structured only after one Kl₂ transform. Neither is structured in any other Gauss-sum (hyper-Kloosterman) basis; the mild excess at k = 3 (6.4, 8.8, 9.8 with m) is the bilinear sum Σ_{p,q} e(spq/m) at small-height s (heuristic).
- This is the numerical form of "an argument blind to S² versus |S|² proves a false statement": the two differ by ε_χ², and that factor moves all the arithmetic structure from the a-variable to the dual variable.

### 1.6 A symmetric form of the parity barrier (sketched)

Let ν(n) = Σ_{d|n, d≤R} λ_d be any Type I weight and f = ν − 1_P. Then

  f⋆f(a) = N(a) − 2 Σ_{xy≡a} ν(x) 1_P(y) + Σ_{xy≡a} ν(x)ν(y).

The middle term is the Type I sum of A_a (Fouvry–Shparlinski, R ≤ m^{1/16−ε}) and the last is a Type I × I sum (Weil, R² ≤ m^{1/2−ε}); both have power-saving asymptotics. So **N(a) and f⋆f(a) differ by a computable quantity**, and in the Fourier picture N♭♭ is literally unchanged under P̂♭ ↦ −P̂♭. With ν an upper-bound sieve weight of mass M|P|, f is a non-negative weight on rough composites of mass (M−1)|P|, and EOS is equivalent to a lower bound for the composite × composite count of relative precision (M−1)⁻². This is the symmetric counterpart of A's sequence A\*.

### 1.7 Barrier checklist for Route K

| Barrier | Verdict | Reason |
|---|---|---|
| (1) random pairing-avoiding set | **fail** | Lemmas H and K hold for every set. The peaks of Π use only the major arcs, which a random avoiding set of the same local density shares. |
| (2) deletion of ≈ 1/log m of P | **fail** | Deletion changes P̂ by an L²-small amount and leaves every peak in place. |
| (3) parity | **fail** | The explicit part is Type I × Type I. §1.6: the ♭♭ part is even under the parity flip and carries at least half the L² mass. |
| (4) A\* | **fail** | A\* has the same Type I data, so the same Kloosterman series. |
| (5) Proposition L | **fail** | Unitary change of basis; the Parseval bound on the remainder is still ≥ \|P\|/2. |
| (6) Theorem G | **pass** | The route is built on the factor ε_χ² that distinguishes S² from \|S\|²; §1.5 shows it sees the difference. Passing G alone is not enough. |

Extra hypotheses: none used. What would be needed is cancellation in m⁻² Σ_{h,l minor} P̂(h)P̂(l) S(h,al;m), which is the Type II problem again.

---

## 2. Route TD: a parity-free ladder (prime × GL₂ coefficient)

**Mechanism.** Replace one prime by a coefficient with a functional equation: C(a) = Σ_{p≤m} d(a p̄ mod m), or the box version C♭(a) = Σ_p #{(d,e) ∈ [1,√m]² : de ≡ a p̄}, or r(n), λ_f(n). This is the Titchmarsh divisor problem for the sequence A_a, i.e. Type I information at level 1/2 in summed form. Voronoi/Poisson in (d,e) gives (sketched)

  C♭(a) − |P| = m^{−1/2} Σ_{p∈P} Σ_{k₁,k₂ ≲ √m} Kl₂(a p̄ k₁k₂; m),

a bilinear form in primes × divisor-type coefficients with a Kl₂ kernel. Tools that do not exist for prime × prime become available: bilinear forms with Kloosterman sums (Kowalski–Michel–Sawin), trace functions over primes (Fouvry–Kowalski–Michel), d₃-type exponents of distribution beyond 1/2 for the Type I pieces [all RECALLED].

**What I checked (sketched).**
- Sieve bounds give 0 < c₁ ≤ C(a)/(|P| log m) ≤ c₂ unconditionally (lower bound from level m^{1/16}; upper bound from the two-dimensional sieve with Weil, as in A §6). The asymptotic is open.
- The Parseval deficit is again exactly one log: the unitary bound is m against a main term m/L for C♭, and mL against m for C.
- Needed: a saving of √m·L over the trivial bound in the bilinear Kl₂ form. KMS-type bounds save at most m^{1/4} here, and Lemma 5.2 of route A caps generic-coefficient bounds at the square root of one range. After Vaughan in p, the Type I part is within reach of d₃-type results for short u ≤ m^{1/23}-ish; the Type II part needs Σ_v β_v Σ_K d♭(K) Kl₂(aK v̄) with saving m^{1/2+δ}. Same wall.

**Barrier checklist.**

| Barrier | Verdict | Reason |
|---|---|---|
| (1) random set | not applicable to TD; **fail** for EOS | TD is a statement about one prime variable. |
| (2) deletion | **pass for TD, irrelevant for EOS** | Deleting R_a removes primes p with d(a p̄ mod m) = 2, a change of O(\|P\|/L) in C(a); TD does not detect it, which is why TD ⇏ EOS. |
| (3) parity | **pass for TD** by design | d(n) is not parity-sensitive. For EOS: fail. |
| (4) A\* | **fail for EOS** | A\* has the Type I data of A_a to every level below √m, so TD holds for A\* as well. |
| (5) Proposition L | **fail** as it stands | One-log deficit against Parseval. |
| (6) Theorem G | **pass** | Uses Kloosterman sums over primes, the input G says is necessary. |

- *Extra hypotheses.* None for the realistic target. A full asymptotic would need a bilinear Kl₂ bound beyond GRH.
- *First lemma.* For prime m, improve the level of distribution of A_a from m^{1/16} on average over well-factorable moduli by sheaf-theoretic bilinear bounds for e(c x̄/m), and feed Greaves' sieve to lower r in "a p̄ mod m ∈ P_r" (record r = 5 per `lit/02` §1.3, unverified there). Overlaps D §4.2 in aim; the tools differ (prime m, not smooth m).
- *Probability.* New almost-prime result for prime m: about 15%. TD asymptotic under GRH: about 2%. EOS: 0.

---

## 3. Route FE: product = Kloosterman transform of quotient

**Mechanism.** For a sequence with a functional equation the two problems are tied by the root number. With T(χ) = Σ_{n≤√m} χ(n) (self-dual length) one has T(χ) ≈ ε_χ·conj T̃(χ), hence T⁴ ≈ ε_χ²·T²·conj(T̃²) and

  D₄(a) − main ≈ m^{−1/2} Σ_c Kl₂(a c̄; m)·(Q(c) − mean), Q(c) = #{n₁n₂ ≡ c·k₁k₂, all ≤ √m}.

The quotient count Q is an additive shifted-convolution problem (n₁n₂ − c₀k₁k₂ = jm). For c of small height it has a second spectral expansion with few terms, over level-1 forms with m entering through λ_j(m): this is how Young and Blomer–Fouvry–Kowalski–Michel–Milićević evaluate Σ_χ |L(1/2,χ)|⁴ [RECALLED]. So over Z there *is* a few-term second expansion, but for the quotient-type (|·|²) problem and only at small height. For primes there is no functional equation for S(χ) (the logarithmic derivative kills the root number); §1.3 is the shadow of this structure that survives, through the major arcs.

**Assessment (heuristic).**
- The peaks of Q at small heights carry the whole logarithmic excess of the eighth moment of T, and they are explicit. Subtracting them leaves a remainder whose ℓ² norm is still too large by one log (same count as in §1.4).
- Directly, the balanced toy needs a saving of √m in Σ_{n₁,n₂,k₃,k₄ ≤ √m} Kl₂(a k₃k₄ \overline{n₁n₂}); with all four variables at Pólya–Vinogradov length the best bilinear bounds save about m^{1/8} [RECALLED exponents, unverified]. Unbalanced boxes (e.g. m^{3/4}, m^{3/4}, m^{1/4}, m^{1/4}) sit exactly at the Weil threshold and need only o(1) cancellation in an m-term Kloosterman sum over Farey fractions; that version may be provable and is the right first test.
- Analogy worth recording: EOS is the split-torus analogue of "least prime in a progression ≤ m²". Under GRH the least prime is ≤ (φ log m)², the same two-log miss at the same critical volume.

**Barrier checklist** (for the toy; for EOS every item fails because the primes have no functional equation).

| Barrier | Verdict | Reason |
|---|---|---|
| (1) random set, (2) deletion, (3) parity, (4) A\* | not applicable to the toy | Smooth variables, complete Type I data. |
| (5) Proposition L | **open** | The point of the toy is whether a one-log Parseval deficit can be beaten anywhere. |
| (6) Theorem G | **pass** | The method is the passage between T⁴ and \|T\|⁴ through ε_χ². |

- *Extra hypotheses.* None.
- *First lemma.* The unbalanced toy: #{n₁n₂n₃n₄ ≡ a, n₁,n₂ ≤ m^{3/4}, n₃,n₄ ≤ m^{1/4}} ~ m²/φ for prime m, via Σ_{r,s≤√m} d♭(r)d♭(s) Kl₂(a r s̄) = o(m).
- *Probability.* Unbalanced toy: about 30%. Balanced toy D₄: 3–5%. A mechanism transferable to primes: under 0.5%.

---

## 4. Considered and discarded

- **Rank-two trace formula.** Σ_χ χ̄(a)(L′/L)(s₁,χ)(L′/L)(s₂,χ) is the Eisenstein × Eisenstein term of the trace formula of Γ(m)\H × Γ(m)\H twisted by Σ_x (diag(x,x̄), diag(a x̄, ā x)). The cuspidal side has ≍ m³ forms per factor and the geometric side is a convolution of two class-number sums. Dead by counting. (sketched)
- **Salié sums / half-integral weight.** Inserting (x/m) turns the kernel into a Salié sum with an explicit evaluation, but by Hasse–Davenport this is the substitution χ ↦ χ², a unitary change of basis. (proved as a statement about the kernel)
- **Reciprocity (Conrey–Young–Bettin type).** The twisted second moment has a reciprocity m ↔ a because n₁ − a n₂ = km can be read modulo a. The product equation pq − km = a has no second modulus to switch to. (heuristic)
- **Kuznetsov over a sifting modulus.** In p·d·e − km = a every candidate modulus (pd, e, k) meets a single fixed number m in the numerator; reciprocity returns e(c p̄/m). Agrees with D §4.9.

## 5. What was established

- **Proved:** Lemma H; Lemma K; the correction to D §4.1(iii).
- **Computed:** the identity of Lemma K; the peaks of Π and their m-stability; the correlation of E(a) with single Kloosterman sums; the θ′² law; the basis scan of §1.5.
- **Heuristic:** the major-arc formula for κ(u/v); the reading via Katz independence; the assessments in §2 and §3.
- **Not established:** any improvement toward EOS. The best single takeaway for the team is the dictionary "product problem = Kl₂-transform; arithmetic structure of N(a) lives at small heights of the dual variable, with amplitude √m/log² m", and the quantitative statement that this structure never accounts for more than a bounded fraction of the fluctuation.
