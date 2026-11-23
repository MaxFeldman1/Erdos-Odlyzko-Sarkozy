# Route B: transferring the function-field proof of EOS

Written 2026-11-22. Standing hypothesis: GRH for Dirichlet L-functions. Extra hypotheses are flagged where used.

**Provenance / status tags.**
- **[READ]**: statement read this session in the source. Xie arXiv:2510.17612v3 was read in full (13 pp.). Sawin arXiv:2102.09730 (= Acta Math. 233 (2024) 285–418) was read from the TeX source: introduction, §1.1 "Precise result", §1.3 "Strategy of proof", and the subsection "Sums of Dirichlet convolutions of von Mangoldt functions" (arXiv labels `vm-c-1`, `vm-c-2`; the latter is what Xie cites as Lemma 9.14 of the published version). Banks arXiv:2609.37434: introduction.
- **[READ-2nd]**: as quoted by one of the above; original not opened (Katz IMRN 2013, Katz *Convolution and Equidistribution*, Keating–Rudnick).
- **[DERIVED, proved]**, **[DERIVED, sketched]**, **[DERIVED, heuristic]**: my own arguments here. Not refereed.
- **[UNVERIFIED]**: not checked.

Notation as in `00-setup.md` and `lit/03`: G = (Z/mZ)^*, φ = φ(m), S_w(χ) = Σ Λ(n)χ(n)w(n/X), w ∈ C_c^∞((1/2,1)), w ≥ 0, W = Mellin transform of w, N_w(a) = (1/φ)Σ_χ χ̄(a)S_w(χ)², E(a) = the χ ≠ χ0 part.

---

## 0. Summary and verdict

1. **Function-field statement.** There are two theorems, in different regimes, with different mechanisms.
   - Xie: n = deg f fixed, q → ∞ (q ≥ n^{23n}). One-dimensional Katz Mellin-transform argument. Saves q^{-1/2}.
   - Sawin: q > 1024e² ≈ 7567 fixed, n → ∞. Cohomology of the (n-dimensional) fibres of the product map. Saves q^{-n/2}·(32e)^n, i.e. a genuine power of the modulus.
   - Neither covers small fixed q (e.g. q = 2, 3) with n → ∞. I believe that case is open **[UNVERIFIED]**. It is the faithful analogue of the integer problem.
2. **Mechanism.** In both proofs the cancellation across characters is *not* deduced from RH for the individual L(s,χ). It comes from the fact that the twisted family sum is itself (a) a Frobenius trace on a geometric object indexed by the class a, to which Deligne's RH is applied a second time, and (b) that object has small complexity (rank / Betti numbers) compared with √q to the relevant power. Monodromy (Katz: G_geom = G_arith = GL(n−1)) enters in Xie's proof only to exclude *punctual* summands, i.e. exact conspiracies.
3. **What the dictionary says.** deg f = n ↔ log m (number of zeros per L-function), |f| = q^n ↔ m, and the barrier factor is n (Parseval) or n² (Weil), exactly as log m and log² m over Z. Xie's regime is "barrier factor bounded, saving → ∞". Over Z the analogue of Xie's subfamily of q − 1 twists has size |μ(Q)| = 2. Sawin's regime needs √q to beat an absolute constant (32e) per unit of degree; over Z the corresponding base is fixed (heuristically q ↔ e) and cannot be made large.
4. **Barriers.** The redacted-primes and random-pairing sets do not defeat the function-field proofs because those proofs never pass through bounds on |S(χ)|. They use an exact algebraic identity (the count is a trace function; the L-function is a characteristic polynomial varying in a sheaf) that a redacted set does not satisfy. The missing structure over Z is exactly this: a second, independent spectral expansion of N(a) with few terms and a weight (purity) dichotomy.
5. **Verdict: (b).** The function-field method does not transfer. No number-field object is known that plays the role of the sheaf on the torus of residue classes. All "honest" L-function substitutes (Dedekind zeta of Q(ζ_m), Chebotarev in a compositum, Rankin–Selberg, Hecke/automorphic GRH) collapse back to GRH for Dirichlet L-functions and give nothing new (§4).
6. **Cleanest conditional reduction (recorded, but it is not weaker than EOS).** GRH + a *twisted ratios-type hypothesis* TR(δ) (§5.1) ⇒ EOS, with p, q ≤ m^{1−δ/3}. The reduction is proved. TR(δ) is the literal integer analogue of Sawin's theorem; it is a new hypothesis of standard shape (CFZ-recipe type), and it is essentially "EOS with a power saving, in analytic-continuation language". It does not reduce EOS to anything independent of EOS.
7. **Partial results that transfer.** (i) Xie's coset decomposition is an exact identity over Z (§5.2) and gives, under GRH, EOS in every quotient of G of order ≤ c·m/log² m (proved, easy). (ii) A precise statement of why leading-order Katz–Sarnak heuristics are insufficient: the EOS main term has relative size 1/log m and so sits at the level of the first lower-order term of a twisted 2-level density (§4.5).

---

## 1. The function-field statements [READ]

Setting: k = F_q, f ∈ k[X] squarefree of degree n ≥ 2 (Sawin writes g, of degree m), B = k[X]/(f), B^× of size ≈ q^n. Λ is the polynomial von Mangoldt function. Monic polynomials of degree exactly n are in bijection with residues mod f, so "primes of degree n" ↔ "primes ≤ m", density 1/n ↔ 1/log m.

### 1.1 Xie (arXiv:2510.17612; Math. Z. 313 (2026) no. 64)

- **Theorem 1.1.** For n ≥ 2 there is Q(n) (one may take n^{23n}) such that for q ≥ Q(n) and every squarefree f of degree n, every a ∈ B^× is f1f2 mod f with f1, f2 monic irreducible of degree ≤ n. The same holds with deg f1 = r, deg f2 = 2n − r for any fixed 1 ≤ r < 2n.
- **Range.** q large in terms of n: log q ≥ 23 n log n. Equivalently n ≲ (log|f| / log log|f|)^{1/2}. Fixed degree, large field.
- **The barrier appears verbatim** (Xie §2). With R(a,n) the non-principal part and M ≈ q^n the main term:
  - Weil pointwise: |R(a,n)| ≤ n² q^n. "Insufficient."
  - Fourth moment + Markov: the exceptional set at d = n has size ≪ n⁴. This is the analogue of the O(log^5 q) (EOS87) and O(log³ q) (Banks–Shparlinski) exceptional sets.
  - So the loss is a power of n = number of zeros of L(χ,T), with no dependence on q. This is the log-power barrier.
- **Error obtained:** |R(a,n)| ≤ C(n) q^{n−1/2} + 2(n+1)n⁴q^{n−1}, C(n) = (2n)^{2n+3}e^{π√(4n/3)}.

### 1.2 Sawin (Acta Math. 233 (2024); arXiv:2102.09730)

- **Main theorem (Thm 1.6 in arXiv numbering, `squarefree-bound-precise`).** For g squarefree of degree m, a ∈ (F_q[t]/g)^×, n ≥ m, and any representation ρ of S_n with associated factorization function F_ρ:
  |Σ_{f ∈ M_n, f ≡ a (g)} F_ρ(f) − (1/φ(g)) Σ_{(f,g)=1} F_ρ(f)| ≤ 2(C_1(ρ) + C_2(ρ)√q) q^{(n−m)/2},
  with C_1, C_2 explicit, independent of q.
- **Binary case (`vm-c-1`, `vm-c-2`; "Lemma 9.14").** For F_{n1,n2} = Λ|_{deg n1} * Λ|_{deg n2}, n = n1 + n2:
  error ≤ binom(n; n1, n2) · (2^{m−1} binom(n+2m+1, 3m+1) q^{(n−m)/2} + 2^{m−2} binom(n+2m−3, 3m−4) q^{(n+1−m)/2}).
  At n1 = n2 = m (the EOS case) this is O(binom(2m,m)(8e√q)^m) = O((32e√q)^m) against a main term ≈ q^m (Xie's reading, which I checked against `vm-c-2` with c = 0, θ = 1/2, ω = 2).
- **Range.** Any n, but useful only when q > (32e)² = 1024e² ≈ 7567; then error/main ≤ (32e/√q)^m → 0 as m → ∞. The saving is |g|^{−1/2 + log(32e)/log q}: a power of the modulus, tending to square-root as q → ∞.
- **Not covered:** fixed q ≤ 7566 with degree → ∞. There the bound is worse than trivial.

### 1.3 Banks (arXiv:2609.37434), §1.1 [READ]

Only a pointer: "Over function fields the analogous problem has been settled for large fields", citing Sawin and Xie as above. Banks' diagnosis of the integer barrier (loss φ(q)/π(q) from the sum over characters) is the same as Xie's n² loss.

---

## 2. The mechanisms, and RH versus monodromy

### 2.1 Xie's proof (large q) [READ; the interpretation in the last bullets is DERIVED, sketched]

1. **RH as an identity, not a bound.** For "totally ramified" χ, L(χ, T/√q) = det(1 − Tθ_χ) with θ_χ ∈ U(n−1), and Ψ(d,χ) = Σ_{deg g = d}Λ(g)χ(g) = −q^{d/2} Tr(θ_χ^d) for every d. So
   R(a,n) = (1/|B^×|) Σ_χ χ(a^{-1}) Σ_{i,j ≤ n} q^{(i+j)/2} Tr(θ_χ^i) Tr(θ_χ^j) + (few bad χ).
2. **Reduce to irreducible representations.** Tr(θ^i)Tr(θ^j) = Σ_{μ ⊢ i+j} χ_{(i,j)}(μ) s_μ(θ) (Frobenius formula). Each s_μ is the character of a nontrivial irreducible representation Λ_μ of U(n−1).
3. **Sum over a one-parameter subfamily only.** Characters of B^× are partitioned into classes {χ·(ρ∘Norm_{B/k}) : ρ ∈ \hat{k^×}}, each of size ≈ q − 1. Xie bounds each inner sum Σ_ρ ρ(Norm c) Tr Λ(θ_{χρ_Norm}) and sums over classes trivially. The characters ρ∘Norm are the power-residue symbols g ↦ ρ(Res(g,f)); their number is |μ(k)| = q − 1.
4. **The inner sum is a stalk trace (Mellin inversion).** Katz attaches to χ the perverse sheaf N(χ) = [f]_*(i_f^* L_χ)(1/2)[1] on G_m, whose Mellin transform at ρ is θ_{χρ_Norm}. Under the Tannakian equivalence ⟨N⟩ ≃ Rep(G_arith), the representation Λ corresponds to an object M_Λ with
   Tr(Λ(θ_{χρ})) = Σ_{s ∈ k^×} ρ(s) Tr(Frob_s | M_Λ) (Lefschetz + vanishing of H^i_c, i ≠ 0),
   hence (1/(q−1)) Σ_ρ ρ(c) Tr Λ(θ_{χρ}) = Tr(Frob_{c^{-1}} | M_Λ), up to the O(n) bad ρ.
5. **Deligne on a curve.** M_Λ is perverse, pure of weight 0, on the curve G_m. If it is *not punctual*, it is j_{!*}F[1] with F lisse of weight −1, so |Tr(Frob_c | M_Λ)| ≤ gen.rank(M_Λ)/√q ≤ (a+b)n^{a+b}/√q.
6. **Monodromy is used exactly once:** Katz's theorem G_geom,N = G_arith,N = GL(n−1) (IMRN 2013, Thm 5.1 [READ-2nd]) implies M_Λ is irreducible and non-punctual for nontrivial Λ. A punctual M_Λ = α^{deg} ⊗ δ_{t0} would have Mellin transform ρ ↦ α ρ(t0), i.e. Tr Λ(θ_{χρ}) = αρ(t0) for all ρ: an *exact* alignment of the "zero statistic" with the twist ρ(c) at c = t0^{-1}.

**Roles.**
- *Weil's RH for L(χ,T)*: gives unitarity of θ_χ, hence the n² bound and nothing more.
- *Rationality + the sheaf structure in χ*: turns the family {θ_χρ}_ρ into the Mellin transform of one geometric object. This is what makes the sum over ρ computable.
- *Deligne's RH (Weil II), second application*: on M_Λ over G_m. This is what gives q^{-1/2}.
- *Monodromy (big image)*: rules out the punctual case. Combined with purity it yields a **dichotomy**: either an exact conspiracy (punctual summand, trace of size 1) or square-root cancellation (trace ≤ rank/√q). Nothing in between is possible, because weights are integers. [DERIVED, sketched: this is my reading of Xie's Prop. 3.3 proof, pp. 8–9.]

**What limits the range:** the rank of M_Λ, ≤ 2n·n^{2n} for the representations needed (degree i + j up to 2n in a group of rank n − 1: far outside the stable range j ≤ N of random-matrix theory). One needs √q ≫ n^{O(n)}.

### 2.2 Sawin's proof (fixed large q, n → ∞) [READ, strategy section]

1. **The count is a point count.** Let X = (A^1[1/g])^n → T = Res(G_m) (torus of residue classes, dim m), (a_1,…,a_n) ↦ Π(t − a_i) mod g. Σ_{f ≡ a} F_ρ(f) = Σ_i (−1)^i Tr(Frob_q | H^i_c(X_a, N_ρ)) for an S_n-equivariant coefficient sheaf N_ρ. The fibre X_a has dimension n − m.
2. **Λ is decomposed, not bounded.** Λ|_{M_n} = Σ_{i=0}^{n−1} (−1)^i F_{∧^i std} (Sawin, Lemma `mangoldt-alternating`), and Dirichlet convolution corresponds to induction from S_{n1} × S_{n2} (`convolution-lemma`). The signs are discarded: each F_ρ is bounded separately. This is the geometric counterpart of a combinatorial (Vaughan/Heath-Brown-type) identity in which *every* piece, Type I or Type II, has square-root cancellation in progressions.
3. **Only two cohomology groups depend on a.** Via an explicit compactification with product-like local models, vanishing cycles and perversity: H^i_c(X_a) is independent of a for i > n − m + 1 (this constant part is the main term), and only degrees n − m and n − m + 1 vary.
4. **Deligne's RH** bounds Frobenius eigenvalues on those two groups by q^{(n−m)/2} and q^{(n−m+1)/2}.
5. **Betti numbers** of the varying part are bounded by C_1(ρ) (Euler characteristic computation) and C_2(ρ) (characteristic cycle + Massey's bound). For the binary von Mangoldt problem these are ≤ (32e)^m-type quantities, independent of q.

**Roles.** No monodromy computation appears. The input is Deligne's RH on the *fibre* X_a plus a Betti bound. In character language (Sawin, strategy section): the contribution of χ is Tr(Diag(q^{-α_i}) | V_ρ), so the theorem says
(1/φ) Σ_{χ ≠ χ0} χ̄(a) Tr(V_ρ(θ_χ)) q^{n/2} = (sum of ≤ C^n numbers of size ≤ q^{(n−m+1)/2}).
The left side has ≈ q^m terms of size dim(V_ρ)·q^{n/2}/q^m. The right side is a *different* spectral expansion of the same number, with exponentially (in m·log q) fewer terms.

### 2.3 The two expansions [DERIVED, sketched]

Over F_q[t] the binary count has two spectral expansions.
- **(A) Explicit formula in the degree variable.** Fixed q, generating function in u = q^{-s}: Σ_d N_d(a)u^d = (1/φ)Σ_χ χ̄(a)(uL'/L(u,χ))². Poles at the ≈ q^n·n inverse zeros of all L(u,χ). Under RH each has modulus q^{1/2}. This is the exact analogue of the integer explicit formula under GRH, and it yields exactly the n² loss.
- **(B) Lefschetz in the field variable.** Fixed (n, f, a), base change F_q → F_{q^r}: N^{(r)}(a) = Σ ± Tr(Frob^r | H^*_c(X_a)). At most C^n eigenvalues, with weights ≤ n − m + 1 on the non-constant part.

GRH over Z is the analogue of RH in (A). The function-field proofs are RH in (B). Expansion (B) has no integer analogue: Z has no constant field to extend, and N(a) is not known to be a coefficient of any L-function other than through (A).

---

## 3. Dictionary and the large-q limit

| Function field | Integers | Comment |
|---|---|---|
| f squarefree, deg n, \|f\| = q^n | modulus m | |
| monic polys of degree n ↔ residues mod f | integers in [1,m] ↔ residues mod m | both bijections |
| primes of degree n: density 1/n | primes ≤ m: density 1/log m | Parseval loss n ↔ log m |
| L(χ,T) has n − 1 zeros | ≈ (1/2π) log m zeros of L(s,χ) per unit height | |
| Weil: \|Ψ(n,χ)\| ≤ (n−1)q^{n/2}; \|R\| ≤ n²q^n | GRH: \|S_w(χ)\| ≪ √X log m; \|E\| ≪ X log² m | identical barrier |
| exceptional set ≪ n⁴ (Xie (2.3)) | ≪ log³ m (Banks–Shparlinski) | |
| θ_χ ∈ U(n−1), exact | zeros on the line, infinitely many, no finite matrix | rationality is lost |
| family χ ↦ θ_χ is a sheaf on the dual torus (Mellin transform) | no known structure on χ ↦ zeros(L(s,χ)) | **missing** |
| twists ρ∘Norm, ρ ∈ \hat{F_q^×}: q − 1 of them | power-residue twists by μ(Q) = {±1}: the Jacobi symbol (·/m) only | subfamily of size 2 |
| base change F_q → F_{q^r} | none | **missing** |
| X_a → T and H^*_c(X_a) | none | **missing** |
| "degree ≤ n" is an affine space (algebraic) | [1,m] is not algebraic mod m | source of the Kloosterman 3/4 barrier too |

**What replaces "q → ∞ with n fixed"?** Nothing. [DERIVED, heuristic but I think decisive.]
- In that limit the barrier factor n² is *bounded* while the available saving √q → ∞. The integer analogue would be "log m bounded while m → ∞".
- Xie's quantitative requirement √q ≥ n^{O(n)} reads, with family size F = q^n, as: equidistribution error F^{-1/(2n)}·n^{2n} must beat 1/n². Transposed to N ≈ log m zeros and F = m, the error term is m^{-1/(2 log m)}(log m)^{2 log m} = e^{-1/2}(log m)^{2 log m} ≫ 1. The method is vacuous at "q = e".
- Sawin's requirement is (32e)² < q. Transposed: the saving is m^{-1/2 + log(32e)/log q}, and the exponent is positive unless q > 7567. With q ↔ e the bound is worse than trivial. The identification q ↔ e is only a heuristic normalisation (there is no canonical q for Z), but no choice makes "q" a free large parameter.
- Concretely in Xie's proof: the subfamily over which cancellation is proved consists of twists by characters of the roots of unity of the base. Over Q that is {1, (·/m)}: two characters. A sum of two terms cannot exhibit a 1/log m saving. Passing to Q(ζ_h) to gain h-th power residue symbols changes the problem (prime ideals of a field of degree φ(h)) and reintroduces the same barrier there.
- Vertical analogues (the cyclotomic Z_p-tower as "constant field extension", Iwasawa theory) give p-adic characteristic polynomials, not archimedean spectral data with weights. I see no way to use them. [heuristic]

**So the function-field proof (Xie's version) works only in the large-q limit, and Sawin's version works only above an absolute threshold for q. Neither regime has an integer counterpart.** Moreover the honest analogue of EOS over Z, namely q fixed and small, n → ∞, is not proved over function fields either, as far as I can tell [UNVERIFIED]. A proof of F_2[t]-EOS (or F_3) for large degree would be real evidence that a transferable mechanism exists; Sawin's method would need Betti bounds below √q^{m}, which fail for q ≤ 7566 by his own estimates.

---

## 4. Candidate number-field substitutes, one by one

All claims in this section are [DERIVED]; status given per item.

### 4.1 GRH for the Dedekind zeta function of Q(ζ_m) or subfields — nothing new [proved, trivial]
ζ_{Q(ζ_m)}(s) = Π_χ L(s,χ*) over the primitive characters inducing the χ mod m. Its GRH is equivalent to GRH for those Dirichlet L-functions. Subfields correspond to subgroups of characters. No new information.

### 4.2 Chebotarev for the pair (Frob_p, Frob_q) — nothing new [proved, trivial]
The condition Frob_p·Frob_q = a is membership of (Frob_p, Frob_q) in D_a = {(g,h) ∈ G×G : gh = a}. The Fourier transform of 1_{D_a} on G×G is supported on the diagonal: \hat{1_{D_a}}(χ1,χ2) = φ·χ̄1(a)·1[χ1 = χ2]. So the count is (1/φ)Σ_χ χ̄(a)S(χ)², the original formula. A pair (p,q) of rational primes is not the Frobenius of a prime in any field, so effective Chebotarev (which counts single primes) does not apply; a compositum K·K' with group G×G would see (Frob_p|_K, Frob_p|_{K'}) for one prime p, a different problem.

### 4.3 Rankin–Selberg, Hecke and automorphic L-functions — nothing new [sketched]
- L(s, χ×χ) = L(s,χ²) (up to bad factors). It encodes Σ_p χ(p)², the diagonal p = q, not S(χ)².
- The Dirichlet series of the binary problem is (L'/L)(s,χ)², or two-variable (L'/L)(s1,χ)(L'/L)(s2,χ). It is not an L-function (no Euler product); its singularities are those of L'/L(s,χ). Everything attached to the abelian extension Q(ζ_m)/Q is built from Dirichlet L-functions.
- The Kloosterman reformulation N(a) = (1/m)Σ_h \hat{1_P}(h) Σ_p e(ha p̄/m) involves e(c p̄/m) summed over primes. Expanding e(c x̄/m) in multiplicative characters gives Gauss sums times S(χ̄): Dirichlet L-functions again (lit/02 §1.1). No GL_2 object appears, so automorphic GRH has nothing to act on. [heuristic that no cleverer route exists]
- Conclusion: assuming GRH for Hecke or automorphic L-functions does not help by any route I can find. The obstruction is not the class of L-functions; it is that every such route is *linear in the family* and ends at Σ_χ χ̄(a)S(χ)².

### 4.4 Explicit formula: what is needed from the zeros [sketched; agrees with lit/03 §2.2]
With Z_χ(X) = Σ_γ W(1/2 + iγ)X^{iγ}: E(a) = (X/φ) Σ_{χ≠χ0} χ̄(a) Z_χ(X)² + small. EOS at scale X ≤ m needs
(1/φ)|Σ_{χ≠χ0} χ̄(a)Z_χ(X)²| ≤ (1 − δ)W(1)²·X/φ ≍ m/φ = O(log log m),
while (1/φ)Σ_χ |Z_χ|² ≍ log X exactly. So the required bias of the phases is tiny: EOS fails for a only if
avg_χ Re(χ̄(a) Z_χ²)/avg_χ |Z_χ|² ≤ −(1+o(1)) (m/φ)/log m.
**A conspiracy of relative strength 1/log m suffices to kill a class.** Any hypothesis strong enough for EOS must control the mean phase to precision o(1/log m).

### 4.5 Katz–Sarnak / random-matrix prediction [heuristic]
- *Prediction.* Model θ_χ as Haar unitary, independent of χ(a) (this is what Katz's Mellin equidistribution theorem proves over F_q as q → ∞: for c ≠ 1 the twisted averages of Tr Λ(θ) tend to 0). Then E(a) is a sum of φ mean-zero terms: E(a) ≈ X log X/√φ, uniformly in a up to √(log φ). This is square-root cancellation over the family, matches Sawin's theorem (error q^{(n−m)/2}C^n with n = 2m), and predicts EOS down to X ≈ √m (log m)^{3/2} (as in lit/03 §1).
- *Why leading-order Katz–Sarnak is not enough.* The twisted 2-level statistic (1/φ)Σ_χ χ̄(a)Z_χ² has "variance scale" log m, and the K–S density conjecture (with its usual o(1) relative error) predicts only that it is o(log m). EOS needs O(1). **The EOS main term X²/φ has relative size ≈ 1/log m compared with the diagonal X log X; it lives at the level of the first lower-order term.** A density conjecture is useful here only with relative error o(1/log m), uniformly in a, for test functions with Fourier support reaching 1 in each variable (total support 2; Hughes–Rudnick-type theorems stop at total support < 2, and for the twisted statistic the trivially computable range is X < √m). That is ratios-conjecture precision; see §5.1.
- *Function-field mirror.* Xie's theorem is precisely "equidistribution with error q^{-1/2}n^{O(n)} beats the lower-order term 1/n²".

### 4.6 Moments in a, and families [sketched]
- L² in a: blocked (lit/02 §2.2, lit/03 §0.2).
- L⁴ in a: Σ_a E(a)⁴ < μ⁴ would give EOS, and it is an a-free statement about the family (phases of S(χ)² along relations χ1χ2 = χ3χ4). The trivial bound is ≈ |P|⁴ and one needs |P|⁴/log⁴ m; the random model gives 3φμ², smaller than needed by a factor ≈ m/log⁴ m. So there is an enormous margin, but no tool: on the physical side it is the 8-prime count #{p1q1 ≡ p2q2 ≡ p3q3 ≡ p4q4} to relative precision 1/φ (lit/02 §2.2). Over F_q[t] the analogue follows from Sawin's pointwise bound, not conversely.
- Varying m: this is the integer analogue of varying f, and is what Friedlander–Kurlberg–Shparlinski do; it gives averages over m, not a single modulus. In function fields the cancellation is for a *single* f; the family is the characters (and the constant field), not the moduli.
- "Algebraic" families mod a prime m = p: a ↦ N(a) is the multiplicative convolution 1_P * 1_P on F_p^×, and 1_P (primes in [1,p]) is not a trace function of bounded conductor. The Fouvry–Kowalski–Michel theory handles Σ_p K(p) for algebraic K, not convolutions of two prime indicators cut by an archimedean interval. [heuristic that nothing can be extracted]

---

## 5. What does transfer

### 5.1 A conditional reduction: twisted ratios hypothesis ⇒ EOS [DERIVED; reduction proved modulo standard GRH facts]

For (a,m) = 1 let a_0 ∈ [1,m) be the least positive residue, and for Re s_j > 1/2 (under GRH the following is holomorphic there) define
R_a(s1,s2) = (1/φ(m)) Σ_{χ≠χ0} χ̄(a) (L'/L)(s1,χ)(L'/L)(s2,χ),  Δ_a(s1,s2) = Σ_{n1n2 = a_0} Λ(n1)Λ(n2) n1^{-s1} n2^{-s2}.

> **Hypothesis TR(δ)** (twisted ratios, binary logarithmic-derivative form). There are A ≥ 0 and m_0 such that for all m ≥ m_0, all (a,m) = 1, and all s1, s2 with Re s1 = Re s2 = 1/2 + δ/4:
> |R_a(s1,s2) − Δ_a(s1,s2)| ≤ m^{-δ} (1+|s1|)^A (1+|s2|)^A.

**Status of the hypothesis.** New as stated (I did not find it in the literature **[UNVERIFIED that it is absent]**). It is of standard shape: it is what the Conrey–Farmer–Zirnbauer recipe predicts (orthogonality χ̄(a)χ(n1n2) ↦ 1[n1n2 = a_0], all other terms discarded with a power-saving error), here for a twist a as large as the conductor. Heuristically it should hold for every δ < 1/2 (insert Sawin-type error (X1X2/m)^{1/2+ε} dyadically; the Mellin integral converges for Re s > 1/2). It is false for δ > 2/3: by the Proposition's proof it would give representations with p, q ≤ m^{(1−δ)/(1−δ/2)+ε} < √m for every a, which is impossible by counting. Its function-field analogue is a theorem for q large in terms of δ (sum `vm-c-1` over n1, n2; the binomial factors force q^{δ/4} > absolute constant) [sketched]. It is **stronger than EOS**: by Mellin inversion it is essentially equivalent to "E_w(a; X1, X2) ≪ (X1X2)^{1/2+δ/4} m^{-δ} for all boxes", a Montgomery-type conjecture for products of two primes at level 1/2. So this is a reformulation in standard language rather than a reduction to something independent.

**Proposition.** Assume GRH and TR(δ) for some δ ∈ (0, 1/2). Then for all large m and all (a,m) = 1 there are primes p, q ∈ (X/2, X] with pq ≡ a (mod m), for every X with m^{1−δ/3} ≤ X ≤ m. In particular EOS holds.

*Proof.*
1. For χ ≠ χ0 and c = 2: S_w(χ) = (1/2πi)∫_{(c)} −(L'/L)(s,χ) W(s) X^s ds. W is entire with W(σ+it) ≪_{k} (1+|t|)^{-k} uniformly for σ in compacts.
2. Under GRH, L(s,χ) has no zeros in Re s > 1/2 (the Euler factors at p | m have zeros only on Re s = 0), and for Re s = 1/2 + η, 0 < η ≤ 1: (L'/L)(s,χ) ≪ η^{-1} log(m(|t|+2)) + Σ_{p|m} log p/(p^{1/2} − 1) ≪_η log(m(|t|+2)) (partial-fraction formula for the primitive character, Montgomery–Vaughan Lemma 12.1-type; the second term accounts for imprimitivity). Hence the contour can be moved to Re s = 1/2 + η, η = δ/4, with no residues.
3. Squaring and averaging: E(a) = (2πi)^{-2} ∬_{Re s_j = 1/2+η} R_a(s1,s2) W(s1)W(s2) X^{s1+s2} ds1 ds2.
4. Insert R_a = Δ_a + (R_a − Δ_a). By Mellin inversion the Δ_a part equals Σ_{n1n2 = a_0} Λ(n1)Λ(n2)w(n1/X)w(n2/X) ≥ 0. By TR(δ) and the decay of W, the remainder is ≤ C_{w,A} m^{-δ} X^{1+2η}. So **E(a) ≥ −C m^{-δ}X^{1+δ/2}.**
5. Main term: S_w(χ0) = W(1)X + O(√X log² X + ω(m) log X) under RH, so S_w(χ0)²/φ ≥ W(1)²X²/(2φ) for large m.
6. N_w(a) ≥ W(1)²X²/(2m) − C m^{-δ}X^{1+δ/2} > 0 as soon as X^{1−δ/2} > C' m^{1−δ}. For X ≥ m^{1−δ/3}: X^{1−δ/2} ≥ m^{1 − 5δ/6 + δ²/6} > C' m^{1−δ} for large m.
7. Prime powers: pairs (n1,n2) counted by N_w with n1 a proper prime power number ≤ √X (choices of n1) × 1 (n2 ≤ X ≤ m is determined by its residue), total weight ≤ 2√X log² X = o(X²/m) since X ≥ m^{5/6}. So some pair has both entries prime. ∎

**Remarks.**
- Only a lower bound for E(a) is needed, and the diagonal term Δ_a has the right sign. One could weaken TR(δ) to the one-sided integrated statement of step 4.
- TR at distance 1/log m from the critical line with a merely small constant (no power saving) would also suffice in principle, but pointwise in (s1,s2) that loses a further log (the mean square of L'/L at that distance is ≍ log² m, dominated by n ≪ m rather than n ≍ m), so the power-saving form is the natural one.
- For the Lean side, this would be a named hypothesis `TwistedRatios δ`. It does **not** follow from GRH, so by the project conventions it is an extra, explicitly flagged assumption, not an admissible "GRH consequence".

### 5.2 Xie's coset decomposition over Z [DERIVED, proved]

Let H ≤ G, h = [G:H]. For ξ ∈ \hat H put T_ξ(a;H) = Σ_{n1n2 ∈ aH} Λ(n1)Λ(n2)w(n1/X)w(n2/X) ξ(n1n2 a^{-1}). Then (Fourier inversion on H, or summing χ over cosets of H^⊥ as Xie does with H = ker Norm):
N_w(a) = (1/|H|) Σ_{ξ ∈ \hat H} T_ξ(a;H),  T_ξ(a;H) = (1/h) Σ_{ψ ∈ H^⊥} \overline{(χψ)}(a) S_w(χψ)² for any χ extending ξ.
- ξ = 1 gives N_w(aH)/|H|, the number of representations of the *coset*, which under GRH is asymptotic to the EOS main term whenever h ≤ c·X/log² m (next item).
- EOS ⇔ Σ_{ξ≠1} T_ξ(a;H) > −T_1(a;H). Xie proves, for H = ker(Norm), h = q − 1, the pointwise bound |T_ξ| ≤ ε T_1 for generic ξ. Over Z the same strategy would need, for some H of index h ≥ (log m)^{2+ε} (so that random phases over a coset of h characters save log m), a bound |T_ξ(a;H)| ≤ ε|P|²/φ·(…) on average over ξ. I have no tool for this: T_ξ is again an h-term twisted sum, phase-blind under GRH. [the last two sentences are heuristic]

**Corollary (GRH).** There is an absolute C such that for all large m, every subgroup H ≤ (Z/mZ)^* with |H| ≥ C log² m, and every a, the coset aH contains a product pq of two primes p, q ∈ (m/2, m].
*Proof.* N_w(aH) = (1/h)Σ_{ψ ∈ H^⊥} ψ̄(a)S_w(ψ)² at X = m. The ψ = χ0 term is ≥ W(1)²m²/(2h). The rest is ≤ max_{ψ≠χ0}|S_w(ψ)|² ≪ m log² m by the GRH bound of lit/03 §0.1. Positive when m/h ≥ C' log² m, i.e. |H| = φ/h ≥ C'(φ/m) log² m. Prime powers: there are at most √m proper prime powers n1 ≤ m, and for each the number of n2 ≤ m with n1n2 ∈ aH is ≤ |H| (one per residue class in the coset). So their total weight is ≤ 2√m·|H|·log² m, which is o(m²/h) because m²/h = m²|H|/φ ≥ m|H|. ∎
This is the subgroup counterpart of Banks–Shparlinski's Theorem 1.3 (third prime ≪ log⁴ m). It is not new in substance, and such H need not exist with |H| ≤ (log m)^{O(1)} (e.g. m a safe prime).

### 5.3 The conspiracy/punctual dictionary [heuristic]
A class a is unrepresented iff E(a) = −μ. In Xie's language this is the statement that the "Mellin transform" χ ↦ S(χ)² has a component aligned with χ(a) of relative size 1/log m (§4.4). Over F_q, purity + monodromy forbid any alignment short of an exact punctual summand. Over Z there is no analogue of weights for the map a ↦ E(a), so partial alignments cannot be excluded a priori. This is the same content as Tao's "sympathetic resonance" remark (lit/03 §3.2), now with the function-field mechanism that excludes it identified.

---

## 6. Confronting the barriers

### 6.1 Redacted primes over F_q[t] [DERIVED, sketched]
Fix f of degree n and a ∈ B^×. Let P_n = monic irreducibles of degree n coprime to f, R_a = {π ∈ P_n : the monic degree-n representative of a·π^{-1} mod f is irreducible}, P' = P_n ∖ R_a. Then a ∉ P'·P', |R_a| ≈ q^n/n², |P'| = (1 − 1/n + …)|P_n|, and heuristically Σ_{π ∈ R_a} χ(π) ≈ q^{n/2}/n, so P' satisfies a Weil-size bound |Σ_{π∈P'} χ(π)| ≪ q^{n/2} for all χ ≠ χ0 (heuristic, as in Tao's and lit/03's versions: the sums over R_a are themselves binary sums), and the exact Parseval identity. So the construction exists in function fields exactly as over Z, and it defeats every argument that uses only |S(χ)| ≤ n q^{n/2} and Parseval, e.g. Xie's §2 preliminary bounds.

It does **not** defeat the actual proofs, for these precise reasons:
1. **Rationality is destroyed.** For the true primes, Ψ(d,χ) = −q^{d/2}Tr(θ_χ^d) for *all* d with a single θ_χ ∈ U(n−1). The sums over P' are not the power sums of any unitary matrix of bounded size, and there is no "L-function of P'" with a functional equation. Xie's step 2 (Schur decomposition) has no meaning for P'.
2. **The sheaf structure in χ is destroyed.** Steps 3–5 of §2.1 use that ρ ↦ θ_{χρ} is the Mellin transform of N(χ). After Mellin inversion, the quantity bounded by Deligne is *literally the twisted count of pairs of primes in a norm-coset*. For P' the corresponding count is a different number, to which no theorem applies. Likewise Sawin bounds #X_a(F_q) (with coefficients) directly.
3. **Redaction is not a small perturbation of the invariants actually used.** In the q → ∞ regime, removing R_a changes each normalised sum q^{-n/2}Ψ(n,χ) = −Tr(θ_χ^n) by a quantity of size ≈ 1, and (by construction) shifts the twisted average avg_χ χ(a^{-1})·(q^{-n/2}Ψ'(n,χ))² by ≈ −1, the whole main term. The equidistribution statement has precision q^{-1/2}n^{O(n)} ≪ 1. So the redacted family is visibly not equidistributed jointly with χ(a): the theorem would detect the redaction, it simply does not apply to it.
4. **Summary.** The proofs are not "PNT + RH-bounds + L²". They are statements about the bilinear object itself. The barrier says phase-blind methods fail; geometry is not phase-blind because the phase sum *is* a trace of Frobenius.

### 6.2 Random pairing set (lit/02 §4.3(b)) [DERIVED, sketched]
Same answer. The random set A has |Â(χ)| ≪ √φ but is not a trace function, has no L-function, and its convolution A*A is not the point count of a variety. Sawin's proof handles each factorization function F_ρ, including the induced ones (convolutions), by geometry of the fibre X_a; nothing is deduced from linear statistics of the factors. In sieve language: the function-field theorem *is* the Type II estimate (for all ranges, with square-root saving), obtained directly. This is consistent with lit/02 §5 item 1: over Z the missing input is bilinear, and no linear-in-the-family consequence of GRH supplies it.

### 6.3 The precise missing ingredient over Z
A structure providing, for each (m, a), a second spectral decomposition of the binary count
N(a) − main = Σ_{j ≤ B} c_j λ_j with |λ_j| ≤ (X²/m)^{1/2}·m^{o(1)}, B·max|c_j| ≤ m^{o(1)} (or even ≤ m^{1/2−δ}),
independent of the decomposition over zeros of {L(s,χ)}. Over F_q[t] this is H^*_c(X_a) with Deligne's weights and Sawin's Betti bounds; equivalently, the statement that χ ↦ (zeros of L(s,χ)) is the Mellin transform of a pure perverse object on the torus of residue classes, with a purity dichotomy excluding partial conspiracies. Over Z:
- there is no Frobenius/base change, so no "RH in the q-aspect";
- the interval [1,m] is not an algebraic subset of Z/m, so even for prime m the function 1_P * 1_P on F_m^× is not a trace function;
- the only one-parameter subfamily with the required rigidity (power-residue twists) has size |μ(Q)| = 2.

---

## 7. Verdict

**(b): the function-field method does not transfer.** The cancellation in Σ_χ χ̄(a)S(χ)² over F_q[t] is produced by applying RH a second time, to a geometric object parametrised by the residue class a (Xie: a rank-n^{O(n)} perverse sheaf on G_m, giving q^{-1/2}; Sawin: the cohomology of the fibre X_a, giving q^{-n/2}C^n), together with a complexity bound that is beaten only when q is large (q ≥ n^{23n}, resp. q > 1024e²). GRH for Dirichlet L-functions is the analogue of the *first* application only (Weil's bound, loss n² ↔ log² m). There is no integer analogue of the second object, of the large-q limit, or of the purity dichotomy; and the faithful function-field analogue of the integer problem (small fixed q, large degree) is itself unproved as far as I know.

**Conditional statement available (§5.1):** GRH + TR(δ) ⇒ EOS with p, q ≤ m^{1−δ/3}. Proved reduction; TR(δ) is a new hypothesis of ratios-conjecture shape and the direct analogue of Sawin's theorem, but it is at least as strong as EOS-with-power-saving, so I do not present it as progress on EOS itself.

**Proved partial results:** §5.2 (coset identity; under GRH every coset of every subgroup of order ≥ C log² m contains a product of two primes in (m/2, m]).

**Suggested follow-ups for other routes.**
1. Treat F_q[t]-EOS for q = 2, 3 and n → ∞ as a test problem: any method that works there without large-q input would be a candidate for Z; any proof that it requires q large is evidence for a genuine barrier.
2. The requirement "phase bias of relative size 1/log m" (§4.4) and "lower-order-term precision" (§4.5) should be used to sanity-check any proposed zero-statistics hypothesis: leading-order Katz–Sarnak or pair-correlation statements cannot suffice.
3. If a numerical experiment is wanted: compute avg_χ Re(χ̄(a)S(χ)²)/avg_χ|S(χ)|² for the classes a with smallest N(a) (the data in `compute/data` should allow this) and compare with −(m/φ)/log m and with the random-phase scale 1/√φ.

---

## Sources

- L. Xie, *On a conjecture of Erdős over function fields*, arXiv:2510.17612v3; Math. Z. 313 (2026), Paper 64. [READ, full]
- W. Sawin, *Square-root cancellation for sums of factorization functions over squarefree progressions in F_q[t]*, arXiv:2102.09730; Acta Math. 233 (2024) 285–418. [READ: intro, precise result, strategy, von Mangoldt convolution lemmas]
- W. D. Banks, *Products of two elements of Granville's random model in residue classes*, arXiv:2609.37434. [READ, intro]
- N. M. Katz, *On a question of Keating and Rudnick about primitive Dirichlet characters with squarefree conductor*, IMRN 2013, 3221–3249; *Convolution and Equidistribution*, Princeton 2012. [READ-2nd via Xie]
- Forey–Fresán–Kowalski, arXiv:2109.11961 (Katz's framework on general commutative groups). [READ-2nd via Xie]
- Keating–Rudnick, IMRN 2014 (variance of primes in progressions, large q). [READ-2nd via Sawin, Xie]
- Conrey–Farmer–Zirnbauer ratios conjecture; Hughes–Rudnick; Fiorilli–Miller: as cited in `lit/03` [RECALLED there; not reopened].
