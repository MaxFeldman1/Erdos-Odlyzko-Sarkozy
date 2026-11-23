# Brainstorm round 1 — wildcard (cross-disciplinary) persona

Written 2026-11-22. Standing hypothesis: GRH for Dirichlet L-functions, used only through route C's bound H
(`C-log-exponent.md` Thm 1) or its sharp-cutoff equivalent |S(χ)| ≪ √m log m. Anything more is flagged.
Scripts and outputs: `compute/brainstorm/wildcard/` (`multiplier_cert.py`, `interval_cert.py`, `linnik_cert.py`, `out_*.txt`).

**Status tags.** *proved* = complete argument written here from cited lemmas of route C. *sketched* = believed
complete, a step only indicated. *heuristic* = not a proof. *computed* = exact script output. [UNVERIFIED] = not checked.
Novelty claims are relative to `notes/` only; I did no literature search this round.

Notation as in `00-setup.md`: G = (Z/mZ)^*, φ = φ(m), L = log m, P = {p ≤ m prime, p ∤ m}, S(χ) = Σ_{p∈P} χ(p),
N(a) = #{(p,q) ∈ P² : pq ≡ a}, λ = |P|²/φ, L′ = φ/|P| (≈ L·φ/m), 𝓔 = G ∖ P·P the exceptional set,
N⁻(b) = #{(p,q) ∈ P² : p ≡ bq} = (1/φ) Σ_χ χ̄(b)|S(χ)|² (route D §1).
For a finite 𝒮 ⊂ G: 1̂_𝒮(χ) = Σ_{c∈𝒮} χ(c), and the k-fold multiplicative energy
E_k(𝒮) = #{(c, c′) ∈ 𝒮^k × 𝒮^k : c₁⋯c_k = c′₁⋯c′_k in G} = (1/φ) Σ_χ |1̂_𝒮(χ)|^{2k}.

---

## 0. Summary

**I have no route to EOS.** What this note adds is a change of problem in the spirit of Goldbach–Linnik and
Zhang–Maynard (relax the target until the method has slack), which turns out to be provable under GRH and to
improve what the notes record.

| # | Statement | Status |
|---|---|---|
| Master inequality (§1.1) | For every 𝒮 ⊂ G and every k ≥ 1: \|Σ_{c∈𝒮} E(c)\| ≤ V°·(M²·E_k(𝒮)/V°)^{1/2k}. Unconditional finite Fourier analysis (Hölder); k = 1, \|𝒮\| = 1 is route C's Lemma D5. | proved |
| Thm W (§1.2) | GRH. For large m every a is **p·q·s** with p, q < m and s prime, **s ≤ K (φ/m)² (log m)² (log log m)²**. The notes record (log m)⁴ (Banks–Shparlinski Thm 1.3) and (log m)³ log log m (route D Rem. 5.1). | proved from route C's lemmas |
| Cor W1 (§1.3) | GRH. For every a, all but ≤ K L² log L of the primes s ≤ exp(L/⌈log L⌉) have a·s̄ ∈ P·P. So 𝓔 (size ≤ K L³) meets every "prime ray" in ≤ K L² log L points. | proved |
| Cor W2 (§1.3) | GRH. Every a is n₁·n₂ with each n_i a product of exactly two primes and n_i ≤ K m L (log L)². (Thm S of route C: two primes ≤ K φ L².) | proved |
| Structure thm (§2.1) | GRH. Every 𝒮 ⊂ 𝓔 satisfies \|𝒮\|^{2k} ≤ K₂ K₁^{2k} (φ/m)^{2k} L^{2k+1} E_k(𝒮) for all k. So 𝓔 is either ≤ K L² log L or multiplicatively structured. k = 1 is route C's Thm E. | proved |
| Thm W-Linnik (§2.2) | GRH + an upper-bound sieve for prime pairs on a lattice (any constant C_s). Every a is **p·q·g^j·s** with 0 ≤ j < K L log L and s prime ≤ K C_s² log L log log L, for any fixed g of order ≥ K L log L (e.g. g = 2). The target set has ≈ L (log L)² elements: below the L² "wall". | proved given C_s; the sieve bound C_s ≪ (log log m)^{O(1)} is sketched |
| Hierarchy (§2.3) | An absolute-value certificate for a target set 𝒮 needs \|𝒮\| ≳ L′·A(𝒮), A = Wiener norm (1/φ)Σ\|1̂_𝒮\|. Sidon-type targets: L′². Geometric progressions: L′ log. Cosets: L′. EOS is \|𝒮\| = 1. Dropping the auxiliary prime s in Thm W-Linnik is **equivalent in this method to a prime-pair sieve constant < 2**. | heuristic lower bound; the equivalence is proved as a statement about the method |
| F_q[t] (§3) | The analogue of Thm W is **unconditional for every q, including q = 2**: every unit mod f (deg f = n ≥ n₀) is P₁P₂S with P_i irreducible of degree n and deg S ≤ 2 log_q n + 2 log_q log n + O(1). | sketched (same proof, Weil in place of GRH) |
| Numerics (§4) | The certificate is < 1 already at 128 small primes for m = 10⁶ and at **32 powers of 2** for m = 10⁶, 10⁷; max_{b≠1} N⁻(b)/λ = 1.29 at both moduli. | computed |

**Ranking of my routes** (probabilities are honest guesses):

1. **W1, Sidon multipliers** (§1). Done: a theorem. Chance the proof is correct: ~90%. Chance it reaches EOS: 0 (it is conjugation-blind, see checklist).
2. **W2, structured targets and the structure of 𝓔** (§2). Thm W-Linnik: ~75% correct as stated (the sieve lemma needs writing). Sub-goal |𝓔| ≪ L^{2+ε} under GRH: ~10%. EOS: < 1%.
3. **W3, F_q[t] with q small, unconditionally** (§3). ~85% that the statement is right; value is a clean unconditional theorem on route D's test bed, and a second place to look for what the missing factor L′ is.

---

## 0.1 What the solved problems had that EOS lacks

| Solved problem | What made it solvable | EOS counterpart |
|---|---|---|
| Vinogradov three primes | A third variable: sup bound on one factor, Parseval on two. | Ternary EOS is easy. Binary has no third factor. |
| Goldbach–Linnik (p + q + K powers of 2) | A sparse structured smoother, an *upper-bound sieve* for the energy ∫\|S·G\|², and a constant spectral gap of G. Parity is never confronted. | **This is the template for §1–§2.** It transfers: Thm W-Linnik is "a ≡ p·q·2^j·s". |
| Zhang / Maynard | The target is relaxed (some gap, not gap 2) until the level of distribution suffices. | Relax "a ∈ P·P" to "a·𝒮 meets P·P" for a small explicit 𝒮 (§1–§2). |
| Green–Tao | Finite complexity; a pseudorandom majorant. | Binary, infinite complexity; and Thm G kills anything inversion-symmetric. |
| Duke–Friedlander–Iwaniec | A spectral family over varying moduli. | One modulus. Dead (route D §4.9). |
| Sawin / Xie in F_q[t] | A second spectral expansion with few terms. | None known over Z (route B). |

**The conservation law (heuristic, but every theorem in the notes obeys it).** Size methods prove
"a is a product of primes from boxes" only when the *integer* product of the box sizes is ≥ m²·L^c:
route C has pq ≤ Kφ²L³ (two primes), Thm W has pqs ≤ m²L^{2+o(1)} (three primes). EOS asks for m² exactly.
The same law, read on the target side, is §2.3: a size method needs a target of ≥ L′ classes.
EOS is the critical case with zero slack, which is why every barrier on the checklist bites simultaneously.

---

## 1. Route W1: Sidon multipliers (the best route; a theorem)

### 1.1 The master inequality (proved, unconditional)

Use route C §2's notation with X₁ = X₂ = X: Θ(X;b) ≥ 0, ϑ̃(χ) = ϑ̃(X,χ), T = T(X), M = max_{χ≠χ0}|ϑ̃(χ)|,
V° = (1/φ)Σ_{χ≠χ0}|ϑ̃(χ)|², R(c) = T²/φ + E(c), E(c) = (1/φ)Σ_{χ≠χ0} χ̄(c) ϑ̃(χ)².

**Lemma M.** For every finite 𝒮 ⊂ G and every integer k ≥ 1,

  |Σ_{c∈𝒮} E(c)| ≤ V° · (M² E_k(𝒮) / V°)^{1/2k} = M^{1/k} · V°^{1−1/2k} · E_k(𝒮)^{1/2k}.

*Proof.* Σ_{c∈𝒮} E(c) = (1/φ) Σ_{χ≠χ0} ϑ̃(χ)² \overline{1̂_𝒮(χ)}, so the left side is ≤ (1/φ)Σ_{χ≠χ0}|ϑ̃|²|1̂_𝒮|.
Hölder with exponents r = 2k/(2k−1) and 2k:

  Σ_{χ≠χ0}|ϑ̃|²|1̂_𝒮| ≤ (Σ_{χ≠χ0}|ϑ̃|^{2r})^{1/r} (Σ_χ|1̂_𝒮|^{2k})^{1/2k}.

Since 2r − 2 = 2/(2k−1): Σ_{χ≠χ0}|ϑ̃|^{2r} ≤ M^{2r−2}·φV°, and (2r−2)/r = 1/k, 1/r = 1 − 1/2k. The second factor is (φE_k(𝒮))^{1/2k}.
The powers of φ are −1 + (1 − 1/2k) + 1/2k = 0. ∎

Remarks.
- k = 1, 𝒮 = {a}: |E(a)| ≤ M·V°^{1/2}, route C's Lemma D5. k = 1, general 𝒮: route C's Lemma D7 / Thm E.
- The inequality is increasing in M and in V°, so upper bounds for both may be inserted.
- The same proof with two different weights gives M₁^{1/2k}M₂^{1/2k}(V°₁V°₂)^{(1−1/2k)/2}E_k^{1/2k} (use |ϑ̃₁ϑ̃₂| ≤ (|ϑ̃₁|²+|ϑ̃₂|²)/2 after rescaling). Not needed below.
- Lean: this is finite Fourier analysis on `DirichletCharacter ℂ m` plus Hölder; no analytic input.

**Lemma S (energy of small primes; proved, unconditional).** Let 𝒲 be a set of primes not dividing m, all ≤ y, and let y^k < m.
Then for every a ∈ G the set 𝒮 = {a·s̄ : s ∈ 𝒲} has E_k(𝒮) = E_k(𝒲) ≤ k!·|𝒲|^k.

*Proof.* E_k is invariant under translation and inversion. A solution of s₁⋯s_k ≡ s′₁⋯s′_k (mod m) has both sides in [1, y^k] ⊂ [1, m),
so it is an equality of integers, and by unique factorisation s′ is a permutation of s. ∎

Computed check (`multiplier_cert.py`, column E_k/(k!Y^k)): the ratio is ≤ 1 whenever y^k < m (e.g. 0.969, 0.909, 0.826 for
k = 2, 3, 4 at Y = 16, m = 10⁷) and exceeds 1 only in rows marked `*`, where y^k > m.

### 1.2 Theorem W (proved from route C's lemmas)

**Theorem W.** Assume GRH (only through H). There are absolute K, m₀ such that for every m ≥ m₀, with k = ⌈log L⌉:
if 𝒲 is a set of primes not dividing m, 𝒲 ⊂ [1, m^{1/k}), and

  |𝒲| ≥ K (φ/m)² L² log L,

then for every a ∈ G there are primes p, q < m and s ∈ 𝒲 with pqs ≡ a (mod m).
In particular one can take s ≤ K′ (φ/m)² (log m)² (log log m)².

*Proof.* Take X = m. Route C gives: T ≥ m/8 (D2), M ≤ C₃√m L (D3, uses H), V° ≤ (log 4) m L (D4(a), exact Parseval because
primes ≤ m are distinct mod m), and R(c) > 0 iff c ∈ P·P with both primes < m.
Let 𝒮 = {a s̄ : s ∈ 𝒲} and suppose R(c) = 0 for every c ∈ 𝒮. (If two s give the same class the argument is unchanged with 𝒮 as a multiset;
here the s are distinct mod m anyway.) Then Σ_{c∈𝒮}E(c) = −|𝒲| T²/φ, and Lemmas M and S give

  |𝒲| m²/(64φ) ≤ (log 4) m L · (C₃² L / log 4)^{1/2k} · (k!)^{1/2k} |𝒲|^{1/2}.

With (k!)^{1/2k} ≤ √k and (C₃²L/log 4)^{1/2k} ≤ C₄ (because L^{1/(2 log L)} = e^{1/2}):

  |𝒲|^{1/2} ≤ 64 (log 4) C₄ (φ/m) L √k, i.e. |𝒲| ≤ K₀ (φ/m)² L² ⌈log L⌉.

This contradicts the hypothesis once K > 2K₀. For the last sentence let 𝒲 be the primes ≤ y not dividing m, y = K′(φ/m)²L²(log L)²:
π(y) − ω(m) ≥ K(φ/m)²L² log L for large m (ω(m) ≤ 2L/log L, and (φ/m)² ≫ (log L)^{-2}; if needed enlarge K′),
and y^k = exp(O((log L)²)) < m. ∎

**What is used.** Exact Parseval for P at X = m; the GRH sup bound, but only through M^{1/k} (a factor O(1) once k ≈ log L);
unique factorisation of small primes. The bound H enters only to make (M²/V°)^{1/2k} bounded, so any bound M ≤ √m·L^{O(1)} suffices.

**Why it beats pigeonhole.** Thm E + pigeonhole treats 𝓔 as an arbitrary set of ≤ KL³ classes. Lemma M with large k uses that the
multiplier 1̂_𝒲(χ) has square-root cancellation for all but a tiny set of χ, which for small primes is unconditional (high moments
are diagonal). GRH is then needed only on that tiny set.

**Why it stops at L² (heuristic).** If |S(χ)|² is flat, Σ_{χ≠χ0}|S|²|1̂_𝒲| ≈ φ|P|·E|1̂_𝒲| ≈ 0.886 φ|P|√|𝒲| against |P|²|𝒲|, so the
absolute-value certificate needs |𝒲| ≥ (0.886 L′)². Thm W is within a factor O(log L) of this. Computed: the certificate ratio
Q = Σ_{χ≠χ0}|S|²|1̂_𝒲| / (|P|²|𝒲|) is 0.85–0.87 of the flat prediction (§4).

**Variants (sketched).**
- p, q ≤ X for X ≤ m: the same proof gives |𝒲| ≥ K(φ/X)²L² log L. So pqs ≤ m²·L^{2+o(1)} in every balance.
- With a zero-free strip Re s > σ₀ in place of GRH, M ≤ m^{σ₀}L^{O(1)} and k ≈ L/log y: I get s ≪ (log m)^{3/(2−2σ₀)+o(1)}, against
  2/(1−σ₀) = 4/(2−2σ₀) recorded from Banks–Shparlinski. Not checked carefully. [UNVERIFIED]

### 1.3 Corollaries (proved)

**Cor W1 (rays).** Assume GRH, m ≥ m₀, k = ⌈log L⌉. For every a ∈ G,

  #{s prime, s < m^{1/k}, s ∤ m : a·s̄ ∉ P·P} < K (φ/m)² L² log L.

*Proof.* Apply Thm W to 𝒲 = that set. ∎ The same holds for a·s (apply it to the inverse set; E_k is inversion-invariant).
So the exceptional set is unstable under multiplication by small primes: if a ∈ 𝓔, then a·s̄ ∈ P·P for all but ≤ KL² log L of the
≈ exp(L/log L) primes s < m^{1/k}.

**Cor W2 (two E₂ numbers).** Assume GRH. Every a ∈ G is n₁n₂ (mod m) with n_i = q_i s_i, q_i < m prime, s_i ≤ K L (log L)² prime.

*Proof.* Apply Lemma M to the multiset 𝒮 = {a·(s₁s₂)^{-1}}: 1̂_𝒮 = χ̄(a)·\overline{1̂_𝒲}², so Σ_χ|1̂_𝒮|^{2k} = φE_{2k}(𝒲) ≤ φ(2k)!|𝒲|^{2k}
if y^{2k} < m. The main term is |𝒲|²T²/φ and the error is ≤ C m L · 2k·|𝒲| (since ((2k)!)^{1/2k} ≤ 2k). So |𝒲| ≥ K(φ/m) L log L suffices. ∎

### 1.4 Barrier checklist for W1

The theorem is a weaker statement than EOS, so "pass" means "the barrier object does not contradict the theorem" and the EOS
column says which barrier stops the method from reaching |𝒮| = 1.

| Barrier | Thm W | As a route to EOS |
|---|---|---|
| (1) random pairing-avoiding set | **Pass.** A set A with A ∩ aA^{-1} = ∅ still has a·s̄ ∈ A·A for the other s. Lemma M holds for every weight. | **Fail.** At 𝒮 = {a} Lemma M is Lemma D5; the random set satisfies everything used. |
| (2) deletion of ~1/L of the primes | **Pass.** To empty all classes a·s̄, s ∈ 𝒲, one must delete ∪_s R_{a s̄}, of size up to \|𝒲\|λ = \|P\|·\|𝒲\|/L′ ≫ \|P\|. This is the reason a size method needs \|𝒮\| ≳ L′ (§2.3). | **Fail.** One class costs a 1/L′ fraction. |
| (3) parity | **Pass.** No sieve; a ternary count. | **Fail** (the output has three primes). |
| (4) A\* | Not applicable: no sieve on A_a, no Type I data. | **Fail** (uses less than A\* has). |
| (5) Proposition L | **Pass**, and consistent: for Sidon-type targets the threshold L′² is the variance wall. | **Fail.** |
| (6) Theorem G | **Pass.** The proof sees only \|S(χ)\|², so it proves the same for P·P^{-1}: every a is p·q̄·s. At a = −1 this says ps + q ≡ 0 for some small s, which is not excluded by Thm G. | **Fail, provably**: a conjugation-blind method cannot reach \|𝒮\| = 1. |

Extra hypotheses: none. First step: done (§1.2). Probability of EOS by this route: 0.

---

## 2. Route W2: structured targets, and the structure of the exceptional set

### 2.1 Structure theorem for 𝓔 (proved)

**Theorem (energy inequality).** Assume GRH (through H), m ≥ m₀. For every 𝒮 ⊂ 𝓔 and every integer k ≥ 1,

  |𝒮|^{2k} ≤ K₂ · K₁^{2k} · (φ/m)^{2k} · L^{2k+1} · E_k(𝒮).

*Proof.* As in Thm W: |𝒮| m²/(64φ) ≤ (log 4) m L (C₃²L/log 4)^{1/2k} E_k(𝒮)^{1/2k}. ∎

Consequences.
- k = 1: |𝓔| ≤ K(φ/m)²L³, route C's Thm E.
- If 𝒮 ⊂ 𝓔 is "generic" in the sense E_k(𝒮) ≤ C^k k!|𝒮|^k for k = ⌈log L⌉, then |𝒮| ≤ K L² log L.
- **Dichotomy.** If |𝓔| = L^θ with θ > 2, then E_k(𝓔) ≥ |𝓔|^{2k − (2k+1)/θ}/K^k for every k: the exponent is a fixed fraction of the way
  from the minimum k to the maximum 2k − 1. An exceptional set larger than L^{2+ε} must be multiplicatively structured.
- Unconditionally (k → ∞, or directly from Parseval): every 𝒮 ⊂ 𝓔 has a χ ≠ χ0 with |1̂_𝒮(χ)| ≥ |𝒮|·m/(89 φ L).
  Every subset of the exceptional set is 1/(89L)-biased. (proved)

The two structured extremes are also excluded at size ≈ L²: cosets of subgroups of order ≥ CL² (route B §5.2), and geometric
progressions {a g^j : j < J} with J ≥ C(φ/m)L² log L and ord(g) ≥ J (proved: split the characters dyadically in ‖θ_χ‖, where
χ(g) = e(θ_χ); #{χ : ‖θ_χ‖ ≤ δ} ≤ 2δφ + φ/ord(g); use min(φV°, #·M²) on each shell).
Sidon sets, progressions and cosets all stop at L^{2+o(1)}. This is my evidence that **|𝓔| ≪ L^{2+ε} under GRH** is a reasonable target.
I could not prove it: polynomial-in-L losses are affordable, but Balog–Szemerédi–Gowers and Freiman-type steps lose more than that.

**Additive corollary (sketched; needs an energy bound I did not verify).** For prime m and fixed k, the interval a₀ + [1, H] ⊂ Z/m has
E_k ≤ H^{k+o(1)} uniformly in a₀ when H ≤ m^{c/k²} (this is the Bourgain–Garaev–Konyagin–Shparlinski type of bound [UNVERIFIED]; for
H = L^{O(1)} a resultant argument shows all non-trivial solutions come from one polynomial of small height vanishing at a₀, and then a
divisor bound in a number field). With the energy inequality: **every interval of (log m)^{2+ε} consecutive residues contains a class
of P·P**, against (log m)³ from pigeonhole. Computed (`interval_cert.py`): for m = 10⁶, E₂/2H² = 0.99–1.02 for random a₀ up to H = 256,
1.5–1.7 for a₀ = −1/2, 2.3–3.1 for a₀ = 0; the certificate is < 1 at H = 128 for every a₀ tried.

### 2.2 Goldbach–Linnik format: a ≡ p·q·g^j·s (proved given a sieve constant)

In prime-count normalisation: M = max_{χ≠χ0}|S(χ)| ≤ C₁√m L (GRH), Σ_χ|S|² = φ|P| (exact).
Fix g ∈ G, write χ(g) = e(θ_χ), and for J ≥ 1 put

  C_s = C_s(g, J) := max(1, max_{0<|h|<J} N⁻(g^h)/λ).

**Lemma B (Bohr mass; proved).** If ord(g) ≥ H′ ≥ 1 and δ = 1/(2H′), then

  Σ_{χ : ‖θ_χ‖ ≤ δ} |S(χ)|² ≤ (π²/4) φ (2δ|P| + C_s(g,H′) λ).

*Proof.* F(θ) = (π²/4H′²)|Σ_{h<H′} e(hθ)|² is ≥ 1 on ‖θ‖ ≤ δ. Σ_χ|S|²F(θ_χ) = (π²φ/4H′²) Σ_{h,h′<H′} N⁻(g^{h−h′}),
the diagonal gives H′|P| and the rest is ≤ H′² C_s λ. ∎

**Theorem W-Linnik.** Assume GRH. There is an absolute K such that for m ≥ m₀: if g ∈ G has order ≥ J, J ≥ K L′ log L,
and 𝓡 is a set of primes not dividing m, 𝓡 ⊂ [1, m^{1/⌈log L⌉}), with |𝓡| ≥ K C_s(g,J)² log L, then every a ∈ G is

  a ≡ p·q·g^j·s (mod m), p, q ≤ m prime, 0 ≤ j < J, s ∈ 𝓡.

*Proof.* The multiset 𝒮 = {a g^{-j} s̄} has 1̂_𝒮(χ) = χ(a)·\overline{D_J(θ_χ) 1̂_𝓡(χ)} with |D_J(θ)| ≤ min(J, 1/(2‖θ‖)).
Put μ(χ) = |S(χ)|²|D_J(θ_χ)| for χ ≠ χ0. Summing Lemma B over dyadic shells 2^i/J < ‖θ‖ ≤ 2^{i+1}/J:

  𝔐 := Σ_{χ≠χ0} μ(χ) ≤ (π²/4) φ (2|P|(log₂J + 1) + 2 C_s λ J) ≤ C C_s φ λ J, using J ≥ L′ log J.

Hölder for the measure μ, then |D_J| ≤ J, |S|² ≤ M² and Lemma S:

  Σ_{χ≠χ0} μ|1̂_𝓡| ≤ 𝔐^{1−1/2k} (M² J φ k! |𝓡|^k)^{1/2k} ≤ C C_s φ λ J · (M²/λ)^{1/2k} · √(k|𝓡|).

M²/λ ≤ C L⁴, so with k = ⌈log L⌉ the error (1/φ)Σ_{χ≠χ0}|S|²|1̂_𝒮| is ≤ C₅ C_s λ J √(|𝓡| log L), against the main term λ J |𝓡|. ∎

**The sieve input (sketched).** N⁻(b) counts primes y ≤ m with (b·y mod m) prime, i.e. points of the lattice {x ≡ by (mod m)} in
[1,m]² with both coordinates prime. Take a reduced basis; the points lie on ≍ λ₁ lines each carrying ≍ m/λ₁ ≥ √m/2 points, and on each
line the two coordinates are linear forms in one variable. An upper-bound sieve on each line and a sum over the lines give
N⁻(b) ≪ 𝔖̃(b)·m/L², uniformly in b ≠ 1, with 𝔖̃ ≪ (log log m)^{O(1)} in the worst case. So C_s ≪ (log log m)^{O(1)}, unconditionally.
Computed: max_{b≠1} N⁻(b)/λ = 1.292 (m = 1000003) and 1.295 (m = 10000019), and no b has N⁻(b) > 2λ.

**Reading.** With g = 2 (if ord_m(2) < J, then ⟨2⟩ is a subgroup of order > log₂ m and one uses the coset version instead):
every a is p·q·2^j·s with j ≪ log m·log log m and s ≪ log log m·(log log log m)·C_s². The target has ≈ L(log L)² classes, which is
**below L²**. The "L² wall" of Prop L and of §1 is a wall for *unstructured* targets only. The price is that 2^j is a huge integer;
the statement is natural in the Linnik sense (few auxiliary classes), not in the size sense.

### 2.3 The hierarchy, and where parity sits (heuristic lower bound; the parity statement is proved)

An absolute-value certificate for "𝒮 meets P·P" is Σ_{χ≠χ0}|S|²|1̂_𝒮| < |𝒮||P|². If |S|² is flat this reads

  |𝒮| > L′ · A(𝒮), A(𝒮) := (1/φ) Σ_χ |1̂_𝒮(χ)| ≥ 1 (the Wiener norm).

| Target 𝒮 | A(𝒮) | threshold | what is proved under GRH |
|---|---|---|---|
| Sidon-type (small primes, generic intervals) | ≈ √\|𝒮\| | L′² | L² log L (Thm W) |
| geometric progression × few primes | ≈ log J · √\|𝓡\| | L′ log | L (log L)² (Thm W-Linnik) |
| geometric progression alone | ≈ (4/π²) log J | L′ log L | L² log L; **L log L iff C_s < 2** |
| coset of a subgroup H | 1 | L′ | L² (route B); **L iff the pair constant on H is < 2** |
| one class (EOS) | 1 | — | impossible for this method: short by exactly L′ |

The deletion barrier gives the same threshold from the other side: deleting ∪_{c∈𝒮}R_c removes ≤ |𝒮|/L′ of the primes, so no method that
survives deletion of a small fraction can go below |𝒮| ≍ L′.

**Parity appears as the number 2 (proved, as a statement about the method).** To drop the auxiliary primes 𝓡 one needs
Σ_{χ≠χ0}|S|²|D_J| < |P|²J directly. Any majorant G ≥ |D_J| whose Fourier coefficients ĝ(h) are ≥ 0 (which is what allows *upper* bounds for
N⁻(g^h) to be inserted) has Σ_h ĝ(h) = G(0) ≥ J, hence

  Σ_{χ≠χ0}|S|²G(θ_χ) ≤ φ ĝ(0)|P| + (C_s − 1) φ λ G(0),

and this is < φλJ only if **C_s < 2**. An upper-bound sieve gives 4 at level 1/2 and 2 at level 1 (Elliott–Halberstam strength), never
less: this is route C §6's "prime-pair bound with constant < 2", now with an exact statement of what it would buy:
a ≡ p·q·2^j with j ≪ log m log log m. Numerically C_s ≈ 1.0–1.3 (§4), so the hypothesis is true with room, and unprovable for the usual reason.
The auxiliary primes 𝓡 are what converts "constant < 2" into "any constant" (the Linnik–Gallagher device).

### 2.4 Barrier checklist for W2

| Barrier | Thm W-Linnik / structure theorem | As a route to EOS |
|---|---|---|
| (1) random pairing-avoiding set | **Pass** (as in W1; the sieve bound for N⁻ is a property of the primes, used only as an upper bound). | **Fail** at \|𝒮\| = 1. |
| (2) deletion | **Pass**; the target has ≫ L′ classes. The method is within (log L)² of the deletion threshold. | **Fail**: \|𝒮\| ≳ L′ is forced. |
| (3) parity | **Pass**: an upper-bound sieve with any constant. Parity is the statement C_s < 2, needed only to remove 𝓡. | **Fail.** |
| (4) A\* | Not applicable (no sieve on A_a). | **Fail.** |
| (5) Proposition L | **Evaded for structured targets**, by using the Fourier structure of the target instead of more about the primes. | **Fail.** |
| (6) Theorem G | **Pass**: conjugation-blind, so the same theorem holds for P·P^{-1}; −1 ≡ p q̄ 2^j s is not excluded by Thm G. | **Fail, provably.** |

Extra hypotheses: none for the theorems. "C_s < 2" is an explicit extra hypothesis of Hardy–Littlewood upper-bound type, beyond GRH and
beyond Elliott–Halberstam; it would give the two unstarred improvements in the table of §2.3 and nothing closer to EOS.
First lemma: write the lattice sieve bound for N⁻(b) with uniform constants. First experiment: done (§4).
Probabilities: Thm W-Linnik correct as stated ~75%; |𝓔| ≪ L^{2+ε} under GRH ~10%; EOS < 1%.

---

## 3. Route W3: the same theorems in F_q[t], unconditionally and for every q

Route D §3 identifies F_2[t] (q fixed and small, deg f → ∞) as the faithful analogue, open because Sawin needs q > 7567.
Lemma M and Lemma S are unconditional and GRH is Weil's theorem, so the relaxed statement transfers with no hypothesis.

**Claim (sketched).** There is an absolute n₀ such that for every prime power q, every f ∈ F_q[t] of degree n ≥ n₀ and every unit a mod f,

  a ≡ P₁·P₂·S (mod f), P₁, P₂ monic irreducible of degree n, S monic irreducible of degree d ≤ 2 log_q n + 2 log_q log n + C.

*Sketch.* P = monic irreducibles of degree n other than f; distinct P are distinct mod f (P − P′ has degree < n), so Parseval is exact
and V° ≤ |P| ≤ q^n/n. For χ ≠ χ0 mod f, Σ_{deg g = n} Λ(g)χ(g) is minus a sum of ≤ n − 1 n-th powers of inverse zeros of modulus ≤ √q,
and prime powers contribute ≤ 2q^{n/2}, so M ≤ 2q^{n/2}: there is no log. Lemma M gives |𝒮|^{2k} ≤ (2n)^{2k}·8n·E_k(𝒮) for 𝒮 ∩ P·P = ∅.
For 𝒲 = irreducibles of degree d coprime to f and kd < n, a congruence between k-fold products is an equality, so E_k ≤ k!|𝒲|^k.
With k = ⌈log n⌉: |𝒲| ≤ 100 n² log n, and |𝒲| ≥ q^d/2d − n/d. ∎ (to be written out; the constants are not optimised.)

The Linnik format also transfers (g = t when t ∤ f), with the function-field sieve for the pair constant.

**As a route.** Mechanism: none beyond §1–§2. Its use is diagnostic: over F_q[t] the missing factor is L′ ↔ n, and Sawin's theorem
supplies it for large q by a second expansion. A proof at q = 2 of *any* statement below the thresholds of §2.3 (e.g. target of size o(n))
would have to use something that is not conjugation-blind, and would be the first such mechanism not relying on large q.
Checklist: identical to W1/W2 (all six barriers are consistent with the relaxed statement and all six block |𝒮| = 1).
Extra hypotheses: none. First step: write the proof; run `compute/routeD/ff2_eos.py`-style checks of the certificate at q = 2.
Probability the claim is correct: ~85%. Probability it leads to EOS over Z: < 1%.

---

## 4. Numerics (computed)

`multiplier_cert.py` (prime m; all characters by FFT over discrete logs). 𝒲 = first Y primes, y = largest.
Q = Σ_{χ≠χ0}|S|²|1̂_𝒲| / (|P|²Y); Q < 1 certifies that every a is pqs with s ∈ 𝒲. "flat" = 0.886·L′/√Y.

| m | L′ | Q at Y = 0 (EOS itself) | Y = 16 | Y = 64 | Y = 128 | Y = 256 | Y = 1024 | flat at Y = 128 | min_a #{pqs}/(λY) at Y = 128 |
|---|---|---|---|---|---|---|---|---|---|
| 100003 | 10.43 | 9.43 | 2.02 | 0.96 | 0.68 | 0.48 | 0.25 | 0.82 | 0.9870 |
| 1000003 | 12.74 | 11.74 | 2.54 | 1.22 | 0.85 | 0.60 | 0.30 | 1.00 | 0.9942 |
| 10000019 | 15.05 | 14.05 | 3.05 | 1.47 | 1.03 | 0.72 | 0.36 | 1.18 | 0.9976 |

- The certificate crosses 1 at Y ≈ 0.75·(0.886 L′)², as predicted by the flat model; Q/flat = 0.85–0.87 throughout.
- The Hölder bound of Lemma M with the measured M and E_k (column H_k in the output) is ≥ Q in every row, e.g. H₂ = 0.99 against Q = 0.36 at m = 10⁷, Y = 1024.
- M²/|P| = 7.4, 8.3, 9.6: the factor (M²/V°)^{1/2k} of Lemma M is harmless in practice.

`linnik_cert.py`. Target {a·g^{-j}·s̄ : j < J, s ∈ first R primes}. Q as above with |1̂_𝒮| = |D_J||1̂_𝓡|.

| m | g | Q at J = 16, R = 1 | J = 32, R = 1 | J = 64, R = 1 | J = 16, R = 4 | J = 32, R = 4 | max_{0<h<256} N⁻(g^h)/λ |
|---|---|---|---|---|---|---|---|
| 1000003 | 2 | 1.47 | **0.82** | 0.46 | 0.68 | 0.38 | 1.026 |
| 1000003 | 3 | 1.50 | 0.85 | 0.47 | 0.69 | 0.39 | 1.026 |
| 10000019 | 2 | 1.77 | **0.999** | 0.56 | 0.82 | 0.46 | 1.010 |
| 10000019 | 6 (primitive root) | 1.86 | 1.05 | 0.59 | 0.84 | 0.48 | 1.015 |

- **32 powers of 2 certify what needs ≈ 130–180 small primes.** This is the hierarchy of §2.3 (L′ log J against L′²), observed.
- max over all b ≠ 1 of N⁻(b)/λ is 1.292 (m = 1000003, at b = 333335 ≡ 2/3) and 1.295 (m = 10000019, at b = 5000011 ≡ 3/2), the small-height classes where route D §1.2 found the singular series largest; the mean is 1.0000. No b exceeds 2λ.
- The Bohr-mass ratio of Lemma B (measured mass over φ(2δ|P| + λ)) is 0.90–0.99: |S|² is flat with respect to arg χ(g).

`interval_cert.py`. E(a) is Gaussian to the precision visible: skewness 0.03, 0.01 and kurtosis 2.98, 3.01 at m = 10⁵, 10⁶;
the minimum is −4.1 and −5.0 standard deviations while λ is 25 and 63 standard deviations. For the worst class the deficit is not carried
by a few characters (the most negative 1% of characters carry about 2–5 times |E|, cancelled by the rest), so there is no small
"exceptional spectrum" to isolate. Every window of H consecutive residues: min count/(λH) = 0.990 at H = 64, m = 10⁶.

---

## 5. Considered and discarded this round

- **Cauchy–Schwarz plus a sieve for the energy Σ|S·1̂_𝒲|²** (the literal Gallagher step). The off-diagonal is ≍ the main term with a
  sieve constant C > 1, so the bound exceeds the main term by √(C L′) once |𝒲| > L′. Only the level-set / Hölder form works.
- **A fourth-moment hypothesis for E(a)** (Σ_a E(a)⁴ ≤ Cφλ² ⇒ EOS, since |𝓔| ≤ Cφ/λ² < 1). a-independent, false for the deleted set and
  for P·P^{-1}, so it passes all six barriers; but it asks for a relative precision m^{−2+ε} in an 8-prime count. A restatement, like TR(δ).
- **Almost all m, all a.** The large sieve over m gives (M² + X)·|P| against M·φ|P| modulus by modulus: no gain in L², and the sup over a
  blocks Bombieri–Vinogradov-type averaging. The variance asymptotic would need Montgomery–Hooley at Q = x^{1/2} exactly.
- **Selberg's formula in the class a mod m up to m².** Needs Brun–Titchmarsh with constant < 2 at q = x^{1/2} (known constants ≥ 3) and
  yields semiprimes ≤ m², not p, q ≤ m. Same death as route D §4.8.
- **GRH as Type I input for A_a.** Σ_p e(h p̄/m) through Gauss sums and GRH is ≤ √(m|P|), worse than trivial. Confirms that route D-S
  needs genuine Kloosterman input.
- **Bounded number of shifts** ("a or 2a is in P·P"). Needs |𝒮| ≥ L′ by §2.3 and the deletion barrier; no bounded version exists for a size method.

---

## 6. Not checked

- Novelty of Thm W, Cor W1, Cor W2 and Thm W-Linnik: relative to `notes/` only. Banks–Shparlinski's text should be checked for a (log q)² variant.
- Route C's lemmas D2, D3, D4(a) are used as stated there (they are refereed in `C-referee.md`); I did not re-derive H.
- The lattice sieve bound N⁻(b) ≪ (log log m)^{O(1)} λ is sketched; the singular-series average over h < J was not computed.
- The interval energy bound of §2.1 is quoted from memory. The zero-free-strip variant in §1.2 is a quick computation.
- §3 is a sketch; "n₀ absolute" needs the constants written out for q = 2.
- All numerics are for three prime moduli; composite m were not run.
- Probabilities are opinions.
