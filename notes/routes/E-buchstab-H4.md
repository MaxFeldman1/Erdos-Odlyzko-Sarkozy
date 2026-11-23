# Route E: the Buchstab reduction, written out. TypeISifted + H4(η) ⇒ N(a) ≥ 0.4μ

Written 2026-11-23. This note completes `notes/brainstorm/r1-analytic.md` §2 (Thm BH, Cor H4, Cor LD) as asked in
`r3-synthesis.md` §3.2: Lemma 2.2 in full including the blocks near √m, Proposition Q for composite m, the final
theorem with H4 and with LD, and the barrier harness. **GRH is not used anywhere in this note.** H4 and LD are
hypotheses beyond GRH, stronger than EOS, and not known to follow from GRH.

Status tags: *proved* = complete argument here from the named inputs of §2. *quoted* = a published theorem, with
the reading status of the source. *sketched*, *heuristic*, *computed*, [UNVERIFIED], [RECALLED] as in the other notes.

## 0. Summary

| Item | Statement | Status |
|---|---|---|
| §1 | Exact part: Buchstab identity (Lemma C), block majorant, Hölder, layer cake | proved, elementary, no asymptotics |
| §2 | Named inputs IN-T1, IN-FL, IN-M, IN-PNT and three derived inputs D-BT, D-RNL, D-RNA | quoted; derivations proved from the quoted ones |
| Lemma 2.1 | TypeISifted: S(A_a, z) ≥ ρΦ_m(m,z)(1 − C₆e^{−1/(17η)}) − m^{1−1/300} | proved from IN-T1, IN-FL |
| **Lemma 2.2** | Σ_j ι_j\|𝒦_j\| ≤ (1 + C₁λ)B₀ + C₅ log(2/λ)·m/L² | **proved** from D-BT, D-RNL; checked numerically |
| **Theorem E** | TypeISifted + BI(η,λ) ⇒ N(a) ≥ 0.4μ for every unit a, m ≥ m₀(η,λ), η ≤ η₀, λ ≤ κη | **proved** from the named inputs |
| Cor H4, Cor LD | H4(η,λ) ⇒ BI(η,λ); LD(η,λ) ⇒ BI(η,λ) | proved |
| Prop Q′ | Conjugate fourth moment ≥ (φ(m;B) − 1)(ρι)⁴ + (1−ρ)⁴ι⁴; above the H4 threshold by ≥ c(φ/m)(log M)/η⁴ | proved, all m (repairs the "− ω(m)" count) |
| §7 | Barrier harness at m = 1000003 and m = 1009² | computed |

**Corrections to the round-1 statement.**
1. The sketch of Lemma 2.2 claimed the block majorant exceeds each block's true count by a factor 1 + O(λ). That is
   false for the blocks near √m: for the top block the ratio tends to 2 (§3.3). The lemma is still true because
   the O(log(1/λ)/λ) top blocks together carry only O(log(1/λ)·m/L²), a 1/L fraction of B₀.
2. I use blocks that tile [z, √m) exactly, so there is no overshoot beyond √m and no "(1+λ)√m".
3. H4 depends on two parameters (η, λ) and must be stated for the specific block system; it is false for
   blocks that are too short (a block with one prime has fourth moment ≈ φρ).
4. The hypothesis actually used is the **summed** block inequality ΣBI (§4). The harness shows that at m ≈ 10⁶ the
   per-block inequality fails for P in the top block while the sum holds with room (§7).

---

## 1. Setup and the exact part (proved; no asymptotics)

m ≥ 3, G = (Z/mZ)^*, φ = φ(m), L = log m. P = primes ≤ m not dividing m, ρ = |P|/φ, μ = |P|²/φ.
For a unit a: A_a = {a·p̄ mod m : p ∈ P} ⊂ [1, m−1], |A_a| = |P|, every element coprime to m.
N(a) = #{(p,q) ∈ P² : pq ≡ a} = #{primes in A_a} (a prime n ∈ A_a is coprime to m and < m, so n ∈ P; conversely
each pair (p,q) gives the element q of A_a).

P⁻(n) is the least prime factor, P⁻(1) = ∞. For a finite set 𝒜 of positive integers, S(𝒜, z) = #{n ∈ 𝒜 : P⁻(n) ≥ z}.
Φ(x,y) = #{1 ≤ n ≤ x : P⁻(n) ≥ y} (n = 1 is counted), Φ_m(x,y) = #{1 ≤ n ≤ x : (n,m) = 1, P⁻(n) ≥ y}.

**Lemma C (Buchstab, exact).** For 2 ≤ z ≤ √m:
 #{primes n ≥ √m in A_a} = S(A_a, z) − [1 ∈ A_a] − B(a), B(a) := Σ_{z ≤ p₁ < √m} #{k : p₁k ∈ A_a, P⁻(k) ≥ p₁}.
In particular N(a) ≥ S(A_a, z) − 1 − B(a).

*Proof.* Let n ∈ A_a, n > 1, P⁻(n) = p₁ ≥ z. If p₁ ≥ √m then n is prime, since n < m. If p₁ < √m then n = p₁k with
P⁻(k) ≥ p₁, counted once in B(a). ∎ (Only p₁ ∤ m contribute, because A_a consists of units.)

**Block system 𝔅(m, η, λ).** Fix 0 < η < 1/2 and 0 < λ ≤ 1. Put z = m^η,
J = ⌈(1/2 − η)L / log(1+λ)⌉, 1 + λ_m = exp((1/2 − η)L/J), M_j = z(1+λ_m)^j (0 ≤ j ≤ J), so M_0 = z, M_J = √m,
λ_m ≤ λ, and λ_m ≥ λ/2 once (1/2 − η)L ≥ 2 log 2. For 0 ≤ j < J:

 I_j = {primes p₁ ∈ [M_j, M_{j+1}), p₁ ∤ m}, ι_j = |I_j|,
 𝒦_j = {1 ≤ k ≤ m/M_j : (k,m) = 1, P⁻(k) ≥ M_j}, so |𝒦_j| = Φ_m(m/M_j, M_j),
 π_j(c) = #{p₁ ∈ I_j : c·p̄₁ mod m ∈ P}, δ_j(c) = π_j(c) − ρι_j (c ∈ G). Note Σ_c δ_j(c) = 0.

**Lemma 1.1 (block majorant; proved).** B(a) ≤ Σ_j Σ_{k∈𝒦_j} π_j(a·k̄) = ρ Σ_j ι_j|𝒦_j| + Σ_j Σ_{k∈𝒦_j} δ_j(a·k̄).

*Proof.* A pair (p₁, k) counted in B(a) has p₁ in exactly one I_j, k ≤ (m−1)/p₁ ≤ m/M_j, (k,m) = 1 and
P⁻(k) ≥ p₁ ≥ M_j, so k ∈ 𝒦_j; and p₁k ∈ A_a means a·k̄·p̄₁ ∈ P. Distinct pairs give distinct terms. All terms of the
right side are ≥ 0. ∎

**Lemma 1.2 (Hölder; proved).** k ↦ a·k̄ is injective from 𝒦_j to G (k < m). Hence
Σ_{k∈𝒦_j} δ_j(a k̄) ≤ |𝒦_j|^{3/4}(Σ_{c∈G} δ_j(c)⁴)^{1/4}.

**Lemma 1.3 (layer cake; proved).** Let T > 0 and E_j(t) = #{c ∈ G : δ_j(c) > t}. Then
Σ_{k∈𝒦_j} δ_j(a k̄) ≤ T|𝒦_j| + Σ_{i≥0} 2^{i+1}T·E_j(2^iT).

*Proof.* Terms ≤ T contribute ≤ T|𝒦_j|. A term in (2^iT, 2^{i+1}T] is ≤ 2^{i+1}T and there are at most E_j(2^iT)
such k, by injectivity. ∎

**The three hypotheses.** For a block system 𝔅(m, η, λ):

- **H4(η,λ; m):** for every j < J: Σ_{c∈G} δ_j(c)⁴ ≤ (η/2)⁴·ρ⁴·ι_j⁴·|𝒦_j|.
- **LD(η,λ; m):** for every j < J and every integer i ≥ 0: E_j(2^iT_j) ≤ (1/4)·|𝒦_j|·4^{−i}, where T_j = ηρι_j/4.
- **BI(η,λ; m, a):** for every j < J: Σ_{k∈𝒦_j} δ_j(a k̄) ≤ (η/2)·ρ·ι_j·|𝒦_j|.
- **ΣBI(η,λ; m, a):** Σ_j Σ_{k∈𝒦_j} δ_j(a k̄) ≤ (η/2)·ρ·Σ_j ι_j|𝒦_j|.

H4 and LD do not mention a. LD is stated on the dyadic values only, which is all that is used.

**Corollary 1.4 (proved).** H4(η,λ; m) ⇒ BI(η,λ; m, a) for every unit a. LD(η,λ; m) ⇒ BI(η,λ; m, a) for every unit a.
BI ⇒ ΣBI.

*Proof.* H4: Lemma 1.2. LD: Lemma 1.3 with T = T_j gives T_j|𝒦_j|(1 + Σ_i 2^{i+1}4^{−i}/4) = 2T_j|𝒦_j| = (η/2)ρι_j|𝒦_j|. ∎

Remark. With these constants H4 does not literally imply LD (H4 gives E_j(T) ≤ 16|𝒦_j|(T_j/T)⁴); both imply BI.

**Corollary 1.5 (finite certificate; proved).** If ΣBI(η,λ; m, a) holds then
N(a) ≥ S(A_a, z) − 1 − (1 + η/2)·ρ·Σ_j ι_j|𝒦_j|.

This is the synthesis's Lemma C′ in the form used below.

---

## 2. The asymptotic inputs, as named propositions

Each is a statement about integers and primes with no reference to a or to GRH. "Quoted" inputs are published
theorems; "derived" inputs follow from the quoted ones by the short arguments given.

**IN-T1 (Type I for A_a; quoted, Fouvry–Shparlinski).** For every ε > 0 there is m₁(ε) such that for all m ≥ m₁,
all units a, and all 1 ≤ d ≤ m with (d,m) = 1:

 |#{n ∈ A_a : d | n} − |P|/d| ≤ m^{15/16+ε}.

Source: Shparlinski, arXiv:1705.06087, Lemma 5.4 (bound for Δ₁(a; x, y) with x = m, y = m/d) and the first display of
§7 [READ this session]; the underlying bound for Σ_{p≤x} e_m(a p̄) is Fouvry–Shparlinski, "On a ternary quadratic
form over primes" (Acta Arith. 2011), Thm 3.1, for arbitrary modulus m [SECONDARY: as quoted in 1705.06087 (5.1)].
At x = m the bound reads m^{15/16} + m^{1/4+2/3} = m^{15/16} + m^{11/12}. The source's main term is π(m)/d; the
difference ω(m)/d is absorbed. The o(1) is uniform in a and d.

**IN-FL (fundamental lemma, dimension 1; quoted).** There are absolute C_F ≥ 1 and s₀ ≥ 1 with the following
property. Let 𝒜 be a finite set of positive integers, 𝒫 a set of primes, z ≥ 2, 𝒫(z) = Π_{p<z, p∈𝒫} p,
V(z) = Π_{p<z, p∈𝒫}(1 − 1/p), and suppose #{n ∈ 𝒜 : d | n} = Y/d + r_d for all d | 𝒫(z). Then for D ≥ z^{s₀},
s = log D/log z:

 |#{n ∈ 𝒜 : (n, 𝒫(z)) = 1} − Y·V(z)| ≤ C_F·e^{−s}·Y·V(z) + Σ_{d | 𝒫(z), d < D} |r_d|.

Source: Friedlander–Iwaniec, *Opera de Cribro*, Cor. 6.10 (with κ = 1, s ≥ 9κ + 1) [RECALLED numbering and the
shape e^{9κ−s}]; Halberstam–Richert, *Sieve Methods*, Thm 2.5 [RECALLED]; Iwaniec–Kowalski Lemma 6.3 [RECALLED].
The density 1/p on a subset 𝒫 of the primes satisfies the dimension-1 condition with an absolute constant.

**IN-M (Mertens with the constant; quoted).** Π_{p<z}(1 − 1/p) = (e^{−γ}/log z)(1 + O(1/log z)) for z ≥ 2.
Source: Mertens 1874; Montgomery–Vaughan, *Multiplicative Number Theory I*, Thm 2.7(e) [RECALLED numbering].

**IN-PNT (quoted).** π(x) = (1 + o(1))x/log x. Used only as: for every ε > 0, π(x) ≥ (1 − ε)x/log x for x ≥ x₀(ε), and
π(2x) − π(x) ≥ x/(2 log x) for x ≥ x₀. Source: Montgomery–Vaughan Thm 6.9.

**D-BT (sieve upper bound in intervals; derived from IN-FL, IN-M).** There is an absolute C₂ ≥ 1 such that for all
real x ≥ 0 and H ≥ y ≥ 2: #{x < n ≤ x + H : P⁻(n) ≥ y} ≤ C₂H/log y.
*Derivation.* Apply IN-FL to the integers in (x, x+H] with Y = H, |r_d| ≤ 1, 𝒫 = all primes, z′ = y^{1/(2s₀)},
D = y^{1/2} ≤ H^{1/2}: the count is ≤ (1 + C_F)H·V(z′) + H^{1/2} ≤ C₂H/log y by IN-M (for y below an absolute bound
the claim is trivial). ∎ Consequences used: (i) Φ(X, y) ≤ 1 + C₂X/log y for all X ≥ 0, y ≥ 2 (if X < y the count is
≤ 1); (ii) #{primes in [M, M + H)} ≤ 2C₂H/log M for M^{1/2} ≤ H ≤ M (primes ≥ M in the interval are H-rough; the
endpoint costs at most 1, absorbed in the constant).
Also standard as Montgomery–Vaughan Thm 3.3 [RECALLED].

**D-RNL (lower bound for rough numbers; derived from IN-FL, IN-M, IN-PNT).** There are absolute c₂ > 0, y₀ such that
Φ(x, y) ≥ c₂x/log y for all y ≥ y₀ and x ≥ 2y.
*Derivation.* Let s₁ ≥ s₀ with C_Fe^{−s₁} ≤ 1/2. If x ≥ y^{2s₁}: IN-FL with D = x^{1/2}, |r_d| ≤ 1 gives
Φ(x,y) ≥ ½xV(y) − x^{1/2} ≥ c·x/log y. If 2y ≤ x < y^{2s₁}: Φ(x,y) ≥ π(x) − π(x/2) ≥ x/(4 log x) ≥ x/(8s₁ log y). ∎
Also a consequence of Φ(x,y) = ω(u)x/log y − y/log y + O(x/log²y) with Buchstab's ω ≥ 1/2 (de Bruijn 1950;
Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Thm III.6.4 [RECALLED numbering]).

**D-RNA (main term with e^{−γ}; derived from IN-FL, IN-M).** For 0 < η ≤ 1/(2s₀) and m ≥ m₂(η):

 Φ_m(m, m^η) ≤ Φ(m, m^η) ≤ (e^{−γ}/η)·(m/L)·(1 + C_Fe^{−1/(2η)})·(1 + C/(ηL)) + m^{1/2}.

*Derivation.* IN-FL for the integers ≤ m, Y = m, |r_d| ≤ 1, z = m^η, D = m^{1/2}, then IN-M. ∎

**Elementary facts used without a name.** ω(m) ≤ log₂m; #{primes p | m, p ≥ m^η} ≤ 1/η; 2^{ω(m)} = m^{o(1)}
(more precisely ≤ m^{1/log log m} for large m); #{n ≤ x : (n,m) = 1} = xφ/m + θ·2^{ω(m)}, |θ| ≤ 1.

### Lemma 2.1 (TypeISifted; proved from IN-T1, IN-FL)

Let 0 < η ≤ 1/(17s₀), z = m^η. There is an absolute C₆ and m₃(η) such that for m ≥ m₃(η) and every unit a:

 **S(A_a, z) ≥ ρ·Φ_m(m, z)·(1 − C₆e^{−1/(17η)}) − m^{1−1/300}.**

*Proof.* Let 𝒫 = primes not dividing m, D = m^{1/17}, s = 1/(17η) ≥ s₀. Elements of A_a are units, so
S(A_a, z) = #{n ∈ A_a : (n, 𝒫(z)) = 1}. By IN-T1 with ε = 10⁻⁴, Y = |P| and |r_d| ≤ m^{15/16+ε}:
S(A_a, z) ≥ |P|V(z)(1 − C_Fe^{−s}) − m^{1/17+15/16+ε}. For 𝒩 = {n ≤ m : (n,m) = 1}: #𝒩_d = φ/d + θ2^{ω(m)}, and
#{n ∈ 𝒩 : (n, 𝒫(z)) = 1} = Φ_m(m,z), so Φ_m(m,z) ≤ φV(z)(1 + C_Fe^{−s}) + m^{1/17}2^{ω(m)}. Eliminate V(z):

 S(A_a,z) ≥ ρ(Φ_m(m,z) − m^{1/17+o(1)})·(1 − C_Fe^{−s})/(1 + C_Fe^{−s}) − m^{271/272+ε} ≥ ρΦ_m(m,z)(1 − 2C_Fe^{−s}) − m^{1−1/300}. ∎

This is the Lean proposition `TypeISifted` of the synthesis, with C₆ = 2C_F.

---

## 3. Lemma 2.2: the count of rough numbers in the blocks (proved)

Let B₀ := Σ_{z ≤ p₁ < √m, p₁∤m} Φ_m((m−1)/p₁, p₁) = #{1 < n < m : (n,m) = 1, z ≤ P⁻(n) < √m}. By Lemma C applied to the
units, B₀ = Φ_m(m, z) − 1 − #{p ∈ P : p ≥ √m}. (For n coprime to m, n ≤ m/p₁ and n ≤ (m−1)/p₁ are the same.)

**Lemma 2.2.** Let C₁ = 8C₂/c₂ and C₅ = 400C₂². For 0 < η < 1/2, 0 < λ ≤ 1 and m ≥ m₄(η, λ), the block system
𝔅(m, η, λ) satisfies

 **Σ_{j<J} ι_j·|𝒦_j| ≤ (1 + C₁λ)·B₀ + C₅·log(2/λ)·m/L².**

Since B₀ ≥ c·m/L, the second term is O_λ(1/L) relative to B₀.

### 3.1 Proof

Put Y* = √(λm)/2. Call block j *bulk* if M_{j+1} ≤ Y* and *top* otherwise. Assume m so large that z ≥ max(y₀, 4λ^{−2}), m ≥ 256/λ²,
z/log z ≥ 4/(ηc₂), and (1/2 − η)L ≥ 2 log 2. Then λ/2 ≤ λ_m ≤ λ, log M_{j+1} ≤ 2 log M_j, and by D-BT(ii)

 (3.1) ι_j ≤ 2C₂λM_j/log M_j for every j.

**Bulk blocks.** Fix a bulk block j and p₁ ∈ I_j; write M = M_j, x = m/p₁. Then p₁ < Y*, so x > 2√(m/λ) > 4p₁. Split

 |𝒦_j| − Φ_m(x, p₁) = #{k ∈ (x, m/M] : (k,m) = 1, P⁻(k) ≥ M} + #{k ≤ x : (k,m) = 1, M ≤ P⁻(k) < p₁} =: (i) + (ii).

(i) m/M − x = x(p₁/M − 1) < λx, and λx = λm/p₁ > λm/Y* = 2√(λm) > Y* > M. So D-BT applies with H = λx ≥ y = M:
(i) ≤ C₂λx/log M.

(ii) Such a k is p′k′ with p′ = P⁻(k) ∈ I_j, p′ < p₁, and k′ ≤ x/p′, P⁻(k′) ≥ p′. By D-BT(i) and (3.1):
(ii) ≤ Σ_{p′∈I_j}(1 + C₂x/(p′ log p′)) ≤ ι_j + C₂ι_jx/(M log M) ≤ ι_j + 2C₂²λx/log²M ≤ ι_j + C₂λx/log M
for m large (log M ≥ ηL ≥ 2C₂).

Lower bound. By D-RNL (x ≥ 2p₁, p₁ ≥ y₀) and since at most 1/η primes ≥ z divide m,
Φ_m(x, p₁) ≥ c₂x/log p₁ − x/(ηp₁) ≥ (c₂/2)x/log p₁ ≥ (c₂/4)x/log M.

Hence (i) + (ii) ≤ 2C₂λx/log M + ι_j ≤ C₁λ·Φ_m(x, p₁) + ι_j. Summing over p₁ ∈ I_j:

 (3.2) ι_j|𝒦_j| ≤ (1 + C₁λ)·Σ_{p₁∈I_j} Φ_m(m/p₁, p₁) + ι_j².

Summing over bulk j: the first sum is ≤ (1 + C₁λ)B₀ (all terms of B₀ are ≥ 0), and by (3.1) and D-BT

 Σ_j ι_j² ≤ (max_j ι_j)·π(√m) ≤ (4C₂λ√m/L)·(5C₂√m/L) = 20C₂²λ·m/L².

**Top blocks.** For a top block, M_j ≥ Y*/(1+λ) ≥ m^{1/4}, so log M_j ≥ L/4. By (3.1) and D-BT(i),

 ι_j|𝒦_j| ≤ (2C₂λM_j/log M_j)·(1 + C₂(m/M_j)/log M_j) ≤ 4C₂²λm/log²M_j ≤ 64C₂²λ·m/L².

The top blocks have M_{j+1} > Y* and M_j < √m, so their number is at most
log(√m/Y*)/log(1+λ_m) + 1 ≤ (4/λ)·log(2/√λ) + 1. Their total is ≤ 64C₂²(4 log(2/√λ) + λ)·m/L² ≤ 350C₂² log(2/λ)·m/L²
(use λ ≤ 1 ≤ 1.45·log(2/λ)).

Adding the two parts (20λ + 350 log(2/λ) ≤ 400 log(2/λ)) gives the lemma with C₅ = 400C₂². ∎

### 3.2 What the proof uses

D-BT (twice: rough numbers in an interval of length λx ≥ M, and primes in [M, (1+λ)M)), D-RNL (once, with x ≥ 4p₁),
and counting. No asymptotic formula for Φ in short intervals is needed, and nothing about the top blocks beyond
the trivial upper bound.

### 3.3 The top blocks: why the round-1 sketch was wrong there, and why it does not matter

For the last block (M = √m/(1+λ_m)) one has 𝒦 = {1} ∪ {primes in [M, (1+λ_m)√m]}, so |𝒦| ≈ 2ι and ι|𝒦| ≈ 2ι²,
while the true count Σ_{p₁∈I}Φ_m(m/p₁, p₁) = ι + #{(p₁, p₂) : p₁ ∈ I, p₁ ≤ p₂ ≤ m/p₁} ≈ ι². The ratio is 2, not
1 + O(λ). The same happens, with a ratio between 1 and 2, in every block with M ≥ √(λm): there the cut-off
k ≤ m/p₁ moves by more than the length of the available k-range. The pointwise comparison (i) needs the interval
(m/p₁, m/M] to be longer than M, which is the condition p₁ ≲ √(λm).
Each block carries ≍ λm/L², the top range [√(λm)/2, √m) has O(log(1/λ)/λ) blocks, and B₀ ≍ m/(ηL), so the loss
is a relative O(η log(1/λ)/L).

### 3.4 Numerical check (computed)

`compute/harness/lemma22_check.py`, output `out_lemma22_check.txt`. η = 1/4. "bulk" and "top" as in the proof.

| m | λ | J | Σι\|𝒦\|/B₀ − 1 | bulk: (maj/B₀ − 1)/λ | top: #blocks | top: maj/(m/L²) |
|---|---|---|---|---|---|---|
| 1000003 | 1 | 5 | 0.572 | 0.50 | 2 | 6.8 |
| 1000003 | 0.25 | 16 | 0.154 | 0.53 | 7 | 5.5 |
| 1000003 | 0.05 | 71 | 0.027 | 0.42 | 46 | 7.9 |
| 4000037 | 1 | 6 | 0.511 | 0.45 | 2 | 6.0 |
| 4000037 | 0.1 | 40 | 0.064 | 0.56 | 20 | 6.5 |
| 4000037 | 0.05 | 78 | 0.029 | 0.45 | 45 | 7.8 |
| 4190209 = 2047² | 0.25 | 18 | 0.143 | 0.48 | 7 | 5.1 |

Reading: on bulk blocks the excess is ≈ 0.5λ (so the true C₁ is about 1/2), and the top-block majorant is
≈ (4 to 8)·m/L², growing slowly as λ decreases, as the lemma predicts. At these m the factor 1/L is not small and
the top blocks are 26–55% of B₀; the overall ratio is still 1 + 0.55λ because their true counts are of the same
size as their majorants. (2047 = 23·89, so the last row is a composite square, not r² with r prime.)

---

## 4. The theorem (proved from the named inputs)

**Theorem E.** Let κ = 1/(4C₁) with C₁ as in Lemma 2.2. There is an absolute η₀ > 0 such that for every 0 < η ≤ η₀
and every 0 < λ ≤ κη there is m₀(η, λ) with: for all m ≥ m₀ and every unit a mod m,

 **ΣBI(η, λ; m, a) ⇒ N(a) ≥ 0.4·μ.**

Inputs: IN-T1, IN-FL, IN-M, IN-PNT. GRH is not used.

*Proof.* Let z = m^η, s = 1/(17η), Φ = Φ_m(m, z), Σ = Σ_j ι_j|𝒦_j|, P_≥ = #{p ∈ P : p ≥ √m} ≥ |P| − √m.
By Corollary 1.5, Lemma 2.1, Lemma 2.2 and B₀ = Φ − 1 − P_≥:

 N(a) ≥ ρΦ(1 − C₆e^{−s}) − m^{1−1/300} − 1 − (1 + η/2)ρ[(1 + C₁λ)(Φ − P_≥) + C₅ log(2/λ)m/L²].

Put β = (1 + η/2)(1 + C₁λ) − 1. Since C₁λ ≤ η/4, 0 ≤ β ≤ 3η/4 + η²/8 ≤ η. So

 N(a) ≥ ρ(1 + β)P_≥ − ρΦ(β + C₆e^{−s}) − 2C₅ρ log(2/λ)m/L² − m^{1−1/300} − 1
   ≥ ρ(|P| − √m) − ρΦ·η·(1 + C₆e^{−1/(17η)}/η) − 2C₅ρ log(2/λ)m/L² − m^{1−1/300} − 1.

Fix ε = 0.005. By D-RNA, for η ≤ η₁ (where C_Fe^{−1/(2η)} ≤ ε/2) and m large, ηΦ ≤ (e^{−γ} + ε)m/L. By IN-PNT and
ω(m) ≤ log₂m, m/L ≤ (1 + ε)|P| for m large. Choose η₀ ≤ min(η₁, 1/(17s₀)) with C₆e^{−1/(17η)}/η ≤ 0.01 for η ≤ η₀. Then

 ρΦη(1 + C₆e^{−1/(17η)}/η) ≤ (0.5615 + 0.005)(1.005)(1.01)·ρ|P| ≤ 0.5751·μ.

The remaining terms: ρ√m ≤ εμ; 2C₅ρ log(2/λ)m/L² ≤ 3C₅ log(2/λ)μ/L ≤ εμ for m ≥ m₀(λ); and m^{1−1/300} + 1 ≤ εμ because
μ ≥ |P|²/m ≥ m/(2L²). Hence N(a) ≥ (1 − 0.5751 − 3ε)μ ≥ 0.4099·μ. ∎

**Corollary H4.** With κ, η₀, m₀ as above: if H4(η, λ; m) holds then N(a) ≥ 0.4μ for every unit a mod m.
**Corollary LD.** The same with LD(η, λ; m) in place of H4.
*Proof.* Corollary 1.4 and Theorem E. ∎

Remarks.
1. **Constants.** η₀ is tied to the Type I level by C₆e^{−1/(17η)} ≤ η/100, so η₀ is of order 1/100–1/150 (C₆ = 2C_F not
   computed), λ ≤ κη with κ = c₂/(32C₂), the constant in H4 is (η/2)⁴ ≈ 10⁻⁹, and m₀ is astronomically large.
   A Type I level m^θ would replace 1/17 by any number below θ.
2. **Positivity alone.** The same proof gives N(a) > 0 from ΣBI with η/2 replaced by θ, for any constant
   θ < (e^{γ} − 1/4)η ≈ 1.53η (the condition is (θ + η/4)·e^{−γ}/η < 1), for η ≤ η₀(θ) and m large. Compare the
   remark after Thm BH (1.7η there, before the loss C₁λ = η/4).
3. **Only an upper bound on the block sums is used**, and only on the arc {a·k̄ : k ∈ 𝒦_j}; H4 and LD extend it to all
   of G so that a disappears.
4. **What depends on a:** only Lemma 2.1 (through IN-T1, uniform in a) and ΣBI.

---

## 5. Proposition Q for composite m (proved)

For the quotient problem the block count is π⁻_j(c) = #{p₁ ∈ I_j : c·p₁ mod m ∈ P}, δ⁻_j(c) = π⁻_j(c) − ρι_j.
(With X = P⁻¹ in the role of P in §1, δ^X_j(c) = δ⁻_j(c̄).) Let φ(m; B) = #{1 ≤ b ≤ B : (b,m) = 1}.

**Proposition Q′.** For every m, every block system and every j < J, with B_j = ⌊(m−1)/M_{j+1}⌋:

 Σ_{c∈G} δ⁻_j(c)⁴ ≥ (φ(m; B_j) − 1)·(ρι_j)⁴ + (1 − ρ)⁴·ι_j⁴.

Moreover φ(m; B) ≥ Bφ/m − 2^{ω(m)}, so for m ≥ m₅ the right side is ≥ (φ/(2M_{j+1}))·(ρι_j)⁴, and

 Σ_c δ⁻_j(c)⁴ / [(η/2)⁴ρ⁴ι_j⁴|𝒦_j|] ≥ (2/C₂)·(φ/m)·(log M_j)/η⁴ ≥ c·(φ/m)·L/η³ → ∞.

So the conjugate of H4(η, λ; m) fails for every block and every large m, prime or composite.

*Proof.* Let 2 ≤ b ≤ B_j with (b,m) = 1 and p₁ ∈ I_j. Then bp₁ < B_jM_{j+1} ≤ m − 1, so the residue b·p₁ mod m is the
integer bp₁, which is composite. Hence π⁻_j(b) = 0 and δ⁻_j(b) = −ρι_j. These b are distinct classes of G, and
there are φ(m; B_j) − 1 of them. For c = 1: π⁻_j(1) = ι_j. This gives the first display.
φ(m; B) = Σ_{d|m}μ(d)⌊B/d⌋ ≥ Bφ/m − 2^{ω(m)}, and B_j ≥ √m − 2 while 2^{ω(m)} = m^{o(1)}, so φ(m;B_j) − 1 ≥ φ/(2M_{j+1}).
|𝒦_j| ≤ 1 + C₂(m/M_j)/log M_j ≤ 2C₂(m/M_j)/log M_j by D-BT, and M_{j+1} ≤ 2M_j. ∎

**The error in round 1.** The count there was "⌊m/((1+λ)M_j)⌋ − 1 − ω(m)", which subtracts the number of prime
divisors of m instead of the number of integers b ≤ B not coprime to m. For prime m the two differ by one, which is
harmless. For composite m the correct count is φ(m;B) − 1 ≈ Bφ/m. The conclusion survives with the factor φ/m ≫ 1/log log m.

**LD is one-sided, and Proposition Q′ does not refute its conjugate.** The classes found above have *negative*
deviation, and LD only restricts {δ > T}. Since Σ_cδ⁻_j(c) = 0 the deficit must be compensated, but the compensating
mass (φ/M)ρι could be spread over all φ classes. The conjugate of LD is expected to fail for a different reason
(heuristic): for small-height classes c = u/v with v ≥ 2, the residue c·p₁ is a linear form (up₁ + jm)/v in p₁, and
the prime-pair singular series is either 0 or ≥ 1.32. There are ≍ m/M such classes with relative deviation ≥ 0.3,
against the LD allowance ≍ η²(m/M)/log M. The harness shows the effect on the arc statistic (max over a of 0.27–0.37
for P⁻¹ against 0.044–0.049 for P, §7), but the tail counts E_j(T_j) at m ≈ 10⁶ are dominated by noise for every
object. **A proof that the conjugate of LD fails is not available here.**

---

## 6. Lean-facing statements (not typechecked; shapes only)

Named propositions, all GRH-free. Each needs a docstring with the citation in §2.

- `TypeISifted : Prop` := ∃ C₆ ≥ 1, ∃ η₁ > 0, ∀ η ∈ (0, η₁], ∃ m₃, ∀ m ≥ m₃, ∀ a unit,
  S(A_a, m^η) ≥ ρ·Φ_m(m, m^η)·(1 − C₆·exp(−1/(17η))) − m^{1 − 1/300}. Unconditional theorem: Lemma 2.1
  (Fouvry–Shparlinski Type I + fundamental lemma).
- `RoughCounts : Prop` := the conjunction of
  (a) D-BT: ∃ C₂, ∀ x ≥ 0, ∀ H ≥ y ≥ 2, #{x < n ≤ x+H : P⁻(n) ≥ y} ≤ C₂H/log y;
  (b) D-RNL: ∃ c₂ > 0, y₀, ∀ y ≥ y₀, ∀ x ≥ 2y, Φ(x,y) ≥ c₂x/log y;
  (c) D-RNA′: ∀ ε > 0, ∃ η₁ > 0, ∀ η ∈ (0, η₁], ∃ m₂, ∀ m ≥ m₂, η·Φ(m, m^η) ≤ (e^{−γ} + ε)·π(m).
  Unconditional (sieve upper bound; Buchstab–de Bruijn; Mertens + PNT). Form (c) is stated against π(m) so that the
  Lean proof of Theorem E needs no separate prime number theorem, only Chebyshev (π(m) ≥ m/(2 log m)) for the
  error terms.
- `H4 (η λ : ℝ) : Prop` := ∃ m₁, ∀ m ≥ m₁, ∀ j < J(m,η,λ), Σ_{c : (ZMod m)ˣ} δ_j(c)⁴ ≤ (η/2)⁴·ρ⁴·ι_j⁴·|𝒦_j|.
  **Beyond GRH; stronger than EOS (it gives N(a) ≥ 0.4μ); not known to follow from GRH.**
- `LD (η λ : ℝ) : Prop` := the same with E_j(2^iT_j) ≤ |𝒦_j|·4^{−i}/4 for all i.

Theorems:
1. `buchstab_certificate` (Corollary 1.5 with Lemmas C, 1.1–1.3): unconditional and finite.
2. `eos_of_H4 : TypeISifted → RoughCounts → (∃ κ η₀ > 0, ∀ η ≤ η₀, ∀ λ ≤ κ·η, H4 η λ → Conjecture)`, and the same
   for LD. The honest signature has **three** inputs. The shape `eos_of_H4 (hT : TypeISifted) (hH : H4 η) : Conjecture`
   in the project rules is reached either by bundling `RoughCounts` into the statement as a second cited hypothesis
   or by fixing λ = κη inside the definition of `H4 η`; the latter makes the definition depend on the constants
   c₂, C₂ of `RoughCounts`, so I recommend the explicit two-parameter form.

Lean cost: the exact part is finite combinatorics. Lemma 2.2 is about 60 lines of inequalities from `RoughCounts`.
Theorem E is real-number bookkeeping with e^{−γ} < 0.5616.

---

## 7. Barrier harness (computed)

Script `compute/harness/barrier_harness.py`; outputs `out_harness_1000003.txt` (prime m), `out_harness_1018081.txt`
(m = 1009²), `out_harness_1000003_lam025.txt` (λ = 1/4). Usage: `python3 barrier_harness.py m eta lam seed`. It needs
a cyclic unit group (discrete-log FFT), so highly composite m is not covered.

For a set X of units of density ρ_X in the role of P, the script evaluates per block: variance relative to the
Bernoulli model, kurtosis, the H4 ratio Σ_cδ⁴/((η/2)⁴ρ_X⁴ι⁴|𝒦|) (H4 asks ≤ 1), the LD ratio
max_i E(2^iT_j)/(|𝒦|4^{−i}/4) (LD asks ≤ 1), E(T_j)/|𝒦|, and the arc statistic
arc_j(a) = Σ_{k∈𝒦_j}δ_j(a/k)/(ρ_Xι_j|𝒦_j|) for **all** a at once (BI asks ≤ η/2); and over all blocks
T(a) = Σ_jΣ_kδ_j(a/k)/(ρ_XΣ_jι_j|𝒦_j|) (ΣBI asks ≤ η/2).

Objects: P; P⁻¹; P ∖ R_a; A\*_a (X = a·(A\*)⁻¹, A\* random of density ρ, no primes ≥ z, z-rough composites boosted by
1 + κ, the simplified construction of `compute/routeA/typeII_vaughan.py`); a random set of density ρ with
X ∩ aX⁻¹ = ∅; and RS_a, a **deterministic antisymmetric signing** f(a/x) = −f(x) built from the Rudin–Shapiro sequence
in discrete-log coordinates, X = {f = 1}, density 1/2, with max_χ|f̂(χ)| = 2.4–2.5·√φ measured. RS_a replaces the
Spencer signing of route C's Prop L, which is an existence statement and cannot be computed at this size; it has
the same properties (no pair in class a, Fourier coefficients O(√φ) without a log). a-dependent objects are built
for a = argmin N and for one random a; the tables give a = argmin N.

Parameters: η = 1/4 (z ≈ 31.6), λ = 1, five blocks. These are far from the η ≈ 1/100 of Theorem E, which cannot be
simulated.

### 7.1 Whole-group statistics (H4, LD), m = 1000003; the ranges are over the five blocks

| Object | ρ_X | var | kurtosis | H4 ratio | LD ratio | E(T_j)/\|𝒦_j\| |
|---|---|---|---|---|---|---|
| P | 0.0785 | 0.955–0.967 | 3.07–3.88 | 1.4·10⁶–8.6·10⁶ | 0.8·10⁵–1.4·10⁵ | 91–1677 |
| P⁻¹ | 0.0785 | 0.955–0.967 | 3.41–4.28 | 2.0·10⁶–8.7·10⁶ | 0.8·10⁵–1.3·10⁵ | 91–1677 |
| P ∖ R_a | 0.0728 | 0.959–0.970 | 3.10–4.03 | 1.7·10⁶–1.1·10⁷ | 0.7·10⁵–1.9·10⁵ | 86–2135 |
| A\*_a | 0.0785 | 0.999–1.002 | 3.11–4.12 | 1.6·10⁶–9.8·10⁶ | 0.8·10⁵–1.5·10⁵ | 90–1681 |
| random avoiding | 0.0786 | 0.998–1.002 | 3.12–4.13 | 1.6·10⁶–9.8·10⁶ | 0.8·10⁵–1.5·10⁵ | 90–1692 |
| RS_a | 0.5 | 0.997–1.002 | 2.71–2.98 | 1.1·10⁴–4.7·10⁴ | 3·10³–9·10³ | 103–1547 |

The m = 1009² table agrees closely: variances and kurtoses to the second decimal, H4 ratios within 5%, LD ratios
within a factor 2 (they depend on a maximum over thresholds).

**Reading.** At m ≈ 10⁶ and η = 1/4, H4 and LD fail for every object by factors 10⁴–10⁷, and they fail equally:
the fourth moment is the Gaussian noise 3φρ²ι², which exceeds the threshold until M ≳ (log m)⁵/η⁴. **There is no
P-versus-A\* gap in the H4 or LD statistics at this size** (ratio A\*/P = 1.11–1.14, entirely the 4% variance
deficit of P). The only whole-group signal is the conjugate's kurtosis in the top block (4.28 against 3.07,
Proposition Q′). H4 and LD are not testable at any m within reach; this was already said in the analytic note §4.1.

### 7.2 Arc statistics (BI, ΣBI): this is where the objects separate

| | m = 1000003 | | | m = 1018081 = 1009² | | |
|---|---|---|---|---|---|---|
| Object | max_a T | sd_a T | T(a₀) | max_a T | sd_a T | T(a₀) |
| P | **0.044** | 0.0093 | – | **0.049** | 0.0092 | – |
| P⁻¹ | 0.277 | 0.0093 | – | 0.272 | 0.0092 | – |
| P ∖ R_a | 0.081 | 0.0097 | 0.081 | 0.096 | 0.0097 | 0.096 |
| A\*_a | 0.726 | 0.0101 | **0.726** | 0.724 | 0.0100 | **0.724** |
| random avoiding | 0.048 | 0.0100 | −0.002 | 0.048 | 0.0100 | 0.002 |
| RS_a | 0.014 | 0.0029 | 0.005 | 0.014 | 0.0029 | 0.003 |

Thresholds for these parameters: ΣBI asks T(a) ≤ η/2 = 0.125. The exact certificate (Corollary 1.5 with
S(A_a, z) = ρΦ_m) gives N(a) > 0 when T(a) < (Φ_m − 1/ρ − Σι|𝒦|)/Σι|𝒦| = 0.305 (λ = 1) or 0.777 (λ = 1/4).

**The P-versus-A\* gap.** Over all φ ≈ 10⁶ classes a, the primes have max_a T(a) = 0.044 (prime m) and 0.049
(m = 1009²), which is 4.7 and 5.3 standard deviations of T. The parity object has T = 0.71–0.74 at its own class:
a factor 15–17 above the worst class of P, and about 70 standard deviations. With λ = 1/4 the numbers are 0.049
against 0.92–0.93. So at m ≈ 10⁶ the target is: prove T(a) ≤ 0.125 (or anything below 0.3) for every a, where the
truth is 0.05 and the parity object sits at 0.7. That is a constant-factor gap, as Theorem E says it should be.
It is visible only on the arc, not in a-independent moments, at this size.

Other readings.
- **Per-block BI fails for P at this size** in the top block: max_a arc_j(a) = 0.142 (prime m) and 0.152 (1009²)
  against 0.125, with 0.09–0.12 in the other four blocks; for λ = 1/4 every block exceeds 0.125 (0.15–0.47).
  The sum over blocks is fine. This is small-number noise (|𝒦_j| = 207), but it is the reason Theorem E is stated
  with ΣBI.
- **Conjugation.** P⁻¹ has max_a T = 0.27–0.37, six to eight times the value for P, and per-block maxima up to 1.09
  (λ = 1) and 7.9 (λ = 1/4, a block with one prime): the small-height classes of the quotient problem. These
  values are still below the certificate thresholds 0.305 and 0.777, so **at this size the arc statistic alone
  does not exclude the quotient problem**. What excludes it is the sifted count: for X = P⁻¹ and a = −1 the set
  A is {m − p}, which is all even, so Lemma 2.1 fails at d = 2. Asymptotically Proposition Q′ adds the failure
  of the conjugate H4.
- **Deletion.** P ∖ R_a has T(a) = 0.08–0.10 ≈ N(a)/|P|: the arc sees only the change of density. As the analytic
  note says, deletion is caught by the exact cardinality in Lemma 2.1, not by the block statistics.
- **Random avoiding set and RS_a** are indistinguishable from random sets in every statistic, as expected: for them
  the route proves a ∈ X·P, which is true.
- **Prime versus r².** No systematic difference in any statistic. The structured empty fibres of
  route D §2.3 for m = r² do not show up after summing over c or over the arc.

### 7.3 Not done

Highly composite m (the unit group is not cyclic; the script would need a multi-dimensional FFT); m ≈ 10⁷; the
F₂[t] version of the δ_I law; the genuine Theorem B construction of A\* (dyadic products of two primes with smooth
weights) in place of the uniform boost; a true Spencer signing.

---

## 8. Not checked

- IN-FL: theorem numbers and the exact form of the error factor are recalled, not re-read. The proof needs only
  some bound C_Fe^{−s} with s = log D/log z ≥ s₀.
- IN-T1: I read Shparlinski's Lemma 5.4 and §7 (arbitrary modulus, uniform in a). Fouvry–Shparlinski's Thm 3.1
  itself was not read.
- The constants C₂, c₂, C_F, s₀, hence C₁, κ, η₀, are not computed. The numerics suggest C₁ ≈ 1/2.
- Theorem E was not tested numerically as a whole (η ≈ 1/100 is out of reach); Lemma 2.2 and the exact part were.
- H4 and LD themselves: nothing here bears on whether they are true or provable.
