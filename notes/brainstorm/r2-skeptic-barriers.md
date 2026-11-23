# Round 2, barrier skeptic: verdicts on the fifteen round-1 proposals

Written 2026-11-22. Standing hypothesis: GRH for Dirichlet L-functions; anything more is flagged **[EXTRA]**.
Status tags as in the other notes: *proved*, *sketched*, *heuristic*, *computed*, [UNVERIFIED].
Notation as in `00-setup.md`: G, φ, L = log m, P, S(χ), N(a), N⁻(a), λ = |P|²/φ, ρ = |P|/φ, A_a = {a·p̄ mod m}.

**What I did.** For each proposal I looked for an object that satisfies every input the proposal uses and makes the
EOS conclusion false. The objects: (1) random pairing-avoiding set R; (2) P′ = P ∖ R_a; (3)/(4) route A's A\*
(parity example with correct Type I data and GRH-size character sums); (5) Prop L's Spencer-signed Θ\*;
(6) the conjugate pair (P, P⁻¹). Where a proposal is a conditional reduction "H ⇒ EOS", no object can break a valid
implication, so I tested the *hypothesis*: which objects satisfy everything a GRH proof of H could use and still violate H.

**Verdict scale.** *dead* = a barrier object satisfies all inputs and the conclusion fails, or the proposer's own
analysis shows this and I agree. *wounded* = valid as far as I can check, but its hypothesis is not weaker than the
problem, or a step is missing. *alive* = I tried to break the stated claim and failed. The stated claim is often weaker
than EOS; "EOS reach" is given separately in every row. Nothing is *promising* as a route to EOS.

## 0. Summary table

| Proposal | Verdict | EOS reach | Barrier object that decides it |
|---|---|---|---|
| Analytic 1: Buchstab + H4(η) | wounded | none without H4; H4 ⇒ more than EOS | A\*: has GRH-size sums and Type I data, violates H4 (their Prop S). So H4 is not provable from sizes + Type I. No object breaks the implication itself |
| Analytic 2: shrinking box a = q·x | alive as a side theorem | none | not EOS; also not conjugation-sensitive (§2.2) |
| Analytic 3: special moduli | wounded | none | A\* (Type I only); level capped at m^{1/4} by the Cauchy–Schwarz diagonal |
| Automorphic K: Kloosterman-dual | dead | none | R, P′, A\*, Θ\* all satisfy both identities (proposer agrees) |
| Automorphic TD: Titchmarsh divisor for A_a | wounded | none | A\* satisfies TD at every level < 1/2 |
| Automorphic FE: toy D₄ | alive as calibration | none | no barrier object exists for the toy; that is why it does not transfer |
| Geometer G1: Schur–Mellin ranks | wounded | none over Z | barrier (6) is vacuous in F_q[t] (§3, new, computed): the "pass" there is uninformative |
| Geometer G2: characteristic-2 structure | dead for Z | none | by design no transfer; own data show nothing special at q = 2 |
| Geometer G3: geometry over Z | dead | none | R, P′, Θ\* (proposer agrees) |
| Combinatorial R1: symmetry space / WL | alive as calibration | none | equivalent reformulation; for WL I found no barrier object inside multiplicative functions (§4.1) |
| Combinatorial R2: entropy decrement | dead | none | no class-preserving dilation of height ≤ √m (proposer's own proof) |
| Combinatorial R3: coset certificate | dead for EOS | none | P′ (coset counts are deletion-stable); Hyp V is a constant-< 2 prime-pair bound |
| Wildcard W1: Theorem W (a = p·q·s, s ≪ L²(log L)²) | alive (theorem) | none, provably | (P, P⁻¹): proof is conjugation-blind |
| Wildcard W2: Linnik format, exceptional-set structure | alive (theorem, one lemma unwritten) | none, provably | (P, P⁻¹) |
| Wildcard W3: F_q[t] transcription | alive (routine) | none | (P, P⁻¹) |

Three things in this note are new: §1.2 (H4 written as an energy asymptotic, and a failed combination with Lemma M),
§3 (barrier 6 has no analogue in the F_2[t] test bed; computed), §4.1 (WL has no multiplicative barrier object under
rigidity).

---

## 1. Analytic Route 1 (Buchstab + H4): wounded

### 1.1 The implication survives every object

I checked the reduction Thm BH + Cor H4 against all six objects. I could not break it.

- **R (random, a ∉ R·R).** The route, run with R in place of P, concludes "a·R⁻¹ contains a true prime", i.e. a ∈ R·P.
  True. The proposer is right that P plays two roles. A sharper check: for a fixed generic t ∈ G, the dilate tP has the same
  H4 data (δ^{tP}(c) = δ^P(c/t)) and the same uniform Type I data (A_a for tP is A_{a/t} for P). So the route proves
  tP·P = G for every t, which is EOS again. No contradiction, and it shows the route never uses "the same set twice".
  (proved)
- **P′ = P ∖ R_a.** A′ = A_a minus its primes. H4 is unchanged to relative 1/L. The input that fails is the sifted count:
  S(A′, z) = S(A_a, z) − N(a) exactly. I rechecked the proposer's bookkeeping; it is correct in substance. Their
  phrasing "remainder ≍ N(a) log D" overstates it (take Y = |P| and r₁ = −N(a), then the remainder is N(a)), but the
  conclusion is the same: the route reads the number of primes in A_a off an exact count, which deletion changes.
  (proved)
- **A\*, Θ\*.** Both violate H4 by a constant factor (Prop S). This is a tautology: Prop S is the contrapositive of the
  implication. It carries no information about whether H4 is approachable.
- **(P, P⁻¹).** P⁻¹ in the role of P violates H4 (Prop Q) and violates T1 at a = −1, d = 2. Consistent.

So the reduction is sound as far as barrier objects can tell, modulo Lemma 2.2 (sketched) and the coupling η ≲ 1/100.

### 1.2 Why it is wounded: H4 is the problem, stated differently

1. **A\* kills every proof of H4 from sizes.** A\*_a (route A, Theorem B) has max_χ|S\*(χ)| ≪ √m·log-power, exact
   cardinality, Type I data to level m^θ, θ < 1/2, and violates H4. H4 is a-independent, but the family {P\*_a} of
   a-dependent sets each violates the a-independent statement. So "a-independent" gives no protection: any proof of H4
   must use an input that fails for P\*_a = a·(A\*)⁻¹, which means a Type II input for A_a. The checklist entries
   "(3), (4): pass conditional on H4" are therefore circular, not passes. (proved, given Theorem B of route A)
2. **H4 is stronger than EOS.** It gives N(a) ≥ 0.4μ for every a. The function-field analogue of an L⁴-in-c statement
   follows from Sawin's pointwise bound, not conversely (route B, line on Σ_a E(a)⁴). I expect the same here. [heuristic]
3. **H4 as a counting statement (new, sketched).** Σ_c π_j(c)⁴ is the four-fold coincidence count
   #{p·p₁ ≡ p′·p₁′ ≡ p″·p₁″ ≡ p‴·p₁‴}. The uncentred value is φ(ρ|I|)⁴. H4 asks for the centred moment to be
   ≤ η⁴ρ⁴|I|⁴|𝒦|, a fraction ≍ η⁴/(M log M) of that. So H4 is an asymptotic for an 8-prime modular count with
   **relative error M⁻¹**, a power saving for M = m^η. "Five logs below trivial" is correct but hides this. It is the
   same shape as M4 and as route B's L⁴ remark.
4. **The arc statement is a critical-volume ternary problem (proved).** What Thm BH uses is, per block,
   #{(p, p₁, k) : p·p₁·k ≡ a, p ≤ m, p₁ ∈ I, k ∈ 𝒦} ≤ (1 + η/2)·(expected). Volume |P||I||𝒦| ≍ m²/L³ against the
   GRH ternary threshold m²·L^C. I tried to combine this with the wildcard's Lemma M (Hölder with high energies):
   the Hölder exponents force ‖S‖₂ unless one factor is Sidon-like, and neither I·𝒦 products nor 𝒦 (|𝒦|² > φ for
   M < √m/L) is. The best bound is (1/φ)‖S‖₂‖U‖₄‖𝒦̂‖₄ ≍ (|P||I||𝒦|)^{1/2}, which misses by exactly L³/η² and uses no
   GRH. This is the proposer's "three logs" for LD. **The combination W1 × Analytic 1 gives nothing.** The deficit comes
   from three sparse densities, not from a sup norm, so the wildcard's device (which only removes the sup-norm loss)
   cannot help.
5. **All blocks at once is Prop L.** Σ_j is ⟨1_P − ρ, 1_{a·𝒞⁻¹}⟩ with 𝒞 the z-rough composites ≤ m, |𝒞| ≍ m/(ηL).
   Cauchy–Schwarz misses by L/η^{3/2}: one log, as always. The Spencer-signed set in the role of P against a generic
   set of size |𝒞| is the equality case. (proved)

### 1.3 Things I tried in order to refute H4 itself, and failed

- Small-height classes: for the direct problem c ≡ p·p₁ forces p·p₁ = c + jm with j ≥ 1 generic; I found no class with a
  forced deviation. (Prop Q's mechanism needs c·p₁ not to wrap; c·p̄₁ always wraps.) [heuristic]
- Composite or even m, square factors: not tested by the proposer (all numerics are for prime m). D §2.3 found
  structured empty fibres for m = r² at c ∈ {±1, ±3, ±1/3}; they disappear after summing over fibres, and H4 sums over
  all c, so I expect no failure. **Untested.** A run of `h4_moments.py` at m = r² and m = 2·3·5·7·11·13·k is cheap.

**Verdict: wounded.** A correct-looking sufficient condition with constant precision; no evidence that it is easier
than Type II for A_a, and proof (1) above that it cannot follow from the GRH-size data.

**Suggested test.** State H4 in F_q[t] and ask whether Sawin's machinery proves it in a range where it proves EOS. If
the eight-fold fibre product has Betti numbers that push the threshold above 7567, H4 is strictly harder than EOS in
the one setting where EOS is a theorem, and should be dropped.

## 2. The other analytic and automorphic proposals

### 2.1 Analytic 3 (special moduli): wounded

For EOS it is Route 1 with a better constant, so §1.2 applies. Against its own target: D §4.2 records that the
Cauchy–Schwarz diagonal caps the level at m^{1/4}. With θ = 1/4 the relation e^{−θ/η} ≪ η gives η ≈ 1/25, not 1/8.
The proposer's own estimate for the balanced range (m^{−1/24}) is below the existing 1/16. I see no evidence of a gain.
A\* has Type I data at every level < 1/2, so no level improvement touches parity.

### 2.2 Analytic 2 (shrinking box): alive as a side theorem, no EOS content

Not EOS, as stated. One caution about its use as a "bookkeeping test": the model is not conjugation-sensitive. The
quotient version (q ≡ a·x, x ≤ m^{1−δ}) is also true by Vinogradov-type sums, so the model never exercises barrier (6).
And the reason it closes (Σ_h|Î(h)| ≪ log m) is the property A\* is built to lack. It tests arithmetic, not the route.

### 2.3 Automorphic K: dead

I checked Lemma H by hand: γ = (∗, ∗; m, d) maps x/m + i/m to height 1/(m((x+d)² + 1)), so equal height forces d = −x
and the image is −x̄/m + i/m. Correct (proved). The identities hold for every set, so R, P′, A\*, Θ\* all satisfy them.
The Kloosterman singular series is real structure but has relative size 1/L of the noise per term and is shared by any
set with the same major-arc data. Dead as a route; keep the two lemmas and the correction to D §4.1(iii).

### 2.4 Automorphic TD: wounded (side result only)

A\* has the Type I data of A_a at every level below 1/2, so TD holds for A\* and TD cannot imply EOS. One point in its
favour that the proposer did not state: the conjugate, Σ_p d(m − p), is the classical Titchmarsh problem (known
unconditionally [UNVERIFIED recall: Linnik; Fouvry; Bombieri–Friedlander–Iwaniec]), while the product version needs
Kloosterman sums over primes. So TD is a clean place to see the product/quotient asymmetry in a provable setting.

### 2.5 Automorphic FE (toy D₄): alive as calibration

No barrier object applies: smooth variables have complete Type I data and no deletion. That is the weakness. A success
would use the functional equation, which S(χ) lacks. A failure would be informative. The unbalanced toy sits at the
classical level-2/3 threshold for d(n) in progressions; check the literature before working on it.

## 3. Geometer: barrier (6) is vacuous in the F_q[t] test bed (new)

G1, G2 and D §3 all record "(6) pass: the product variety is not the quotient variety". That is true and proves
nothing, because **in F_q[t] with P = monic irreducibles of degree exactly n = deg f the quotient problem has no
obstructed class.**

*Reason (sketched).* P₁ ≡ a·P₂ with a = u/v of small height is u·P₂ − v·P₁ = c·f. Over Z the obstruction at a = −1 is:
the wrap count is forced (k = 1) by the archimedean cut, and then the prime 2 forbids p + q = m. In F_q[t] the degree
and leading coefficient of c are forced, but its lower coefficients are free unless deg c = 0, and deg c = 0 needs
deg u = deg v ≤ 1 with cancelling leading terms. For q = 2 that leaves {u, v} = {t, t+1}, where the conditions at t and
t+1 are consistent. For q = 3 and constants a = −1 the equation P₁ + P₂ + f = 0 is locally solvable at every point.
The "interval" {deg = n, monic} is a coset of an additive subgroup, compatible with every local condition.

*Computed* (script and output in the session scratchpad,
`/private/tmp/claude-501/-Users-maxfeldman-Desktop-maths-research/9e4c9912-0c7a-4fa9-a228-3de7c709a385/scratchpad/ff2_conjugate.py`
and `out_ff2_conjugate.txt` in the same folder; not in the repo because I was told to write one file only). F_2[t],
f primitive, two moduli per degree, all classes by FFT:

| n | product: classes with N = 0 | product min N/λ | quotient: classes a ≠ 1 with N⁻ = 0 | quotient min, max N⁻/λ |
|---|---|---|---|---|
| 9 | 13, 16 | 0 | 0, 0 | 0.17–0.34, 1.86–2.03 |
| 10 | 7, 5 | 0 | 0, 0 | 0.21–0.32, 2.02–2.34 |
| 12 | 0, 0 | 0.22 | 0, 0 | 0.40–0.44, 1.76–1.80 |
| 14 | 0, 0 | 0.49–0.51 | 0, 0 | 0.52–0.56, 1.69–1.72 |
| 17 | 0, 0 | 0.70–0.75 | 0, 0 | 0.53–0.54, 1.67–1.71 |

The quotient count has singular-series structure (min ≈ 0.53λ, max ≈ 1.7λ, stable in n) but never vanishes, even at
n = 9, 10 where the product problem still has empty classes.

**Consequences.**
- A function-field proof may be conjugation-blind and still correct. So a proof of F_2[t]-EOS is *not* evidence of a
  mechanism that separates S² from |S|². D §3's sentence "a proof for q = 2 would be the first mechanism not obviously
  unavailable over Z" needs this caveat.
- The test bed is faithful for barriers (1)–(5) only. To make it faithful for (6) one needs a variant with an
  obstructed quotient class; I did not find one. Candidates to try: P = all irreducibles of degree ≤ n − 1 (not a
  coset), or a "sign" condition on the second coefficient.

**G1: wounded.** Function-field only. By the proposer's own heuristic, keeping signs gains a polynomial factor and the
growth ratio stays near 3.7–4, so the reach is q₀ ≈ 14–16 at best, never q = 2; and the tower experiment cannot see
rank. No transfer mechanism. **G2: dead for Z** by design; their own F_2 data show ordinary square-root behaviour.
**G3: dead**, agreed.

## 4. Combinatorial

### 4.1 R1 (symmetry space, WL): alive as a calibration problem, not a route

The reformulation is an equivalence, so no barrier object can satisfy its "inputs" and fail the conclusion; equally it
proves nothing. The useful part is WL. I tried to kill WL as a calibration problem by finding a barrier object, i.e. a
completely multiplicative f : U → {±1} with f∘ι_a = f that shares whatever a proof would use about λ.

- f = 1, f = a real character χ with χ(a) = 1, and f = −1 on a dyadic EOS pair {r, r′} are symmetries. All three are
  pretentious (close to a character). A proof of WL must use that λ is far from every character at every scale.
- A symmetry f with f(p) = −1 for all p ≤ √m would be a barrier object. Its values on the ≍ m/L large primes are then
  fixed by ≍ φ/2 linear equations over F_2. Under the rigidity conjecture none exists (it would need a real character
  equal to −1 on all primes ≤ √m). So **within multiplicative functions I found no barrier object for WL** (conditional
  on rigidity, which is computed, not proved). The random ι_a-invariant sign function is not multiplicative.
- I also tried an elementary proof (wrap-around multiplicativity with d = 2, 3, …). Failure of WL is equivalent to
  λ(N) = +1 for every N ≡ a (mod m), N ≤ m², having a divisor in (N/m, m). The relations between different n are all
  consistent with that pattern, and the GRH bound for Σ_{k ≤ K} λ(a₀ + km) is non-trivial only for K > m^{1+ε}. So WL
  is "λ is not constant on a progression mod m up to m²", level 1/2 exactly. I agree with the proposer's assessment.
  (sketched)

So WL is a fair test: no deletion, no log deficit, and no cheap counterexample. A method that cannot decide WL cannot
prove EOS. It remains a test, with EOS reach zero.

### 4.2 R2: dead. R3: dead for EOS

R2: agreed with the autopsy. R3: P′ leaves every coset count unchanged to relative 1/L, so no coset statement reaches a
single class. Hypothesis V **[EXTRA]** is, on the physical side, an upper bound for Σ_{k ≤ x/q} #{p, p + kq ≤ x} within
a factor 1 + ε/2 of the expected value at x/q ≈ L. That is a prime-pair upper bound with constant below 2, with moduli
q ≈ x/L. It is the same hypothesis as W2's "C_s < 2" and route C §6. [UNVERIFIED: Fiorilli–Martin's disproof of
Hooley's variance conjecture concerns a different range, as far as I recall; check before quoting Hooley in support.]

## 5. Wildcard: the theorems stand, the reach is zero

### 5.1 W1 (Theorem W): alive

I rederived Lemma M: Hölder with exponents 2k/(2k−1) and 2k, |S|^{2·2k/(2k−1)} ≤ M^{2/(2k−1)}|S|², Σ_χ|1̂_S|^{2k} = φE_k(S).
It gives V°(M²E_k/V°)^{1/2k} as stated. With E_k ≤ k!|W|^k (integer equality since y^k < m), M²/|P| ≪ L³ and
k = ⌈log L⌉ the condition is |W| ≥ K(φ/|P|)²·log L. Correct as far as I can check (proved, modulo route C's lemmas).

Barrier objects against the theorem: deleting all R_{a/s}, s ∈ W, removes |W|/L′ ≫ 1 of the primes, impossible. A
Spencer-type set avoiding L² log L Sidon classes with GRH-size sums cannot exist, by the theorem. (P, P⁻¹): the theorem
holds for it too. That last point is the kill for EOS: the proof sees only |S(χ)|², so by Theorem G it cannot be pushed
to |S| = 1 by any refinement.

### 5.2 W2 (Linnik format): alive, one lemma unwritten

I rechecked the chain Lemma B → dyadic shells → Hölder against the Sidon set 𝓡; the exponents come out as stated. The
small-order case I worried about (m | 2^k − 1 with k ≈ log₂ m, where g^h = 1 recurs inside the Fejér sum) is already
handled by the hypothesis ord(g) ≥ J and the coset remark. The open item is the lattice sieve bound for C_s, uniform
in b = g^h of arbitrary height. I see no obstruction (each line has ≥ √m/2 points, sieve level m^ε suffices), but the
worst-case singular series needs writing.

The device that is new here is Lemma B: a prime-pair *upper bound* (N⁻(b) ≤ C_sλ) becomes a bound for the |S|²-mass of
a Bohr set through a positive-definite majorant. It is the one place in round 1 where a sieve input enters the
character side. It is conjugation-blind by construction (it bounds N⁻). I could not see a product-side analogue:
N(b) has no positive-definite expression.

### 5.3 W3: alive (routine transcription). By §3 above, conjugation-blindness costs nothing in F_q[t], so this may be
closer to the full function-field statement than its integer twin is to EOS. Still far: the missing factor is n.

---

## 6. What the round shows

1. Every proposal that passes all six barriers does so by assuming a statement the barrier objects violate (H4), or by
   working where the barrier objects do not exist (F_q[t] geometry, smooth toys). None passes by an argument.
2. Every unconditional or GRH-only theorem delivered (W, W-Linnik, M1, Lemma H/K) is conjugation-blind or holds for
   arbitrary sets. That is consistent with D's synthesis and adds no exception to it.
3. Two calibration problems survived my attempts to trivialise them: WL (parity only) and the toy D₄ (log deficit
   only). They isolate different barriers and neither has a known barrier object.

## 7. New ideas for round 3

1. **Barrier harness.** One script that evaluates any proposed hypothesis on the six objects at m ≈ 10⁶: P, P⁻¹,
   P ∖ R_a, A\*_a (route A already builds it), a random avoiding set, and a Spencer-type signed set. H4/LD were run only
   on P and P⁻¹. Running LD on A\* would show how far apart P and A\* are at finite m, which is the actual size of the
   target a proof must hit. Every round-3 hypothesis should ship with this table.
2. **Make the F_2[t] test bed faithful to barrier (6), or stop citing it for (6).** Find a function-field variant with an
   obstructed quotient class (§3). If none exists, record that a function-field proof says nothing about S² versus |S|².
3. **H4 in F_q[t] as a decision experiment** (§1.2): does Sawin's method reach H4 where it reaches EOS? This decides
   whether H4 is a reduction or an inflation.
4. **TD as the provable product/quotient asymmetry** (§2.4): the quotient Titchmarsh problem is classical, the product
   one needs Kloosterman sums over primes. A proved asymptotic difference between the two secondary terms would be the
   first *theorem* that sees S² versus |S|² at level 1/2. Parity-free, so no EOS, but it exercises the one input
   Theorem G says is necessary.
5. **Look for a product-side analogue of Lemma B.** W2 converts an upper-bound sieve into character-side mass bounds
   because N⁻ is positive-definite. The Kloosterman-dual identity (Lemma K) is the product-side expression. Is there a
   positive-definite majorant in the dual variable c (the variable of Π = P̂ ⋆ P̂) whose physical side is a sieve-bounded
   count? If yes, it would be the first conjugation-sensitive size bound. I expect no (Π is not positive), but nobody
   has checked. [heuristic]
6. **Test H4 numerics on non-prime m** (m = r², highly composite m) before anyone invests in it (§1.3).

## 8. Not checked

- Lemma 2.2 of the analytic note (sketched there); I did not write it out.
- The lattice sieve lemma for C_s; route C's lemmas D2–D5 behind Theorem W.
- The geometer's Schur–Mellin identity and rank heuristics; I took the proposer's numbers.
- §3: two primitive moduli per degree, n ≤ 17, q = 2 only; the local argument is a sketch, not a proof that no
  obstructed class exists for every f.
- Literature recalls in §2.4 and §4.2 are from memory.
