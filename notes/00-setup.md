# Setup and the basic barrier (orchestrator's notes, to be verified)

Notation: P = {primes p ≤ m, p ∤ m}, viewed in G = (Z/mZ)^*. S(χ) = Σ_{p ≤ m} χ(p).
N(a) = #{(p, q) ∈ P² : pq ≡ a (mod m)} = (1/φ(m)) Σ_χ χ̄(a) S(χ)².

## Reformulations
1. **Character sum.** N(a) = |P|²/φ(m) + E(a), with E(a) = (1/φ) Σ_{χ≠χ0} χ̄(a) S(χ)².
2. **Primes in a Kloosterman-type sequence.** Since q ≤ m and q ≡ a p̄ (mod m) pins down q,
   EOS ⇔ for some prime p ≤ m, the least positive residue of a·p̄ mod m is prime.
   The question is whether the sequence A_a = {a p̄ mod m : p ≤ m} ⊂ [1, m], of size ~ m/log m, contains a prime.
3. **Semiprimes in an AP at level 1/2.** n = pq = a + km ≤ m², with both prime factors ≤ m.
   This is the distribution of a bilinear form α*β (both factors of length m) in a residue class mod m = x^{1/2}, pointwise in a.

## The basic barrier (log-power loss)
- Orthogonality is exact here: since distinct primes ≤ m are incongruent mod m,
  Σ_χ |S(χ)|² = φ(m)|P|. So |E(a)| ≤ |P| trivially. The main term |P|²/φ ≈ |P|/log m · (m/φ(m))
  is *smaller* than this by a factor of about log m / (m/φ(m)).
- GRH pointwise: |S(χ)| ≪ √m log m gives |E(a)| ≪ m log² m, versus a main term of ≈ m/log² m. That is worse.
- Asymmetric (p ≤ y, q ≤ m) with GRH on the short factor needs y ≫ m log^5 m.
- Type II via sieve (sequence A_a, bilinear uv): the error is ≤ max_{χ≠χ0} |S(χ)| · ‖α‖₂‖β‖₂, so it needs
  UV ≫ m log^4 m, but uv ≤ m. It fails by log powers in every range.
- Expected consequence: GRH alone gives p, q ≤ m (log m)^C. Check whether this is already in EOS (1987).

The whole difficulty seems to be **saving powers of log**. That needs cancellation in the phase
χ̄(a)S(χ)², or moment information (multiplicative energy of primes mod m, i.e. L⁴ of S),
not just L² or L^∞ bounds on S.
