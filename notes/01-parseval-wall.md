# The Parseval wall (primer)

## Setup
G = (Z/mZ)^*, with φ = |G|. P = {primes p ≤ m, p ∤ m} ⊂ G. Each such prime is its own residue,
because p < m. ρ = |P|/φ ≈ 1/log m. S(χ) = Σ_{p∈P} χ(p) is the Fourier transform of 1_P on G.

N(a) = #{(p,q) ∈ P² : pq ≡ a} = (1_P * 1_P)(a) = (1/φ) Σ_χ χ̄(a) S(χ)².

- The principal character gives the main term μ = |P|²/φ = ρ|P| ≈ m / log² m.
- The rest is E(a) = (1/φ) Σ_{χ≠χ0} χ̄(a) S(χ)².

## The identity
Parseval: (1/φ) Σ_χ |S(χ)|² = Σ_{x∈G} 1_P(x)² = |P|.
This is **exact**: 1_P is 0/1 valued, and there is no wrap-around because P ⊂ [1, m).
Hence (1/φ) Σ_{χ≠χ0} |S(χ)|² = |P|(1 − ρ).

## The wall
The best a size-only argument can do is |E(a)| ≤ (1/φ) Σ_{χ≠χ0} |S(χ)|² = |P|(1 − ρ).
That is (1 − ρ)/ρ ≈ log m times the main term μ. **We lose exactly one log.**

The loss is not an artifact of the triangle inequality: the sizes |S(χ)| allow E(a) = −μ.
- **Fourier side (Theorem G).** The quotient count N⁻(b) = (1/φ) Σ χ̄(b) |S(χ)|² has *identical* magnitudes.
  But N⁻(−1) = #{p + q = m} = 0 for odd m with m − 2 composite.
- **Physical side.** E(a) ≈ Σ_x f(x) f(a x̄), where f = 1_P − ρ.
  Cauchy–Schwarz gives |E(a)| ≤ ‖f‖², with equality when f is anti-symmetric under the involution ι_a : x ↦ a x̄.
  That is, when P contains at most one element of each pair {x, a x̄} (the "random pairing-avoiding set").

So EOS is exactly the statement that P is not anti-correlated with its reflection under ι_a.
That makes it a **binary problem**, the multiplicative analogue of Goldbach, where the involution is x ↦ N − x.

## Why GRH does not help
GRH gives |S(χ)| ≪ √m log m. That is, |S(χ)|² is at most about log³ m times its average |P|.
So no single character dominates, but GRH says nothing about the **phases** of χ̄(a) S(χ)².
- Random phases would give |E(a)| ≈ |P|/√φ ≈ √m / log m. This is the truth numerically (compute/RESULTS.md).
- A proof needs only a log's worth of phase cancellation, and no known tool supplies it pointwise in a.

## The three layers above range m (range X > m)
At range X > m, Parseval is no longer exact. The gap then has three layers:
- the GRH sup bound loses 2 logs, giving X ≍ φ log² m (Theorem S, formalized in Lean);
- a variance asymptotic (Hooley / Friedlander–Goldston type, not known for a single modulus under GRH alone) would recover one;
- the last log needs phase information. At X = m, Parseval is exact and only this last layer remains.

## Ternary versus binary
For p1 p2 p3 ≡ a, the error is ≤ sup|S| · (1/φ) Σ |S|². Here the sup bound only has to beat the trivial bound by a log, and GRH (or less) suffices.
This is why three primes ≤ m is known (EOS 1987 under GRH; Matomäki–Teräväinen unconditionally for cube-free m),
just as Vinogradov's three-primes theorem is known while binary Goldbach is not.

## Where phase information has been obtained elsewhere
- **Algebraic structure.** Weil/Deligne for complete sums. Example: a ≡ xy with integers x, y ≤ m^{1/2+ε} via Kloosterman sums.
  Over F_q[t], Sawin and Xie get a second Deligne expansion (route B).
- **Averaging over moduli.** Spectral theory of Kloosterman sums (Deshouillers–Iwaniec, Bombieri–Friedlander–Iwaniec).
  Not available at a fixed m.
- **Bilinear structure of one factor.** Friedlander–Iwaniec x² + y⁴, Heath-Brown x³ + 2y³.
  Here both factors are primes, which is the hard case.
