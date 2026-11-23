# EOS numerics: results

All numbers below are **computed** (exact integer counts unless stated otherwise). Interpretations against random
models are marked *[heuristic]*. Notation follows `../notes/00-setup.md`: P = {p ≤ m prime, p ∤ m}, π = π_m = |P|,
φ = φ(m), N(a) = #{(p,q) ∈ P², ordered, pq ≡ a}, λ = π²/φ (the mean of N), δ = π/φ (the density of P in G).

Hardware: 18-core Apple M5 Pro. Total compute was about 17 minutes of wall time.

## Contents
| file | what |
|---|---|
| `src/common.h` | sieve, factorisation, modular inverse |
| `src/eos_cover.c` | exact coverage test for every m ≤ 10⁶ (Task 1) and the one-small-prime cutoff z(m), θ(m) (Task 3b) |
| `src/eos_full.c` | full counts N(a) by direct π²/2 enumeration: R(m), y(m), the energy E(m), and class breakdowns (Tasks 2, 3a, 4) |
| `src/eos_char.c` | prime m via discrete log and FFT (FFTW): every S(χ) at once, N = IFFT(F²), E = Σ|S|⁴/φ (Tasks 2 and 4, up to m ≈ 9·10⁷) |
| `src/make_lists.py`, `src/analyze.py`, `src/profile_a.py` | sample lists, statistics and fits, plots |
| `data/cover_1e6.csv` | per m ≤ 10⁶: φ, π, nfail, nfail_distinct, z, θ |
| `data/fails_1e6.csv` | every failing (m, a), base variant and distinct-prime variant |
| `data/full_range.csv` | per m in [3, 10⁵]: R, argmin, E, X, y, class breakdown (36 columns) |
| `data/full_sample.csv` | the same for 446 typed moduli in (2·10⁴, 10⁶]: powers of 2 and 3, multiples of 2310/30030/510510, random m, p, 2p, p² |
| `data/char_small.csv`, `data/char_big.csv` | prime m: all primes 5 ≤ m ≤ 2·10⁴ and about 6 primes per eighth-decade up to 9·10⁷ |
| `data/summary.txt` | the full printed output of `analyze.py` |
| `fig/eos_trends.png` | R(m), depth of the minimum, y(m)/m, θ(m) |
| `fig/eos_energy_chars.png` | excess energy, max |S(χ)|/√π |

To rebuild: `make && bin/eos_cover 2 1000000 data/cover_1e6.csv data/fails_1e6.csv && bin/eos_full range 3 100000 data/full_range.csv && python3 src/make_lists.py && ./run_rest.sh && python3 src/analyze.py`.

**Cross-checks.**
- `eos_cover` and `eos_full` agree on nfail and nfail_distinct for every m ≤ 2000.
- `eos_full` agrees with a brute-force Python count (min N, E, y) on 9 moduli, including 210, 360, 1024 and 1155.
- The FFT method (`eos_char`) reproduces min N, E and R exactly for all 301 primes ≤ 2000. Over all FFT runs the maximum rounding error is 1.7·10⁻⁹, and Σ N = π² exactly in every case.

---

## Task 1: verification

**Result (computed).** For every m ≤ 10⁶ and every a coprime to m, there are primes p, q ≤ m with pq ≡ a (mod m),
**except for the 48 moduli below**. The largest failing modulus is **m = 401** (bad class a = 385). The next largest is 397 (a = 308).
There is no failure in 402 ≤ m ≤ 10⁶. The fail list for m ≤ 10⁶ is byte-identical to the list for m ≤ 10⁵.

Failing m with their bad classes a (33 of the 48 are prime; the composite ones are 4, 6, 9, 10, 15, 25, 27, 33, 35, 55, 57, 69, 91, 121, 169):

```
2: 1; 3: 2; 4: 3; 5: 2 3; 6: 5; 7: 5; 9: 2; 10: 3 7; 11: 1 7 8; 13: 5 11; 15: 13; 17: 3 11 12 13; 19: 18;
23: 7 20; 25: 17; 27: 17; 29: 1 12 23; 31: 11 12; 33: 17; 35: 31 32; 37: 5 16 29; 41: 19; 43: 23; 47: 43;
53: 18 30 48; 55: 42; 57: 11; 59: 30 31; 61: 17 59; 67: 3 59; 69: 61; 71: 31 42 68; 73: 53; 83: 24 44;
89: 18 61 83; 91: 8; 97: 56 78; 101: 37 66 79; 103: 54; 121: 16; 127: 84 97; 137: 83; 169: 42; 173: 90;
179: 107 151; 191: 19; 397: 308; 401: 385
```

**Variants.**
- *Strict p, q < m:* this is **identical** to the base problem, by a proof rather than a computation. p = m is possible only when m is prime, and then p | m, which is excluded (and in any case pq ≡ a with gcd(a, m) = 1 forces p, q ∤ m).
- *p ≤ q:* also **identical**, since pq = qp. The representation counts halve, but coverage does not change.
- *Distinct primes p < q* (the meaningful strengthening, which excludes the representation a = p²) was computed instead. It fails for 62 moduli, and the **largest is m = 431, a = 169 = 13²**: the only representation is 13·13. The moduli that fail only in this variant are 8, 12, 16, 21, 24, 26, 49, 51, 77, 93, 133, 149, 193 and 431. The full list is in `data/fails_1e6.csv` (variant `distinct_only`).

So EOS (with "sufficiently large" = m ≥ 402) holds for all m ≤ 10⁶. The distinct-prime version holds for 432 ≤ m ≤ 10⁶.

---

## Task 2: the normalised minimum R(m) = min_a N(a) / λ

### Trend (computed)
| m range | min R | median R | median R_rand* | worst m in range |
|---|---|---|---|---|
| [402, 10⁵] overall | 0.064 (m = 431) | | | |
| [500, 1000) | 0.109 | 0.586 | 0.499 | 557 (prime) |
| [10³, 2·10³) | 0.136 | 0.639 | 0.569 | 1007 = 19·53 |
| [2·10³, 5·10³) | 0.333 | 0.701 | 0.636 | 2131 (prime) |
| [5·10³, 10⁴) | 0.483 | 0.755 | 0.708 | 5107 (prime) |
| [10⁴, 2·10⁴) | 0.572 | 0.797 | 0.759 | 10057 |
| [2·10⁴, 5·10⁴) | 0.623 | 0.841 | 0.811 | 22927 |
| [5·10⁴, 10⁵] | 0.720 | 0.875 | 0.854 | 53093 (prime) |
| sample (2·10⁴, 10⁶] | 0.727 | | | 22201, 26449 |
| primes [10⁶, 2·10⁶) (FFT) | 0.927 | 0.932 | 0.922 | |
| primes [10⁷, 2·10⁷) (FFT) | 0.968 | 0.972 | 0.970 | |
| primes [5·10⁷, 9·10⁷] (FFT) | 0.983 | 0.985 | 0.984 | |

\*R_rand = 1 − 2(1−δ)√(log φ / λ). This is the Gaussian extreme-value prediction for a uniformly random subset of G of size π. *[heuristic]* Each N(a) has mean λ and variance ≈ 2λ(1−δ)². The factor 2 comes from (p,q) ↔ (q,p), and the factor (1−δ)² from fixing |P| = π.

**Conclusions.**
1. **R(m) is bounded below and increases to 1.** It does not decay like a power of log, or at all. min R > 0 for every m ≥ 402. min R ≥ 0.136 for m ≥ 1000 and ≥ 0.57 for m ≥ 10⁴. By 9·10⁷, R ≈ 0.985.
2. **Rate.** On prime m from 10³ to 9·10⁷, an empirical fit gives 1 − R ≈ 6.3·m^(−0.31). This is the pre-asymptotic form of the random-model law 1 − R ≈ 2c(1−δ)√(log φ/λ) ≍ (log m)^{3/2}/√m. The observed depth of the minimum is a fraction c of the Gaussian prediction, and c rises slowly with m: median (1−R)/(1−R_rand) on primes is 0.78 (10³–10⁴), 0.83 (10⁴–10⁵), 0.87 (10⁵–10⁶), 0.87 (10⁶–10⁷) and 0.91 (10⁷–10⁸). The minimum is therefore slightly *shallower* than random, consistent with the reduced fourth moment in Task 4. The second panel of `fig/eos_trends.png` shows this ratio. Its spread for m ≤ 10⁵ is 0.6–1.3, and for large m it is 0.82–1.03.
3. **Worst moduli: primes, prime powers, and m with φ(m)/m ≈ 1** (e.g. 1007 = 19·53, 22201 = 149²). These have the smallest λ ≈ (m/φ)·m/log² m for their size. In [5000, 10⁵]: mean R is 0.766 for primes, 0.751 for prime powers, 0.845 for "other" m and 0.924 for φ/m < 0.3. **Relative to the random model, every type behaves the same.** The mean depth ratio is 0.83–0.85 for every type, so smooth m are better only because λ is larger. The best R in the sample (≈ 0.978) occurs at multiples of 30030 and 510510.
4. **Worst classes a: none is special.** Averaged over m ∈ [5000, 10⁵]:
   - N(1)/λ = 0.9997 and N(−1)/λ = 0.999.
   - The minimum over a ≤ 100 has mean 0.909, larger than the global minimum (≈ 0.845), as expected for a minimum over 100 classes rather than φ.
   - The argmin is ±1 in 0.01% of moduli and is ≤ 100 in 0.36%, both consistent with chance.
   - *Squares.* The mean of N over squares is 1.0008λ, slightly higher than over non-squares (0.9999λ), because of the diagonal p² ≡ a, which adds D(a) = #{p : p² ≡ a}. Correspondingly the argmin is a square slightly less often than the share of squares: 0.203 vs 0.213 over all m, and 0.472 vs 0.5 over prime m.
   - *Position a/m.* N(a)/λ is flat in a/m to within 2·10⁻⁴, and its standard deviation is flat as well (`data/profile_a.txt`). The small skew of argmin toward small a in the CSV is a tie-breaking artifact (the first minimiser is kept).

---

## Task 3: thinner sets

### (a) Symmetric cutoff y(m) = least y such that p, q ≤ y covers every reduced class (computed for all m ≤ 10⁵ and the sample)
| m range | median y/m | max y/m | median y/(√m log m) | median π(y)²/(2φ log φ) |
|---|---|---|---|---|
| [10³, 10⁴) | 0.254 | 0.771 (m = 1021) | 2.04 | 0.925 |
| [10⁴, 2·10⁴) | 0.172 | 0.385 | 2.15 | |
| [2·10⁴, 5·10⁴) | 0.128 | 0.291 | 2.24 | 0.946 (over 10⁴–10⁵) |
| [5·10⁴, 10⁵] | 0.096 | 0.204 | 2.31 | |
| sample, m > 5·10⁵ | 0.033 | 0.068 | | 0.966 (over 10⁵–10⁶) |

- The largest m with y(m)/m > 0.9 is 433, with y/m > 0.75 is 1021, with y/m > 0.5 is 3403, and with y/m > 0.25 is 35071.
- A fit gives y ≈ 0.47·√m·(log m)^1.86, which is the coupon-collector law. *[heuristic]* All classes are covered once the π(y)²/2 unordered products reach about φ log φ. The measured ratio π(y)²/(2 φ log φ) is 0.93–0.97 (max 2.1) and tends to 1, so y(m) ≈ √(2 φ log φ)·log y ≍ √m (log m)^{3/2}.
- **Slack:** y(m)/m → 0 like m^(−1/2) times a power of log. Already at 10⁶, primes up to ~3–7% of m suffice.

### (b) One small prime: z(m) = max_a min{p : ∃ prime q ≤ m, pq ≡ a}, θ(m) = log z / log m (computed for all m ≤ 10⁶)
| m range | max z | max θ | mean θ | max z/log² m | mean z/log² m |
|---|---|---|---|---|---|
| [10³, 10⁴) | 641 | 0.854 (m = 1061) | 0.575 | 7.95 | 2.12 |
| [10⁴, 10⁵) | 1049 | 0.684 | 0.509 | 8.71 | 2.39 |
| [10⁵, 10⁶] | 1669 (m = 770131) | 0.606 (m = 121337) | 0.459 | 9.88 | 2.68 |

- **p ≤ 1669 suffices for every m ≤ 10⁶** (with q ≤ m free).
- Block maxima fit z ≈ 3.3·(log m)^2.4. *[heuristic]* The geometric-trials model, in which each p succeeds independently with probability δ = π/φ, predicts that the number of small primes needed is π(z) ≈ log φ / (−log(1−δ)) ≈ (φ/m)·log m·log φ, i.e. z ≍ log² m · log log m. The measured ratio π(z)/(log φ/(−log(1−δ))) has median 1.12 → 1.05 → 1.02 over the three decades (max 2.5–3.3).
- So θ(m) → 0 like (2 log log m + O(1))/log m. **The asymmetric route (one prime ≤ (log m)^{2+o(1)}, the other ≤ m) is numerically very plausible.** It is in fact the most economical numerical route. Note that this is reformulation 2 with p restricted to the first ~log² m primes.

---

## Task 4: moments

### Multiplicative energy E(m) = Σ_a N(a)² = #{p₁p₂ ≡ p₃p₄}
Since Σ N = π² exactly, E − π⁴/φ = Σ_a (N(a) − λ)². The comparison with π⁴/φ + 2π² is therefore made through the excess
**X = (E − π⁴/φ)/(2π²)**. The naive random model predicts X = 1. A random subset of exactly π elements predicts X ≈ (1−δ)² *[heuristic, derivation in Task 2 footnote]*.
The raw ratio E/(π⁴/φ + 2π²) is 0.987–0.999. It tends to 1 trivially, because π⁴/φ dominates by a factor of about λ/2.

| m | X mean (min–max) | X/(1−δ)² mean |
|---|---|---|
| composite [10³, 5·10³) | 0.455 (0.087–0.667) | 0.910 |
| prime [10³, 5·10³) | 0.629 (0.578–0.669) | 0.862 |
| composite [5·10³, 2·10⁴) | 0.516 (0.142–0.701) | 0.897 |
| prime [5·10³, 2·10⁴) | 0.676 (0.636–0.702) | 0.874 |
| composite [2·10⁴, 10⁵] | 0.572 (0.178–0.737) | 0.902 |
| prime [2·10⁴, 10⁵] | 0.717 (0.683–0.739) | 0.890 |
| primes [2·10⁵, 2·10⁶) (FFT) | 0.767 | 0.910 |
| primes [2·10⁶, 2·10⁷) (FFT) | 0.802 | 0.925 |
| primes [2·10⁷, 9·10⁷] (FFT) | 0.825 | 0.935 |

**Conclusion (computed).** The energy is *below* the random-model value π⁴/φ + 2π² in every case. Its excess over π⁴/φ is about 0.86–0.94 × the fixed-size random-subset value 2(1−δ)²π², and this factor creeps up towards 1. In character terms, (1/φ)Σ_{χ≠χ₀}|S(χ)|⁴ ≈ 0.9 × the Gaussian value 2(π(1−δ))², so the L⁴ norm of S is no larger than that of a random set. For composite m with small φ/m, X is much smaller simply because δ = π/φ is large; for example δ ≈ 0.4 for m = 510510, where X = 0.27. *[heuristic]* A plausible source of the remaining deficit is that primes have a deterministic count in every subinterval [1, x] (the prime number theorem), which removes low-frequency variance that a random set would have.

### Character sums, prime m (all primes 5 ≤ m ≤ 2·10⁴, plus 84 primes in (2·10⁴, 9·10⁷])
| primes | median max_{χ≠χ₀}|S|/√π | max of that | median max|S|²/(π log φ) | max of max|S|/(√m log m) | max attained by quadratic χ |
|---|---|---|---|---|---|
| [5, 10³) | 1.87 | 2.47 | 0.58 | 0.56 | 3% |
| [10³, 2·10⁴) | 2.26 | 3.00 | 0.56 | 0.138 | 1% |
| [2·10⁴, 2·10⁵) | 2.47 | 2.79 | 0.57 | 0.084 | 0 |
| [2·10⁵, 2·10⁶) | 2.78 | 3.05 | 0.58 | 0.069 | 0 |
| [2·10⁶, 2·10⁷) | 3.07 | 3.29 | 0.60 | 0.058 | 0 |
| [2·10⁷, 9·10⁷] | 3.29 | 3.50 | 0.60 | 0.052 | 0 |

- **max_{χ≠χ₀}|S(χ)| ≈ √(0.6·π_m·log φ).** This is a "square-root plus √log" size and smaller than the Gaussian extreme √((1−δ)π log(φ/2)). For example at m ≈ 9·10⁷ it is 3.3√π against a Gaussian 4.1√π (second panel of `fig/eos_energy_chars.png`). The tails of |S(χ)|²/π are lighter than exponential: for m ≤ 2·10⁶ no character has |S|² > 10π, whereas an exponential law with mean 1−δ would predict about 20 per modulus at m ≈ 10⁶. For m ∈ [2·10⁶, 2·10⁷) there are 16 such characters in total across 49 moduli, against roughly 250 predicted per modulus.
- Relative to the GRH-type scale √m log m, the observed max is tiny: max|S|/(√m log m) ≤ 0.058 for m ≥ 2·10⁶ and decreasing. The maximising character always has large order. The quadratic character is unremarkable: mean |S(χ_quad)|/√π = 0.80, with a mean signed value of −0.34, a small Chebyshev-type bias.

---

## What this says about the proof strategy (heuristic summary)
- EOS is true for all 402 ≤ m ≤ 10⁶, and numerically N(a) behaves like a fixed-size random set, slightly *better* than random:
  - the minimum is 0.8–0.9 of the Gaussian depth;
  - the fourth moment is 0.87–0.94 of the Gaussian value;
  - the sup of the character sums is ≈ √(0.6 π log φ).
  
  Nothing in the data looks like a log-power obstruction. The obstruction in `notes/00-setup.md` comes from proof technique: the sup over a costs √log φ, while L²/L^∞ bounds lose log powers.
- Size of the true error *[heuristic, matches data]*: |N(a) − λ| ≲ 2(1−δ)√(λ log φ) ≈ 2√m/√(log m) for prime m. This is a factor ≈ √m/√(log m) below the trivial bound |E(a)| ≤ π ≈ m/log m, and a factor ≈ √m/(log m)^{3/2} below the main term λ ≈ m/log² m. So the truth has enormous room. The difficulty is entirely in proving pointwise (in a) cancellation in Σ_χ χ̄(a)S(χ)², which energy/L⁴ information cannot give by itself. L⁴ only controls the mean square of E(a) over a, which the data say is ≈ 0.9 × random.
- The most numerically robust weakened target is asymmetric: **p among the first ≍ log² m · log log m primes and q ≤ m** already covers everything. max θ is 0.61 for m ∈ [10⁵, 10⁶] and is decreasing.
