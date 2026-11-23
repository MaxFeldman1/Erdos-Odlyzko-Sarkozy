# EOS: Lean formalization

Lean 4 + Mathlib (from the cache only; never build Mathlib from source) for the Erdős–Odlyzko–Sárközy conjecture
project. See `../README.md` and `../CLAUDE.md`.

| File | Main results |
|---|---|
| `EOS/Statement.lean` | `CoveredBy`, `Conjecture`, `GRHBounds`; the open target `eos_of_grhBounds` (the only `sorry`) |
| `EOS/LogFour.lean` | `coveredBy_of_grhBounds`: p, q ≤ K m log⁴ m under `GRHBounds` |
| `EOS/LogSquare.lean` | `GRHSmoothBound`; `coveredBy_log_sq` (p, q ≤ K m log² m); `coveredByAsym_m_log_cube` (p ≤ m, q ≤ K m log³ m) |
| `EOS/ThreePrimes.lean` | `coveredBy_three_primes`: a ≡ pqs, p, q ≤ m, s ≪ log² m (log log m)² |
| `EOS/Buchstab.lean` | unconditional Buchstab identity `lemmaC` and finite certificate `lemmaC'` |
| `EOS/GapH4.lean` | `eos_of_H4`: `TypeISifted → RoughCounts → H4 η λ → Conjecture` (no GRH; H4 is the open gap) |

All main theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. The hypotheses are audited in
`../notes/lean-referee.md`.

Check: `lake exe cache get && lake build`.
