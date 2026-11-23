# Project rules (EOS conjecture, conditional on GRH)

## Lean / Mathlib
- **Never build Mathlib from source.** Use the cache only. If Mathlib oleans are missing or stale, run
  `lake exe cache get` in `EOS/`. If that fails, stop and report; do not fall back to compiling Mathlib.
- Do not change `EOS/lean-toolchain`, the Mathlib `rev` in `EOS/lakefile.toml`, or `lake-manifest.json`.
  Any of those changes invalidates the cache.
- Check a single file with `cd EOS && lake env lean EOS/<File>.lean`, or use `lake build EOS.<Module>`.
  If a build output shows Mathlib files being *compiled* (not replayed), kill it immediately.

## Mathematical conventions
- Analytic input: the GRH-conditional theorems assume standard *consequences* of GRH (`EOS.GRHBounds`,
  `EOS.GRHSmoothBound`). Any new analytic hypothesis must be a named `def ... : Prop` with a citation showing it
  follows from GRH.
- Literal GRH (decided with the user on 2026-11-23): `EOS.GRH` in `EOS/EOS/GRH.lean` is GRH stated via zeros of
  `DirichletCharacter.LFunction`. The goal is `GRH → GRHSmoothBound` following `notes/grh-blueprint.md` (Landau-lemma
  route, no Hadamard). `GRHBounds` is dropped from the GRH chain; log⁴ follows from log² by monotonicity.
- Vendored code: files from PrimeNumberTheoremAnd (Apache-2.0) may be vendored into `EOS/EOS/Vendor/PNT/`. Keep the
  original copyright and attribution header with the upstream commit, add a note of local modifications, and keep
  the Apache-2.0 licence text in `EOS/EOS/Vendor/PNT/LICENSE`. Do not add Lake dependencies or change the Mathlib pin.
- Deliverables (decided with the user on 2026-11-23):
  1. GRH-conditional approximations to EOS (`coveredBy_of_grhBounds`, `coveredBy_log_sq`, `coveredByAsym_m_log_cube`,
     `coveredBy_three_primes`), with GRH entering only through named GRH-consequence hypotheses.
  2. The gap theorem, in the shape `eos_of_H4 (hT : TypeISifted) (hR : RoughCounts) (hH : H4 η λ) : Conjecture` (Buchstab
     route; see notes/brainstorm/r3-synthesis.md §5 and notes/routes/E-buchstab-H4.md, which has the complete paper proof). It does **not** mention GRH. `TypeISifted` and any other asymptotic input are
     named `Prop`s for cited *unconditional* theorems. `H4` is the single beyond-GRH hypothesis isolating the gap.
     Do not add GRH as an unused hypothesis. Every docstring must say plainly that H4 is stronger than EOS and not
     known to follow from GRH.
  3. Other conditional reductions may use an *open* beyond-GRH hypothesis (currently `H4` and
     `SumTwoSquares.TypeIHalf`) only if that hypothesis is a single named `Prop` whose docstring says plainly that it is
     open, not implied by GRH, and that the theorem is a conditional reduction. Such hypotheses are exempt from the
     "citation showing it follows from GRH" rule above.
  - `EOS.eos_of_grhBounds` in Statement.lean stays as the (sorry'd) statement of the open problem.
- In notes, mark every claim as proved / sketched / heuristic / [UNVERIFIED].
- Do not run git. The orchestrator commits.
