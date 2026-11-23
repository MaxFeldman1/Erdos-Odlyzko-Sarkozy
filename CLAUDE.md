# Project rules (EOS conjecture, conditional on GRH)

## Lean / Mathlib
- **Never build Mathlib from source.** Use the cache only. If Mathlib oleans are missing or stale, run
  `lake exe cache get` in `EOS/`. If that fails, stop and report; do not fall back to compiling Mathlib.
- Do not change `EOS/lean-toolchain`, the Mathlib `rev` in `EOS/lakefile.toml`, or `lake-manifest.json`.
  Any of those changes invalidates the cache.
- Check a single file with `cd EOS && lake env lean EOS/<File>.lean`, or use `lake build EOS.<Module>`.
  If a build output shows Mathlib files being *compiled* (not replayed), kill it immediately.

## Mathematical conventions
- Analytic input: in the approach phase we assume standard *consequences* of GRH (see `EOS.GRHBounds` in
  `EOS/EOS/Statement.lean`). Any new analytic hypothesis must be a named `def ... : Prop` with a citation
  showing it follows from GRH. Deriving these from a literal GRH statement is deferred.
- Target: `EOS.eos_of_grhBounds`. The fallback is the strongest provable weaker statement (e.g. `CoveredBy m (m * (log m)^C)`),
  with the gap isolated as a single named hypothesis.
- In notes, mark every claim as proved / sketched / heuristic / [UNVERIFIED].
- Do not run git. The orchestrator commits.
