# Vendored code from PrimeNumberTheoremAnd

This directory contains Lean files copied, with light local modifications, from the
PrimeNumberTheoremAnd project ("PNT+"):

- Repository: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
- Commit: `a4fb6989b07e9c76b511807ae93e33e25b820e9b` (2026-11-15)
- Licence: Apache License 2.0. The full text is in `LICENSE` in this directory, copied from the
  upstream repository at that commit. Copyright belongs to the PrimeNumberTheoremAnd contributors.
  Files that carried an individual copyright header upstream keep it verbatim.

Vendored on 2026-11-23 for the literal-GRH project (`notes/grh-blueprint.md`, milestone M1).

## Why vendor rather than depend

PNT+ pins Mathlib v4.35.0 and this project pins v4.36.0-rc2. Lake resolves a single Mathlib, so a
Lake dependency would force one of the two pins to move and invalidate the Mathlib cache. It would
also add four packages (LeanArchitect, checkdecls, leancert, PrimeCert). So we copy the few files
the blueprint's route needs (no Lake dependency, no Mathlib pin change).

## What was vendored

| Local file (module `EOS.Vendor.PNT.…`) | Upstream file | Used for |
|---|---|---|
| `Rectangle.lean` | `PrimeNumberTheoremAnd/Rectangle.lean` (whole) | rectangles, `RectangleBorder`, `Square` |
| `ResidueCalcOnRectangles.lean` | `PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean` (whole) | `RectangleIntegral'`, `VerticalIntegral'`, `HasSimplePolesOn`, `residue`, `sumResiduesIn`, `ResidueTheoremOnRectangleWithSimplePole`, `RectangleIntegral'_eq_sumResiduesIn` (blueprint V1, D1) |
| `RectangleArgumentPrinciple.lean` | `PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean` (whole) | `logDeriv_residue_eq_meromorphicOrderAt`, `logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top`, `rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt` (V1, D1) |
| `Mathlib/Analysis/Meromorphic/DivisorSupport.lean` | `PrimeNumberTheoremAnd/Mathlib/Analysis/Meromorphic/DivisorSupport.lean` (whole) | dependency of the above |
| `PerronFormula.lean` | `PrimeNumberTheoremAnd/PerronFormula.lean` (whole) | `Perron.formulaGtOne`, `Perron.formulaLtOne` for the kernel x^s/(s(s+1)) (V2, A2) |
| `Mathlib/Analysis/Asymptotics/Asymptotics.lean`, `Mathlib/Analysis/Asymptotics/Uniformly.lean` | same paths under `PrimeNumberTheoremAnd/` (whole) | dependencies of `PerronFormula.lean` |
| `StrongPNT.lean` | `PrimeNumberTheoremAnd/StrongPNT.lean`, **excerpt**: lines 1–1231, 1516–1523, 1719–1735 | `borelCaratheodory'`, `BorelCaratheodoryDeriv`, `LogOfAnalyticFunction`, Blaschke lemmas, `ZerosBound` (Jensen-type zero count), `FinalBound` (Landau's lemma), and the affine-transfer lemmas `analyticOrderNatAt_fun_div_const`, `analyticOrderNatAt_fun_comp_add_left/right` (V3, V4, B3) |
| `ZetaBounds.lean` | `PrimeNumberTheoremAnd/ZetaBounds.lean`, **excerpt**: header (lines 1–21) and lines 500–578 | `ResidueMult` (residue of f·g at a simple pole of f) (V4, D1) |

Not vendored (blueprint V5): the ζ Abel continuation files
`PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaAbel{Continuation,Kernel}.lean` and their
helper files. Also not vendored: `Wiener.lean` (contains `sorry`) and `MediumPNT.lean`, which upstream
`PerronFormula.lean` and `StrongPNT.lean` import but do not use in the vendored parts.

## Local modifications (common to all files)

Each file's header lists its own modifications. Common to all:

- The Lean module system keywords (`module`, `public`, `@[expose] public section`, `public import`)
  and `import Architect` are removed.
- LeanArchitect `@[blueprint …]` attributes are removed. Where an attribute carried a
  `statement := /-- … -/`, that text is kept as a plain comment. `blueprint_comment /-- … -/` commands and
  tactic-level docstrings inside proofs (LeanArchitect features) become plain comments.
- Imports `PrimeNumberTheoremAnd.*` become `EOS.Vendor.PNT.*`. Declaration names and namespaces are
  unchanged (all vendored declarations compile alongside the rest of `EOS` without clashes).
- Style linters are disabled per file by `set_option`, as in the upstream lakefile.
- Seven small version-drift fixes (Mathlib v4.35.0 → v4.36.0-rc2), listed in the file headers:
  two `simp only [smul_add]; abel` lines in `ResidueCalcOnRectangles.lean`; one
  `rw [smul_sub, smul_add, smul_sub]; abel` line and one binder annotation in `PerronFormula.lean`;
  `dist_zero_right` replaced by `Complex.dist_eq, sub_zero` in five `simp` calls in `StrongPNT.lean`.
  `PerronFormula.lean` and `StrongPNT.lean` import `Mathlib` in place of the unused upstream
  imports `Wiener`/`MediumPNT`.

The stripping was done by a script and the fixes by hand; no proof was otherwise changed.

## Status

All vendored files build with `lake build` against the pinned Mathlib (cache only), with no `sorry`.
`#print axioms` gives `propext, Classical.choice, Quot.sound` for `RectangleIntegral'_eq_sumResiduesIn`,
`ResidueTheoremOnRectangleWithSimplePole`, `rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt`,
`logDeriv_residue_eq_meromorphicOrderAt`, `logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top`,
`Perron.formulaGtOne`, `Perron.formulaLtOne`, `borelCaratheodory'`, `BorelCaratheodoryDeriv`, `ZerosBound`,
`FinalBound`, `ResidueMult` and the three `analyticOrderNatAt_*` lemmas.
