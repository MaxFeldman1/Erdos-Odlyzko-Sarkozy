/-
Vendored from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
file `PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean`,
commit a4fb6989b07e9c76b511807ae93e33e25b820e9b (2026-11-15).
Licence: Apache License 2.0, see `EOS/EOS/Vendor/PNT/LICENSE`.
Copyright: the upstream file has no copyright header; copyright belongs to the
PrimeNumberTheoremAnd contributors (Apache License 2.0).
See `EOS/EOS/Vendor/PNT/NOTICE.md`.

Local modifications:
- Removed the Lean module system keywords (`module`, `public`, `@[expose] public`,
  `public import`) and the `import Architect` line.
- Removed the LeanArchitect `@[blueprint ...]` attributes; where an attribute carried a
  `statement := /-- ... -/`, that text is kept as a plain comment `/- Blueprint statement ... -/`.
- Tactic-level docstrings `/-- ... -/` inside proofs (a LeanArchitect feature) are now plain
  comments `/- ... -/`.
- `blueprint_comment /-- ... -/` commands are kept as plain comments `/- ... -/`.
- Import paths `PrimeNumberTheoremAnd.*` renamed to `EOS.Vendor.PNT.*`. Declaration names and
  namespaces unchanged.
- Trailing whitespace removed. Style linters disabled by `set_option` after the imports,
  as the upstream lakefile does (plus `linter.style.missingEnd`).
-/

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Order.Compact

-- Local modification: style linters disabled as in the upstream lakefile.
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.openClassical false
set_option linter.style.missingEnd false


section

open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem isLittleO_const_id_cocompact [ProperSpace F'']
    (c : E'') : (fun _x : F'' => c) =o[cocompact F''] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_norm_cocompact_atTop

-- to replace existing `isLittleO_const_id_atTop`
theorem isLittleO_const_id_atTop2 [LinearOrder F''] [NoMaxOrder F''] [ClosedIciTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atTop] id :=
 (isLittleO_const_id_cocompact c).mono atTop_le_cocompact

-- to replace existing `isLittleO_const_id_atBot`
theorem isLittleO_const_id_atBot2 [LinearOrder F''] [NoMinOrder F''] [ClosedIicTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atBot] id :=
  (isLittleO_const_id_cocompact c).mono atBot_le_cocompact

theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf

theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics
