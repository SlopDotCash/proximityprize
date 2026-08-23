/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAGS
import ArkLib.Data.CodingTheory.ProximityGap.MCAGSBounds
import ArkLib.Data.CodingTheory.ProximityGap.MCAGSFieldUniversal

/-!
# The per-domain "uniform GS-exposed prize" is closed — as stated, it is the proven trivial bound

`epsMCAgsPrizeUniformConjecture` (`GrandChallenge141PrizeMath.lean`) was introduced as "the honest
open GS-exposed prize", with the constant triple quantified before the per-rate data. But the
**evaluation domain (hence the field `F`) is fixed before the existential**, so the statement is
character-for-character the per-domain `epsMCAgs_prizeBound_conjecture domain m` (`MCAGS.lean`) —
which `epsMCAgs_prizeBound_conjecture_holds` (`GrandChallenge141UniformResolved.lean`) proves
outright by fixed-field inflation: take `c₁ = c₂ = 0` and `c₃ = n` with `(15/16)^n ≤ 1/|F|`; the
prize rates are bounded below by `1/16`, so `η ≤ 15/16` uniformly and the bound inflates past `1`.

This file records the discharge, de-laundering the "deliberately unproved" label: the statement
*as formalized* carries no open content. The genuinely open prize is the **field-universal** form
`epsMCAgsPrizeUniversalConjecture` (`GrandChallenge141PrizeReduction.lean`), whose constants are
quantified before the field and therefore cannot absorb `q = |F|`; its open core is the beyond-UDR
Guruswami–Sudan list-decoder mass bound (`UniversalGSListMassBound`). Tracking: issue #141.
-/

namespace ProximityGap.MCAGS

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The per-domain "uniform prize" Prop is true as stated** — it is definitionally the
per-domain `epsMCAgs_prizeBound_conjecture`, already proven by fixed-field inflation
(`epsMCAgs_prizeBound_conjecture_holds`). The formalization does not capture the open prize;
see the module docstring and `epsMCAgsPrizeUniversalConjecture` for the genuinely open form. -/
theorem epsMCAgsPrizeUniformConjecture_holds_as_stated (domain : ι ↪ F) (m : ℕ) :
    epsMCAgsPrizeUniformConjecture domain m :=
  epsMCAgs_prizeBound_conjecture_holds domain m

end ProximityGap.MCAGS

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.MCAGS.epsMCAgsPrizeUniformConjecture_holds_as_stated
