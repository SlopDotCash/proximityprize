/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage

/-!
# Bridge theorems for Grand Challenges and Line Decoding

This file provides the bridge theorems linking `LineDecodingCoverage` to `GrandChallenges`.
This is isolated to a separate file to avoid circular imports between `GrandChallenges`,
`LineDecodingCoverage`, and `GrandChallengeCollapse`.
-/

namespace ProximityGap

open CodingTheory
open scoped NNReal ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Bridge from a repaired line-decoding target.** If a code satisfies the named
line-decoding-to-MCA target at radius `δ`, and the resulting `a/|F|` bound is within
`ε*`, then the target certifies an `MCALowerWitness`.

This deliberately consumes the GS double-coverage interpolation data as an explicit hypothesis. -/
def GrandChallenges.MCALowerWitness.ofLineDecodingTarget
    (C : ModuleCode ι F F) (δ a ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hcov : ProximityGap.MCAForallDoubleCover (F := F) (A := F) (C : Set (ι → F)) δ)
    (hle : (a : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    GrandChallenges.MCALowerWitness (C : Set (ι → F)) ε_star :=
  GrandChallenges.MCALowerWitness.ofLe (C := (C : Set (ι → F))) (ε_star := ε_star) (δ := δ) hδ_le_one (le_trans (lineDecodable_imp_epsMCA_le_target C δ a hcov) hle)

end ProximityGap
