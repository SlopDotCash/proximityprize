/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Collapse
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount

/-!
# Grand MCA challenge as a bad-scalar count

This file keeps the endpoint-collapse specialization out of `MCABadCount.lean`, so the
finite bad-scalar count lemmas remain below `LineDecodingCoverage` in the import graph.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators NNReal ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The top/full linear code gives a one-sided Grand MCA lower witness at every radius
`δ ≤ 1` and every target threshold. -/
def GrandChallenges.MCALowerWitness.top (δ ε_star : ℝ≥0) (hδ : δ ≤ 1) :
    GrandChallenges.MCALowerWitness (((⊤ : LinearCode ι F) : Set (ι → F))) ε_star :=
  GrandChallenges.MCALowerWitness.ofLe hδ <| by
    rw [epsMCA_top_eq_zero]
    exact zero_le _

/-- **The formalized Grand MCA Challenge is a finite extremal-count statement.** For a
linear code `C` and threshold `ε*`, the challenge predicate holds iff *every* line word
has at most `ε*·q` bad scalars at radius one. -/
theorem grandMCAChallenge_iff_forall_badCount_le (C : LinearCode ι F) (ε_star : ℝ≥0) :
    grandMCAChallenge C ε_star ↔
      ∀ u : WordStack F (Fin 2) ι,
        (mcaBadCount (F := F) ((C : Set (ι → F))) 1 (u 0) (u 1) : ℝ≥0∞) ≤
          (ε_star : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞) := by
  rw [grandMCAChallenge_iff_epsMCA_one, epsMCA_eq_iSup_mcaBadCount]
  have hq0 : (Fintype.card F : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact Fintype.card_ne_zero
  have hqt : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.div_le_iff hq0 hqt, iSup_le_iff]

/-- The top/full linear code satisfies the formal Grand MCA Challenge at every threshold. This
is the direct challenge-level endpoint form of `mcaBadCount_univ_eq_zero`: the top code has no
bad scalars for any stack, so the radius-one finite-count criterion is immediate. -/
theorem grandMCAChallenge_top (ε_star : ℝ≥0) :
    grandMCAChallenge (F := F) (ι := ι) (⊤ : LinearCode ι F) ε_star := by
  classical
  rw [grandMCAChallenge_iff_forall_badCount_le]
  intro u
  rw [mcaBadCount_top_eq_zero]
  simp

#print axioms ProximityGap.GrandChallenges.MCALowerWitness.top
#print axioms ProximityGap.grandMCAChallenge_iff_forall_badCount_le
#print axioms ProximityGap.grandMCAChallenge_top

end ProximityGap
