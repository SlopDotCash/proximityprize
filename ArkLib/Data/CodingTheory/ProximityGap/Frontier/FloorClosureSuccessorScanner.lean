/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.FloorFiniteRungUniformityBarrier
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorClosureContract

/-!
# Scanner bridge for the floor-localization successor step

`FloorFiniteRungUniformityBarrier.lean` records the generic logic:

* finite prefix evidence does not imply `UniformFrom`;
* a `SuccessorStep` plus a verified prefix does imply `UniformFrom`;
* if a verified prefix does not extend to `UniformFrom`, the successor step fails at an adjacent
  rung.

The floor closure contract has the concrete predicate
`CandidateListExactAt FloorBad a`: the singleton least-split-prime candidate list is extensionally
exact for the true floor-bad predicate at dyadic rung `a`.

This file connects those two surfaces.  It does not prove the successor theorem; it states the
exact scanner consequence for the actual floor-localization route.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.FloorClosureContract

open ArkLib.ProximityGap.Frontier.FloorFiniteRungUniformityBarrier

/-- Uniform singleton candidate-list exactness is exactly generic uniformity of the concrete
per-rung predicate `CandidateListExactAt FloorBad`. -/
theorem candidateListExactSmallestFamily_iff_uniformFrom_candidateListExactAt
    (FloorBad : ℕ -> ℕ -> Prop) :
    CandidateListExactSmallestFamily FloorBad ↔
      UniformFrom 4 (CandidateListExactAt FloorBad) := by
  constructor
  · intro hexact a ha
    exact hexact a ha
  · intro huniform a ha
    exact huniform a ha

/-- The concrete floor-localization successor theorem is exactly the generic successor step for
`CandidateListExactAt FloorBad`. -/
theorem candidateListExactSuccessor_iff_successorStep_candidateListExactAt
    (FloorBad : ℕ -> ℕ -> Prop) :
    CandidateListExactSuccessor FloorBad ↔
      SuccessorStep 4 (CandidateListExactAt FloorBad) := by
  constructor
  · intro hsuccessor a ha hexact
    exact hsuccessor a ha hexact
  · intro hstep a ha hexact
    exact hstep a ha hexact

/-- Prefix evidence plus the concrete successor step gives uniform singleton exactness. -/
theorem candidateListExactSmallestFamily_of_verifiedPrefix_and_successorStep
    (FloorBad : ℕ -> ℕ -> Prop) {cutoff : ℕ}
    (hcutoff : 4 ≤ cutoff)
    (hprefix : VerifiedPrefix 4 cutoff (CandidateListExactAt FloorBad))
    (hstep : CandidateListExactSuccessor FloorBad) :
    CandidateListExactSmallestFamily FloorBad := by
  exact (candidateListExactSmallestFamily_iff_uniformFrom_candidateListExactAt FloorBad).mpr
    (uniformFrom_of_verifiedPrefix_and_successorStep hcutoff hprefix
      ((candidateListExactSuccessor_iff_successorStep_candidateListExactAt FloorBad).mp hstep))

/-- Interval-finset evidence plus the concrete successor step gives uniform singleton exactness. -/
theorem candidateListExactSmallestFamily_of_verifiedOn_Icc_and_successorStep
    (FloorBad : ℕ -> ℕ -> Prop) {cutoff : ℕ}
    (hcutoff : 4 ≤ cutoff)
    (hverified : VerifiedOn (Finset.Icc 4 cutoff) (CandidateListExactAt FloorBad))
    (hstep : CandidateListExactSuccessor FloorBad) :
    CandidateListExactSmallestFamily FloorBad := by
  exact (candidateListExactSmallestFamily_iff_uniformFrom_candidateListExactAt FloorBad).mpr
    (uniformFrom_of_verifiedOn_Icc_and_successorStep hcutoff hverified
      ((candidateListExactSuccessor_iff_successorStep_candidateListExactAt FloorBad).mp hstep))

/-- Once a concrete candidate-list prefix has been verified, any failure of uniform singleton
exactness refutes the concrete successor theorem. -/
theorem not_candidateListExactSuccessor_of_verifiedPrefix_of_not_candidateListExactSmallestFamily
    (FloorBad : ℕ -> ℕ -> Prop) {cutoff : ℕ}
    (hcutoff : 4 ≤ cutoff)
    (hprefix : VerifiedPrefix 4 cutoff (CandidateListExactAt FloorBad))
    (hnot : ¬ CandidateListExactSmallestFamily FloorBad) :
    ¬ CandidateListExactSuccessor FloorBad := by
  intro hstep
  exact hnot
    (candidateListExactSmallestFamily_of_verifiedPrefix_and_successorStep
      FloorBad hcutoff hprefix hstep)

/-- Interval-finset version of
`not_candidateListExactSuccessor_of_verifiedPrefix_of_not_candidateListExactSmallestFamily`. -/
theorem not_candidateListExactSuccessor_of_verifiedOn_Icc_of_not_candidateListExactSmallestFamily
    (FloorBad : ℕ -> ℕ -> Prop) {cutoff : ℕ}
    (hcutoff : 4 ≤ cutoff)
    (hverified : VerifiedOn (Finset.Icc 4 cutoff) (CandidateListExactAt FloorBad))
    (hnot : ¬ CandidateListExactSmallestFamily FloorBad) :
    ¬ CandidateListExactSuccessor FloorBad := by
  intro hstep
  exact hnot
    (candidateListExactSmallestFamily_of_verifiedOn_Icc_and_successorStep
      FloorBad hcutoff hverified hstep)

/-- Concrete scanner form: if verified prefix evidence does not extend to uniform exactness, some
adjacent dyadic rung is exact but its successor is not. -/
theorem exists_exact_rung_next_fails_of_verifiedPrefix_of_not_candidateListExactSmallestFamily
    (FloorBad : ℕ -> ℕ -> Prop) {cutoff : ℕ}
    (hcutoff : 4 ≤ cutoff)
    (hprefix : VerifiedPrefix 4 cutoff (CandidateListExactAt FloorBad))
    (hnot : ¬ CandidateListExactSmallestFamily FloorBad) :
    ∃ a : ℕ, 4 ≤ a ∧ CandidateListExactAt FloorBad a ∧
      ¬ CandidateListExactAt FloorBad (a + 1) :=
  (not_candidateListExactSuccessor_iff_exists_exact_rung_next_fails FloorBad).mp
    (not_candidateListExactSuccessor_of_verifiedPrefix_of_not_candidateListExactSmallestFamily
      FloorBad hcutoff hprefix hnot)

/-- Interval-finset version of
`exists_exact_rung_next_fails_of_verifiedPrefix_of_not_candidateListExactSmallestFamily`. -/
theorem exists_exact_rung_next_fails_of_verifiedOn_Icc_of_not_candidateListExactSmallestFamily
    (FloorBad : ℕ -> ℕ -> Prop) {cutoff : ℕ}
    (hcutoff : 4 ≤ cutoff)
    (hverified : VerifiedOn (Finset.Icc 4 cutoff) (CandidateListExactAt FloorBad))
    (hnot : ¬ CandidateListExactSmallestFamily FloorBad) :
    ∃ a : ℕ, 4 ≤ a ∧ CandidateListExactAt FloorBad a ∧
      ¬ CandidateListExactAt FloorBad (a + 1) :=
  (not_candidateListExactSuccessor_iff_exists_exact_rung_next_fails FloorBad).mp
    (not_candidateListExactSuccessor_of_verifiedOn_Icc_of_not_candidateListExactSmallestFamily
      FloorBad hcutoff hverified hnot)

#print axioms candidateListExactSmallestFamily_iff_uniformFrom_candidateListExactAt
#print axioms candidateListExactSuccessor_iff_successorStep_candidateListExactAt
#print axioms candidateListExactSmallestFamily_of_verifiedPrefix_and_successorStep
#print axioms candidateListExactSmallestFamily_of_verifiedOn_Icc_and_successorStep
#print axioms
  not_candidateListExactSuccessor_of_verifiedPrefix_of_not_candidateListExactSmallestFamily
#print axioms
  not_candidateListExactSuccessor_of_verifiedOn_Icc_of_not_candidateListExactSmallestFamily
#print axioms exists_exact_rung_next_fails_of_verifiedPrefix_of_not_candidateListExactSmallestFamily
#print axioms exists_exact_rung_next_fails_of_verifiedOn_Icc_of_not_candidateListExactSmallestFamily

end ArkLib.ProximityGap.Frontier.FloorClosureContract
