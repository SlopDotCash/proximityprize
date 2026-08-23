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

/-- Uniform singleton exactness includes exactness at the base rung `a = 4`. -/
theorem candidateListExactAt_four_of_candidateListExactSmallestFamily
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : CandidateListExactSmallestFamily FloorBad) :
    CandidateListExactAt FloorBad 4 :=
  hexact 4 le_rfl

/-- Uniform singleton exactness implies the concrete successor theorem. -/
theorem candidateListExactSuccessor_of_candidateListExactSmallestFamily
    (FloorBad : ℕ -> ℕ -> Prop)
    (hexact : CandidateListExactSmallestFamily FloorBad) :
    CandidateListExactSuccessor FloorBad := by
  intro a ha _hexactA
  exact hexact (a + 1) (Nat.le_trans ha (Nat.le_succ a))

/-- Uniform singleton exactness is exactly base exactness plus the concrete successor theorem. -/
theorem candidateListExactSmallestFamily_iff_base_and_successor
    (FloorBad : ℕ -> ℕ -> Prop) :
    CandidateListExactSmallestFamily FloorBad ↔
      CandidateListExactAt FloorBad 4 ∧ CandidateListExactSuccessor FloorBad := by
  constructor
  · intro hexact
    exact ⟨candidateListExactAt_four_of_candidateListExactSmallestFamily FloorBad hexact,
      candidateListExactSuccessor_of_candidateListExactSmallestFamily FloorBad hexact⟩
  · rintro ⟨hbase, hstep⟩
    exact candidateListExactSmallestFamily_of_base_and_successor FloorBad hbase hstep

/-- Failure of uniform singleton exactness is either base-rung failure or failure of the concrete
successor theorem. -/
theorem not_candidateListExactSmallestFamily_iff_not_base_or_not_successor
    (FloorBad : ℕ -> ℕ -> Prop) :
    (¬ CandidateListExactSmallestFamily FloorBad) ↔
      ¬ CandidateListExactAt FloorBad 4 ∨ ¬ CandidateListExactSuccessor FloorBad := by
  classical
  constructor
  · intro hnot
    by_cases hbase : CandidateListExactAt FloorBad 4
    · refine Or.inr ?_
      intro hstep
      exact hnot
        ((candidateListExactSmallestFamily_iff_base_and_successor FloorBad).mpr
          ⟨hbase, hstep⟩)
    · exact Or.inl hbase
  · rintro (hbase | hstep) hexact
    · exact hbase (candidateListExactAt_four_of_candidateListExactSmallestFamily FloorBad hexact)
    · exact hstep
        (candidateListExactSuccessor_of_candidateListExactSmallestFamily FloorBad hexact)

/-- Global scanner form: uniform singleton exactness fails exactly by base-rung failure or by an
adjacent exact-then-failing rung. -/
theorem not_candidateListExactSmallestFamily_iff_not_base_or_exists_exact_rung_next_fails
    (FloorBad : ℕ -> ℕ -> Prop) :
    (¬ CandidateListExactSmallestFamily FloorBad) ↔
      ¬ CandidateListExactAt FloorBad 4 ∨
        ∃ a : ℕ, 4 ≤ a ∧ CandidateListExactAt FloorBad a ∧
          ¬ CandidateListExactAt FloorBad (a + 1) := by
  constructor
  · intro hnot
    rcases (not_candidateListExactSmallestFamily_iff_not_base_or_not_successor
      FloorBad).mp hnot with hbase | hstep
    · exact Or.inl hbase
    · exact Or.inr
        ((not_candidateListExactSuccessor_iff_exists_exact_rung_next_fails FloorBad).mp hstep)
  · rintro (hbase | hnext)
    · exact (not_candidateListExactSmallestFamily_iff_not_base_or_not_successor
        FloorBad).mpr (Or.inl hbase)
    · exact (not_candidateListExactSmallestFamily_iff_not_base_or_not_successor
        FloorBad).mpr
        (Or.inr
          ((not_candidateListExactSuccessor_iff_exists_exact_rung_next_fails FloorBad).mpr hnext))

/-- If the base rung is exact, any failure of uniform singleton exactness produces an adjacent
exact-then-failing rung. -/
theorem exists_exact_rung_next_fails_of_base_of_not_candidateListExactSmallestFamily
    (FloorBad : ℕ -> ℕ -> Prop)
    (hbase : CandidateListExactAt FloorBad 4)
    (hnot : ¬ CandidateListExactSmallestFamily FloorBad) :
    ∃ a : ℕ, 4 ≤ a ∧ CandidateListExactAt FloorBad a ∧
      ¬ CandidateListExactAt FloorBad (a + 1) := by
  rcases (not_candidateListExactSmallestFamily_iff_not_base_or_exists_exact_rung_next_fails
    FloorBad).mp hnot with hbaseFail | hnext
  · exact False.elim (hbaseFail hbase)
  · exact hnext

/-- With the base rung verified, uniform singleton exactness fails exactly when an adjacent
exact-then-failing rung exists. -/
theorem not_candidateListExactSmallestFamily_iff_exists_exact_rung_next_fails_of_base
    (FloorBad : ℕ -> ℕ -> Prop)
    (hbase : CandidateListExactAt FloorBad 4) :
    (¬ CandidateListExactSmallestFamily FloorBad) ↔
      ∃ a : ℕ, 4 ≤ a ∧ CandidateListExactAt FloorBad a ∧
        ¬ CandidateListExactAt FloorBad (a + 1) := by
  constructor
  · exact exists_exact_rung_next_fails_of_base_of_not_candidateListExactSmallestFamily
      FloorBad hbase
  · intro hnext
    exact (not_candidateListExactSmallestFamily_iff_not_base_or_exists_exact_rung_next_fails
      FloorBad).mpr (Or.inr hnext)

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

/-- Stronger concrete scanner form: after a verified prefix, any adjacent exact/failing pair forced
by non-uniformity occurs at or beyond the checked cutoff. -/
theorem exists_candidate_exact_next_failure_at_or_after_cutoff
    (FloorBad : ℕ -> ℕ -> Prop) {cutoff : ℕ}
    (hcutoff : 4 ≤ cutoff)
    (hprefix : VerifiedPrefix 4 cutoff (CandidateListExactAt FloorBad))
    (hnot : ¬ CandidateListExactSmallestFamily FloorBad) :
    ∃ a : ℕ, cutoff ≤ a ∧ 4 ≤ a ∧ CandidateListExactAt FloorBad a ∧
      ¬ CandidateListExactAt FloorBad (a + 1) := by
  have hnotUniform : ¬ UniformFrom 4 (CandidateListExactAt FloorBad) := by
    intro huniform
    exact hnot
      ((candidateListExactSmallestFamily_iff_uniformFrom_candidateListExactAt FloorBad).mpr
        huniform)
  exact exists_next_failure_at_or_after_cutoff_of_verifiedPrefix_of_not_uniformFrom
    hcutoff hprefix hnotUniform

/-- Interval-finset version of
`exists_candidate_exact_next_failure_at_or_after_cutoff`. -/
theorem exists_candidate_exact_next_failure_at_or_after_cutoff_Icc
    (FloorBad : ℕ -> ℕ -> Prop) {cutoff : ℕ}
    (hcutoff : 4 ≤ cutoff)
    (hverified : VerifiedOn (Finset.Icc 4 cutoff) (CandidateListExactAt FloorBad))
    (hnot : ¬ CandidateListExactSmallestFamily FloorBad) :
    ∃ a : ℕ, cutoff ≤ a ∧ 4 ≤ a ∧ CandidateListExactAt FloorBad a ∧
      ¬ CandidateListExactAt FloorBad (a + 1) := by
  have hprefix : VerifiedPrefix 4 cutoff (CandidateListExactAt FloorBad) :=
    (verifiedOn_Icc_iff_verifiedPrefix 4 cutoff (CandidateListExactAt FloorBad)).mp hverified
  exact exists_candidate_exact_next_failure_at_or_after_cutoff
    FloorBad hcutoff hprefix hnot

#print axioms candidateListExactSmallestFamily_iff_uniformFrom_candidateListExactAt
#print axioms candidateListExactSuccessor_iff_successorStep_candidateListExactAt
#print axioms candidateListExactAt_four_of_candidateListExactSmallestFamily
#print axioms candidateListExactSuccessor_of_candidateListExactSmallestFamily
#print axioms candidateListExactSmallestFamily_iff_base_and_successor
#print axioms not_candidateListExactSmallestFamily_iff_not_base_or_not_successor
#print axioms not_candidateListExactSmallestFamily_iff_not_base_or_exists_exact_rung_next_fails
#print axioms exists_exact_rung_next_fails_of_base_of_not_candidateListExactSmallestFamily
#print axioms not_candidateListExactSmallestFamily_iff_exists_exact_rung_next_fails_of_base
#print axioms candidateListExactSmallestFamily_of_verifiedPrefix_and_successorStep
#print axioms candidateListExactSmallestFamily_of_verifiedOn_Icc_and_successorStep
#print axioms
  not_candidateListExactSuccessor_of_verifiedPrefix_of_not_candidateListExactSmallestFamily
#print axioms
  not_candidateListExactSuccessor_of_verifiedOn_Icc_of_not_candidateListExactSmallestFamily
#print axioms exists_exact_rung_next_fails_of_verifiedPrefix_of_not_candidateListExactSmallestFamily
#print axioms exists_exact_rung_next_fails_of_verifiedOn_Icc_of_not_candidateListExactSmallestFamily
#print axioms exists_candidate_exact_next_failure_at_or_after_cutoff
#print axioms exists_candidate_exact_next_failure_at_or_after_cutoff_Icc

end ArkLib.ProximityGap.Frontier.FloorClosureContract
