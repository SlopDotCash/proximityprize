/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveCosetWeight
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveQuotientBall

/-!
# Unification of the projective quotient ball and coset metric

The finite union of admissible quotient support subspaces is exactly the sublevel set of relative
coset weight.  Thus the metric and finite-ball projective census formulations are the same
reduction, while the latter additionally provides the affine Fourier expansion.  The accompanying
basis-free/failure-of-joint-proximity equivalence is proved in `ProjectiveQuotientBall` for general
module-valued words.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal
open ProximityGap Code

namespace ProximityGap.ProjectiveMetricUnification

open MCAProjectiveEquivariance
open ProjectiveCosetWeight
open ProjectiveQuotientBall
open ProjectiveQuotientSupport

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The support-union quotient ball is exactly the sublevel set of relative coset weight. -/
theorem mem_quotientSyndromeBall_iff_cosetRelWeight_le
    (C : Submodule F (ι → F)) (δ : ℝ≥0) (q : (ι → F) ⧸ C) :
    q ∈ quotientSyndromeBall C δ ↔ cosetRelWeight C q ≤ δ := by
  classical
  refine Submodule.Quotient.induction_on C q (fun u => ?_)
  constructor
  · intro hball
    obtain ⟨S, hS, hsupport⟩ :=
      (mem_quotientSyndromeBall_iff C δ (Submodule.Quotient.mk u)).1 hball
    obtain ⟨w, hw, hagree⟩ :=
      (quotient_mk_mem_quotientSupportSubmodule_iff C S u).1 hsupport
    rw [cosetRelWeight_mk, relCloseToCode_iff_relCloseToCodeword_of_minDist]
    refine ⟨w, hw, ?_⟩
    rw [relCloseToWord_iff_exists_agreementCols]
    refine ⟨S, (relDist_floor_bound_iff_complement_bound _ _ _).mpr ?_, ?_⟩
    · simpa [WitnessAdmissible] using hS
    · intro i
      refine ⟨fun hi => (hagree i hi).symm, fun hne hi => ?_⟩
      exact hne (hagree i hi).symm
  · intro hlow
    rw [cosetRelWeight_mk, relCloseToCode_iff_relCloseToCodeword_of_minDist] at hlow
    obtain ⟨w, hw, hclose⟩ := hlow
    rw [relCloseToWord_iff_exists_agreementCols] at hclose
    obtain ⟨S, hS, hagree⟩ := hclose
    apply (mem_quotientSyndromeBall_iff C δ (Submodule.Quotient.mk u)).2
    refine ⟨S, ?_, ?_⟩
    · have hS' := (relDist_floor_bound_iff_complement_bound _ _ _).mp hS
      simpa [WitnessAdmissible] using hS'
    · apply (quotient_mk_mem_quotientSupportSubmodule_iff C S u).2
      exact ⟨w, hw, fun i hi => ((hagree i).1 hi).symm⟩

/-- The quotient line-ball incidence is literally the number of normalized slots of relative
coset weight at most `delta`. -/
theorem projectiveBallIncidence_eq_lowCosetWeightCount
    (C : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) :
    projectiveBallIncidence C δ u₀ u₁ =
      (Finset.univ.filter (fun s : Option F =>
        cosetRelWeight C
          (quotientPencilPoint C u₀ u₁ (slotCoords s).1 (slotCoords s).2) ≤ δ)).card := by
  classical
  unfold projectiveBallIncidence
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_quotientSyndromeBall_iff_cosetRelWeight_le]
  simp only [quotientSlotPoint, quotientPencilPoint_eq_mk]

end ProximityGap.ProjectiveMetricUnification

/-! ## Axiom audit -/
#print axioms
  ProximityGap.ProjectiveMetricUnification.mem_quotientSyndromeBall_iff_cosetRelWeight_le
#print axioms
  ProximityGap.ProjectiveMetricUnification.projectiveBallIncidence_eq_lowCosetWeightCount
