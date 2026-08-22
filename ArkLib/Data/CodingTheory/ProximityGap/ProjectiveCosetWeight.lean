/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveRankTwoAPI
import ArkLib.Data.CodingTheory.Basic.RelDistTranslation

/-!
# Relative coset weight on projective quotient pencils

For a linear code over a finite field, relative distance to the code descends to a relative
coset-leader weight on the quotient syndrome space.  This module identifies the metric envelope
of the projective MCA census:

* every bad projective slot has relative coset weight at most `delta`;
* the resulting low-weight slot count always upper-bounds the bad-slot count;
* away from the jointly-close branch, badness and low coset weight are exactly equivalent; and
* a genuine rank-two quotient pencil has `|F| + 1` distinct normalized slot points.

The jointly-close hypothesis in the exact statement is essential: quotient rank two alone does
not remove the local joint-explainability clause in `mcaEventProj`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal
open ProximityGap Code

namespace ProximityGap.ProjectiveCosetWeight

open MCAProjectiveEquivariance
open ProjectiveWorstCaseIncidence

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Relative coset-leader weight on the quotient syndrome space. -/
noncomputable def cosetRelWeight (C : Submodule F (ι → F)) :
    ((ι → F) ⧸ C) → ℝ≥0∞ :=
  Quotient.lift
    (fun u : ι → F => relDistFromCode u (C : Set (ι → F)))
    (fun u v huv => by
      exact relDistFromCode_eq_of_sub_mem C ((Submodule.quotientRel_def C).mp huv))

@[simp]
theorem cosetRelWeight_mk (C : Submodule F (ι → F)) (u : ι → F) :
    cosetRelWeight C (Submodule.Quotient.mk u) =
      relDistFromCode u (C : Set (ι → F)) := rfl

/-- The homogeneous quotient-pencil point represented by the coefficient pair `(alpha,beta)`. -/
def quotientPencilPoint (C : Submodule F (ι → F))
    (u₀ u₁ : ι → F) (α β : F) : (ι → F) ⧸ C :=
  α • (Submodule.Quotient.mk u₀ : (ι → F) ⧸ C) +
    β • (Submodule.Quotient.mk u₁ : (ι → F) ⧸ C)

theorem quotientPencilPoint_eq_mk (C : Submodule F (ι → F))
    (u₀ u₁ : ι → F) (α β : F) :
    quotientPencilPoint C u₀ u₁ α β =
      Submodule.Quotient.mk (α • u₀ + β • u₁) := by
  rfl

/-- Every projectively bad point has relative coset-leader weight at most `delta`. -/
theorem mcaEventProj_imp_cosetRelWeight_le
    (C : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (α β : F)
    (hbad : mcaEventProj (F := F) (C : Set (ι → F)) δ u₀ u₁ α β) :
    cosetRelWeight C (quotientPencilPoint C u₀ u₁ α β) ≤ δ := by
  classical
  obtain ⟨S, hS_card, ⟨w, hw_mem, hw_eq⟩, _hpair⟩ := hbad
  rw [quotientPencilPoint_eq_mk, cosetRelWeight_mk,
    relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨w, hw_mem, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols]
  refine ⟨S, (relDist_floor_bound_iff_complement_bound _ _ _).mpr hS_card, ?_⟩
  intro j
  refine ⟨fun hj => ?_, fun hne hj => ?_⟩
  · simpa [Pi.add_apply, Pi.smul_apply] using (hw_eq j hj).symm
  · exact hne (by simpa [Pi.add_apply, Pi.smul_apply] using (hw_eq j hj).symm)

/-- Away from the jointly-close branch, low quotient weight is exactly projective MCA badness. -/
theorem mcaEventProj_iff_cosetRelWeight_le_of_not_jointProximity
    (C : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (α β : F)
    (hjoint : ¬ jointProximity (C := (C : Set (ι → F)))
      (u := finMapTwoWords u₀ u₁) δ) :
    mcaEventProj (F := F) (C : Set (ι → F)) δ u₀ u₁ α β ↔
      cosetRelWeight C (quotientPencilPoint C u₀ u₁ α β) ≤ δ := by
  constructor
  · exact mcaEventProj_imp_cosetRelWeight_le C δ u₀ u₁ α β
  · intro hlow
    classical
    rw [quotientPencilPoint_eq_mk, cosetRelWeight_mk,
      relCloseToCode_iff_relCloseToCodeword_of_minDist] at hlow
    obtain ⟨w, hw_mem, hw_close⟩ := hlow
    rw [relCloseToWord_iff_exists_agreementCols] at hw_close
    obtain ⟨S, hS_card_nat, h_word_agree⟩ := hw_close
    have hS_card_real : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι :=
      (relDist_floor_bound_iff_complement_bound _ _ _).mp hS_card_nat
    refine ⟨S, hS_card_real,
      ⟨w, hw_mem, fun i hi => ((h_word_agree i).1 hi).symm⟩, ?_⟩
    intro h_pair
    apply hjoint
    rw [← jointAgreement_iff_jointProximity]
    obtain ⟨v₀, hv₀_mem, v₁, hv₁_mem, h_pair_agree⟩ := h_pair
    refine ⟨S, hS_card_real, finMapTwoWords v₀ v₁, ?_⟩
    intro i
    refine ⟨?_, ?_⟩
    · fin_cases i
      · exact hv₀_mem
      · exact hv₁_mem
    · intro j hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      fin_cases i
      · exact (h_pair_agree j hj).1
      · exact (h_pair_agree j hj).2

/-- Slotwise metric characterization on the non-jointly-close branch. -/
theorem badSlot_iff_cosetRelWeight_le_of_not_jointProximity
    (C : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F)
    (hjoint : ¬ jointProximity (C := (C : Set (ι → F)))
      (u := finMapTwoWords u₀ u₁) δ) (s : Option F) :
    badSlot (F := F) (C : Set (ι → F)) δ u₀ u₁ s ↔
      cosetRelWeight C
        (quotientPencilPoint C u₀ u₁ (slotCoords s).1 (slotCoords s).2) ≤ δ := by
  exact mcaEventProj_iff_cosetRelWeight_le_of_not_jointProximity
    C δ u₀ u₁ (slotCoords s).1 (slotCoords s).2 hjoint

/-- Unconditionally, bad slots form a subset of the low-coset-weight slots. -/
theorem badSlotCount_le_lowCosetWeightCount
    (C : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) :
    badSlotCount (F := F) (C : Set (ι → F)) δ u₀ u₁ ≤
      (Finset.univ.filter (fun s : Option F =>
        cosetRelWeight C
          (quotientPencilPoint C u₀ u₁ (slotCoords s).1 (slotCoords s).2) ≤ δ)).card := by
  classical
  unfold badSlotCount
  apply Finset.card_le_card
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact mcaEventProj_imp_cosetRelWeight_le C δ u₀ u₁
    (slotCoords s).1 (slotCoords s).2 hs

/-- Exact metric census identity on the non-jointly-close branch. -/
theorem badSlotCount_eq_lowCosetWeightCount_of_not_jointProximity
    (C : Submodule F (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F)
    (hjoint : ¬ jointProximity (C := (C : Set (ι → F)))
      (u := finMapTwoWords u₀ u₁) δ) :
    badSlotCount (F := F) (C : Set (ι → F)) δ u₀ u₁ =
      (Finset.univ.filter (fun s : Option F =>
        cosetRelWeight C
          (quotientPencilPoint C u₀ u₁ (slotCoords s).1 (slotCoords s).2) ≤ δ)).card := by
  classical
  unfold badSlotCount
  apply congrArg Finset.card
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact badSlot_iff_cosetRelWeight_le_of_not_jointProximity C δ u₀ u₁ hjoint s

/-! ## Genuine rank-two pencils -/

/-- Quotient independence makes the coefficient-to-syndrome map injective. -/
theorem quotientPencilPoint_coeff_injective_of_rowsIndependent
    (C : Submodule F (ι → F)) (u₀ u₁ : ι → F)
    (hind : RowsIndependentModCode C u₀ u₁) :
    Function.Injective (fun p : F × F => quotientPencilPoint C u₀ u₁ p.1 p.2) := by
  intro p q hpq
  by_contra hpne
  apply hind
  refine ⟨p.1 - q.1, p.2 - q.2, ?_, ?_⟩
  · by_contra hzero
    have hz := not_or.mp hzero
    have hfst : p.1 = q.1 := sub_eq_zero.mp (not_ne_iff.mp hz.1)
    have hsnd : p.2 = q.2 := sub_eq_zero.mp (not_ne_iff.mp hz.2)
    exact hpne (Prod.ext hfst hsnd)
  · have hmk :
        Submodule.Quotient.mk (p := C) (p.1 • u₀ + p.2 • u₁) =
          Submodule.Quotient.mk (p := C) (q.1 • u₀ + q.2 • u₁) := by
      simpa only [quotientPencilPoint_eq_mk] using hpq
    have hmem :
        (p.1 • u₀ + p.2 • u₁) - (q.1 • u₀ + q.2 • u₁) ∈ C :=
      (Submodule.Quotient.eq C).mp hmk
    have hlin :
        (p.1 - q.1) • u₀ + (p.2 - q.2) • u₁ =
          (p.1 • u₀ + p.2 • u₁) - (q.1 • u₀ + q.2 • u₁) := by
      module
    rw [hlin]
    exact hmem

/-- The normalized projective slot coordinates are injective. -/
theorem slotCoords_injective :
    Function.Injective (slotCoords (F := F)) := by
  intro s t h
  rcases s with _ | s <;> rcases t with _ | t
  · rfl
  · simp [slotCoords] at h
  · simp [slotCoords] at h
  · simpa [slotCoords] using h

/-- A genuine rank-two quotient pencil has distinct normalized projective slot points. -/
theorem slotQuotientPoint_injective_of_rowsIndependent
    (C : Submodule F (ι → F)) (u₀ u₁ : ι → F)
    (hind : RowsIndependentModCode C u₀ u₁) :
    Function.Injective (fun s : Option F =>
      quotientPencilPoint C u₀ u₁ (slotCoords s).1 (slotCoords s).2) :=
  (quotientPencilPoint_coeff_injective_of_rowsIndependent C u₀ u₁ hind).comp
    slotCoords_injective

open Classical in
/-- A genuine rank-two quotient pencil has exactly `|F| + 1` normalized slot points. -/
theorem card_slotQuotientPoints_of_rowsIndependent
    (C : Submodule F (ι → F)) (u₀ u₁ : ι → F)
    (hind : RowsIndependentModCode C u₀ u₁) :
    ((Finset.univ : Finset (Option F)).image (fun s : Option F =>
      quotientPencilPoint C u₀ u₁ (slotCoords s).1 (slotCoords s).2)).card =
        Fintype.card F + 1 := by
  rw [Finset.card_image_of_injective _
    (slotQuotientPoint_injective_of_rowsIndependent C u₀ u₁ hind), Finset.card_univ]
  simp

end ProximityGap.ProjectiveCosetWeight

/-! ## Axiom audit -/
#print axioms ProximityGap.ProjectiveCosetWeight.cosetRelWeight_mk
#print axioms ProximityGap.ProjectiveCosetWeight.quotientPencilPoint_eq_mk
#print axioms ProximityGap.ProjectiveCosetWeight.mcaEventProj_imp_cosetRelWeight_le
#print axioms
  ProximityGap.ProjectiveCosetWeight.mcaEventProj_iff_cosetRelWeight_le_of_not_jointProximity
#print axioms
  ProximityGap.ProjectiveCosetWeight.badSlot_iff_cosetRelWeight_le_of_not_jointProximity
#print axioms ProximityGap.ProjectiveCosetWeight.badSlotCount_le_lowCosetWeightCount
#print axioms
  ProximityGap.ProjectiveCosetWeight.badSlotCount_eq_lowCosetWeightCount_of_not_jointProximity
#print axioms
  ProximityGap.ProjectiveCosetWeight.quotientPencilPoint_coeff_injective_of_rowsIndependent
#print axioms ProximityGap.ProjectiveCosetWeight.slotCoords_injective
#print axioms
  ProximityGap.ProjectiveCosetWeight.slotQuotientPoint_injective_of_rowsIndependent
#print axioms
  ProximityGap.ProjectiveCosetWeight.card_slotQuotientPoints_of_rowsIndependent
