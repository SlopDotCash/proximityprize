/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveQuotientBall

/-!
# The unconditional proper quotient ball

The ordinary quotient syndrome ball forgets whether a witness support submodule contains the
entire quotient pencil.  Retaining that local properness predicate gives a pencil-dependent ball
whose projective incidence is exactly the MCA bad-slot census without a far hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal
open ProximityGap

namespace ProximityGap.ProjectiveProperQuotientBall

open MCAProjectiveEquivariance
open ProjectiveQuotientBall
open ProjectiveQuotientSupport

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

attribute [local instance] Classical.propDecidable

/-- The pencil-dependent quotient ball retaining exactly those support witnesses which do not
contain the whole pencil. -/
noncomputable def properQuotientBall
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (P : Submodule F ((ι → A) ⧸ C)) :
    Finset ((ι → A) ⧸ C) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ S : Finset ι, WitnessAdmissible δ S ∧
      q ∈ quotientSupportSubmodule C S ∧
      ¬ P ≤ quotientSupportSubmodule C S

@[simp] theorem mem_properQuotientBall_iff
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (P : Submodule F ((ι → A) ⧸ C))
    (q : (ι → A) ⧸ C) :
    q ∈ properQuotientBall C δ P ↔
      ∃ S : Finset ι, WitnessAdmissible δ S ∧
        q ∈ quotientSupportSubmodule C S ∧
        ¬ P ≤ quotientSupportSubmodule C S := by
  classical
  simp [properQuotientBall]

/-- The proper quotient ball is a subset of the ordinary quotient syndrome ball. -/
theorem properQuotientBall_subset_quotientSyndromeBall
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (P : Submodule F ((ι → A) ⧸ C)) :
    properQuotientBall C δ P ⊆ quotientSyndromeBall C δ := by
  intro q hq
  obtain ⟨S, hS, hmem, _hproper⟩ :=
    (mem_properQuotientBall_iff C δ P q).1 hq
  exact (mem_quotientSyndromeBall_iff C δ q).2 ⟨S, hS, hmem⟩

/-- The incidence of the normalized quotient pencil with its proper quotient ball. -/
/-- On a jointly-far pencil, the proper quotient ball is the ordinary quotient syndrome ball. -/
theorem properQuotientBall_eq_quotientSyndromeBall_of_pencilJointFar
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (P : Submodule F ((ι → A) ⧸ C))
    (hfar : PencilJointFar C δ P) :
    properQuotientBall C δ P = quotientSyndromeBall C δ := by
  ext q
  constructor
  · intro hq
    exact properQuotientBall_subset_quotientSyndromeBall C δ P hq
  · intro hq
    obtain ⟨S, hS, hmem⟩ :=
      (mem_quotientSyndromeBall_iff C δ q).1 hq
    exact (mem_properQuotientBall_iff C δ P q).2
      ⟨S, hS, hmem, hfar S hS⟩

/-- The normalized-slot incidence of a quotient pencil with its proper quotient ball.  Dependent
row pairs may represent the same quotient point in more than one slot. -/
noncomputable def properProjectiveBallIncidence
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℕ := by
  classical
  exact (Finset.univ.filter fun s : Option F =>
    quotientSlotPoint C u₀ u₁ s ∈
      properQuotientBall C δ (quotientPencil C u₀ u₁)).card

/-- The affine-chart part of the proper quotient line--ball incidence. -/
noncomputable def properAffineBallIncidence
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℕ := by
  classical
  exact (Finset.univ.filter fun γ : F =>
    (Submodule.Quotient.mk (p := C) u₀ : (ι → A) ⧸ C) +
      γ • Submodule.Quotient.mk (p := C) u₁ ∈
        properQuotientBall C δ (quotientPencil C u₀ u₁)).card

/-- Under joint farness, proper projective incidence agrees with ordinary projective
line--ball incidence. -/
theorem properProjectiveBallIncidence_eq_projectiveBallIncidence_of_pencilJointFar
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (hfar : PencilJointFar C δ (quotientPencil C u₀ u₁)) :
    properProjectiveBallIncidence C δ u₀ u₁ =
      projectiveBallIncidence C δ u₀ u₁ := by
  classical
  unfold properProjectiveBallIncidence projectiveBallIncidence
  rw [properQuotientBall_eq_quotientSyndromeBall_of_pencilJointFar C δ _ hfar]

/-- **Unconditional slotwise dictionary.**  A projective slot is MCA-bad exactly when its quotient
point lies in the pencil-dependent proper quotient ball. -/
theorem badSlot_iff_mem_properQuotientBall
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (s : Option F) :
    badSlot (F := F) (C : Set (ι → A)) δ u₀ u₁ s ↔
      quotientSlotPoint C u₀ u₁ s ∈
        properQuotientBall C δ (quotientPencil C u₀ u₁) := by
  rw [mem_properQuotientBall_iff]
  simpa [badSlot, quotientSlotPoint, WitnessAdmissible] using
    (mcaEventProj_iff_quotientPencilSupport C δ u₀ u₁
      (slotCoords s).1 (slotCoords s).2)

/-- **Unconditional exact projective incidence law.**  The MCA bad-slot census equals the
incidence of the quotient pencil with its proper quotient ball for every row pair. -/
/-- **Unconditional exact projective slot-incidence law.**  The MCA bad-slot census equals the
normalized-slot incidence of the quotient pencil with its proper quotient ball for every row pair.
-/
theorem badSlotCount_eq_properProjectiveBallIncidence
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ =
      properProjectiveBallIncidence C δ u₀ u₁ := by
  classical
  unfold badSlotCount properProjectiveBallIncidence
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact badSlot_iff_mem_properQuotientBall C δ u₀ u₁ s

/-- The proper projective incidence is its affine-chart incidence plus the indicator of
incidence at infinity. -/
theorem properProjectiveBallIncidence_eq_affine_add_infty
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    properProjectiveBallIncidence C δ u₀ u₁ =
      properAffineBallIncidence C δ u₀ u₁ +
        (if (Submodule.Quotient.mk (p := C) u₁ : (ι → A) ⧸ C) ∈
            properQuotientBall C δ (quotientPencil C u₀ u₁) then 1 else 0) := by
  classical
  unfold properProjectiveBallIncidence properAffineBallIncidence
  have hunion : (Finset.univ : Finset (Option F)) =
      Finset.univ.image Option.some ∪ {none} := by
    apply Finset.eq_of_subset_of_card_le
    · intro s _
      rcases s with _ | γ
      · exact Finset.mem_union_right _ (Finset.mem_singleton_self none)
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ γ))
    · exact Finset.card_le_univ _
  rw [hunion, Finset.filter_union, Finset.card_union_of_disjoint, Finset.filter_image]
  · congr 1
    · rw [Finset.card_image_of_injective _ (Option.some_injective F)]
      congr 1
      apply Finset.filter_congr
      intro γ _
      simp only [quotientSlotPoint, slotCoords, one_smul]
      change C.mkQ (u₀ + γ • u₁) ∈
          properQuotientBall C δ (quotientPencil C u₀ u₁) ↔
        C.mkQ u₀ + γ • C.mkQ u₁ ∈
          properQuotientBall C δ (quotientPencil C u₀ u₁)
      rw [map_add, map_smul]
    · by_cases h : (Submodule.Quotient.mk (p := C) u₁ : (ι → A) ⧸ C) ∈
          properQuotientBall C δ (quotientPencil C u₀ u₁)
      · rw [if_pos h, Finset.filter_singleton, if_pos]
        · exact Finset.card_singleton none
        · simpa [quotientSlotPoint, slotCoords] using h
      · rw [if_neg h, Finset.filter_singleton, if_neg]
        · exact Finset.card_empty
        · simpa [quotientSlotPoint, slotCoords] using h
  · refine Finset.disjoint_filter_filter ?_
    rw [Finset.disjoint_left]
    intro s hs hns
    rw [Finset.mem_image] at hs
    obtain ⟨γ, _, rfl⟩ := hs
    exact Option.some_ne_none γ (Finset.mem_singleton.mp hns)

/-- The affine part of the proper quotient incidence has the generic exact Fourier expansion on
the quotient module. -/
theorem properAffineBallIncidence_spectral
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    ((properAffineBallIncidence C δ u₀ u₁ : ℕ) : ℂ) *
        (Fintype.card ((ι → A) ⧸ C) : ℂ) =
      (Fintype.card F : ℂ) *
        ∑ ψ : AddChar ((ι → A) ⧸ C) ℂ,
          (if ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ
              (Submodule.Quotient.mk (p := C) u₁) = 0 then
            ∑ q ∈ properQuotientBall C δ (quotientPencil C u₀ u₁),
              ψ (Submodule.Quotient.mk (p := C) u₀ - q)
          else 0) := by
  classical
  simpa [properAffineBallIncidence] using
    (ArkLib.ProximityGap.LineIncidenceSpectral.lineIncidence_spectral
      (F := F) (V := (ι → A) ⧸ C)
      (properQuotientBall C δ (quotientPencil C u₀ u₁))
      (Submodule.Quotient.mk (p := C) u₀)
      (Submodule.Quotient.mk (p := C) u₁))

end ProximityGap.ProjectiveProperQuotientBall

/-! ## Axiom audit -/
#print axioms
  ProximityGap.ProjectiveProperQuotientBall.properQuotientBall_subset_quotientSyndromeBall
#print axioms
  ProximityGap.ProjectiveProperQuotientBall.badSlot_iff_mem_properQuotientBall
#print axioms
  ProximityGap.ProjectiveProperQuotientBall.badSlotCount_eq_properProjectiveBallIncidence
  ProximityGap.ProjectiveProperQuotientBall.properQuotientBall_eq_quotientSyndromeBall_of_pencilJointFar
#print axioms
  ProximityGap.ProjectiveProperQuotientBall.properProjectiveBallIncidence_eq_projectiveBallIncidence_of_pencilJointFar
#print axioms
  ProximityGap.ProjectiveProperQuotientBall.badSlot_iff_mem_properQuotientBall
#print axioms
  ProximityGap.ProjectiveProperQuotientBall.badSlotCount_eq_properProjectiveBallIncidence
#print axioms
  ProximityGap.ProjectiveProperQuotientBall.properProjectiveBallIncidence_eq_affine_add_infty
#print axioms
  ProximityGap.ProjectiveProperQuotientBall.properAffineBallIncidence_spectral
