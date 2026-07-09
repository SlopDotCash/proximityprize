/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveQuotientSupport
import ArkLib.Data.CodingTheory.ProximityGap.LineIncidenceSpectral

/-!
# The projective MCA census as quotient line--ball incidence

The quotient-support dictionary identifies the finite syndrome ball as the union of all
admissible support submodules.  For a quotient pencil which is not contained in any one of those
submodules, the MCA no-joint clause is automatic.  Its full projective bad-slot census is then
exactly the incidence of the projective quotient line with the syndrome ball.

This basis-free condition is weaker than requiring one chosen row to be far from the code.  It is
also the precise condition under which the generic spectral line-incidence identity applies to
the MCA census without discarding the no-joint clause.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal
open ProximityGap

namespace ProximityGap.ProjectiveQuotientBall

open MCAProjectiveEquivariance
open ProjectiveQuotientSupport

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

attribute [local instance] Classical.propDecidable

/-- A coordinate set is admissible at radius `delta` when it is large enough to witness an MCA
event. -/
def WitnessAdmissible (δ : ℝ≥0) (S : Finset ι) : Prop :=
  (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι

/-- The finite quotient syndrome ball: the union of the quotient support submodules attached to
all witness-sized coordinate sets. -/
noncomputable def quotientSyndromeBall
    (C : Submodule F (ι → A)) (δ : ℝ≥0) : Finset ((ι → A) ⧸ C) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ S : Finset ι, WitnessAdmissible δ S ∧ q ∈ quotientSupportSubmodule C S

@[simp] theorem mem_quotientSyndromeBall_iff
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (q : (ι → A) ⧸ C) :
    q ∈ quotientSyndromeBall C δ ↔
      ∃ S : Finset ι, WitnessAdmissible δ S ∧
        q ∈ quotientSupportSubmodule C S := by
  classical
  simp [quotientSyndromeBall]

/-- A quotient pencil is jointly far at radius `delta` when no witness-sized support submodule
contains the whole pencil.  This is independent of any chosen basis of the pencil. -/
def PencilJointFar (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (P : Submodule F ((ι → A) ⧸ C)) : Prop :=
  ∀ S : Finset ι, WitnessAdmissible δ S →
    ¬ P ≤ quotientSupportSubmodule C S

/-- The quotient class represented by a normalized projective slot. -/
def quotientSlotPoint (C : Submodule F (ι → A)) (u₀ u₁ : ι → A)
    (s : Option F) : (ι → A) ⧸ C :=
  Submodule.Quotient.mk (p := C)
    ((slotCoords s).1 • u₀ + (slotCoords s).2 • u₁)

/-- The projective incidence of a quotient pencil with the finite syndrome ball. -/
noncomputable def projectiveBallIncidence
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℕ := by
  classical
  exact (Finset.univ.filter fun s : Option F =>
    quotientSlotPoint C u₀ u₁ s ∈ quotientSyndromeBall C δ).card

/-- The usual affine-chart part of the quotient line--ball incidence. -/
noncomputable def affineBallIncidence
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℕ := by
  classical
  exact (Finset.univ.filter fun γ : F =>
    (Submodule.Quotient.mk (p := C) u₀ : (ι → A) ⧸ C) +
      γ • Submodule.Quotient.mk (p := C) u₁ ∈ quotientSyndromeBall C δ).card

/-- Every projectively bad slot lies in the quotient syndrome ball. -/
theorem badSlot_imp_mem_quotientSyndromeBall
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (s : Option F) :
    badSlot (F := F) (C : Set (ι → A)) δ u₀ u₁ s →
      quotientSlotPoint C u₀ u₁ s ∈ quotientSyndromeBall C δ := by
  intro hbad
  obtain ⟨S, hS, hpoint, _hproper⟩ :=
    (mcaEventProj_iff_quotientPencilSupport C δ u₀ u₁
      (slotCoords s).1 (slotCoords s).2).1 hbad
  exact (mem_quotientSyndromeBall_iff C δ _).2 ⟨S, hS, hpoint⟩

/-- On a jointly-far quotient pencil, membership in the quotient syndrome ball is exactly MCA
badness of the corresponding projective slot. -/
theorem badSlot_iff_mem_quotientSyndromeBall_of_pencilJointFar
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (hfar : PencilJointFar C δ (quotientPencil C u₀ u₁)) (s : Option F) :
    badSlot (F := F) (C : Set (ι → A)) δ u₀ u₁ s ↔
      quotientSlotPoint C u₀ u₁ s ∈ quotientSyndromeBall C δ := by
  constructor
  · exact badSlot_imp_mem_quotientSyndromeBall C δ u₀ u₁ s
  · intro hball
    obtain ⟨S, hS, hpoint⟩ :=
      (mem_quotientSyndromeBall_iff C δ _).1 hball
    exact (mcaEventProj_iff_quotientPencilSupport C δ u₀ u₁
      (slotCoords s).1 (slotCoords s).2).2
      ⟨S, hS, hpoint, hfar S hS⟩

/-- The MCA projective census is always bounded by projective quotient line--ball incidence. -/
theorem badSlotCount_le_projectiveBallIncidence
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ ≤
      projectiveBallIncidence C δ u₀ u₁ := by
  classical
  unfold badSlotCount projectiveBallIncidence
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, badSlot_imp_mem_quotientSyndromeBall C δ u₀ u₁ s hs.2⟩

/-- **Exact projective line--ball incidence law.**  When the quotient pencil is jointly far,
its MCA bad-slot census is exactly its incidence with the finite quotient syndrome ball. -/
theorem badSlotCount_eq_projectiveBallIncidence_of_pencilJointFar
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (hfar : PencilJointFar C δ (quotientPencil C u₀ u₁)) :
    badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ =
      projectiveBallIncidence C δ u₀ u₁ := by
  classical
  unfold badSlotCount projectiveBallIncidence
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact badSlot_iff_mem_quotientSyndromeBall_of_pencilJointFar C δ u₀ u₁ hfar s

/-- The projective quotient line--ball incidence is its affine-chart incidence plus the
indicator of incidence at infinity. -/
theorem projectiveBallIncidence_eq_affine_add_infty
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    projectiveBallIncidence C δ u₀ u₁ =
      affineBallIncidence C δ u₀ u₁ +
        (if (Submodule.Quotient.mk (p := C) u₁ : (ι → A) ⧸ C) ∈
            quotientSyndromeBall C δ then 1 else 0) := by
  classical
  unfold projectiveBallIncidence affineBallIncidence
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
      change C.mkQ (u₀ + γ • u₁) ∈ quotientSyndromeBall C δ ↔
        C.mkQ u₀ + γ • C.mkQ u₁ ∈ quotientSyndromeBall C δ
      rw [map_add, map_smul]
    · by_cases h : (Submodule.Quotient.mk (p := C) u₁ : (ι → A) ⧸ C) ∈
          quotientSyndromeBall C δ
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

/-- The affine part of the quotient MCA incidence has the generic exact Fourier expansion on the
quotient module. -/
theorem affineBallIncidence_spectral
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    ((affineBallIncidence C δ u₀ u₁ : ℕ) : ℂ) *
        (Fintype.card ((ι → A) ⧸ C) : ℂ) =
      (Fintype.card F : ℂ) *
        ∑ ψ : AddChar ((ι → A) ⧸ C) ℂ,
          (if ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ
              (Submodule.Quotient.mk (p := C) u₁) = 0 then
            ∑ q ∈ quotientSyndromeBall C δ,
              ψ (Submodule.Quotient.mk (p := C) u₀ - q)
          else 0) := by
  classical
  simpa [affineBallIncidence] using
    (ArkLib.ProximityGap.LineIncidenceSpectral.lineIncidence_spectral
      (F := F) (V := (ι → A) ⧸ C) (quotientSyndromeBall C δ)
      (Submodule.Quotient.mk (p := C) u₀)
      (Submodule.Quotient.mk (p := C) u₁))

end ProximityGap.ProjectiveQuotientBall

/-! ## Axiom audit -/
#print axioms ProximityGap.ProjectiveQuotientBall.badSlot_imp_mem_quotientSyndromeBall
#print axioms
  ProximityGap.ProjectiveQuotientBall.badSlot_iff_mem_quotientSyndromeBall_of_pencilJointFar
#print axioms ProximityGap.ProjectiveQuotientBall.badSlotCount_le_projectiveBallIncidence
#print axioms
  ProximityGap.ProjectiveQuotientBall.badSlotCount_eq_projectiveBallIncidence_of_pencilJointFar
#print axioms ProximityGap.ProjectiveQuotientBall.projectiveBallIncidence_eq_affine_add_infty
#print axioms ProximityGap.ProjectiveQuotientBall.affineBallIncidence_spectral
