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
noncomputable def properProjectiveBallIncidence
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℕ := by
  classical
  exact (Finset.univ.filter fun s : Option F =>
    quotientSlotPoint C u₀ u₁ s ∈
      properQuotientBall C δ (quotientPencil C u₀ u₁)).card

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

end ProximityGap.ProjectiveProperQuotientBall

/-! ## Axiom audit -/
#print axioms
  ProximityGap.ProjectiveProperQuotientBall.properQuotientBall_subset_quotientSyndromeBall
#print axioms
  ProximityGap.ProjectiveProperQuotientBall.badSlot_iff_mem_properQuotientBall
#print axioms
  ProximityGap.ProjectiveProperQuotientBall.badSlotCount_eq_properProjectiveBallIncidence
