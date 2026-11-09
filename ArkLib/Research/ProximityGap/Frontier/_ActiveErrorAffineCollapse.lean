/-
Copyright (c) 2026 Alex Astro. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Alex Astro (alexastro01)
-/
import ArkLib.Research.ProximityGap.Frontier._IncidenceDependencyArithmetic
import ArkLib.Research.ProximityGap.Frontier._SixErrorRankSupportMultiplicity

/-!
# Affine collapse of the relation-active decoding errors

An error is active when it has a nonzero coefficient in some linear relation among the full
error family. Restricting any relation to the active indices preserves its sum: every inactive
coefficient is zero. If there are fewer active indices than field elements, the full-support
lemma supplies one relation containing all active errors.

The small-error collapse theorem then puts all active decoded heads on one code-valued affine
line, provided their total error budget is less than twice the code distance and two active
parameters are distinct. The size bounds concern the active subfamily, not the whole family.
Inactive errors are excluded from the conclusion. No activity or production threshold is proved.
-/

set_option autoImplicit false

namespace ProximityGap.ActiveErrorAffineCollapse

/-- Any relation restricts to a set containing all relation-active indices. This does not
require every index of the full family to participate in a relation. -/
theorem relation_sum_restrict
    {F V I : Type*} [Field F] [AddCommGroup V] [Module F V] [Fintype I]
    (e : I → V) (A : Finset I)
    (hcover : ∀ i, (∃ c : I → F, (∑ j, c j • e j = 0) ∧ c i ≠ 0) → i ∈ A)
    (c : I → F) (hc : ∑ i, c i • e i = 0) :
    (∑ i : A, c i • e i) = 0 := by
  classical
  rw [Finset.sum_coe_sort A (fun i ↦ c i • e i)]
  calc
    (∑ i ∈ A, c i • e i) = ∑ i : I, c i • e i := by
      apply Finset.sum_subset (Finset.subset_univ A)
      intro i _ hi
      have hci : c i = 0 := by
        by_contra hne
        exact hi (hcover i ⟨c, hc, hne⟩)
      simp [hci]
    _ = 0 := hc

/-- The active part of a vector family has one full-support relation when its size is less
than the field size. Activity is measured in the original family, before restriction. -/
theorem full_support_relation_on_active
    {F V I : Type*} [Field F] [Fintype F] [Fintype I]
    [AddCommGroup V] [Module F V]
    (e : I → V) (A : Finset I)
    (hA : ∀ i, i ∈ A ↔ ∃ c : I → F, (∑ j, c j • e j = 0) ∧ c i ≠ 0)
    (hcard : A.card < Fintype.card F) :
    ∃ c : A → F, (∑ i, c i • e i = 0) ∧ ∀ i, c i ≠ 0 := by
  classical
  apply SixErrorRankSupportMultiplicity.full_support_relation_of_active_coordinates
    (fun i : A ↦ e i) (by simpa using hcard)
  intro i
  obtain ⟨c, hc, hci⟩ := (hA i).mp i.property
  exact ⟨fun j ↦ c j,
    relation_sum_restrict e A (fun j hj ↦ (hA j).mpr hj) c hc, hci⟩

/-- All relation-active decoded heads lie on one affine code line under the active-family
size and error-budget bounds. Inactive heads need not satisfy this conclusion. -/
theorem affine_heads_of_active_errors
    {F I Coord : Type*} [Field F] [Fintype F] [Fintype I] [Finite Coord]
    (C : Submodule F (Coord → F)) (u₀ u₁ : Coord → F)
    (w : I → (Coord → F)) (γ : I → F) (Q : I → Finset Coord)
    (A : Finset I)
    (hA : ∀ i, i ∈ A ↔ ∃ c : I → F,
      (∑ j, c j • (u₀ + γ j • u₁ - w j) = 0) ∧ c i ≠ 0)
    (D t : ℕ) (hw : ∀ i ∈ A, w i ∈ C)
    (hagree : ∀ i ∈ A, ∀ x ∉ Q i, w i x = u₀ x + γ i * u₁ x)
    (hweight : ∀ i ∈ A, (Q i).card ≤ t)
    (hcard : A.card < Fintype.card F) (hsmall : A.card * t < 2 * D)
    (i₀ i₁ : A) (hγ : γ i₀ ≠ γ i₁)
    (hdistance : ∀ v ∈ C, ∀ B : Finset Coord, B.card < D →
      (∀ x ∉ B, v x = 0) → v = 0) :
    ∃ U V, U ∈ C ∧ V ∈ C ∧ ∀ i ∈ A, w i = U + γ i • V := by
  classical
  letI : Fintype Coord := Fintype.ofFinite Coord
  obtain ⟨c, hc, hnonzero⟩ := full_support_relation_on_active
    (fun i ↦ u₀ + γ i • u₁ - w i) A hA hcard
  obtain ⟨U, V, hU, hV, hline⟩ :=
    IncidenceDependencyArithmetic.affine_heads_of_small_error_relation
      C u₀ u₁ (fun i : A ↦ w i) (fun i : A ↦ γ i) c (fun i : A ↦ Q i) D t
      (fun i ↦ hw i i.property) hnonzero (fun i ↦ hagree i i.property)
      (fun i ↦ hweight i i.property) (by simpa using hsmall) hc i₀ i₁ hγ hdistance
  exact ⟨U, V, hU, hV, fun i hi ↦ hline ⟨i, hi⟩⟩

end ProximityGap.ActiveErrorAffineCollapse

#print axioms ProximityGap.ActiveErrorAffineCollapse.relation_sum_restrict
#print axioms ProximityGap.ActiveErrorAffineCollapse.full_support_relation_on_active
#print axioms ProximityGap.ActiveErrorAffineCollapse.affine_heads_of_active_errors
