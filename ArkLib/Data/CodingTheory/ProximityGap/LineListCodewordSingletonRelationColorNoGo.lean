/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListCodewordSingletonRelationColorCover

/-!
# Same-color singleton relation no-go

`LineListCodewordSingletonRelationColorCover.lean` packages a useful bounded-color certificate:
equal colors should force relation edges.  The first tempting specialization is to make the
relation itself be equality of colors.  Under the singleton forbidden-edge condition, that
specialization is tautological: the color is injective on every singleton-witness fiber, so its
image has exactly the same cardinality as the fiber.

This file records that collapse so future color invariants have a crisp target: they must force a
different algebraic relation, not merely the same-color relation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F C : Type} [DecidableEq F] [DecidableEq C]

/-- The relation that connects exactly equal-color scalar pairs. -/
def scalarSameColorRelation (χ : F → C) (γ γ' : F) : Prop :=
  χ γ = χ γ'

omit [DecidableEq F] [DecidableEq C] in
/-- Independence for the same-color relation is exactly injectivity of the color map on the
finite scalar set. -/
theorem scalarRelationIndependent_sameColorRelation_iff_injOn
    (χ : F → C) (Ω : Finset F) :
    scalarRelationIndependent (scalarSameColorRelation χ) Ω ↔
      Set.InjOn χ (↑Ω : Set F) := by
  classical
  constructor
  · intro hind γ hγ γ' hγ' hsame
    by_contra hne
    exact (hind γ hγ γ' hγ' hne) hsame
  · intro hinj γ hγ γ' hγ' hne hsame
    exact hne (hinj hγ hγ' hsame)

omit [DecidableEq F] in
/-- An independent set for the same-color relation has no color collisions. -/
theorem scalarSameColorRelation_image_card_eq_of_independent
    (χ : F → C) (Ω : Finset F)
    (hind : scalarRelationIndependent (scalarSameColorRelation χ) Ω) :
    (Ω.image χ).card = Ω.card := by
  exact Finset.card_image_of_injOn
    ((scalarRelationIndependent_sameColorRelation_iff_injOn χ Ω).mp hind)

omit [DecidableEq F] [DecidableEq C] in
/-- The equal-color forcing condition is automatic for the same-color relation. -/
theorem scalarRelationColorForcesEdges_sameColorRelation
    (χ : F → C) (Ω : Finset F) :
    scalarRelationColorForcesEdges (scalarSameColorRelation χ) Ω χ := by
  intro γ _hγ γ' _hγ' _hne hsame
  exact hsame

variable [Field F] [Fintype F]
variable {n : ℕ} [NeZero n]

/-- If same-color edges are forbidden on singleton-witness fibers, then the color image is as
large as the original singleton-witness fiber. -/
theorem codewordSingletonWitnessScalars_image_card_eq_of_sameColor_forbidden
    (dom : Fin n ↪ F) (k a : ℕ)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a
      (fun u₀ u₁ c γ γ' => scalarSameColorRelation (χ u₀ u₁ c) γ γ'))
    (u₀ u₁ c : Fin n → F)
    (hnotEligible : ¬ SupportEligibleLineDirection a u₁)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hc : c ∈ lineAppearingCodewords dom k a u₀ u₁) :
    ((codewordSingletonWitnessScalars dom k a u₀ u₁ c).image
        (χ u₀ u₁ c)).card =
      (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card :=
  scalarSameColorRelation_image_card_eq_of_independent
    (χ u₀ u₁ c)
    (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
    (hforbid u₀ u₁ hnotEligible hsafe c hc)

/-- Under forbidden same-color edges, a bounded-color certificate is exactly the direct
singleton-fiber budget.  Thus this specialization provides no compression over the original
per-codeword singleton cap. -/
theorem sameColorRelationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden
    (dom : Fin n ↪ F) (k a S : ℕ)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a
      (fun u₀ u₁ c γ γ' => scalarSameColorRelation (χ u₀ u₁ c) γ γ')) :
    UniformLargeZeroSafeCodewordRelationColorBudgeted dom k a
        (fun u₀ u₁ c γ γ' => scalarSameColorRelation (χ u₀ u₁ c) γ γ') χ S ↔
      UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
  constructor
  · intro hχ
    exact uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationColorBudgeted
      dom k a S
      (fun u₀ u₁ c γ γ' => scalarSameColorRelation (χ u₀ u₁ c) γ γ')
      χ hforbid hχ
  · intro hsingle u₀ u₁ hnotEligible hsafe c hc
    constructor
    · exact Finset.card_image_le.trans (hsingle u₀ u₁ hnotEligible hsafe c hc)
    · exact scalarRelationColorForcesEdges_sameColorRelation (χ u₀ u₁ c)
        (codewordSingletonWitnessScalars dom k a u₀ u₁ c)

open Classical in
/-- Failure of the same-color bounded-color route is exactly failure of the original singleton
budget. -/
theorem
    not_sameColorRelationColorBudgeted_iff_exists_singleton_card_gt_of_forbidden
    (dom : Fin n ↪ F) (k a S : ℕ)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a
      (fun u₀ u₁ c γ γ' => scalarSameColorRelation (χ u₀ u₁ c) γ γ')) :
    (¬ UniformLargeZeroSafeCodewordRelationColorBudgeted dom k a
        (fun u₀ u₁ c γ γ' => scalarSameColorRelation (χ u₀ u₁ c) γ γ') χ S) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            S < (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card := by
  constructor
  · intro hnot
    have hnotSingleton :
        ¬ UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
      intro hsingle
      exact hnot
        ((sameColorRelationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden
          dom k a S χ hforbid).mpr hsingle)
    exact (not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
      dom k a S).mp hnotSingleton
  · intro hex hχ
    have hsingle :
        UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S :=
      (sameColorRelationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden
        dom k a S χ hforbid).mp hχ
    exact
      ((not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
        dom k a S).mpr hex) hsingle

section SourceAudit

#print axioms scalarSameColorRelation
#print axioms scalarRelationIndependent_sameColorRelation_iff_injOn
#print axioms scalarSameColorRelation_image_card_eq_of_independent
#print axioms codewordSingletonWitnessScalars_image_card_eq_of_sameColor_forbidden
#print axioms scalarRelationColorForcesEdges_sameColorRelation
#print axioms sameColorRelationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden
#print axioms
  not_sameColorRelationColorBudgeted_iff_exists_singleton_card_gt_of_forbidden

end SourceAudit

end ProximityGap.Ownership
