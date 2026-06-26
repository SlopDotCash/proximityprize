/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListCodewordSingletonRelationCliqueCover

/-!
# Color certificates for singleton scalar relation clique covers

`LineListCodewordSingletonRelationCliqueCover.lean` reduces the witness-local singleton graph
budget to a finite clique-cover certificate.  This file gives a convenient way to build such a
cover from a bounded invariant, or "color": if equal colors force a relation edge, then the color
fibers are relation-cliques and the number of colors bounds the independence number.

This is intended for future interpolation or exceptional-pencil invariants whose image on an
actual singleton-witness fiber can be bounded directly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F C : Type} [DecidableEq F] [DecidableEq C]

/-- A bounded-color certificate: equal colors inside `Ω` force relation edges. -/
def scalarRelationColorForcesEdges
    (R : F → F → Prop) (Ω : Finset F) (χ : F → C) : Prop :=
  ∀ γ ∈ Ω, ∀ γ' ∈ Ω, γ ≠ γ' → χ γ = χ γ' → R γ γ'

open Classical in
/-- If equal color values force relation edges, then color fibers form a clique cover. -/
theorem scalarRelationCliqueCover_of_colorForcesEdges
    (R : F → F → Prop) (Ω : Finset F) (χ : F → C)
    (hχ : scalarRelationColorForcesEdges R Ω χ) :
    ∃ cover : Finset (Finset F), cover.card ≤ (Ω.image χ).card ∧
      scalarRelationCliqueCover R Ω cover := by
  let fiber : C → Finset F := fun color => Ω.filter (fun γ => χ γ = color)
  let cover : Finset (Finset F) := (Ω.image χ).image fiber
  refine ⟨cover, ?_, ?subset, ?cliques⟩
  · simpa [cover] using (Finset.card_image_le : cover.card ≤ (Ω.image χ).card)
  · intro γ hγ
    rw [Finset.mem_biUnion]
    refine ⟨fiber (χ γ), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨χ γ, Finset.mem_image.mpr ⟨γ, hγ, rfl⟩, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hγ, rfl⟩
  · intro K hK
    rw [Finset.mem_image] at hK
    rcases hK with ⟨color, hcolor, rfl⟩
    intro γ hγ γ' hγ' hne
    rw [Finset.mem_filter] at hγ hγ'
    exact hχ γ hγ.1 γ' hγ'.1 hne (hγ.2.trans hγ'.2.symm)

variable [Field F] [Fintype F]
variable {n : ℕ} [NeZero n]

/-- Uniform bounded-color certificate for the witness-local relation route.  The color map may
depend on the line, the appearing codeword, and the scalar. -/
def UniformLargeZeroSafeCodewordRelationColorBudgeted
    (dom : Fin n ↪ F) (k a : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C) (S : ℕ) :
    Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        ((codewordSingletonWitnessScalars dom k a u₀ u₁ c).image
            (χ u₀ u₁ c)).card ≤ S ∧
          scalarRelationColorForcesEdges
            (fun γ γ' => R u₀ u₁ c γ γ')
            (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
            (χ u₀ u₁ c)

open Classical in
/-- A uniform bounded-color certificate gives a uniform clique-cover certificate. -/
theorem
    uniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted_of_relationColorBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (hχ : UniformLargeZeroSafeCodewordRelationColorBudgeted dom k a R χ S) :
    UniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted dom k a R S := by
  intro u₀ u₁ hnotEligible hsafe c hc
  rcases hχ u₀ u₁ hnotEligible hsafe c hc with ⟨hcard, hforces⟩
  rcases scalarRelationCliqueCover_of_colorForcesEdges
      (fun γ γ' => R u₀ u₁ c γ γ')
      (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
      (χ u₀ u₁ c) hforces with
    ⟨cover, hcoverCard, hcover⟩
  exact ⟨cover, hcoverCard.trans hcard, hcover⟩

/-- A uniform bounded-color certificate gives the witness-local independence budget. -/
theorem
    uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationColorBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (hχ : UniformLargeZeroSafeCodewordRelationColorBudgeted dom k a R χ S) :
    UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted dom k a R S :=
  uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationCliqueCover
    dom k a S R
    (uniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted_of_relationColorBudgeted
      dom k a S R χ hχ)

/-- A forbidden-edge theorem plus a bounded-color certificate gives the direct singleton cap. -/
theorem uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationColorBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hχ : UniformLargeZeroSafeCodewordRelationColorBudgeted dom k a R χ S) :
    UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S :=
  uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationCliqueCover
    dom k a S R hforbid
    (uniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted_of_relationColorBudgeted
      dom k a S R χ hχ)

/-- Production wrapper for the bounded-color relation route. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationColorBudgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hχ : UniformLargeZeroSafeCodewordRelationColorBudgeted dom k a R χ S)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationCliqueCover
    dom k a L S B R hSupport hFits hZeroSafe hforbid
    (uniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted_of_relationColorBudgeted
      dom k a S R χ hχ)
    hbudget

section SourceAudit

#print axioms scalarRelationColorForcesEdges
#print axioms scalarRelationCliqueCover_of_colorForcesEdges
#print axioms UniformLargeZeroSafeCodewordRelationColorBudgeted
#print axioms
  uniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted_of_relationColorBudgeted
#print axioms
  uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationColorBudgeted
#print axioms uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationColorBudgeted
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationColorBudgeted

end SourceAudit

end ProximityGap.Ownership
