/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListCodewordSingletonSupportRatio

/-!
# Clique-cover certificates for singleton scalar relations

The singleton-scalar graph route asks for a witness-local independence bound: every independent
subset of the actual singleton-witness scalars must have size at most `S`.  This file provides a
standard finite-graph certificate for that obligation.  If the singleton-witness set is covered by
at most `S` relation-cliques, then an independent subset meets each clique in at most one scalar,
so it has size at most `S`.

This does not propose a specific algebraic relation.  It gives future interpolation or
exceptional-pencil relations a precise small-clique-cover target, and gives the scanner an exact
failure object when that target is not available.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [DecidableEq F]

/-- A finite scalar set is a clique for a binary scalar relation. -/
def scalarRelationClique (R : F → F → Prop) (K : Finset F) : Prop :=
  ∀ γ ∈ K, ∀ γ' ∈ K, γ ≠ γ' → R γ γ'

/-- A finite clique cover of a scalar vertex set.  The cover sets need not be disjoint. -/
def scalarRelationCliqueCover
    (R : F → F → Prop) (Γ : Finset F) (cover : Finset (Finset F)) : Prop :=
  Γ ⊆ cover.biUnion (fun K : Finset F => K) ∧
    ∀ K ∈ cover, scalarRelationClique R K

/-- An independent scalar set meets a relation-clique in at most one scalar. -/
theorem scalarRelationIndependent_inter_clique_card_le_one
    (R : F → F → Prop) (Γ K : Finset F)
    (hind : scalarRelationIndependent R Γ)
    (hclique : scalarRelationClique R K) :
    (K ∩ Γ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ hγ γ' hγ'
  rw [Finset.mem_inter] at hγ hγ'
  by_contra hne
  exact (hind γ hγ.2 γ' hγ'.2 hne) (hclique γ hγ.1 γ' hγ'.1 hne)

/-- A clique cover of an ambient scalar set bounds every independent subset of that ambient set
by the number of cliques. -/
theorem scalarRelationIndependent_card_le_of_cliqueCover
    (R : F → F → Prop) {Γ Ω : Finset F} {cover : Finset (Finset F)}
    (hΓ : Γ ⊆ Ω)
    (hind : scalarRelationIndependent R Γ)
    (hcover : scalarRelationCliqueCover R Ω cover) :
    Γ.card ≤ cover.card := by
  have hsub : Γ ⊆ cover.biUnion (fun K : Finset F => K ∩ Γ) := by
    intro γ hγ
    have hγΩ : γ ∈ Ω := hΓ hγ
    have hγcover := hcover.1 hγΩ
    rw [Finset.mem_biUnion] at hγcover ⊢
    rcases hγcover with ⟨K, hK, hγK⟩
    exact ⟨K, hK, Finset.mem_inter.mpr ⟨hγK, hγ⟩⟩
  calc
    Γ.card ≤ (cover.biUnion (fun K : Finset F => K ∩ Γ)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ K ∈ cover, (K ∩ Γ).card := Finset.card_biUnion_le
    _ ≤ ∑ _K ∈ cover, 1 := by
      refine Finset.sum_le_sum ?_
      intro K hK
      exact scalarRelationIndependent_inter_clique_card_le_one R Γ K hind (hcover.2 K hK)
    _ = cover.card := by
      simpa using (Finset.card_eq_sum_ones cover).symm

/-- The singleton cover is always a clique cover, for any scalar relation. -/
theorem scalarRelationCliqueCover_singletons
    (R : F → F → Prop) (Ω : Finset F) :
    ∃ cover : Finset (Finset F), cover.card ≤ Ω.card ∧
      scalarRelationCliqueCover R Ω cover := by
  let cover : Finset (Finset F) := Ω.image (fun γ => ({γ} : Finset F))
  refine ⟨cover, ?_, ?_⟩
  · exact Finset.card_image_le
  · constructor
    · intro γ hγ
      rw [Finset.mem_biUnion]
      exact ⟨{γ}, Finset.mem_image.mpr ⟨γ, hγ, rfl⟩, by simp⟩
    · intro K hK
      rw [Finset.mem_image] at hK
      rcases hK with ⟨γ, _hγ, rfl⟩
      intro x hx y hy hne
      rw [Finset.mem_singleton] at hx hy
      subst x
      subst y
      exact (hne rfl).elim

/-- If the ambient scalar set is independent, every clique cover of it has at least as many
cliques as vertices. -/
theorem scalarRelationCliqueCover_card_ge_of_independent
    (R : F → F → Prop) (Ω : Finset F) {cover : Finset (Finset F)}
    (hind : scalarRelationIndependent R Ω)
    (hcover : scalarRelationCliqueCover R Ω cover) :
    Ω.card ≤ cover.card :=
  scalarRelationIndependent_card_le_of_cliqueCover R (by intro γ hγ; exact hγ) hind hcover

variable [Field F] [Fintype F]
variable {n : ℕ} [NeZero n]

/-- Uniform clique-cover certificate for the witness-local scalar relation route. -/
def UniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted
    (dom : Fin n ↪ F) (k a : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop) (S : ℕ) :
    Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        ∃ cover : Finset (Finset F), cover.card ≤ S ∧
          scalarRelationCliqueCover (fun γ γ' => R u₀ u₁ c γ γ')
            (codewordSingletonWitnessScalars dom k a u₀ u₁ c) cover

/-- A uniform clique-cover certificate gives the witness-local relation-independence budget. -/
theorem
    uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationCliqueCover
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hcover : UniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted dom k a R S) :
    UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted dom k a R S := by
  intro u₀ u₁ hnotEligible hsafe c hc Γ hΓ hindΓ
  rcases hcover u₀ u₁ hnotEligible hsafe c hc with ⟨cover, hcard, hcoverΓ⟩
  exact
    (scalarRelationIndependent_card_le_of_cliqueCover
      (fun γ γ' => R u₀ u₁ c γ γ') hΓ hindΓ hcoverΓ).trans hcard

/-- A forbidden-edge theorem plus a clique-cover certificate gives the direct per-codeword
singleton cap. -/
theorem uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationCliqueCover
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hcover : UniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted dom k a R S) :
    UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S :=
  uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationWitnessIndependence
    dom k a S R hforbid
    (uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationCliqueCover
      dom k a S R hcover)

open Classical in
/-- A direct singleton-fiber budget always gives a clique-cover certificate, by covering with
singletons. -/
theorem uniformRelationCliqueCoverBudgeted_of_codewordSingletonBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hbudget : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S) :
    UniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted dom k a R S := by
  intro u₀ u₁ hnotEligible hsafe c hc
  rcases
    scalarRelationCliqueCover_singletons
      (fun γ γ' => R u₀ u₁ c γ γ')
      (codewordSingletonWitnessScalars dom k a u₀ u₁ c) with
    ⟨cover, hcard, hcover⟩
  exact ⟨cover, hcard.trans (hbudget u₀ u₁ hnotEligible hsafe c hc), hcover⟩

/-- With forbidden edges fixed, a clique-cover certificate is extensionally equivalent to the
original singleton-fiber budget.  The clique cover can still be a proof method, but it is not a
weaker theorem statement. -/
theorem relationCliqueCoverBudgeted_iff_codewordSingletonBudgeted_of_forbidden
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R) :
    UniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted dom k a R S ↔
      UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
  constructor
  · intro hcover
    exact uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationCliqueCover
      dom k a S R hforbid hcover
  · intro hbudget
    exact uniformRelationCliqueCoverBudgeted_of_codewordSingletonBudgeted
      dom k a S R hbudget

open Classical in
/-- Negated form of the clique-cover collapse under forbidden edges. -/
theorem not_relationCliqueCoverBudgeted_iff_exists_singleton_card_gt_of_forbidden
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R) :
    (¬ UniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted dom k a R S) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            S < (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card := by
  constructor
  · intro hnot
    have hnotSingleton :
        ¬ UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
      intro hbudget
      exact hnot
        ((relationCliqueCoverBudgeted_iff_codewordSingletonBudgeted_of_forbidden
          dom k a S R hforbid).mpr hbudget)
    exact (not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
      dom k a S).mp hnotSingleton
  · intro hex hcover
    have hsingle :
        UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S :=
      (relationCliqueCoverBudgeted_iff_codewordSingletonBudgeted_of_forbidden
        dom k a S R hforbid).mp hcover
    exact
      ((not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
        dom k a S).mpr hex) hsingle

/-- Production wrapper for the relation clique-cover route. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationCliqueCover
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hcover : UniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted dom k a R S)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationWitnessIndependence
    dom k a L S B R hSupport hFits hZeroSafe hforbid
    (uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationCliqueCover
      dom k a S R hcover)
    hbudget

open Classical in
/-- Exact failure form for the uniform relation clique-cover budget. -/
theorem
    not_uniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted_iff_exists_no_cover
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop) :
    (¬ UniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted dom k a R S) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            ¬ ∃ cover : Finset (Finset F), cover.card ≤ S ∧
              scalarRelationCliqueCover (fun γ γ' => R u₀ u₁ c γ γ')
                (codewordSingletonWitnessScalars dom k a u₀ u₁ c) cover := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe c hc
    by_contra hnoCover
    exact hnone ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hnoCover⟩
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hnoCover⟩ hcover
    exact hnoCover (hcover u₀ u₁ hnotEligible hsafe c hc)

open Classical in
/-- Scanner for the relation clique-cover route.  With the forbidden-edge half fixed, failed
production exposes either the usual arithmetic failure or an appearing codeword whose singleton
scalars admit no at-most-`S` clique cover for the proposed relation. -/
theorem exists_largeZero_safe_codewordRelationCliqueCoverRouteFailure_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        (¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
            + (lineAppearingCodewords dom k a u₀ u₁).card * S ≤ 2 * B ∨
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            ¬ ∃ cover : Finset (Finset F), cover.card ≤ S ∧
              scalarRelationCliqueCover (fun γ γ' => R u₀ u₁ c γ γ')
                (codewordSingletonWitnessScalars dom k a u₀ u₁ c) cover) := by
  by_cases hcover : UniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted dom k a R S
  · have hperCode :
        UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S :=
      uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationCliqueCover
        dom k a S R hforbid hcover
    rcases
      exists_largeZero_safe_codewordSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
        dom k a L S B hSupport hFits hZeroSafe hperCode hnot with
      ⟨u₀, u₁, hnotEligible, hsafe, harith⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inl harith⟩
  · rcases
      (not_uniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted_iff_exists_no_cover
        dom k a S R).mp hcover with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hnoCover⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr ⟨c, hc, hnoCover⟩⟩

open Classical in
/-- Full scanner for the relation clique-cover route.  Without assuming the forbidden-edge half,
failed production exposes an actual forbidden edge, the usual arithmetic failure, or the absence
of an at-most-`S` clique cover for one singleton-witness fiber. -/
theorem exists_largeZero_safe_codewordRelationCliqueCoverRouteObstruction_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ((∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            ∃ γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
              ∃ γ' ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
                γ ≠ γ' ∧ R u₀ u₁ c γ γ') ∨
          (¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
              + (lineAppearingCodewords dom k a u₀ u₁).card * S ≤ 2 * B ∨
            ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
              ¬ ∃ cover : Finset (Finset F), cover.card ≤ S ∧
                scalarRelationCliqueCover (fun γ γ' => R u₀ u₁ c γ γ')
                  (codewordSingletonWitnessScalars dom k a u₀ u₁ c) cover)) := by
  by_cases hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R
  · rcases
      exists_largeZero_safe_codewordRelationCliqueCoverRouteFailure_of_not_budgeted
        dom k a L S B R hSupport hFits hZeroSafe hforbid hnot with
      ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr hfail⟩
  · rcases
      (not_uniformLargeZeroSafeCodewordSingletonRelationForbidden_iff_exists_edge
        dom k a R).mp hforbid with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, γ, hγ, γ', hγ', hne, hR⟩
    exact
      ⟨u₀, u₁, hnotEligible, hsafe, Or.inl
        ⟨c, hc, γ, hγ, γ', hγ', hne, hR⟩⟩

section SourceAudit

#print axioms scalarRelationClique
#print axioms scalarRelationCliqueCover
#print axioms scalarRelationIndependent_inter_clique_card_le_one
#print axioms scalarRelationIndependent_card_le_of_cliqueCover
#print axioms scalarRelationCliqueCover_singletons
#print axioms scalarRelationCliqueCover_card_ge_of_independent
#print axioms UniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted
#print axioms
  uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationCliqueCover
#print axioms uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationCliqueCover
#print axioms uniformRelationCliqueCoverBudgeted_of_codewordSingletonBudgeted
#print axioms relationCliqueCoverBudgeted_iff_codewordSingletonBudgeted_of_forbidden
#print axioms not_relationCliqueCoverBudgeted_iff_exists_singleton_card_gt_of_forbidden
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationCliqueCover
#print axioms
  not_uniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted_iff_exists_no_cover
#print axioms
  exists_largeZero_safe_codewordRelationCliqueCoverRouteFailure_of_not_budgeted
#print axioms
  exists_largeZero_safe_codewordRelationCliqueCoverRouteObstruction_of_not_budgeted

end SourceAudit

end ProximityGap.Ownership
