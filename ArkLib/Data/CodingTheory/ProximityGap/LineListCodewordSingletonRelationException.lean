/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListCodewordSingletonRelationCliqueCover

/-!
# Exceptional-set relation certificates for singleton scalar graphs

The forbidden-edge singleton graph route collapses extensionally to the original singleton cap:
under forbidden edges, the whole singleton-witness fiber is already independent.  This file
records the next strictly more flexible contract.  A proposed algebraic relation may have edges on
a classified exceptional set `Ξ`; outside `Ξ`, singleton scalars must be independent, and the
exceptional part is budgeted separately.

The resulting per-codeword cap is `S + E`: `S` for the non-exceptional independent part and `E`
for the exceptional residue.  The scanners expose the three honest failure modes: an edge outside
the exception set, an overlarge independent good subset, or too many exceptional singleton
scalars.

The file also records the corresponding partition collapse: under outside-forbidden edges, the
good-part independence budget is equivalent to directly bounding the non-exceptional singleton
scalars.  Thus the relation is useful only if it helps prove a genuinely small exceptional family
or a genuinely small non-exceptional partition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [DecidableEq F]

/-- A scalar set is relation-independent after deleting a proposed exceptional set. -/
def scalarRelationIndependentOutside
    (R : F → F → Prop) (Ω Ξ : Finset F) : Prop :=
  scalarRelationIndependent R (Ω \ Ξ)

/-- Exact failure form for independence outside an exceptional set. -/
theorem not_scalarRelationIndependentOutside_iff_exists_edge
    (R : F → F → Prop) (Ω Ξ : Finset F) :
    (¬ scalarRelationIndependentOutside R Ω Ξ) ↔
      ∃ γ ∈ Ω, γ ∉ Ξ ∧
        ∃ γ' ∈ Ω, γ' ∉ Ξ ∧ γ ≠ γ' ∧ R γ γ' := by
  classical
  constructor
  · intro hnot
    rcases
        (not_scalarRelationIndependent_iff_exists_edge R (Ω \ Ξ)).mp hnot with
      ⟨γ, hγ, γ', hγ', hne, hR⟩
    rw [Finset.mem_sdiff] at hγ hγ'
    exact ⟨γ, hγ.1, hγ.2, γ', hγ'.1, hγ'.2, hne, hR⟩
  · rintro ⟨γ, hγΩ, hγΞ, γ', hγ'Ω, hγ'Ξ, hne, hR⟩ hind
    exact hind γ (Finset.mem_sdiff.mpr ⟨hγΩ, hγΞ⟩)
      γ' (Finset.mem_sdiff.mpr ⟨hγ'Ω, hγ'Ξ⟩) hne hR

/-- If the non-exceptional part is independent and every independent subset of it has size at
most `S`, while the exceptional part has size at most `E`, then the whole set has size at most
`S + E`. -/
theorem scalarRelation_card_le_goodIndependence_add_exception
    (R : F → F → Prop) (Ω Ξ : Finset F) {S E : ℕ}
    (houtside : scalarRelationIndependentOutside R Ω Ξ)
    (hgood : ∀ Γ : Finset F, Γ ⊆ Ω \ Ξ →
      scalarRelationIndependent R Γ → Γ.card ≤ S)
    (hexception : (Ω ∩ Ξ).card ≤ E) :
    Ω.card ≤ S + E := by
  have hgoodCard : (Ω \ Ξ).card ≤ S :=
    hgood (Ω \ Ξ) (fun _ hγ => hγ) houtside
  have hcover : Ω ⊆ (Ω \ Ξ) ∪ (Ω ∩ Ξ) := by
    intro γ hγ
    by_cases hγΞ : γ ∈ Ξ
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_inter.mpr ⟨hγ, hγΞ⟩))
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_sdiff.mpr ⟨hγ, hγΞ⟩))
  have hΩ : Ω.card ≤ (Ω \ Ξ).card + (Ω ∩ Ξ).card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  omega

variable [Field F] [Fintype F]
variable {n : ℕ} [NeZero n]

/-- Uniform forbidden-edge condition outside a proposed exceptional scalar set. -/
def UniformLargeZeroSafeCodewordRelationForbiddenOutside
    (dom : Fin n ↪ F) (k a : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F) :
    Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        scalarRelationIndependentOutside
          (fun γ γ' => R u₀ u₁ c γ γ')
          (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
          (Ξ u₀ u₁ c)

/-- Uniform independence-number bound for independent subsets of the non-exceptional singleton
scalars. -/
def UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted
    (dom : Fin n ↪ F) (k a : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F) (S : ℕ) :
    Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        ∀ Γ : Finset F,
          Γ ⊆ codewordSingletonWitnessScalars dom k a u₀ u₁ c \ Ξ u₀ u₁ c →
            scalarRelationIndependent (fun γ γ' => R u₀ u₁ c γ γ') Γ →
              Γ.card ≤ S

/-- Uniform budget for singleton scalars that land in the exceptional set. -/
def UniformLargeZeroSafeCodewordRelationExceptionBudgeted
    (dom : Fin n ↪ F) (k a : ℕ)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F) (E : ℕ) :
    Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        (codewordSingletonWitnessScalars dom k a u₀ u₁ c ∩ Ξ u₀ u₁ c).card ≤ E

/-- Uniform budget for the non-exceptional singleton scalars. -/
def UniformLargeZeroSafeCodewordGoodOutsideBudgeted
    (dom : Fin n ↪ F) (k a : ℕ)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F) (S : ℕ) :
    Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        (codewordSingletonWitnessScalars dom k a u₀ u₁ c \ Ξ u₀ u₁ c).card ≤ S

/-- The older witness-local independence budget implies the good-part independence budget. -/
theorem
    uniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted_of_relationWitnessIndependence
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F)
    (hind : UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted dom k a R S) :
    UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted dom k a R Ξ S := by
  intro u₀ u₁ hnotEligible hsafe c hc Γ hΓ hindΓ
  exact hind u₀ u₁ hnotEligible hsafe c hc Γ
    (fun γ hγ => (Finset.mem_sdiff.mp (hΓ hγ)).1) hindΓ

/-- A direct non-exceptional singleton budget gives the good-part independence budget for any
relation. -/
theorem
    uniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted_of_goodOutsideBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F)
    (hgood : UniformLargeZeroSafeCodewordGoodOutsideBudgeted dom k a Ξ S) :
    UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted dom k a R Ξ S := by
  intro u₀ u₁ hnotEligible hsafe c hc Γ hΓ _hindΓ
  exact (Finset.card_le_card hΓ).trans
    (hgood u₀ u₁ hnotEligible hsafe c hc)

/-- Under the outside-forbidden hypothesis, the good-part independence budget is just the direct
non-exceptional singleton budget. -/
theorem
    uniformLargeZeroSafeCodewordGoodOutsideBudgeted_of_relationGoodIndependence
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F)
    (houtside : UniformLargeZeroSafeCodewordRelationForbiddenOutside dom k a R Ξ)
    (hgood : UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted
      dom k a R Ξ S) :
    UniformLargeZeroSafeCodewordGoodOutsideBudgeted dom k a Ξ S := by
  intro u₀ u₁ hnotEligible hsafe c hc
  exact hgood u₀ u₁ hnotEligible hsafe c hc
    (codewordSingletonWitnessScalars dom k a u₀ u₁ c \ Ξ u₀ u₁ c)
    (fun _ hγ => hγ)
    (houtside u₀ u₁ hnotEligible hsafe c hc)

/-- Once outside edges are forbidden, the relation-independent good-part budget is extensionally
equivalent to directly bounding the non-exceptional singleton set. -/
theorem
    relationGoodIndependenceBudgeted_iff_goodOutsideBudgeted_of_forbiddenOutside
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F)
    (houtside : UniformLargeZeroSafeCodewordRelationForbiddenOutside dom k a R Ξ) :
    UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted dom k a R Ξ S ↔
      UniformLargeZeroSafeCodewordGoodOutsideBudgeted dom k a Ξ S := by
  constructor
  · exact
      uniformLargeZeroSafeCodewordGoodOutsideBudgeted_of_relationGoodIndependence
        dom k a S R Ξ houtside
  · exact
      uniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted_of_goodOutsideBudgeted
        dom k a S R Ξ

/-- Direct partition form of the exceptional route: bounding the non-exceptional and exceptional
singleton parts bounds the whole singleton fiber by `S + E`. -/
theorem uniformLargeZeroSafeCodewordSingletonBudgeted_of_goodOutside_and_exception
    (dom : Fin n ↪ F) (k a S E : ℕ)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F)
    (hgood : UniformLargeZeroSafeCodewordGoodOutsideBudgeted dom k a Ξ S)
    (hexception : UniformLargeZeroSafeCodewordRelationExceptionBudgeted dom k a Ξ E) :
    UniformLargeZeroSafeCodewordSingletonBudgeted dom k a (S + E) := by
  intro u₀ u₁ hnotEligible hsafe c hc
  let Ω := codewordSingletonWitnessScalars dom k a u₀ u₁ c
  let Ξc := Ξ u₀ u₁ c
  have hgoodCard : (Ω \ Ξc).card ≤ S :=
    hgood u₀ u₁ hnotEligible hsafe c hc
  have hexceptionCard : (Ω ∩ Ξc).card ≤ E :=
    hexception u₀ u₁ hnotEligible hsafe c hc
  have hcover : Ω ⊆ (Ω \ Ξc) ∪ (Ω ∩ Ξc) := by
    intro γ hγ
    by_cases hγΞ : γ ∈ Ξc
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_inter.mpr ⟨hγ, hγΞ⟩))
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_sdiff.mpr ⟨hγ, hγΞ⟩))
  have hΩ : Ω.card ≤ (Ω \ Ξc).card + (Ω ∩ Ξc).card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  exact hΩ.trans (Nat.add_le_add hgoodCard hexceptionCard)

/-- Outside-forbidden relation edges, a good-part independence theorem, and an exception budget
give a direct per-codeword singleton cap with budget `S + E`. -/
theorem uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationGoodIndependenceOutside
    (dom : Fin n ↪ F) (k a S E : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F)
    (houtside : UniformLargeZeroSafeCodewordRelationForbiddenOutside dom k a R Ξ)
    (hgood : UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted dom k a R Ξ S)
    (hexception : UniformLargeZeroSafeCodewordRelationExceptionBudgeted dom k a Ξ E) :
    UniformLargeZeroSafeCodewordSingletonBudgeted dom k a (S + E) := by
  intro u₀ u₁ hnotEligible hsafe c hc
  exact
    scalarRelation_card_le_goodIndependence_add_exception
      (fun γ γ' => R u₀ u₁ c γ γ')
      (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
      (Ξ u₀ u₁ c)
      (houtside u₀ u₁ hnotEligible hsafe c hc)
      (hgood u₀ u₁ hnotEligible hsafe c hc)
      (hexception u₀ u₁ hnotEligible hsafe c hc)

open Classical in
/-- Exact failure form for the outside-forbidden half. -/
theorem not_uniformLargeZeroSafeCodewordRelationForbiddenOutside_iff_exists_edge
    (dom : Fin n ↪ F) (k a : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F) :
    (¬ UniformLargeZeroSafeCodewordRelationForbiddenOutside dom k a R Ξ) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            ∃ γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
              γ ∉ Ξ u₀ u₁ c ∧
                ∃ γ' ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
                  γ' ∉ Ξ u₀ u₁ c ∧ γ ≠ γ' ∧ R u₀ u₁ c γ γ' := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe c hc
    by_contra hbad
    rcases
        (not_scalarRelationIndependentOutside_iff_exists_edge
          (fun γ γ' => R u₀ u₁ c γ γ')
          (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
          (Ξ u₀ u₁ c)).mp hbad with
      ⟨γ, hγ, hγΞ, γ', hγ', hγ'Ξ, hne, hR⟩
    exact hnone
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, γ, hγ, hγΞ, γ', hγ', hγ'Ξ, hne, hR⟩
  · rintro
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, γ, hγ, hγΞ,
        γ', hγ', hγ'Ξ, hne, hR⟩ houtside
    exact
      (not_scalarRelationIndependentOutside_iff_exists_edge
        (fun γ γ' => R u₀ u₁ c γ γ')
        (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
        (Ξ u₀ u₁ c)).mpr
        ⟨γ, hγ, hγΞ, γ', hγ', hγ'Ξ, hne, hR⟩
        (houtside u₀ u₁ hnotEligible hsafe c hc)

open Classical in
/-- Exact failure form for the good-part independence budget. -/
theorem
    exists_largeZero_safe_codewordRelationGoodIndependent_gt_of_not_goodIndependence
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F)
    (hnot : ¬
      UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted dom k a R Ξ S) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁, ∃ Γ : Finset F,
          Γ ⊆ codewordSingletonWitnessScalars dom k a u₀ u₁ c \ Ξ u₀ u₁ c ∧
            scalarRelationIndependent (fun γ γ' => R u₀ u₁ c γ γ') Γ ∧
              S < Γ.card := by
  by_contra hnone
  apply hnot
  intro u₀ u₁ hnotEligible hsafe c hc Γ hΓ hindΓ
  exact le_of_not_gt
    (fun hgt => hnone
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, Γ, hΓ, hindΓ, hgt⟩)

open Classical in
/-- Exact failure form for the exceptional-scalar budget. -/
theorem not_uniformLargeZeroSafeCodewordRelationExceptionBudgeted_iff_exists_card_gt
    (dom : Fin n ↪ F) (k a E : ℕ)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F) :
    (¬ UniformLargeZeroSafeCodewordRelationExceptionBudgeted dom k a Ξ E) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            E < (codewordSingletonWitnessScalars dom k a u₀ u₁ c ∩ Ξ u₀ u₁ c).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe c hc
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe c hc)) hgt

open Classical in
/-- Exact failure form for the non-exceptional singleton budget. -/
theorem not_uniformLargeZeroSafeCodewordGoodOutsideBudgeted_iff_exists_card_gt
    (dom : Fin n ↪ F) (k a S : ℕ)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F) :
    (¬ UniformLargeZeroSafeCodewordGoodOutsideBudgeted dom k a Ξ S) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            S < (codewordSingletonWitnessScalars dom k a u₀ u₁ c \ Ξ u₀ u₁ c).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe c hc
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe c hc)) hgt

open Classical in
/-- If the `S + E` singleton cap fails, then any fixed exceptional set fails either the
non-exceptional budget or the exceptional budget on one concrete appearing codeword. -/
theorem
    exists_largeZero_safe_codewordPartitionBudgetFailure_of_not_codewordSingletonBudgeted
    (dom : Fin n ↪ F) (k a S E : ℕ)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F)
    (hnot : ¬ UniformLargeZeroSafeCodewordSingletonBudgeted dom k a (S + E)) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
          S < (codewordSingletonWitnessScalars dom k a u₀ u₁ c \ Ξ u₀ u₁ c).card ∨
            E < (codewordSingletonWitnessScalars dom k a u₀ u₁ c ∩ Ξ u₀ u₁ c).card := by
  by_cases hgood : UniformLargeZeroSafeCodewordGoodOutsideBudgeted dom k a Ξ S
  · have hnotException :
        ¬ UniformLargeZeroSafeCodewordRelationExceptionBudgeted dom k a Ξ E := by
      intro hexception
      exact hnot
        (uniformLargeZeroSafeCodewordSingletonBudgeted_of_goodOutside_and_exception
          dom k a S E Ξ hgood hexception)
    rcases
        (not_uniformLargeZeroSafeCodewordRelationExceptionBudgeted_iff_exists_card_gt
          dom k a E Ξ).mp hnotException with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, c, hc, Or.inr hgt⟩
  · rcases
      (not_uniformLargeZeroSafeCodewordGoodOutsideBudgeted_iff_exists_card_gt
        dom k a S Ξ).mp hgood with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, c, hc, Or.inl hgt⟩

open Classical in
/-- If the relative relation hypotheses hold but the resulting `S + E` singleton cap fails, then
the exceptional set is over budget for a concrete appearing codeword. -/
theorem exists_largeZero_safe_codewordRelationException_gt_of_not_codewordSingletonBudgeted
    (dom : Fin n ↪ F) (k a S E : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F)
    (houtside : UniformLargeZeroSafeCodewordRelationForbiddenOutside dom k a R Ξ)
    (hgood : UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted dom k a R Ξ S)
    (hnot : ¬ UniformLargeZeroSafeCodewordSingletonBudgeted dom k a (S + E)) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
          E < (codewordSingletonWitnessScalars dom k a u₀ u₁ c ∩ Ξ u₀ u₁ c).card := by
  have hnotException :
      ¬ UniformLargeZeroSafeCodewordRelationExceptionBudgeted dom k a Ξ E := by
    intro hexception
    exact hnot
      (uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationGoodIndependenceOutside
        dom k a S E R Ξ houtside hgood hexception)
  exact
    (not_uniformLargeZeroSafeCodewordRelationExceptionBudgeted_iff_exists_card_gt
      dom k a E Ξ).mp hnotException

/-- Production wrapper for the exceptional-set relation route. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationException
    (dom : Fin n ↪ F) (k a L S E B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (houtside : UniformLargeZeroSafeCodewordRelationForbiddenOutside dom k a R Ξ)
    (hgood : UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted dom k a R Ξ S)
    (hexception : UniformLargeZeroSafeCodewordRelationExceptionBudgeted dom k a Ξ E)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B (S + E)) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSingletonBudget
    dom k a L (S + E) B hSupport hFits hZeroSafe
    (uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationGoodIndependenceOutside
      dom k a S E R Ξ houtside hgood hexception)
    hbudget

open Classical in
/-- Scanner for the relative exceptional-set route when the outside-edge and good-independence
halves are fixed.  Failed production exposes either the usual arithmetic failure at budget
`S + E`, or too many exceptional singleton scalars for one appearing codeword. -/
theorem exists_largeZero_safe_codewordRelationExceptionRouteFailure_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S E B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (houtside : UniformLargeZeroSafeCodewordRelationForbiddenOutside dom k a R Ξ)
    (hgood : UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted dom k a R Ξ S)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        (¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
            + (lineAppearingCodewords dom k a u₀ u₁).card * (S + E) ≤ 2 * B ∨
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            E < (codewordSingletonWitnessScalars dom k a u₀ u₁ c ∩ Ξ u₀ u₁ c).card) := by
  by_cases hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a (S + E)
  · rcases
      exists_largeZero_safe_codewordSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
        dom k a L (S + E) B hSupport hFits hZeroSafe hperCode hnot with
      ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inl hfail⟩
  · rcases
      exists_largeZero_safe_codewordRelationException_gt_of_not_codewordSingletonBudgeted
        dom k a S E R Ξ houtside hgood hperCode with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr ⟨c, hc, hgt⟩⟩

open Classical in
/-- Relation-free scanner for the exceptional-set partition route.  Failed production exposes
either the usual arithmetic failure at budget `S + E`, or a concrete appearing codeword where the
non-exceptional/exceptional partition overruns one of its two budgets. -/
theorem exists_largeZero_safe_codewordPartitionRouteFailure_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S E B : ℕ)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        (¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
            + (lineAppearingCodewords dom k a u₀ u₁).card * (S + E) ≤ 2 * B ∨
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            S < (codewordSingletonWitnessScalars dom k a u₀ u₁ c \ Ξ u₀ u₁ c).card ∨
              E < (codewordSingletonWitnessScalars dom k a u₀ u₁ c ∩ Ξ u₀ u₁ c).card) := by
  by_cases hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a (S + E)
  · rcases
      exists_largeZero_safe_codewordSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
        dom k a L (S + E) B hSupport hFits hZeroSafe hperCode hnot with
      ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inl hfail⟩
  · rcases
      exists_largeZero_safe_codewordPartitionBudgetFailure_of_not_codewordSingletonBudgeted
        dom k a S E Ξ hperCode with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hfail⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr ⟨c, hc, hfail⟩⟩

open Classical in
/-- Full scanner for the relative exceptional-set route.  Without assuming either relation half,
failed production exposes one of four finite obstructions: an edge outside the exception set, an
overlarge independent good subset, the usual arithmetic failure, or too many exceptional
singleton scalars. -/
theorem exists_largeZero_safe_codewordRelationExceptionRouteObstruction_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S E B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (Ξ : (Fin n → F) → (Fin n → F) → (Fin n → F) → Finset F)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ((∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            ∃ γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
              γ ∉ Ξ u₀ u₁ c ∧
                ∃ γ' ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
                  γ' ∉ Ξ u₀ u₁ c ∧ γ ≠ γ' ∧ R u₀ u₁ c γ γ') ∨
          ((∃ c ∈ lineAppearingCodewords dom k a u₀ u₁, ∃ Γ : Finset F,
              Γ ⊆ codewordSingletonWitnessScalars dom k a u₀ u₁ c \ Ξ u₀ u₁ c ∧
                scalarRelationIndependent (fun γ γ' => R u₀ u₁ c γ γ') Γ ∧
                  S < Γ.card) ∨
            (¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
                + (lineAppearingCodewords dom k a u₀ u₁).card * (S + E) ≤ 2 * B ∨
              ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
                E < (codewordSingletonWitnessScalars dom k a u₀ u₁ c ∩
                  Ξ u₀ u₁ c).card))) := by
  by_cases houtside : UniformLargeZeroSafeCodewordRelationForbiddenOutside dom k a R Ξ
  · by_cases hgood :
        UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted dom k a R Ξ S
    · rcases
        exists_largeZero_safe_codewordRelationExceptionRouteFailure_of_not_budgeted
          dom k a L S E B R Ξ hSupport hFits hZeroSafe houtside hgood hnot with
        ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
      exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr (Or.inr hfail)⟩
    · rcases
        exists_largeZero_safe_codewordRelationGoodIndependent_gt_of_not_goodIndependence
          dom k a S R Ξ hgood with
        ⟨u₀, u₁, hnotEligible, hsafe, c, hc, Γ, hΓ, hindΓ, hgt⟩
      exact
        ⟨u₀, u₁, hnotEligible, hsafe, Or.inr
          (Or.inl ⟨c, hc, Γ, hΓ, hindΓ, hgt⟩)⟩
  · rcases
      (not_uniformLargeZeroSafeCodewordRelationForbiddenOutside_iff_exists_edge
        dom k a R Ξ).mp houtside with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, γ, hγ, hγΞ,
        γ', hγ', hγ'Ξ, hne, hR⟩
    exact
      ⟨u₀, u₁, hnotEligible, hsafe, Or.inl
        ⟨c, hc, γ, hγ, hγΞ, γ', hγ', hγ'Ξ, hne, hR⟩⟩

section SourceAudit

#print axioms scalarRelationIndependentOutside
#print axioms not_scalarRelationIndependentOutside_iff_exists_edge
#print axioms scalarRelation_card_le_goodIndependence_add_exception
#print axioms UniformLargeZeroSafeCodewordRelationForbiddenOutside
#print axioms UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted
#print axioms UniformLargeZeroSafeCodewordRelationExceptionBudgeted
#print axioms UniformLargeZeroSafeCodewordGoodOutsideBudgeted
#print axioms
  uniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted_of_relationWitnessIndependence
#print axioms
  uniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted_of_goodOutsideBudgeted
#print axioms
  uniformLargeZeroSafeCodewordGoodOutsideBudgeted_of_relationGoodIndependence
#print axioms
  relationGoodIndependenceBudgeted_iff_goodOutsideBudgeted_of_forbiddenOutside
#print axioms uniformLargeZeroSafeCodewordSingletonBudgeted_of_goodOutside_and_exception
#print axioms uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationGoodIndependenceOutside
#print axioms not_uniformLargeZeroSafeCodewordRelationForbiddenOutside_iff_exists_edge
#print axioms
  exists_largeZero_safe_codewordRelationGoodIndependent_gt_of_not_goodIndependence
#print axioms not_uniformLargeZeroSafeCodewordRelationExceptionBudgeted_iff_exists_card_gt
#print axioms not_uniformLargeZeroSafeCodewordGoodOutsideBudgeted_iff_exists_card_gt
#print axioms
  exists_largeZero_safe_codewordPartitionBudgetFailure_of_not_codewordSingletonBudgeted
#print axioms
  exists_largeZero_safe_codewordRelationException_gt_of_not_codewordSingletonBudgeted
#print axioms uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationException
#print axioms
  exists_largeZero_safe_codewordRelationExceptionRouteFailure_of_not_budgeted
#print axioms
  exists_largeZero_safe_codewordPartitionRouteFailure_of_not_budgeted
#print axioms
  exists_largeZero_safe_codewordRelationExceptionRouteObstruction_of_not_budgeted

end SourceAudit

end ProximityGap.Ownership
