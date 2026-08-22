/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
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
set_option linter.unnecessarySimpa false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F C : Type} [DecidableEq F] [DecidableEq C]

/-- A bounded-color certificate: equal colors inside `Ω` force relation edges. -/
def scalarRelationColorForcesEdges
    (R : F → F → Prop) (Ω : Finset F) (χ : F → C) : Prop :=
  ∀ γ ∈ Ω, ∀ γ' ∈ Ω, γ ≠ γ' → χ γ = χ γ' → R γ γ'

/-- Concrete failure of a bounded-color certificate: either too many colors appear, or two
same-colored vertices fail to be related. -/
def scalarRelationColorFailure
    (R : F → F → Prop) (Ω : Finset F) (χ : F → C) (S : ℕ) : Prop :=
  S < (Ω.image χ).card ∨
    ∃ γ ∈ Ω, ∃ γ' ∈ Ω, γ ≠ γ' ∧ χ γ = χ γ' ∧ ¬ R γ γ'

omit [DecidableEq F] [DecidableEq C] in
/-- Exact failure form for the equal-color edge condition. -/
theorem not_scalarRelationColorForcesEdges_iff_exists_pair
    (R : F → F → Prop) (Ω : Finset F) (χ : F → C) :
    (¬ scalarRelationColorForcesEdges R Ω χ) ↔
      ∃ γ ∈ Ω, ∃ γ' ∈ Ω, γ ≠ γ' ∧ χ γ = χ γ' ∧ ¬ R γ γ' := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro γ hγ γ' hγ' hne hsame
    by_contra hnotR
    exact hnone ⟨γ, hγ, γ', hγ', hne, hsame, hnotR⟩
  · rintro ⟨γ, hγ, γ', hγ', hne, hsame, hnotR⟩ hforces
    exact hnotR (hforces γ hγ γ' hγ' hne hsame)

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

omit [DecidableEq F] [DecidableEq C] in
/-- If a scalar set is independent and equal colors force relation edges, then the color is
injective on that scalar set. -/
theorem scalarRelationColor_injOn_of_independent_of_forcesEdges
    (R : F → F → Prop) (Ω : Finset F) (χ : F → C)
    (hind : scalarRelationIndependent R Ω)
    (hforces : scalarRelationColorForcesEdges R Ω χ) :
    Set.InjOn χ ↑Ω := by
  classical
  intro γ hγ γ' hγ' hsame
  by_contra hne
  exact (hind γ hγ γ' hγ' hne) (hforces γ hγ γ' hγ' hne hsame)

omit [DecidableEq F] in
/-- Under independence plus a color-forces-edges theorem, the color-image has exactly the
same cardinality as the original scalar set. -/
theorem scalarRelationColor_image_card_eq_of_independent_of_forcesEdges
    (R : F → F → Prop) (Ω : Finset F) (χ : F → C)
    (hind : scalarRelationIndependent R Ω)
    (hforces : scalarRelationColorForcesEdges R Ω χ) :
    (Ω.image χ).card = Ω.card := by
  exact Finset.card_image_of_injOn
    (scalarRelationColor_injOn_of_independent_of_forcesEdges R Ω χ hind hforces)

variable [Field F] [Fintype F]
variable {n : ℕ} [NeZero n]

/-- Uniform edge-forcing half of the bounded-color route, separated from the image-size cap. -/
def UniformLargeZeroSafeCodewordRelationColorForcesEdges
    (dom : Fin n ↪ F) (k a : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C) :
    Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        scalarRelationColorForcesEdges
          (fun γ γ' => R u₀ u₁ c γ γ')
          (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
          (χ u₀ u₁ c)

/-- Uniform image-size half of the bounded-color route. -/
def UniformLargeZeroSafeCodewordRelationColorImageBudgeted
    (dom : Fin n ↪ F) (k a : ℕ)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C) (S : ℕ) :
    Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        ((codewordSingletonWitnessScalars dom k a u₀ u₁ c).image
            (χ u₀ u₁ c)).card ≤ S

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

theorem relationColorForcesEdges_of_relationColorBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (hχ : UniformLargeZeroSafeCodewordRelationColorBudgeted dom k a R χ S) :
    UniformLargeZeroSafeCodewordRelationColorForcesEdges dom k a R χ := by
  intro u₀ u₁ hnotEligible hsafe c hc
  exact (hχ u₀ u₁ hnotEligible hsafe c hc).2

theorem relationColorImageBudgeted_of_relationColorBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (hχ : UniformLargeZeroSafeCodewordRelationColorBudgeted dom k a R χ S) :
    UniformLargeZeroSafeCodewordRelationColorImageBudgeted dom k a χ S := by
  intro u₀ u₁ hnotEligible hsafe c hc
  exact (hχ u₀ u₁ hnotEligible hsafe c hc).1

theorem relationColorBudgeted_of_imageBudgeted_and_forcesEdges
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (himage : UniformLargeZeroSafeCodewordRelationColorImageBudgeted dom k a χ S)
    (hforces : UniformLargeZeroSafeCodewordRelationColorForcesEdges dom k a R χ) :
    UniformLargeZeroSafeCodewordRelationColorBudgeted dom k a R χ S := by
  intro u₀ u₁ hnotEligible hsafe c hc
  exact ⟨himage u₀ u₁ hnotEligible hsafe c hc,
    hforces u₀ u₁ hnotEligible hsafe c hc⟩

open Classical in
/-- On a forbidden singleton relation, an edge-forcing color is injective on every actual
singleton-witness fiber. -/
theorem codewordSingletonColor_image_card_eq_of_forbidden_of_forcesEdges
    (dom : Fin n ↪ F) (k a : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hforces : UniformLargeZeroSafeCodewordRelationColorForcesEdges dom k a R χ)
    (u₀ u₁ c : Fin n → F)
    (hnotEligible : ¬ SupportEligibleLineDirection a u₁)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hc : c ∈ lineAppearingCodewords dom k a u₀ u₁) :
    ((codewordSingletonWitnessScalars dom k a u₀ u₁ c).image
        (χ u₀ u₁ c)).card =
      (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card :=
  scalarRelationColor_image_card_eq_of_independent_of_forcesEdges
    (fun γ γ' => R u₀ u₁ c γ γ')
    (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
    (χ u₀ u₁ c)
    (hforbid u₀ u₁ hnotEligible hsafe c hc)
    (hforces u₀ u₁ hnotEligible hsafe c hc)

open Classical in
/-- Once the forbidden-edge half and the edge-forcing half are both fixed, bounding the color
image is exactly the original singleton-fiber cap. -/
theorem relationColorImageBudgeted_iff_codewordSingletonBudgeted_of_forbidden_of_forcesEdges
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hforces : UniformLargeZeroSafeCodewordRelationColorForcesEdges dom k a R χ) :
    UniformLargeZeroSafeCodewordRelationColorImageBudgeted dom k a χ S ↔
      UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
  constructor
  · intro himage u₀ u₁ hnotEligible hsafe c hc
    have hcard :=
      codewordSingletonColor_image_card_eq_of_forbidden_of_forcesEdges
        dom k a R χ hforbid hforces u₀ u₁ c hnotEligible hsafe hc
    simpa [hcard] using himage u₀ u₁ hnotEligible hsafe c hc
  · intro hsingle u₀ u₁ hnotEligible hsafe c hc
    have hcard :=
      codewordSingletonColor_image_card_eq_of_forbidden_of_forcesEdges
        dom k a R χ hforbid hforces u₀ u₁ c hnotEligible hsafe hc
    simpa [hcard] using hsingle u₀ u₁ hnotEligible hsafe c hc

open Classical in
/-- With a uniform edge-forcing theorem fixed, the full bounded-color certificate is
extensionally equivalent to the original singleton cap under forbidden edges. -/
theorem relationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden_of_forcesEdges
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hforces : UniformLargeZeroSafeCodewordRelationColorForcesEdges dom k a R χ) :
    UniformLargeZeroSafeCodewordRelationColorBudgeted dom k a R χ S ↔
      UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
  constructor
  · intro hχ
    exact
      (relationColorImageBudgeted_iff_codewordSingletonBudgeted_of_forbidden_of_forcesEdges
        dom k a S R χ hforbid hforces).mp
        (relationColorImageBudgeted_of_relationColorBudgeted dom k a S R χ hχ)
  · intro hsingle
    exact relationColorBudgeted_of_imageBudgeted_and_forcesEdges dom k a S R χ
      ((relationColorImageBudgeted_iff_codewordSingletonBudgeted_of_forbidden_of_forcesEdges
        dom k a S R χ hforbid hforces).mpr hsingle)
      hforces

open Classical in
/-- Negated form of the color collapse: under fixed forbidden-edge and edge-forcing halves,
failing the bounded-color budget is exactly failing the original singleton-fiber cap. -/
theorem not_relationColorBudgeted_iff_exists_singleton_card_gt_of_forbidden_of_forcesEdges
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
    (hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R)
    (hforces : UniformLargeZeroSafeCodewordRelationColorForcesEdges dom k a R χ) :
    (¬ UniformLargeZeroSafeCodewordRelationColorBudgeted dom k a R χ S) ↔
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
        ((relationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden_of_forcesEdges
          dom k a S R χ hforbid hforces).mpr hsingle)
    exact (not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
      dom k a S).mp hnotSingleton
  · intro hex hχ
    have hsingle :
        UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S :=
      (relationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden_of_forcesEdges
        dom k a S R χ hforbid hforces).mp hχ
    exact
      ((not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
        dom k a S).mpr hex) hsingle

open Classical in
/-- Exact failure form for the uniform bounded-color certificate. -/
theorem not_uniformLargeZeroSafeCodewordRelationColorBudgeted_iff_exists_colorFailure
    (dom : Fin n ↪ F) (k a S : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C) :
    (¬ UniformLargeZeroSafeCodewordRelationColorBudgeted dom k a R χ S) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            scalarRelationColorFailure
              (fun γ γ' => R u₀ u₁ c γ γ')
              (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
              (χ u₀ u₁ c) S := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe c hc
    constructor
    · by_contra hcard
      exact hnone
        ⟨u₀, u₁, hnotEligible, hsafe, c, hc,
          Or.inl (Nat.lt_of_not_ge hcard)⟩
    · by_contra hforces
      rcases
        (not_scalarRelationColorForcesEdges_iff_exists_pair
          (fun γ γ' => R u₀ u₁ c γ γ')
          (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
          (χ u₀ u₁ c)).mp hforces with
        ⟨γ, hγ, γ', hγ', hne, hsame, hnotR⟩
      exact hnone
        ⟨u₀, u₁, hnotEligible, hsafe, c, hc,
          Or.inr ⟨γ, hγ, γ', hγ', hne, hsame, hnotR⟩⟩
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hfail⟩ hχ
    rcases hχ u₀ u₁ hnotEligible hsafe c hc with ⟨hcard, hforces⟩
    rcases hfail with htooMany | hpair
    · exact not_lt_of_ge hcard htooMany
    · rcases hpair with ⟨γ, hγ, γ', hγ', hne, hsame, hnotR⟩
      exact hnotR (hforces γ hγ γ' hγ' hne hsame)

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

open Classical in
/-- Scanner for the bounded-color relation route.  Once support-side hypotheses and the
forbidden-edge half are fixed, failed production exposes either the usual arithmetic failure or
a concrete appearing codeword where the color certificate fails. -/
theorem exists_largeZero_safe_codewordRelationColorRouteFailure_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
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
            scalarRelationColorFailure
              (fun γ γ' => R u₀ u₁ c γ γ')
              (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
              (χ u₀ u₁ c) S) := by
  by_cases hχ : UniformLargeZeroSafeCodewordRelationColorBudgeted dom k a R χ S
  · have hperCode :
        UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S :=
      uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationColorBudgeted
        dom k a S R χ hforbid hχ
    rcases
      exists_largeZero_safe_codewordSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
        dom k a L S B hSupport hFits hZeroSafe hperCode hnot with
      ⟨u₀, u₁, hnotEligible, hsafe, harith⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inl harith⟩
  · rcases
      (not_uniformLargeZeroSafeCodewordRelationColorBudgeted_iff_exists_colorFailure
        dom k a S R χ).mp hχ with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hfail⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr ⟨c, hc, hfail⟩⟩

open Classical in
/-- Full scanner for the bounded-color relation route.  Without assuming the forbidden-edge
half, failed production exposes a forbidden relation edge, the usual arithmetic failure, or a
concrete color-certificate failure. -/
theorem exists_largeZero_safe_codewordRelationColorRouteObstruction_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (R : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → F → Prop)
    (χ : (Fin n → F) → (Fin n → F) → (Fin n → F) → F → C)
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
              scalarRelationColorFailure
                (fun γ γ' => R u₀ u₁ c γ γ')
                (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
                (χ u₀ u₁ c) S)) := by
  by_cases hforbid : UniformLargeZeroSafeCodewordSingletonRelationForbidden dom k a R
  · rcases
      exists_largeZero_safe_codewordRelationColorRouteFailure_of_not_budgeted
        dom k a L S B R χ hSupport hFits hZeroSafe hforbid hnot with
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

#print axioms scalarRelationColorForcesEdges
#print axioms scalarRelationColorFailure
#print axioms not_scalarRelationColorForcesEdges_iff_exists_pair
#print axioms scalarRelationCliqueCover_of_colorForcesEdges
#print axioms scalarRelationColor_injOn_of_independent_of_forcesEdges
#print axioms scalarRelationColor_image_card_eq_of_independent_of_forcesEdges
#print axioms UniformLargeZeroSafeCodewordRelationColorForcesEdges
#print axioms UniformLargeZeroSafeCodewordRelationColorImageBudgeted
#print axioms UniformLargeZeroSafeCodewordRelationColorBudgeted
#print axioms relationColorForcesEdges_of_relationColorBudgeted
#print axioms relationColorImageBudgeted_of_relationColorBudgeted
#print axioms relationColorBudgeted_of_imageBudgeted_and_forcesEdges
#print axioms codewordSingletonColor_image_card_eq_of_forbidden_of_forcesEdges
#print axioms
  relationColorImageBudgeted_iff_codewordSingletonBudgeted_of_forbidden_of_forcesEdges
#print axioms relationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden_of_forcesEdges
#print axioms
  not_relationColorBudgeted_iff_exists_singleton_card_gt_of_forbidden_of_forcesEdges
#print axioms
  not_uniformLargeZeroSafeCodewordRelationColorBudgeted_iff_exists_colorFailure
#print axioms
  uniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted_of_relationColorBudgeted
#print axioms
  uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationColorBudgeted
#print axioms uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationColorBudgeted
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationColorBudgeted
#print axioms exists_largeZero_safe_codewordRelationColorRouteFailure_of_not_budgeted
#print axioms exists_largeZero_safe_codewordRelationColorRouteObstruction_of_not_budgeted

end SourceAudit

end ProximityGap.Ownership
