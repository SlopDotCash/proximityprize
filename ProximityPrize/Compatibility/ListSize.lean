/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/

import ProximityPrize.Extensions.Data.CodingTheory.ListDecodability

/-!
# Finite list-size compatibility

The legacy `ListDecodable.Lambda` casts `Set.ncard`, while canonical `Code.Lambda` uses
`Set.encard`. Their point lists agree, but their sizes agree only when those lists are finite.
These bridges retain that condition explicitly, including for finite codes over infinite
alphabets. No global identification of the two maximized sizes is installed.
-/

namespace ProximityPrize.Compatibility

variable {ι : Type*} [Fintype ι] {A : Type*}

/-- Both APIs use the same relative-distance point list. -/
theorem legacy_pointList_eq_canonical (C : Set (ι → A)) (f : ι → A) (δ : ℝ) :
    ListDecodable.closeCodewordsRel C f δ = Code.closeCodewordsRel C f δ := rfl

/-- Finite point lists make `ncard` and `encard` agree before taking their suprema. -/
theorem legacyLambda_eq_canonical_of_finite_pointLists
    (C : Set (ι → A)) (δ : ℝ)
    (h : ∀ f, (ListDecodable.closeCodewordsRel C f δ).Finite) :
    ListDecodable.Lambda C δ = Code.Lambda C δ := by
  unfold ListDecodable.Lambda Code.Lambda
  apply iSup_congr
  intro f
  exact (h f).cast_ncard_eq

/-- A finite code has finite point lists even when its alphabet is infinite. -/
theorem legacyLambda_eq_canonical_of_finite_code
    (C : Set (ι → A)) (δ : ℝ) (hC : C.Finite) :
    ListDecodable.Lambda C δ = Code.Lambda C δ :=
  legacyLambda_eq_canonical_of_finite_pointLists C δ
    (fun f => hC.subset (ListDecodable.closeCodewordsRel_subset_code δ f))

/-- Over a finite alphabet the two APIs agree for every code and radius. -/
theorem legacyLambda_eq_canonical [Finite A] (C : Set (ι → A)) (δ : ℝ) :
    ListDecodable.Lambda C δ = Code.Lambda C δ :=
  legacyLambda_eq_canonical_of_finite_code C δ (Set.toFinite C)

end ProximityPrize.Compatibility
