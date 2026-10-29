/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/

import ProximityPrize.Compatibility.ListSize

/-!
# List-size compatibility boundaries

A finite code can use the bridge over an infinite alphabet. An infinite point list cannot:
at radius one the full natural-number code has legacy list size zero and canonical size top.
-/

namespace ArkLibTest.Compatibility.ListSize

open ProximityPrize.Compatibility

/-- Finiteness of the code is sufficient; the alphabet need not be finite. -/
theorem singleton_code_bridge (δ : ℝ) :
    ListDecodable.Lambda ({fun _ : Unit => (0 : ℕ)} : Set (Unit → ℕ)) δ =
      Code.Lambda ({fun _ : Unit => (0 : ℕ)} : Set (Unit → ℕ)) δ :=
  legacyLambda_eq_canonical_of_finite_code _ δ (Set.finite_singleton _)

private theorem full_pointList_at_one (f : Unit → ℕ) :
    ListDecodable.closeCodewordsRel Set.univ f 1 = Set.univ := by
  rw [legacy_pointList_eq_canonical]
  ext c
  simp only [Code.mem_closeCodewordsRel_iff, Set.mem_univ, true_and, iff_true]
  exact_mod_cast (Code.relHammingDist_le_one (u := f) (v := c))

/-- An infinite point list contributes zero to the historical `ncard` supremum. -/
theorem legacy_infinite_list_size_zero :
    ListDecodable.Lambda (Set.univ : Set (Unit → ℕ)) 1 = 0 := by
  simp only [ListDecodable.Lambda, full_pointList_at_one,
    (Set.infinite_univ : (Set.univ : Set (Unit → ℕ)).Infinite).ncard,
    Nat.cast_zero, iSup_const]

/-- Canonical `encard` instead records that the same point list is infinite. -/
theorem canonical_infinite_list_size_top :
    Code.Lambda (Set.univ : Set (Unit → ℕ)) 1 = ⊤ := by
  simp only [Code.Lambda, ← legacy_pointList_eq_canonical, full_pointList_at_one,
    (Set.infinite_univ : (Set.univ : Set (Unit → ℕ)).Infinite).encard_eq, iSup_const]

#print axioms singleton_code_bridge
#print axioms legacy_infinite_list_size_zero
#print axioms canonical_infinite_list_size_top

end ArkLibTest.Compatibility.ListSize
