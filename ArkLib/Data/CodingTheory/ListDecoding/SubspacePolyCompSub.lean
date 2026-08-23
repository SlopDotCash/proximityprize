/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyAdditive

/-!
# Subtractive translation of the subspace polynomial

The `X - C w` form of the polynomial additivity `subspacePoly_comp_X_add_C_eq`:
`(subspacePoly L).comp (X - C w) = subspacePoly L - C ((subspacePoly L).eval w)` for a finite
additive subgroup `L`.  This is exactly the per-coset factor in the subspace-polynomial recursion
(`s_{V'}(X - c·u) = s_{V'}(X) - s_{V'}(c·u)`).
-/

open Polynomial BigOperators

namespace BKR06

variable {K : Type*} [Field K]

/-- `(subspacePoly L).comp (X - C w) = subspacePoly L - C ((subspacePoly L).eval w)`. -/
theorem subspacePoly_comp_X_sub_C_eq
    (L : Finset K) (h0 : (0 : K) ∈ L)
    (hsub : ∀ x ∈ L, ∀ y ∈ L, x - y ∈ L)
    (hadd : ∀ x ∈ L, ∀ y ∈ L, x + y ∈ L) (w : K) :
    (subspacePoly L).comp (X - C w) = subspacePoly L - C ((subspacePoly L).eval w) := by
  have hneg : (subspacePoly L).eval (-w) = -(subspacePoly L).eval w := by
    have hadd_ev := subspacePoly_eval_add L h0 hsub hadd w (-w)
    rw [add_neg_cancel, subspacePoly_eval_zero L h0] at hadd_ev
    exact eq_neg_of_add_eq_zero_right hadd_ev.symm
  have hkey := subspacePoly_comp_X_add_C_eq L h0 hsub hadd (-w)
  rw [map_neg, ← sub_eq_add_neg, hneg, map_neg, ← sub_eq_add_neg] at hkey
  exact hkey

end BKR06

-- Axiom audit.
#print axioms BKR06.subspacePoly_comp_X_sub_C_eq
