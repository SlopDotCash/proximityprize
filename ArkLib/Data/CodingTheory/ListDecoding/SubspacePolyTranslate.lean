/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly

/-!
# Translation of the subspace polynomial

`subspacePoly (L + w) = (subspacePoly L).comp (X - C w)`: translating the root finset `L` by `w`
shifts the subspace polynomial by `X ↦ X - w`.  A char-free identity, the geometric ingredient of
the subspace-polynomial recursion (`s_{V'+c·u}(X) = s_{V'}(X - c·u)`, grouping the roots of
`V = V' ⊕ 𝔽_q·u` into the cosets `V' + c·u`).
-/

open Polynomial BigOperators

namespace BKR06

variable {K : Type*} [Field K] [DecidableEq K]

/-- **Translation of the subspace polynomial.** `subspacePoly (L.image (· + w)) =
(subspacePoly L).comp (X - C w)`. -/
theorem subspacePoly_image_add_eq_comp (L : Finset K) (w : K) :
    subspacePoly (L.image (· + w)) = (subspacePoly L).comp (X - C w) := by
  classical
  unfold subspacePoly
  rw [Polynomial.prod_comp,
    Finset.prod_image (fun x _ y _ h => add_right_cancel h)]
  refine Finset.prod_congr rfl (fun ℓ _ => ?_)
  rw [sub_comp, X_comp, C_comp, map_add]
  ring

end BKR06

-- Axiom audit.
#print axioms BKR06.subspacePoly_image_add_eq_comp
