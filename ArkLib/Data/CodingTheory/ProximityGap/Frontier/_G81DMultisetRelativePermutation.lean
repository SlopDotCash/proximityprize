/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G81D: equal padding multisets admit one relative position permutation

G80R showed that the two ordered padding words left after common-multiset cancellation need not
have the same order.  G81C therefore added a relative permutation to the reconstruction code.
This file proves that this coordinate is sufficient: two words with the same multiset differ by
a permutation of their positions, including when values repeat.

This is the finite-combinatorics bridge only.  It does not construct the maximally cancelled
primitive sector or bound its number of cores.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G81DMultisetRelativePermutation

/-- Equal multisets of entries give a bijection of their position types which preserves values.
The construction uses `List.Perm.idxBij`, which matches repeated occurrences by occurrence index.
-/
theorem exists_indexEquiv_of_multiset_eq
    {A : Type*} [DecidableEq A] (left right : List A)
    (h : (left : Multiset A) = right) :
    ∃ e : Fin right.length ≃ Fin left.length, ∀ i, left[e i] = right[i] := by
  have hp : right.Perm left := Multiset.coe_eq_coe.mp h.symm
  let e : Fin right.length ≃ Fin left.length :=
    { toFun := hp.idxBij
      invFun := hp.symm.idxBij
      left_inv := hp.idxBij_rightInverse_idxBij_symm
      right_inv := hp.idxBij_leftInverse_idxBij_symm }
  exact ⟨e, hp.getElem_idxBij_eq_getElem⟩

end ArkLib.ProximityGap.Frontier.G81DMultisetRelativePermutation

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G81DMultisetRelativePermutation.exists_indexEquiv_of_multiset_eq
