/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly
import ArkLib.ToMathlib.LinearizedKernel

/-!
# Subspace polynomial of the whole finite field

`subspacePoly (univ : Finset K) = X^{|K|} - X`: the subspace polynomial whose roots are *all* of a
finite field `K` is the field's defining polynomial.  The top instance of the linearized-support
theory (the whole field is itself an 𝔽_q-subspace).
-/

open Polynomial BigOperators

namespace BKR06

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **Subspace polynomial of the whole field.** `subspacePoly univ = X^{|K|} - X`. -/
theorem subspacePoly_univ_eq_pow_card_sub :
    subspacePoly (Finset.univ : Finset K) = X ^ (Fintype.card K) - X := by
  unfold subspacePoly
  exact ArkLib.LinearizedKernel.prod_X_sub_C_univ_eq_pow_card_sub (F := K)

end BKR06

-- Axiom audit.
#print axioms BKR06.subspacePoly_univ_eq_pow_card_sub
