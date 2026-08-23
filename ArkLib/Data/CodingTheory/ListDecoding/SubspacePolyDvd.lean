/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyTop

/-!
# The subspace polynomial divides the field polynomial

For a finite `𝔽_q`-subspace `W ⊆ K`, `subspacePoly W ∣ X^{|K|} - X`: the roots of `P_W` (namely `W`)
are a subset of the field `K` (the roots of `X^{|K|} - X`), so the product over `W` divides the
product over `K`.
-/

open Polynomial BigOperators

namespace BKR06

variable {F : Type*} [Field F] {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Module F K]

/-- **The subspace polynomial divides the field polynomial.** -/
theorem subspacePoly_subFinset_dvd_pow_card_sub (W : Submodule F K) [Fintype W] :
    subspacePoly (subFinset W) ∣ X ^ (Fintype.card K) - X := by
  rw [← subspacePoly_univ_eq_pow_card_sub]
  unfold subspacePoly
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)

end BKR06

-- Axiom audit.
#print axioms BKR06.subspacePoly_subFinset_dvd_pow_card_sub
