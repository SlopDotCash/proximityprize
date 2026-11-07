/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.Commitments.Functional.Hachi.Gadget.Core

/-!
# Compatibility for the former gadget module

The gadget construction is defined in `Gadget.Core`. This module retains the former
constant-ring spelling and the downstream evaluation lemma without redefining the construction.
-/

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus

namespace ArkLib.Lattices.Ajtai

abbrev constRq := @Rq.constRq
abbrev constRq_val := @Rq.constRq_val
abbrev constRq_mul_coeff := @Rq.constRq_mul_coeff
abbrev coeff_eq_zero_of_natDegree_le := @Rq.coeff_eq_zero_of_natDegree_le
abbrev phi_natDegree_le_degree := @Rq.phi_natDegree_le_degree

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]
  (Φ : CyclotomicModulus R) [IsCyclotomic Φ] {base : R}

/-- The former constant-ring spelling sends one to one. -/
@[simp] theorem constRq_one : constRq Φ (1 : R) = 1 := by
  have hC : (CompPoly.CPolynomial.C (1 : R)) = 1 := by
    refine CompPoly.CPolynomial.eq_iff_coeff.mpr (fun i => ?_)
    rw [CompPoly.CPolynomial.coeff_C, CompPoly.CPolynomial.coeff_one]
  change Rq.mk Φ (CompPoly.CPolynomial.C 1) = 1
  rw [hC]
  rfl

/-- Value of `gadgetDecompose` at the flattened index `finProdFinEquiv (i, e)`. -/
theorem gadgetDecompose_apply {rows digits : Nat} (dd : DigitDecomposition base digits)
    (x : PolyVec (Rq Φ) rows) (i : Fin rows) (e : Fin digits) :
    gadgetDecompose Φ dd x (finProdFinEquiv (i, e))
      = Rq.ofFinCoeff Φ Φ.φ.natDegree (fun k => dd.digit ((x i).1.coeff k) e) := by
  exact gadgetDecomposeFun_apply Φ dd.digit x i e

end ArkLib.Lattices.Ajtai
