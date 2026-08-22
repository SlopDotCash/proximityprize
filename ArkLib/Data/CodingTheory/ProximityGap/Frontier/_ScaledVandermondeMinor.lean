/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Universally invertible scaled Vandermonde minors

The singleton blocks of the support divided-difference matrix have rows

```text
(label(anchor₀)-label(anchor₁)) * (1, x, ..., x^(K-1)).
```

After selecting `K` usable coordinates, this is a Vandermonde matrix with each row multiplied by
a nonzero label difference.  This file records the exact determinant and injectivity consumer.
-/

set_option autoImplicit false

open scoped BigOperators Matrix

namespace ArkLib.ProximityGap.Frontier.ScaledVandermondeMinor

variable {F : Type} [Field F]

/-- Vandermonde evaluation matrix with an independent nonzero scale on every row. -/
def scaledVandermonde {n : Nat} (node weight : Fin n → F) : Matrix (Fin n) (Fin n) F :=
  Matrix.diagonal weight * Matrix.vandermonde node

@[simp]
theorem scaledVandermonde_apply {n : Nat} (node weight : Fin n → F) (i j : Fin n) :
    scaledVandermonde node weight i j = weight i * node i ^ (j : Nat) := by
  classical
  simp [scaledVandermonde, Matrix.mul_apply, Matrix.vandermonde, Matrix.diagonal]

/-- Exact determinant factorization into the row scales and the ordinary Vandermonde
determinant. -/
theorem det_scaledVandermonde {n : Nat} (node weight : Fin n → F) :
    (scaledVandermonde node weight).det =
      (∏ i, weight i) * (Matrix.vandermonde node).det := by
  simp [scaledVandermonde, Matrix.det_mul]

/-- Distinct nodes and nonzero row scales make the scaled Vandermonde minor nonsingular. -/
theorem det_scaledVandermonde_ne_zero {n : Nat} (node weight : Fin n → F)
    (hnode : Function.Injective node) (hweight : ∀ i, weight i ≠ 0) :
    (scaledVandermonde node weight).det ≠ 0 := by
  rw [det_scaledVandermonde]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _hi => hweight i)
    (Matrix.det_vandermonde_ne_zero_iff.mpr hnode)

/-- The selected singleton block has trivial coefficient kernel. -/
theorem scaledVandermonde_mulVec_injective {n : Nat} (node weight : Fin n → F)
    (hnode : Function.Injective node) (hweight : ∀ i, weight i ≠ 0) :
    Function.Injective (scaledVandermonde node weight).mulVec := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  apply (scaledVandermonde node weight).isUnit_iff_isUnit_det.mpr
  exact isUnit_iff_ne_zero.mpr (det_scaledVandermonde_ne_zero node weight hnode hweight)

/-- Evaluation form: a degree-`<n` coefficient vector killed by `n` distinctly-supported,
nonzero-scaled evaluation rows is zero. -/
theorem coeff_eq_zero_of_scaled_evaluations {n : Nat} (node weight coeff : Fin n → F)
    (hnode : Function.Injective node) (hweight : ∀ i, weight i ≠ 0)
    (hzero : ∀ i, ∑ j : Fin n, weight i * node i ^ (j : Nat) * coeff j = 0) :
    coeff = 0 := by
  apply (scaledVandermonde_mulVec_injective node weight hnode hweight)
  funext i
  simpa [Matrix.mulVec_eq_sum, scaledVandermonde_apply, mul_comm, mul_left_comm, mul_assoc]
    using hzero i

end ArkLib.ProximityGap.Frontier.ScaledVandermondeMinor

#print axioms ArkLib.ProximityGap.Frontier.ScaledVandermondeMinor.det_scaledVandermonde
#print axioms ArkLib.ProximityGap.Frontier.ScaledVandermondeMinor.det_scaledVandermonde_ne_zero
#print axioms ArkLib.ProximityGap.Frontier.ScaledVandermondeMinor.scaledVandermonde_mulVec_injective
#print axioms ArkLib.ProximityGap.Frontier.ScaledVandermondeMinor.coeff_eq_zero_of_scaled_evaluations
