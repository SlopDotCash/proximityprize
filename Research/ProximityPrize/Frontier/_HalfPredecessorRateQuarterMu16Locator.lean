/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The universal collinear locator triple on `mu_16`

For a primitive sixteenth root `z`, the three disjoint exponent triples

```text
A = {0,1,8},  B = {2,9,10},  C = {3,5,7}
```

have monic cubic locators on one affine polynomial line.  This is the
field-universal algebraic seed for the rate-quarter smooth scale lift.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Polynomial

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterMu16Locator

variable {F : Type} [Field F]

noncomputable def locatorA (z : F) : F[X] :=
  (X - C 1) * (X - C z) * (X - C (z ^ 8))

noncomputable def locatorB (z : F) : F[X] :=
  (X - C (z ^ 2)) * (X - C (z ^ 9)) * (X - C (z ^ 10))

noncomputable def locatorC (z : F) : F[X] :=
  (X - C (z ^ 3)) * (X - C (z ^ 5)) * (X - C (z ^ 7))

/-- The universal affine parameter of the locator triple. -/
noncomputable def locatorLambda (z : F) : F :=
  (1 - z ^ 2 - z ^ 4 - z ^ 6) / 2

theorem pow_nine_eq_neg (z : F) (h8 : z ^ 8 = -1) : z ^ 9 = -z := by
  calc
    z ^ 9 = z ^ 8 * z := by ring
    _ = -z := by rw [h8]; ring

theorem pow_ten_eq_neg_sq (z : F) (h8 : z ^ 8 = -1) : z ^ 10 = -(z ^ 2) := by
  calc
    z ^ 10 = z ^ 8 * z ^ 2 := by ring
    _ = -(z ^ 2) := by rw [h8]; ring

/-- **Universal locator collinearity.**  Only the cyclotomic relation
`z^8=-1` and invertibility of `2` are used. -/
theorem locatorC_eq_affine
    (z : F) (h8 : z ^ 8 = -1) (h2 : (2 : F) ≠ 0) :
    locatorC z =
      C (1 - locatorLambda z) * locatorA z +
        C (locatorLambda z) * locatorB z := by
  have hLambda :
      (2 : F) * locatorLambda z = 1 - z ^ 2 - z ^ 4 - z ^ 6 := by
    simp only [locatorLambda]
    field_simp [h2]
  have hOneMinus :
      (2 : F) * (1 - locatorLambda z) =
        2 - (1 - z ^ 2 - z ^ 4 - z ^ 6) := by
    linear_combination -hLambda
  have h9 := pow_nine_eq_neg z h8
  have h10 := pow_ten_eq_neg_sq z h8
  have hcyclo : C (z ^ 8 + 1) = (0 : F[X]) := by rw [h8]; simp
  have hC2 : C (2 : F) ≠ (0 : F[X]) := C_ne_zero.mpr h2
  apply mul_left_cancel₀ hC2
  rw [mul_add]
  simp only [← mul_assoc, ← C_mul]
  rw [hOneMinus, hLambda]
  simp only [locatorA, locatorB, locatorC]
  rw [h8, h9, h10]
  simp only [map_add, map_sub, map_pow, map_neg, map_one, map_ofNat] at hcyclo ⊢
  linear_combination
    (-C z * (2 * C z ^ 6 + C z ^ 2 + 1) +
      (2 * C z ^ 4 + C z ^ 2 + 1) * X) * hcyclo

theorem locatorA_eval_one (z : F) : (locatorA z).eval 1 = 0 := by
  simp [locatorA]

theorem locatorA_eval_z (z : F) : (locatorA z).eval z = 0 := by
  simp [locatorA]

theorem locatorA_eval_z8 (z : F) : (locatorA z).eval (z ^ 8) = 0 := by
  simp [locatorA]

theorem locatorB_eval_z2 (z : F) : (locatorB z).eval (z ^ 2) = 0 := by
  simp [locatorB]

theorem locatorB_eval_z9 (z : F) : (locatorB z).eval (z ^ 9) = 0 := by
  simp [locatorB]

theorem locatorB_eval_z10 (z : F) : (locatorB z).eval (z ^ 10) = 0 := by
  simp [locatorB]

theorem locatorC_eval_z3 (z : F) : (locatorC z).eval (z ^ 3) = 0 := by
  simp [locatorC]

theorem locatorC_eval_z5 (z : F) : (locatorC z).eval (z ^ 5) = 0 := by
  simp [locatorC]

theorem locatorC_eval_z7 (z : F) : (locatorC z).eval (z ^ 7) = 0 := by
  simp [locatorC]

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterMu16Locator

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterMu16Locator
#print axioms locatorC_eq_affine
