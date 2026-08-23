/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# R380: the field-uniform `2e+1` half-radius line bound is false

In the `[6,2]` Reed--Solomon syndrome geometry over `ZMod 7`, use the four-moment
Vandermonde column `v(x)=(1,x,x^2,x^3)`.  Every nonzero point of the affine line

`L(gamma) = (0,1,gamma,0)`

is a linear combination of two evaluation columns.  The six displayed certificates
therefore exceed the proposed field-uniform count `2e+1=5` at `e=2`.

The identity behind the example is cubic: after the zeroth and first moments fix the
coefficients, the remaining equations say `x+y=gamma` and `x^2+xy+y^2=0`.  Thus the
ratio `x/y` is a nontrivial cube root of unity.  This resonance is absent from the
prize domain of order `2^30`, so the counterexample refutes the unrestricted claim but
does not refute a dyadic-domain sharpening.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R380HalfRadiusTwoEPlusOneRefuted

abbrev F := ZMod 7

def column (x : F) : Fin 4 → F := fun j => x ^ (j : Nat)

def linePoint (gamma : F) : Fin 4 → F := fun j =>
  if j = 1 then 1 else if j = 2 then gamma else 0

/-- An explicit two-column certificate for a point on the syndrome line. -/
def twoColumnCertificate (gamma x y a b : F) : Prop :=
  linePoint gamma = fun j => a * column x j + b * column y j

theorem gamma_one : twoColumnCertificate 1 3 5 3 4 := by
  funext j
  fin_cases j <;> decide

theorem gamma_two : twoColumnCertificate 2 3 6 2 5 := by
  funext j
  fin_cases j <;> decide

theorem gamma_three : twoColumnCertificate 3 1 2 6 1 := by
  funext j
  fin_cases j <;> decide

theorem gamma_four : twoColumnCertificate 4 5 6 6 1 := by
  funext j
  fin_cases j <;> decide

theorem gamma_five : twoColumnCertificate 5 1 4 2 5 := by
  funext j
  fin_cases j <;> decide

theorem gamma_six : twoColumnCertificate 6 2 4 3 4 := by
  funext j
  fin_cases j <;> decide

/-- The six distinct bad scalars already outnumber `2e+1=5`. -/
theorem six_gt_two_mul_two_add_one : 2 * 2 + 1 < 6 := by omega

end ArkLib.ProximityGap.Frontier.R380HalfRadiusTwoEPlusOneRefuted

#print axioms ArkLib.ProximityGap.Frontier.R380HalfRadiusTwoEPlusOneRefuted.gamma_one
#print axioms ArkLib.ProximityGap.Frontier.R380HalfRadiusTwoEPlusOneRefuted.gamma_six
