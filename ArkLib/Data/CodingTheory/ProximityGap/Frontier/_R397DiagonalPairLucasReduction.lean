/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R396SimultaneousCyclotomicBezoutCertificate

/-!
# R397: diagonal pair supports reduce to a Lucas common-root obstruction

After scaling a nonzero diagonal representation `(a,a)` to `(1,1)`, every other pair support has
the form `x+y=2`.  Put `s=xy`.  The power sum `x^k+y^k` obeys the Lucas recurrence

`P_0=2`, `P_1=2`, `P_{k+2}=2 P_{k+1}-s P_k`.

Consequently, if `x` and `y` are `n`th roots of unity, then `s^n=1` and `P_n(s)=2`.  Thus two
additional unordered supports force two distinct nontrivial common roots of the explicit
polynomials `X^n-1` and `P_n(X)-2`.  This is the exact input to the degree-one subresultant
obstruction isolated in the accompanying R397 arithmetic audit.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R397DiagonalPairLucasReduction

variable {F : Type*} [Field F] [DecidableEq F]

open ArkLib.ProximityGap.Frontier.R395PairMultiplicitySixRootReduction

/-- Lucas power-sum recurrence for a pair whose sum is `2` and product is `s`. -/
def pairLucas (s : F) : Nat → F
  | 0 => 2
  | 1 => 2
  | k + 2 => 2 * pairLucas s (k + 1) - s * pairLucas s k

/-- The Lucas recurrence exactly computes the power sum of a pair with sum `2`. -/
theorem pairLucas_eq_pow_add_pow
    {x y s : F} (hsum : x + y = 2) (hprod : x * y = s) :
    ∀ k : Nat, pairLucas s k = x ^ k + y ^ k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => norm_num [pairLucas]
  | one => simpa [pairLucas] using hsum.symm
  | more k hk hk1 =>
      rw [pairLucas, hk, hk1, ← hprod, ← hsum]
      ring

/-- A pair of `n`th roots with sum `2` gives the Lucas common-root equations. -/
theorem lucas_common_root_of_pair
    {x y : F} {n : Nat} (hsum : x + y = 2)
    (hx : x ^ n = 1) (hy : y ^ n = 1) :
    (x * y) ^ n = 1 ∧ pairLucas (x * y) n = 2 := by
  constructor
  · rw [mul_pow, hx, hy, one_mul]
  · rw [pairLucas_eq_pow_add_pow hsum rfl, hx, hy]
    norm_num

/-- At fixed sum, the product determines an unordered pair support. -/
theorem pairSupport_eq_of_sum_eq_of_product_eq
    {x y x' y' : F} (hsum : x + y = x' + y') (hprod : x * y = x' * y') :
    ({x, y} : Finset F) = {x', y'} := by
  classical
  have hfactor : (x - x') * (x - y') = 0 := by
    linear_combination x * hsum - hprod
  rcases mul_eq_zero.mp hfactor with hxx | hxy
  · have hxx' : x = x' := sub_eq_zero.mp hxx
    have hyy' : y = y' := by
      rw [hxx'] at hsum
      exact add_left_cancel hsum
    subst x
    subst y
    rfl
  · have hxy' : x = y' := sub_eq_zero.mp hxy
    have hyx' : y = x' := by
      linear_combination hsum - hxy'
    subst x
    subst y
    exact Finset.pair_comm _ _

/-- Distinct fixed-sum supports have distinct products. -/
theorem product_ne_of_pairSupport_ne
    {x y x' y' : F} (hsum : x + y = x' + y')
    (hne : ({x, y} : Finset F) ≠ {x', y'}) : x * y ≠ x' * y' := by
  intro hprod
  exact hne (pairSupport_eq_of_sum_eq_of_product_eq hsum hprod)

end ArkLib.ProximityGap.Frontier.R397DiagonalPairLucasReduction

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R397DiagonalPairLucasReduction.lucas_common_root_of_pair
#print axioms
  ArkLib.ProximityGap.Frontier.R397DiagonalPairLucasReduction.product_ne_of_pairSupport_ne
