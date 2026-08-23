/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Production subset birthday crossover and a distributed Wick budget

This file records two exact arithmetic facts suggested by the centered subset-trajectory probe.
For the first certified production field, five-subsets are still sparse while six-subsets are
already very dense:

`30720 * C(n,5) < q < 30721 * C(n,5)`

and

`5825 * q < C(n,6) < 5826 * q`.

Thus the load jumps by `(n-5)/6 = 178956969 + 5/6` precisely at `5 -> 6`.  This does not prove a
discrepancy contraction: finite exact probes contain direct birthday-crossing counterexamples.
It only identifies the production transition at which a load-sensitive arithmetic theorem would
have to act.

The second fact is an alternative to improving one Wick numerator by a full integer.  Replacing
the last two Wick entries `(11,13)` by `(21/2,25/2)` gives product `124031.25`; even allowing a
factor `501/500` at every one of the six steps leaves product below `126871`.  Consequently a
half-unit defect shared between `5 -> 6` and `6 -> 7` is also a valid production socket.

No transition inequality is asserted here.  Issue #466.
-/

set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKProductionBirthdayCrossover

def productionN : Nat := 2 ^ 30

def productionQ : Nat := productionN * (2 ^ 128 + 192) + 1

/-- The five-subset count, written via the falling factorial so literal evaluation is shallow. -/
def productionFiveSubsetCount : Nat :=
  productionN.descFactorial 5 / Nat.factorial 5

/-- The six-subset count, written via the falling factorial so literal evaluation is shallow. -/
def productionSixSubsetCount : Nat :=
  productionN.descFactorial 6 / Nat.factorial 6

theorem productionFiveSubsetCount_eq_choose :
    productionFiveSubsetCount = productionN.choose 5 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  rfl

theorem productionSixSubsetCount_eq_choose :
    productionSixSubsetCount = productionN.choose 6 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  rfl

/-- Exact narrow window for the sparse five-subset load. -/
theorem production_fiveSubset_sparse_window :
    30720 * productionFiveSubsetCount < productionQ ∧
      productionQ < 30721 * productionFiveSubsetCount := by
  norm_num [productionFiveSubsetCount, productionQ, productionN,
    Nat.descFactorial_succ, Nat.descFactorial_zero]

/-- Exact narrow window for the dense six-subset load. -/
theorem production_sixSubset_dense_window :
    5825 * productionQ < productionSixSubsetCount ∧
      productionSixSubsetCount < 5826 * productionQ := by
  norm_num [productionSixSubsetCount, productionQ, productionN,
    Nat.descFactorial_succ, Nat.descFactorial_zero]

/-- The production birthday crossover is between depths five and six. -/
theorem production_five_sparse_six_dense :
    productionFiveSubsetCount < productionQ ∧
      productionQ < productionSixSubsetCount := by
  constructor
  · have h := production_fiveSubset_sparse_window.1
    omega
  · have hq : 0 < productionQ := by
      norm_num [productionQ, productionN]
    have hscale : productionQ < 5825 * productionQ := by
      nlinarith
    exact lt_trans hscale production_sixSubset_dense_window.1

/-- The exact multiplicative jump between the two loads. -/
theorem production_load_jump_exact :
    (productionSixSubsetCount : ℚ) / productionFiveSubsetCount =
      (productionN - 5 : ℚ) / 6 := by
  norm_num [productionSixSubsetCount, productionFiveSubsetCount, productionN,
    Nat.descFactorial_succ, Nat.descFactorial_zero]

/-! ## A distributed half-unit Wick defect -/

def robustScale : ℚ := 501 / 500

/-- Wick `(3,5,7,9,11,13)` with a half-unit removed from each of the last two entries. -/
def distributedLastTwoWick (i : Fin 6) : ℚ :=
  if i.val = 4 then 21 / 2
  else if i.val = 5 then 25 / 2
  else 2 * i.val + 3

theorem distributedLastTwoWick_product :
    ∏ i : Fin 6, distributedLastTwoWick i = 496125 / 4 := by
  norm_num [distributedLastTwoWick, Fin.prod_univ_succ]

theorem robust_distributedLastTwoWick_product_lt :
    robustScale ^ 6 * ∏ i : Fin 6, distributedLastTwoWick i < (126871 : ℚ) := by
  rw [distributedLastTwoWick_product]
  norm_num [robustScale]

/-- Pointwise robust bounds by the distributed profile close the coefficient product. -/
theorem product_lt_126871_of_robust_distributedLastTwo
    (c : Fin 6 → ℚ)
    (hc0 : ∀ i, 0 ≤ c i)
    (hc : ∀ i, c i ≤ robustScale * distributedLastTwoWick i) :
    ∏ i : Fin 6, c i < 126871 := by
  have hprod : (∏ i : Fin 6, c i) ≤
      ∏ i : Fin 6, robustScale * distributedLastTwoWick i := by
    exact Finset.prod_le_prod (fun i _ => hc0 i) (fun i _ => hc i)
  calc
    (∏ i : Fin 6, c i) ≤
        robustScale ^ 6 * ∏ i : Fin 6, distributedLastTwoWick i := by
      simpa [Finset.prod_mul_distrib] using hprod
    _ < 126871 := robust_distributedLastTwoWick_product_lt

#print axioms productionFiveSubsetCount_eq_choose
#print axioms productionSixSubsetCount_eq_choose
#print axioms production_fiveSubset_sparse_window
#print axioms production_sixSubset_dense_window
#print axioms production_five_sparse_six_dense
#print axioms production_load_jump_exact
#print axioms distributedLastTwoWick_product
#print axioms robust_distributedLastTwoWick_product_lt
#print axioms product_lt_126871_of_robust_distributedLastTwo

end ArkLib.ProximityGap.Frontier.BGKProductionBirthdayCrossover
