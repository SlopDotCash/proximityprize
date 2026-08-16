/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum

/-!
# Exact production gaps for current per-prime depth-seven inputs

This file certifies, using integer arithmetic only, the two sharpest numeric exclusions from the
2026-07-11 literature audit.

Let `n = 2^30`, `m = 2^128 + 192`, and `q = n*m+1`.  Applying Lu--Zheng's multivariate Jacobi
moment estimate to the thirteen-variable all-nontrivial tensor gives the real upper bound

`(m-1)^12 * sqrt(q)`.

The deliberately generous whole-coefficient socket is `2^18*m^7`.  Squaring both positive
quantities, the first theorem proves that the literature bound misses this socket by a factor
strictly between `2^701` and `2^702`.

The second theorem records the exact Bhakta--Shparlinski sparse-polynomial regime failure:
the production exponent gcd `m` exceeds `q^(91/299)`.  These are insufficiency certificates, not
statements of either cited analytic theorem.  Issue #466.
-/

set_option autoImplicit false
set_option exponentiation.threshold 4096

namespace ArkLib.ProximityGap.Frontier.BGKJacobiTensorProductionGap

/-- Production subgroup order. -/
def productionN : ℕ := 2 ^ 30

/-- Production multiplicative index. -/
def productionM : ℕ := 2 ^ 128 + 192

/-- Production field cardinality. -/
def productionQ : ℕ := productionN * productionM + 1

/-- The intentionally generous coefficient-`2^18` socket for the top Jacobi stratum. -/
def generousJacobiSocket : ℕ := 2 ^ 18 * productionM ^ 7

/-- The square of the Lu--Zheng theorem's applicable upper bound. -/
def luZhengBoundSq : ℕ := (productionM - 1) ^ 24 * productionQ

/-- **Exact 701--702 bit gap.**  After squaring, the applicable Lu--Zheng bound is strictly
between `2^(2*701)` and `2^(2*702)` times the square of the generous target socket. -/
theorem luZheng_production_gap_sq :
    generousJacobiSocket ^ 2 * 2 ^ (2 * 701) < luZhengBoundSq ∧
      luZhengBoundSq < generousJacobiSocket ^ 2 * 2 ^ (2 * 702) := by
  norm_num [generousJacobiSocket, luZhengBoundSq, productionM, productionQ, productionN]

/-- The production monomial exponent fails the most permissive displayed sparse-polynomial gcd
gate `m <= q^(91/299)`: clearing the fractional exponent gives `m^299 > q^91`. -/
theorem sparsePolynomial_production_gcd_gate_fails :
    productionQ ^ 91 < productionM ^ 299 := by
  norm_num [productionM, productionQ, productionN]

/-- Basic exact bracket used throughout the production audit. -/
theorem productionQ_between_powers : 2 ^ 158 < productionQ ∧ productionQ < 2 ^ 159 := by
  norm_num [productionQ, productionN, productionM]

/-- Exact factorization of the production quotient character-group order.  It exposes a small
`2^6 * 7^3` component and four larger odd components for CRT-based tensor experiments. -/
theorem productionM_factorization :
    productionM =
      2 ^ 6 * 7 ^ 3 * 26407 * 279991 * 4533259 * 462478642316479903 := by
  norm_num [productionM]

#print axioms luZheng_production_gap_sq
#print axioms sparsePolynomial_production_gcd_gate_fails
#print axioms productionQ_between_powers
#print axioms productionM_factorization

end ArkLib.ProximityGap.Frontier.BGKJacobiTensorProductionGap
