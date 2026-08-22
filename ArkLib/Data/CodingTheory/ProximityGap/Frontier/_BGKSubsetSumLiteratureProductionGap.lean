/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Production gap for the classical subgroup subset-sum asymptotic

Zhu--Wan's subset-sum theorem bounds the error for a `k`-subset fibre of a multiplicative
subgroup of index `m` by a generalized binomial expression at scale `sqrt(q)`.  At depth seven
that displayed error is at least `2*q^3/7!`.  This file records the exact production arithmetic
showing why that theorem is vacuous in the thin-subgroup prize cell:

* the index is more than `2^48*sqrt(q)` (expressed without irrational square roots);
* `2*q^3/7! > 2^462`;
* the lower estimate for the published error exceeds the entire seven-subset population by more
  than `2^252`.

These are comparisons between the theorem's *guaranteed error bar* and the trivial population,
not lower bounds on the actual subset-sum discrepancy.  Issue #466.
-/

set_option autoImplicit false
set_option exponentiation.threshold 1024

namespace ArkLib.ProximityGap.Frontier.BGKSubsetSumLiteratureProductionGap

def productionN : Nat := 2 ^ 30

def productionM : Nat := 2 ^ 128 + 192

def productionQ : Nat := productionN * productionM + 1

/-- Squared, rational form of `m > 2^48 * sqrt(q)`. -/
theorem production_index_beyond_sqrt_range :
    2 ^ 96 * productionQ < productionM ^ 2 := by
  norm_num [productionQ, productionM, productionN]

/-- The depth-seven Zhu--Wan error scale `2*q^3/7!` is already above `2^462`. -/
theorem zhuWan_depthSeven_errorScale_gt :
    2 ^ 462 * Nat.factorial 7 < 2 * productionQ ^ 3 := by
  norm_num [productionQ, productionM, productionN, Nat.factorial]

/-- The theorem's error scale exceeds the complete seven-subset population by over 252 bits. -/
theorem zhuWan_errorScale_gt_population :
    2 ^ 252 * productionN.choose 7 * Nat.factorial 7 < 2 * productionQ ^ 3 := by
  calc
    2 ^ 252 * productionN.choose 7 * Nat.factorial 7 ≤
        2 ^ 252 * productionN ^ 7 * Nat.factorial 7 := by
      gcongr
      exact Nat.choose_le_pow productionN 7
    _ < 2 * productionQ ^ 3 := by
      norm_num [productionQ, productionM, productionN, Nat.factorial]

/-- The raw seven-subset population itself is below `2^210`. -/
theorem sevenSubset_population_lt : productionN.choose 7 < 2 ^ 210 := by
  calc
    productionN.choose 7 < productionN ^ 7 :=
      Nat.choose_lt_pow (by norm_num [productionN]) (by norm_num)
    _ = 2 ^ 210 := by norm_num [productionN]

#print axioms production_index_beyond_sqrt_range
#print axioms zhuWan_depthSeven_errorScale_gt
#print axioms zhuWan_errorScale_gt_population
#print axioms sevenSubset_population_lt

end ArkLib.ProximityGap.Frontier.BGKSubsetSumLiteratureProductionGap
