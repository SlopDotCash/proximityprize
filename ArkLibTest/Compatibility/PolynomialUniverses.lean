/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/

import ArkLib.Data.Polynomial.SplitFold
import ArkLib.Data.Polynomial.Bivariate
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ULift

/-!
# Higher-universe clients of canonical polynomial APIs

The reviewed SplitFold and bivariate weighted-degree adaptations generalize the coefficient
universe. These clients use `ULift.{1} ℚ : Type 1`, so restricting either API back to `Type`
breaks elaboration. Every proof calls the canonical API directly.

The source and reviewed adaptations are recorded in `scripts/arklib-upstream.json`.
-/

namespace ArkLibTest.Compatibility.PolynomialUniverses

open Polynomial
open scoped BigOperators

/-- Coefficient extraction accepts a polynomial with coefficients in `Type 1`. -/
theorem split_coefficients (n : ℕ) (f : Polynomial (ULift.{1} ℚ)) (i : Fin n) (m : ℕ) :
    (splitNth f n i).coeff m = f.coeff (m * n + i.val) :=
  splitNth_coeff i m

/-- Splitting and recombining preserves an arbitrary higher-universe polynomial. -/
theorem split_recombination (n : ℕ) [NeZero n] (f : Polynomial (ULift.{1} ℚ)) :
    f = ∑ i : Fin n, X ^ i.val * eval₂ C (X ^ n) (splitNth f n i) :=
  eq_sum_splitNth n f

/-- The field-level folding formula also accepts higher-universe coefficients. -/
theorem fold_recombination (n : ℕ) [NeZero n]
    (u : Fin n → Polynomial (ULift.{1} ℚ)) (r : ULift.{1} ℚ) :
    FoldingPolynomial.polyFold (∑ i, X ^ i.val * (u i).comp (X ^ n)) n r =
      ∑ i, r ^ i.val • u i :=
  polyFold_sum

/-- The canonical weighted-degree bound applies to the same higher-universe field. -/
theorem weighted_degree_bounds_X (Q : Polynomial (Polynomial (ULift.{1} ℚ))) (k : ℕ) :
    Bivariate.degreeX Q ≤ Bivariate.natWeightedDegree Q 1 k :=
  Bivariate.degreeX_le_natWeightedDegree Q k

/--
info: 'ArkLibTest.Compatibility.PolynomialUniverses.split_coefficients' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms split_coefficients

/--
info: 'ArkLibTest.Compatibility.PolynomialUniverses.split_recombination' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms split_recombination

/--
info: 'ArkLibTest.Compatibility.PolynomialUniverses.fold_recombination' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fold_recombination

/--
info: 'ArkLibTest.Compatibility.PolynomialUniverses.weighted_degree_bounds_X' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms weighted_degree_bounds_X

end ArkLibTest.Compatibility.PolynomialUniverses
