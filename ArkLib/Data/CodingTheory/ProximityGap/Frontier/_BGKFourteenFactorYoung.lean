/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Fourteen-factor Young/AM--GM socket for repeated depth-seven strata

The Newton--Möbius decomposition of the repeated depth-seven sector produces products of at most
thirteen shifted Gauss-period magnitudes.  The analytic input needed to absorb those monomials is
ordinary generalized Hölder.  This file begins its kernel-checked finite form with the pointwise
fourteen-factor Young inequality

`14 * product_i z_i <= sum_i z_i^14`.

Padding a `k`-factor monomial by `14-k` copies of a scale `R` and summing this inequality is the
root-free route to the production absorption certificate in
`_BGKRepeatedSectorNewtonAbsorption.lean`.

Issue #466.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKFourteenFactorYoung

/-- Equal-weight AM--GM applied to the fourteenth powers. -/
theorem fourteen_mul_prod_le_sum_pow (z : Fin 14 → NNReal) :
    14 * (∏ i, z i) ≤ ∑ i, z i ^ 14 := by
  let w : Fin 14 → NNReal := fun _ => 1 / 14
  have hw : ∑ i, w i = 1 := by
    norm_num [w, Fin.sum_univ_succ]
  have h := NNReal.geom_mean_le_arith_mean_weighted
    (s := (Finset.univ : Finset (Fin 14))) w (fun i => z i ^ 14) hw
  have hroot : ∀ i : Fin 14, (z i ^ 14) ^ ((w i : ℝ)) = z i := by
    intro i
    simpa [w, div_eq_mul_inv] using
      (NNReal.pow_rpow_inv_natCast (z i) (n := 14) (by norm_num))
  simp only [hroot] at h
  have h' : (∏ i, z i) ≤ (1 / 14 : NNReal) * ∑ i, z i ^ 14 := by
    simpa [w, Finset.mul_sum] using h
  calc
    14 * (∏ i, z i) ≤ 14 * ((1 / 14 : NNReal) * ∑ i, z i ^ 14) := by gcongr
    _ = ∑ i, z i ^ 14 := by
      rw [← mul_assoc]
      norm_num

/-- Summed fourteen-factor Young inequality.  This is generalized Hölder before optimizing the
padding scale: the right side separates completely into fourteen individual moments. -/
theorem summed_fourteen_factor_young
    {B : Type*} [Fintype B] (z : B → Fin 14 → NNReal) :
    14 * (∑ b, ∏ i, z b i) ≤ ∑ i, ∑ b, z b i ^ 14 := by
  calc
    14 * (∑ b, ∏ i, z b i) = ∑ b, 14 * (∏ i, z b i) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ b, ∑ i, z b i ^ 14 :=
      Finset.sum_le_sum fun b _ => fourteen_mul_prod_le_sum_pow (z b)
    _ = ∑ i, ∑ b, z b i ^ 14 := Finset.sum_comm

/-- Consumer form: supply an individual fourteenth-moment budget for each of the fourteen
factors.  Padding coordinates may be constant, so their budgets are explicit cardinality terms. -/
theorem fourteen_mul_sum_prod_le_sum_budget
    {B : Type*} [Fintype B] (z : B → Fin 14 → NNReal) (budget : Fin 14 → NNReal)
    (hbudget : ∀ i, ∑ b, z b i ^ 14 ≤ budget i) :
    14 * (∑ b, ∏ i, z b i) ≤ ∑ i, budget i := by
  exact (summed_fourteen_factor_young z).trans
    (Finset.sum_le_sum fun i _ => hbudget i)

end ArkLib.ProximityGap.Frontier.BGKFourteenFactorYoung

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.BGKFourteenFactorYoung.fourteen_mul_prod_le_sum_pow
#print axioms
  ArkLib.ProximityGap.Frontier.BGKFourteenFactorYoung.summed_fourteen_factor_young
#print axioms
  ArkLib.ProximityGap.Frontier.BGKFourteenFactorYoung.fourteen_mul_sum_prod_le_sum_budget
