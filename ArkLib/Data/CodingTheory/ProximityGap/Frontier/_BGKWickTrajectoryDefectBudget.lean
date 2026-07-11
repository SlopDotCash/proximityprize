/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The one-unit Wick-defect principle for the six-step injective trajectory

`_BGKSevenStepFlatteningProductionNoGo` packages the depth-seven injective target as a product of
six normalized transition constants.  This file identifies the more informative nonuniform
baseline.  The Gaussian/Wick increments are

`3, 5, 7, 9, 11, 13`,

whose product is exactly `13!! = 135135`.  The production trajectory allowance is not merely
between `7^6` and `8^6`: after retaining the exact finite-population and DC normalizations it is a
rational number strictly between `126871` and `126872`.

Consequently **one integer unit of improvement at any one Wick step is enough**.  Replacing any
one entry of `(3,5,7,9,11,13)` by its predecessor gives product at most `124740`, already below
`126871`.  The residual margin is robust: multiplying all six resulting bounds by `501/500`
(a uniform `0.2%` overhead per step) still fits.  A future proof need not obtain a small uniform
improvement at all six transitions; it may instead find one structurally distinguished step with
coefficient `2j` rather than `2j+1`, while allowing small finite-population losses elsewhere.

The file also proves the abstract six-ratio telescoping identity.  If `D_j` is a positive centered
chi-square discrepancy and `c_j = n D_{j+1}/D_j`, then

`prod_(j=0)^5 c_j = n^6 D_6 / D_0`.

Thus the one-unit theorem is an actual trajectory consumer, not only a numerical coincidence.
No such improved subgroup transition is asserted here; producing one is the remaining analytic
task.  Issue #466.
-/

set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKWickTrajectoryDefectBudget

/-! ## Exact production trajectory allowance -/

/-- Production subgroup size. -/
def productionN : Nat := 2 ^ 30

/-- Production multiplicative index in the first certified prime. -/
def productionM : Nat := 2 ^ 128 + 192

/-- First certified production field size. -/
def productionQ : Nat := productionN * productionM + 1

/-- Total mass of ordered injective seven-tuples. -/
def productionInjectiveMass : Nat := productionN.descFactorial 7

/-- Remaining injective coefficient after the repeated sector is absorbed. -/
def injectiveCoefficient : Nat := 126871

/-- The numerator of the exact normalized six-transition allowance. -/
def trajectoryAllowanceNumerator : Nat :=
  injectiveCoefficient * productionQ * productionN ^ 14

/-- The denominator of the exact normalized six-transition allowance. -/
def trajectoryAllowanceDenominator : Nat :=
  (productionQ - productionN) * productionInjectiveMass ^ 2

/-- The exact allowed product of the six constants `n D_(j+1) / D_j`, starting from the
one-subset chi-square discrepancy `(q-n)/n`. -/
noncomputable def productionTrajectoryAllowance : ℚ :=
  (trajectoryAllowanceNumerator : ℚ) / trajectoryAllowanceDenominator

/-- Exact chi-square discrepancy of the uniform one-subset law. -/
noncomputable def productionOneStepChiSquare : ℚ :=
  ((productionQ - productionN : Nat) : ℚ) / productionN

/-- Exact depth-seven chi-square ceiling equivalent to the coefficient-`126871` target. -/
noncomputable def productionDepthSevenChiSquareTarget : ℚ :=
  ((injectiveCoefficient * productionQ * productionN ^ 7 : Nat) : ℚ) /
    productionInjectiveMass ^ 2

/-- The finite-population/DC correction raises the literal coefficient `126871` by less than one.
This is the sharp integer window relevant to combinatorial transition coefficients. -/
theorem productionTrajectoryAllowance_strict_window :
    (126871 : ℚ) < productionTrajectoryAllowance ∧
      productionTrajectoryAllowance < 126872 := by
  norm_num [productionTrajectoryAllowance, trajectoryAllowanceNumerator,
    trajectoryAllowanceDenominator, injectiveCoefficient, productionInjectiveMass,
    productionQ, productionM, productionN, Nat.descFactorial_succ,
    Nat.descFactorial_zero]

/-- The allowance is exactly `n^6` times the permitted endpoint/start discrepancy ratio. -/
theorem productionTrajectoryAllowance_eq_endpointRatio :
    productionTrajectoryAllowance =
      (productionN : ℚ) ^ 6 * productionDepthSevenChiSquareTarget /
        productionOneStepChiSquare := by
  norm_num [productionTrajectoryAllowance, trajectoryAllowanceNumerator,
    trajectoryAllowanceDenominator, productionOneStepChiSquare,
    productionDepthSevenChiSquareTarget, injectiveCoefficient, productionInjectiveMass,
    productionQ, productionM, productionN, Nat.descFactorial_succ,
    Nat.descFactorial_zero]

theorem productionOneStepChiSquare_pos : 0 < productionOneStepChiSquare := by
  norm_num [productionOneStepChiSquare, productionQ, productionM, productionN]

/-! ## Wick increments and the one-unit principle -/

/-- The six Gaussian/Wick transition numerators. -/
def wickStepNumerator (i : Fin 6) : ℚ := 2 * i.val + 3

/-- Improve the selected Wick transition by one integer unit. -/
def oneUnitImprovedWick (k i : Fin 6) : ℚ :=
  if i = k then wickStepNumerator i - 1 else wickStepNumerator i

/-- A convenient uniform overhead factor.  Six copies still fit inside the spare margin left by
any one-unit Wick improvement. -/
def robustWickScale : ℚ := 501 / 500

/-- A distributed alternative: save half a unit at each of the two dense final transitions. -/
def twoLateHalfUnitWick (i : Fin 6) : ℚ :=
  if i = (4 : Fin 6) then 21 / 2
  else if i = (5 : Fin 6) then 25 / 2
  else wickStepNumerator i

/-- The six Wick increments multiply to the primitive coefficient `13!! = 135135`. -/
theorem wickStepNumerator_product :
    ∏ i : Fin 6, wickStepNumerator i = 135135 := by
  norm_num [wickStepNumerator, Fin.prod_univ_succ]

/-- Exact primitive saving still required after the Wick baseline. -/
theorem wick_product_exact_gap :
    (∏ i : Fin 6, wickStepNumerator i) - 126871 = 8264 := by
  rw [wickStepNumerator_product]
  norm_num

/-- Improving any one of the six integer Wick numerators by one is already enough.  The weakest
such improvement is the last one, `13 -> 12`, whose product is `124740`. -/
theorem oneUnitImprovedWick_product_eq_erase (k : Fin 6) :
    (∏ i : Fin 6, oneUnitImprovedWick k i) =
      (wickStepNumerator k - 1) *
        ∏ i ∈ (Finset.univ.erase k), wickStepNumerator i := by
  calc
    (∏ i : Fin 6, oneUnitImprovedWick k i) =
        oneUnitImprovedWick k k *
          ∏ i ∈ (Finset.univ.erase k), oneUnitImprovedWick k i :=
      (Finset.mul_prod_erase Finset.univ (oneUnitImprovedWick k)
        (Finset.mem_univ k)).symm
    _ = (wickStepNumerator k - 1) *
          ∏ i ∈ (Finset.univ.erase k), wickStepNumerator i := by
      congr 1
      · simp [oneUnitImprovedWick]
      · apply Finset.prod_congr rfl
        intro i hi
        have hik : i ≠ k := (Finset.mem_erase.mp hi).1
        simp [oneUnitImprovedWick, hik]

theorem oneUnitImprovedWick_product_formula (k : Fin 6) :
    (∏ i : Fin 6, oneUnitImprovedWick k i) =
      (wickStepNumerator k - 1) * (135135 / wickStepNumerator k) := by
  rw [oneUnitImprovedWick_product_eq_erase]
  have hk : wickStepNumerator k ≠ 0 := by
    have hkpos : 0 < wickStepNumerator k := by
      simp [wickStepNumerator]
      positivity
    exact ne_of_gt hkpos
  have htotal := Finset.mul_prod_erase Finset.univ wickStepNumerator
    (Finset.mem_univ k)
  rw [wickStepNumerator_product] at htotal
  have hrest : (∏ i ∈ (Finset.univ.erase k), wickStepNumerator i) =
      135135 / wickStepNumerator k := by
    apply (eq_div_iff hk).2
    simpa [mul_comm] using htotal
  rw [hrest]

theorem oneUnitImprovedWick_product_lt (k : Fin 6) :
    ∏ i : Fin 6, oneUnitImprovedWick k i ≤ 124740 ∧
      ∏ i : Fin 6, oneUnitImprovedWick k i < 126871 := by
  rw [oneUnitImprovedWick_product_formula]
  fin_cases k <;> norm_num [wickStepNumerator]

/-- The weakest one-unit improvement leaves enough room for a `0.2%` multiplicative overrun at
each of the six transitions. -/
theorem robustWickScale_six_margin :
    robustWickScale ^ 6 * 124740 < (126871 : ℚ) := by
  norm_num [robustWickScale]

/-- The distributed late-step profile has exact product `124031.25`, smaller than every
single-one-unit profile. -/
theorem twoLateHalfUnitWick_product :
    ∏ i : Fin 6, twoLateHalfUnitWick i = 496125 / 4 := by
  norm_num [twoLateHalfUnitWick, wickStepNumerator, Fin.prod_univ_succ, Fin.ext_iff]

/-- A `0.2%` overrun at every transition also fits around the distributed profile. -/
theorem robustTwoLateHalfUnit_margin :
    robustWickScale ^ 6 * (∏ i : Fin 6, twoLateHalfUnitWick i) < (126871 : ℚ) := by
  rw [twoLateHalfUnitWick_product]
  norm_num [robustWickScale]

/-- Robust pointwise consumer: all six transition estimates may exceed the selected improved
Wick profile by the factor `501/500`. -/
theorem product_lt_injectiveCoefficient_of_robustOneUnit
    (c : Fin 6 → ℚ) (k : Fin 6)
    (hc0 : ∀ i, 0 ≤ c i)
    (hc : ∀ i, c i ≤ robustWickScale * oneUnitImprovedWick k i) :
    ∏ i : Fin 6, c i < injectiveCoefficient := by
  have hprod : (∏ i : Fin 6, c i) ≤
      ∏ i : Fin 6, robustWickScale * oneUnitImprovedWick k i := by
    exact Finset.prod_le_prod (fun i _ => hc0 i) (fun i _ => hc i)
  have hwick := (oneUnitImprovedWick_product_lt k).1
  calc
    (∏ i : Fin 6, c i) ≤
        robustWickScale ^ 6 * ∏ i : Fin 6, oneUnitImprovedWick k i := by
      simpa [Finset.prod_mul_distrib] using hprod
    _ ≤ robustWickScale ^ 6 * 124740 := by
      exact mul_le_mul_of_nonneg_left hwick (by norm_num [robustWickScale])
    _ < 126871 := robustWickScale_six_margin
    _ = injectiveCoefficient := by norm_num [injectiveCoefficient]

/-- Robust distributed consumer: half-unit improvements at both final transitions suffice. -/
theorem product_lt_injectiveCoefficient_of_robustTwoLateHalfUnit
    (c : Fin 6 → ℚ)
    (hc0 : ∀ i, 0 ≤ c i)
    (hc : ∀ i, c i ≤ robustWickScale * twoLateHalfUnitWick i) :
    ∏ i : Fin 6, c i < injectiveCoefficient := by
  have hprod : (∏ i : Fin 6, c i) ≤
      ∏ i : Fin 6, robustWickScale * twoLateHalfUnitWick i := by
    exact Finset.prod_le_prod (fun i _ => hc0 i) (fun i _ => hc i)
  calc
    (∏ i : Fin 6, c i) ≤
        robustWickScale ^ 6 * ∏ i : Fin 6, twoLateHalfUnitWick i := by
      simpa [Finset.prod_mul_distrib] using hprod
    _ < 126871 := robustTwoLateHalfUnit_margin
    _ = injectiveCoefficient := by norm_num [injectiveCoefficient]

/-- A pointwise transition bound by any one-unit-improved Wick profile closes the literal
coefficient product. -/
theorem product_lt_injectiveCoefficient_of_oneUnitImproved
    (c : Fin 6 → ℚ) (k : Fin 6)
    (hc0 : ∀ i, 0 ≤ c i)
    (hc : ∀ i, c i ≤ oneUnitImprovedWick k i) :
    ∏ i : Fin 6, c i < injectiveCoefficient := by
  have hprod : (∏ i : Fin 6, c i) ≤ ∏ i : Fin 6, oneUnitImprovedWick k i := by
    exact Finset.prod_le_prod (fun i _ => hc0 i) (fun i _ => hc i)
  have hstrict := (oneUnitImprovedWick_product_lt k).2
  exact lt_of_le_of_lt hprod (by simpa [injectiveCoefficient] using hstrict)

/-- The same pointwise hypothesis lies strictly inside the exact production allowance, including
the finite-population and DC corrections. -/
theorem product_lt_productionTrajectoryAllowance_of_oneUnitImproved
    (c : Fin 6 → ℚ) (k : Fin 6)
    (hc0 : ∀ i, 0 ≤ c i)
    (hc : ∀ i, c i ≤ oneUnitImprovedWick k i) :
    ∏ i : Fin 6, c i < productionTrajectoryAllowance := by
  exact lt_trans
    (product_lt_injectiveCoefficient_of_oneUnitImproved c k hc0 hc)
    (by simpa [injectiveCoefficient] using productionTrajectoryAllowance_strict_window.1)

/-- The robust profile also lies inside the exact production allowance. -/
theorem product_lt_productionTrajectoryAllowance_of_robustOneUnit
    (c : Fin 6 → ℚ) (k : Fin 6)
    (hc0 : ∀ i, 0 ≤ c i)
    (hc : ∀ i, c i ≤ robustWickScale * oneUnitImprovedWick k i) :
    ∏ i : Fin 6, c i < productionTrajectoryAllowance := by
  exact lt_trans
    (product_lt_injectiveCoefficient_of_robustOneUnit c k hc0 hc)
    (by simpa [injectiveCoefficient] using productionTrajectoryAllowance_strict_window.1)

/-- The robust distributed profile lies inside the exact production allowance. -/
theorem product_lt_productionTrajectoryAllowance_of_robustTwoLateHalfUnit
    (c : Fin 6 → ℚ)
    (hc0 : ∀ i, 0 ≤ c i)
    (hc : ∀ i, c i ≤ robustWickScale * twoLateHalfUnitWick i) :
    ∏ i : Fin 6, c i < productionTrajectoryAllowance := by
  exact lt_trans
    (product_lt_injectiveCoefficient_of_robustTwoLateHalfUnit c hc0 hc)
    (by simpa [injectiveCoefficient] using productionTrajectoryAllowance_strict_window.1)

/-! ## Abstract telescoping consumer -/

/-- Product of six normalized discrepancy ratios. -/
noncomputable def sixStepRatioProduct (n : ℚ) (D : Nat → ℚ) : ℚ :=
  ∏ j : Fin 6, n * D (j.val + 1) / D j.val

/-- The six normalized ratios telescope to the endpoint discrepancy ratio. -/
theorem sixStepRatioProduct_eq (n : ℚ) (D : Nat → ℚ)
    (h0 : D 0 ≠ 0) (h1 : D 1 ≠ 0) (h2 : D 2 ≠ 0)
    (h3 : D 3 ≠ 0) (h4 : D 4 ≠ 0) (h5 : D 5 ≠ 0) :
    sixStepRatioProduct n D = n ^ 6 * D 6 / D 0 := by
  simp [sixStepRatioProduct, Fin.prod_univ_succ]
  field_simp [h0, h1, h2, h3, h4, h5]

/-- **End-to-end one-unit consumer.**  If the six actual normalized discrepancy ratios are
pointwise bounded by a Wick profile with one numerator improved by one, then the final discrepancy
is strictly below the coefficient-`126871` production target. -/
theorem final_discrepancy_lt_target_of_oneUnitImproved
    (D : Nat → ℚ) (k : Fin 6)
    (hD0 : D 0 = productionOneStepChiSquare)
    (h0 : D 0 ≠ 0) (h1 : D 1 ≠ 0) (h2 : D 2 ≠ 0)
    (h3 : D 3 ≠ 0) (h4 : D 4 ≠ 0) (h5 : D 5 ≠ 0)
    (hratio0 : ∀ i : Fin 6,
      0 ≤ (productionN : ℚ) * D (i.val + 1) / D i.val)
    (hratio : ∀ i : Fin 6,
      (productionN : ℚ) * D (i.val + 1) / D i.val ≤ oneUnitImprovedWick k i) :
    D 6 < productionDepthSevenChiSquareTarget := by
  have hp := product_lt_productionTrajectoryAllowance_of_oneUnitImproved
    (fun i : Fin 6 => (productionN : ℚ) * D (i.val + 1) / D i.val)
    k hratio0 hratio
  change sixStepRatioProduct productionN D < productionTrajectoryAllowance at hp
  rw [sixStepRatioProduct_eq productionN D h0 h1 h2 h3 h4 h5,
    productionTrajectoryAllowance_eq_endpointRatio, hD0] at hp
  have hstep : 0 < productionOneStepChiSquare := productionOneStepChiSquare_pos
  have hscaled : (productionN : ℚ) ^ 6 * D 6 <
      (productionN : ℚ) ^ 6 * productionDepthSevenChiSquareTarget :=
    (div_lt_div_iff_of_pos_right hstep).mp hp
  have hn6 : (0 : ℚ) < (productionN : ℚ) ^ 6 := by norm_num [productionN]
  nlinarith

/-- Robust end-to-end consumer, allowing a `501/500` overhead at every transition around the
one-unit-improved Wick profile. -/
theorem final_discrepancy_lt_target_of_robustOneUnit
    (D : Nat → ℚ) (k : Fin 6)
    (hD0 : D 0 = productionOneStepChiSquare)
    (h0 : D 0 ≠ 0) (h1 : D 1 ≠ 0) (h2 : D 2 ≠ 0)
    (h3 : D 3 ≠ 0) (h4 : D 4 ≠ 0) (h5 : D 5 ≠ 0)
    (hratio0 : ∀ i : Fin 6,
      0 ≤ (productionN : ℚ) * D (i.val + 1) / D i.val)
    (hratio : ∀ i : Fin 6,
      (productionN : ℚ) * D (i.val + 1) / D i.val ≤
        robustWickScale * oneUnitImprovedWick k i) :
    D 6 < productionDepthSevenChiSquareTarget := by
  have hp := product_lt_productionTrajectoryAllowance_of_robustOneUnit
    (fun i : Fin 6 => (productionN : ℚ) * D (i.val + 1) / D i.val)
    k hratio0 hratio
  change sixStepRatioProduct productionN D < productionTrajectoryAllowance at hp
  rw [sixStepRatioProduct_eq productionN D h0 h1 h2 h3 h4 h5,
    productionTrajectoryAllowance_eq_endpointRatio, hD0] at hp
  have hstep : 0 < productionOneStepChiSquare := productionOneStepChiSquare_pos
  have hscaled : (productionN : ℚ) ^ 6 * D 6 <
      (productionN : ℚ) ^ 6 * productionDepthSevenChiSquareTarget :=
    (div_lt_div_iff_of_pos_right hstep).mp hp
  have hn6 : (0 : ℚ) < (productionN : ℚ) ^ 6 := by norm_num [productionN]
  nlinarith

/-- Distributed end-to-end consumer: robust half-unit savings at both final transitions prove the
same depth-seven target. -/
theorem final_discrepancy_lt_target_of_robustTwoLateHalfUnit
    (D : Nat → ℚ)
    (hD0 : D 0 = productionOneStepChiSquare)
    (h0 : D 0 ≠ 0) (h1 : D 1 ≠ 0) (h2 : D 2 ≠ 0)
    (h3 : D 3 ≠ 0) (h4 : D 4 ≠ 0) (h5 : D 5 ≠ 0)
    (hratio0 : ∀ i : Fin 6,
      0 ≤ (productionN : ℚ) * D (i.val + 1) / D i.val)
    (hratio : ∀ i : Fin 6,
      (productionN : ℚ) * D (i.val + 1) / D i.val ≤
        robustWickScale * twoLateHalfUnitWick i) :
    D 6 < productionDepthSevenChiSquareTarget := by
  have hp := product_lt_productionTrajectoryAllowance_of_robustTwoLateHalfUnit
    (fun i : Fin 6 => (productionN : ℚ) * D (i.val + 1) / D i.val)
    hratio0 hratio
  change sixStepRatioProduct productionN D < productionTrajectoryAllowance at hp
  rw [sixStepRatioProduct_eq productionN D h0 h1 h2 h3 h4 h5,
    productionTrajectoryAllowance_eq_endpointRatio, hD0] at hp
  have hstep : 0 < productionOneStepChiSquare := productionOneStepChiSquare_pos
  have hscaled : (productionN : ℚ) ^ 6 * D 6 <
      (productionN : ℚ) ^ 6 * productionDepthSevenChiSquareTarget :=
    (div_lt_div_iff_of_pos_right hstep).mp hp
  have hn6 : (0 : ℚ) < (productionN : ℚ) ^ 6 := by norm_num [productionN]
  nlinarith

/-- Consolidated arithmetic target: the Wick path misses by `8264`, the exact production
allowance is below the next integer, and any single one-unit Wick improvement fits. -/
theorem wickTrajectory_oneUnit_boundary :
    (∏ i : Fin 6, wickStepNumerator i) = 135135 ∧
      (126871 : ℚ) < productionTrajectoryAllowance ∧
      productionTrajectoryAllowance < 126872 ∧
      ∀ k : Fin 6, ∏ i : Fin 6, oneUnitImprovedWick k i < 126871 := by
  exact ⟨wickStepNumerator_product,
    productionTrajectoryAllowance_strict_window.1,
    productionTrajectoryAllowance_strict_window.2,
    fun k => (oneUnitImprovedWick_product_lt k).2⟩

end ArkLib.ProximityGap.Frontier.BGKWickTrajectoryDefectBudget

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.BGKWickTrajectoryDefectBudget.productionTrajectoryAllowance_strict_window
#print axioms
  ArkLib.ProximityGap.Frontier.BGKWickTrajectoryDefectBudget.product_lt_productionTrajectoryAllowance_of_oneUnitImproved
#print axioms
  ArkLib.ProximityGap.Frontier.BGKWickTrajectoryDefectBudget.sixStepRatioProduct_eq
#print axioms
  ArkLib.ProximityGap.Frontier.BGKWickTrajectoryDefectBudget.final_discrepancy_lt_target_of_oneUnitImproved
#print axioms
  ArkLib.ProximityGap.Frontier.BGKWickTrajectoryDefectBudget.final_discrepancy_lt_target_of_robustOneUnit
#print axioms
  ArkLib.ProximityGap.Frontier.BGKWickTrajectoryDefectBudget.final_discrepancy_lt_target_of_robustTwoLateHalfUnit
#print axioms
  ArkLib.ProximityGap.Frontier.BGKWickTrajectoryDefectBudget.wickTrajectory_oneUnit_boundary
