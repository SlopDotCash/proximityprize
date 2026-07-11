/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Exact collision-defect ledgers for the five surviving Wick transitions

For an `r`-subset sum histogram let

`Delta_r = q * C_r - binom(n,r)^2`,

where `C_r` is its additive collision count.  Apart from the common positive factor `q`, the
normalized centered discrepancy is `Delta_r / binom(n,r)^2`.  This file clears every denominator
without assuming that an abstract defect is positive.  A cap `A/B` on the transition `r -> r+1`
is exactly

`B*n*(r+1)^2*Delta_(r+1) <= A*(n-r)^2*Delta_r`.

For the robust Wick scale `501/500`, the five still-possible selected caps are therefore obtained
by taking `A = 501*(2r)` for `r=2,...,6`; the ordinary caps use `A = 501*(2r+1)`.  The resulting
integer ledgers are the precise missing collision theorems, rather than asymptotic ratio slogans.

Production has a sharp structural crossover between the last two candidate transitions:
`binom(n,5) < q < binom(n,6)`.  More precisely, the depth-five mass is between `2^14` and `2^15`
times smaller than the field, while the depth-six mass is between `2^12` and `2^13` times larger.
Thus `5 -> 6` is the first ambient birthday crossover; `6 -> 7` starts on the dense side and asks
for the smallest relative one-unit saving (`13 -> 12`).

Finally, a distributed late defect is arithmetically cheaper than either full-unit demand.  Keeping
`3,5,7,9` and replacing the last two Wick numerators by `21/2,25/2` gives product `496125/4`.
Even after a factor `501/500` at all six steps this is below `126871`.  Hence it suffices to prove
half-unit savings simultaneously at `5 -> 6` and `6 -> 7`; the exact cleared ledgers for those two
caps are included below.  No analytic collision estimate is asserted.  Issue #466.
-/

set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKLaterTransitionDefectLedgers

/-! ## Production constants and abstract collision defects -/

def productionN : Nat := 2 ^ 30

def productionM : Nat := 2 ^ 128 + 192

def productionQ : Nat := productionN * productionM + 1

def injectiveCoefficient : Nat := 126871

def robustWickScale : ℚ := 501 / 500

/-- Integer numerator of a centered collision discrepancy. -/
def collisionDefect (q mass collision : Int) : Int := q * collision - mass ^ 2

/-- The actual production collision defect attached to an arbitrary collision-count profile. -/
def productionCollisionDefect (C : Nat → Nat) (r : Nat) : Int :=
  collisionDefect productionQ (productionN.choose r) (C r)

/-- Defect density after removing the common field-size factor. -/
noncomputable def defectDensity (mass : Nat) (D : Int) : ℚ :=
  (D : ℚ) / (mass : ℚ) ^ 2

/-- A rational cap `capNumerator / capDenominator` on an `r -> r+1` transition. -/
def RationalTransitionAt (n r capNumerator capDenominator : Nat) (D : Nat → Int) : Prop :=
  (n : ℚ) * defectDensity (n.choose (r + 1)) (D (r + 1)) ≤
    ((capNumerator : ℚ) / capDenominator) *
      defectDensity (n.choose r) (D r)

/-- The direct denominator-cleared ledger, before cancelling adjacent binomial masses. -/
def ClearedTransitionAt (n r capNumerator capDenominator : Nat) (D : Nat → Int) : Prop :=
  (capDenominator : Int) * n * (n.choose r : Int) ^ 2 * D (r + 1) ≤
    (capNumerator : Int) * (n.choose (r + 1) : Int) ^ 2 * D r

/-- Clearing rational denominators is exact for arbitrary signed defects.  Positivity is needed
only for the explicit cap denominator and the two binomial denominators, never for `D r`. -/
theorem rationalTransitionAt_iff_cleared
    (n : Nat) (D : Nat → Int) {r capNumerator capDenominator : Nat}
    (hr : r + 1 ≤ n) (hcap : 0 < capDenominator) :
    RationalTransitionAt n r capNumerator capDenominator D ↔
      ClearedTransitionAt n r capNumerator capDenominator D := by
  have hNrNat : 0 < n.choose r :=
    Nat.choose_pos (le_trans (Nat.le_add_right r 1) hr)
  have hNsNat : 0 < n.choose (r + 1) := Nat.choose_pos hr
  have hNrQ : (0 : ℚ) < n.choose r := by exact_mod_cast hNrNat
  have hNsQ : (0 : ℚ) < n.choose (r + 1) := by exact_mod_cast hNsNat
  have hNr : (0 : ℚ) < (n.choose r : ℚ) ^ 2 := pow_pos hNrQ 2
  have hNs : (0 : ℚ) < (n.choose (r + 1) : ℚ) ^ 2 := pow_pos hNsQ 2
  have hcapQ : (0 : ℚ) < capDenominator := by exact_mod_cast hcap
  have hright : (0 : ℚ) <
      (capDenominator : ℚ) * (n.choose r : ℚ) ^ 2 :=
    mul_pos hcapQ hNr
  unfold RationalTransitionAt defectDensity ClearedTransitionAt
  constructor
  · intro h
    have hfrac :
        ((n : ℚ) * (D (r + 1) : ℚ)) /
            (n.choose (r + 1) : ℚ) ^ 2 ≤
          ((capNumerator : ℚ) * (D r : ℚ)) /
            ((capDenominator : ℚ) * (n.choose r : ℚ) ^ 2) := by
      calc
        ((n : ℚ) * (D (r + 1) : ℚ)) /
            (n.choose (r + 1) : ℚ) ^ 2 =
            (n : ℚ) * ((D (r + 1) : ℚ) / (n.choose (r + 1) : ℚ) ^ 2) := by ring
        _ ≤ ((capNumerator : ℚ) / capDenominator) *
              ((D r : ℚ) / (n.choose r : ℚ) ^ 2) := h
        _ = ((capNumerator : ℚ) * (D r : ℚ)) /
            ((capDenominator : ℚ) * (n.choose r : ℚ) ^ 2) := by ring
    have hcross := (div_le_div_iff₀ hNs hright).mp hfrac
    have hcrossInt :
        ((n : Int) * D (r + 1)) *
            ((capDenominator : Int) * (n.choose r : Int) ^ 2) ≤
          ((capNumerator : Int) * D r) *
            (n.choose (r + 1) : Int) ^ 2 := by
      exact_mod_cast hcross
    convert hcrossInt using 1 <;> ring
  · intro h
    have hcrossInt :
        ((n : Int) * D (r + 1)) *
            ((capDenominator : Int) * (n.choose r : Int) ^ 2) ≤
          ((capNumerator : Int) * D r) *
            (n.choose (r + 1) : Int) ^ 2 := by
      convert h using 1 <;> ring
    have hcross :
        ((n : ℚ) * (D (r + 1) : ℚ)) *
            ((capDenominator : ℚ) * (n.choose r : ℚ) ^ 2) ≤
          ((capNumerator : ℚ) * (D r : ℚ)) *
            (n.choose (r + 1) : ℚ) ^ 2 := by
      exact_mod_cast hcrossInt
    have hfrac := (div_le_div_iff₀ hNs hright).mpr hcross
    calc
      (n : ℚ) * ((D (r + 1) : ℚ) / (n.choose (r + 1) : ℚ) ^ 2) =
          ((n : ℚ) * (D (r + 1) : ℚ)) / (n.choose (r + 1) : ℚ) ^ 2 := by ring
      _ ≤ ((capNumerator : ℚ) * (D r : ℚ)) /
          ((capDenominator : ℚ) * (n.choose r : ℚ) ^ 2) := hfrac
      _ = ((capNumerator : ℚ) / capDenominator) *
          ((D r : ℚ) / (n.choose r : ℚ) ^ 2) := by ring

/-- Adjacent binomial masses cancel, leaving the compact integer defect ledger. -/
def CompactTransitionLedger (n r capNumerator capDenominator : Nat)
    (D : Nat → Int) : Prop :=
  (capDenominator : Int) * n * (r + 1 : Int) ^ 2 * D (r + 1) ≤
    (capNumerator : Int) * (n - r : Int) ^ 2 * D r

/-- Exact equivalence between the choose-square and compact ledgers. -/
theorem clearedTransitionAt_iff_compact
    (n : Nat) (D : Nat → Int) {r capNumerator capDenominator : Nat}
    (hr : r + 1 ≤ n) :
    ClearedTransitionAt n r capNumerator capDenominator D ↔
      CompactTransitionLedger n r capNumerator capDenominator D := by
  have hNrNat : 0 < n.choose r :=
    Nat.choose_pos (le_trans (Nat.le_add_right r 1) hr)
  have hstepNat := Nat.choose_succ_right_eq n r
  have hstep :
      (n.choose (r + 1) : Int) * (r + 1 : Int) =
        (n.choose r : Int) * (n - r : Int) := by
    exact_mod_cast hstepNat
  have hstepSq :
      (n.choose (r + 1) : Int) ^ 2 * (r + 1 : Int) ^ 2 =
        (n.choose r : Int) ^ 2 * (n - r : Int) ^ 2 := by
    calc
      (n.choose (r + 1) : Int) ^ 2 * (r + 1 : Int) ^ 2 =
          ((n.choose (r + 1) : Int) * (r + 1 : Int)) ^ 2 := by ring
      _ = ((n.choose r : Int) * (n - r : Int)) ^ 2 := by rw [hstep]
      _ = (n.choose r : Int) ^ 2 * (n - r : Int) ^ 2 := by ring
  have hNrSq : (0 : Int) < (n.choose r : Int) ^ 2 := by
    exact pow_pos (by exact_mod_cast hNrNat) 2
  have hrsq : (0 : Int) < (r + 1 : Int) ^ 2 := by positivity
  unfold ClearedTransitionAt CompactTransitionLedger
  constructor
  · intro h
    have hs := mul_le_mul_of_nonneg_right h (show (0 : Int) ≤ (r + 1 : Int) ^ 2 by positivity)
    have hs' :
        (n.choose r : Int) ^ 2 *
            ((capDenominator : Int) * n * (r + 1 : Int) ^ 2 * D (r + 1)) ≤
          (n.choose r : Int) ^ 2 *
            ((capNumerator : Int) * (n - r : Int) ^ 2 * D r) := by
      calc
        (n.choose r : Int) ^ 2 *
            ((capDenominator : Int) * n * (r + 1 : Int) ^ 2 * D (r + 1)) =
            ((capDenominator : Int) * n * (n.choose r : Int) ^ 2 * D (r + 1)) *
              (r + 1 : Int) ^ 2 := by ring
        _ ≤ ((capNumerator : Int) * (n.choose (r + 1) : Int) ^ 2 * D r) *
              (r + 1 : Int) ^ 2 := hs
        _ = (n.choose r : Int) ^ 2 *
            ((capNumerator : Int) * (n - r : Int) ^ 2 * D r) := by
          calc
            ((capNumerator : Int) * (n.choose (r + 1) : Int) ^ 2 * D r) *
                (r + 1 : Int) ^ 2 =
                (capNumerator : Int) * D r *
                  ((n.choose (r + 1) : Int) ^ 2 * (r + 1 : Int) ^ 2) := by ring
            _ = (capNumerator : Int) * D r *
                  ((n.choose r : Int) ^ 2 * (n - r : Int) ^ 2) := by
              rw [hstepSq]
            _ = (n.choose r : Int) ^ 2 *
                ((capNumerator : Int) * (n - r : Int) ^ 2 * D r) := by ring
    exact le_of_mul_le_mul_left hs' hNrSq
  · intro h
    have hs := mul_le_mul_of_nonneg_left h
      (show (0 : Int) ≤ (n.choose r : Int) ^ 2 by positivity)
    have hs' :
        (r + 1 : Int) ^ 2 *
            ((capDenominator : Int) * n * (n.choose r : Int) ^ 2 * D (r + 1)) ≤
          (r + 1 : Int) ^ 2 *
            ((capNumerator : Int) * (n.choose (r + 1) : Int) ^ 2 * D r) := by
      calc
        (r + 1 : Int) ^ 2 *
            ((capDenominator : Int) * n * (n.choose r : Int) ^ 2 * D (r + 1)) =
            (n.choose r : Int) ^ 2 *
              ((capDenominator : Int) * n * (r + 1 : Int) ^ 2 * D (r + 1)) := by ring
        _ ≤ (n.choose r : Int) ^ 2 *
              ((capNumerator : Int) * (n - r : Int) ^ 2 * D r) := hs
        _ = (r + 1 : Int) ^ 2 *
            ((capNumerator : Int) * (n.choose (r + 1) : Int) ^ 2 * D r) := by
          calc
            (n.choose r : Int) ^ 2 *
                ((capNumerator : Int) * (n - r : Int) ^ 2 * D r) =
                (capNumerator : Int) * D r *
                  ((n.choose r : Int) ^ 2 * (n - r : Int) ^ 2) := by ring
            _ = (capNumerator : Int) * D r *
                  ((n.choose (r + 1) : Int) ^ 2 * (r + 1 : Int) ^ 2) := by
              rw [hstepSq]
            _ = (r + 1 : Int) ^ 2 *
                ((capNumerator : Int) * (n.choose (r + 1) : Int) ^ 2 * D r) := by ring
    exact le_of_mul_le_mul_left hs' hrsq

/-- Fully consolidated denominator-clearing theorem. -/
theorem rationalTransitionAt_iff_compact
    (n : Nat) (D : Nat → Int) {r capNumerator capDenominator : Nat}
    (hr : r + 1 ≤ n) (hcap : 0 < capDenominator) :
    RationalTransitionAt n r capNumerator capDenominator D ↔
      CompactTransitionLedger n r capNumerator capDenominator D :=
  (rationalTransitionAt_iff_cleared n D hr hcap).trans
    (clearedTransitionAt_iff_compact n D hr)

/-! ## The five surviving robust cap ledgers -/

def RobustOrdinaryLedger (r : Nat) (D : Nat → Int) : Prop :=
  CompactTransitionLedger productionN r (501 * (2 * r + 1)) 500 D

def RobustSelectedLedger (r : Nat) (D : Nat → Int) : Prop :=
  CompactTransitionLedger productionN r (501 * (2 * r)) 500 D

/-- The selected-defect cap at `2 -> 3` is `4 * 501/500`. -/
theorem robustSelectedLedger_two_iff (D : Nat → Int) :
    RobustSelectedLedger 2 D ↔
      (500 : Int) * productionN * 9 * D 3 ≤
        2004 * (productionN - 2 : Int) ^ 2 * D 2 := by
  norm_num [RobustSelectedLedger, CompactTransitionLedger]

/-- The selected-defect cap at `3 -> 4` is `6 * 501/500`. -/
theorem robustSelectedLedger_three_iff (D : Nat → Int) :
    RobustSelectedLedger 3 D ↔
      (500 : Int) * productionN * 16 * D 4 ≤
        3006 * (productionN - 3 : Int) ^ 2 * D 3 := by
  norm_num [RobustSelectedLedger, CompactTransitionLedger]

/-- The selected-defect cap at `4 -> 5` is `8 * 501/500`. -/
theorem robustSelectedLedger_four_iff (D : Nat → Int) :
    RobustSelectedLedger 4 D ↔
      (500 : Int) * productionN * 25 * D 5 ≤
        4008 * (productionN - 4 : Int) ^ 2 * D 4 := by
  norm_num [RobustSelectedLedger, CompactTransitionLedger]

/-- The selected-defect cap at the birthday crossover `5 -> 6` is `10 * 501/500`. -/
theorem robustSelectedLedger_five_iff (D : Nat → Int) :
    RobustSelectedLedger 5 D ↔
      (500 : Int) * productionN * 36 * D 6 ≤
        5010 * (productionN - 5 : Int) ^ 2 * D 5 := by
  norm_num [RobustSelectedLedger, CompactTransitionLedger]

/-- The selected-defect cap at the dense transition `6 -> 7` is `12 * 501/500`. -/
theorem robustSelectedLedger_six_iff (D : Nat → Int) :
    RobustSelectedLedger 6 D ↔
      (500 : Int) * productionN * 49 * D 7 ≤
        6012 * (productionN - 6 : Int) ^ 2 * D 6 := by
  norm_num [RobustSelectedLedger, CompactTransitionLedger]

/-- Exact ordinary robust Wick numerators for `r=2,...,6`. -/
theorem robustOrdinaryLedger_later_table (D : Nat → Int) :
    RobustOrdinaryLedger 2 D = CompactTransitionLedger productionN 2 2505 500 D ∧
      RobustOrdinaryLedger 3 D = CompactTransitionLedger productionN 3 3507 500 D ∧
      RobustOrdinaryLedger 4 D = CompactTransitionLedger productionN 4 4509 500 D ∧
      RobustOrdinaryLedger 5 D = CompactTransitionLedger productionN 5 5511 500 D ∧
      RobustOrdinaryLedger 6 D = CompactTransitionLedger productionN 6 6513 500 D := by
  norm_num [RobustOrdinaryLedger]

/-- Exact selected robust Wick numerators for `r=2,...,6`. -/
theorem robustSelectedLedger_later_table (D : Nat → Int) :
    RobustSelectedLedger 2 D = CompactTransitionLedger productionN 2 2004 500 D ∧
      RobustSelectedLedger 3 D = CompactTransitionLedger productionN 3 3006 500 D ∧
      RobustSelectedLedger 4 D = CompactTransitionLedger productionN 4 4008 500 D ∧
      RobustSelectedLedger 5 D = CompactTransitionLedger productionN 5 5010 500 D ∧
      RobustSelectedLedger 6 D = CompactTransitionLedger productionN 6 6012 500 D := by
  norm_num [RobustSelectedLedger]

/-! ## Exact production birthday crossover -/

/-- The depth-five mass is `14--15` binary orders below the ambient field. -/
theorem production_choose_five_field_window :
    2 ^ 14 * productionN.choose 5 < productionQ ∧
      productionQ < 2 ^ 15 * productionN.choose 5 := by
  have hdesc : productionN.descFactorial 5 = 120 * productionN.choose 5 := by
    have h := Nat.descFactorial_eq_factorial_mul_choose productionN 5
    norm_num only [Nat.factorial] at h
    exact h
  have hlo : 2 ^ 14 * productionN.descFactorial 5 < 120 * productionQ := by
    norm_num [productionN, productionQ, productionM, Nat.descFactorial_succ,
      Nat.descFactorial_zero]
  have hhi : 120 * productionQ < 2 ^ 15 * productionN.descFactorial 5 := by
    norm_num [productionN, productionQ, productionM, Nat.descFactorial_succ,
      Nat.descFactorial_zero]
  omega

/-- The depth-six mass is `12--13` binary orders above the ambient field. -/
theorem production_choose_six_field_window :
    2 ^ 12 * productionQ < productionN.choose 6 ∧
      productionN.choose 6 < 2 ^ 13 * productionQ := by
  have hdesc : productionN.descFactorial 6 = 720 * productionN.choose 6 := by
    have h := Nat.descFactorial_eq_factorial_mul_choose productionN 6
    norm_num only [Nat.factorial] at h
    exact h
  have hlo : 720 * (2 ^ 12 * productionQ) < productionN.descFactorial 6 := by
    norm_num [productionN, productionQ, productionM, Nat.descFactorial_succ,
      Nat.descFactorial_zero]
  have hhi : productionN.descFactorial 6 < 720 * (2 ^ 13 * productionQ) := by
    norm_num [productionN, productionQ, productionM, Nat.descFactorial_succ,
      Nat.descFactorial_zero]
  omega

/-- Exact location of the first ambient birthday crossover. -/
theorem production_birthday_crossover :
    productionN.choose 5 < productionQ ∧ productionQ < productionN.choose 6 := by
  have h5 := production_choose_five_field_window.1
  have h6 := production_choose_six_field_window.1
  omega

/-! ## Ranking and the distributed late half-unit socket -/

/-- A full one-unit improvement is relatively cheapest at the last transition. -/
theorem selected_relative_cost_strict_order :
    (4 : ℚ) / 5 < 6 / 7 ∧ (6 : ℚ) / 7 < 8 / 9 ∧
      (8 : ℚ) / 9 < 10 / 11 ∧ (10 : ℚ) / 11 < 12 / 13 := by
  norm_num

/-- Half a Wick unit at each of the two late transitions. -/
def distributedLateHalfUnit (i : Fin 6) : ℚ :=
  if i.val = 4 then 21 / 2 else if i.val = 5 then 25 / 2 else 2 * i.val + 3

theorem distributedLateHalfUnit_product :
    ∏ i : Fin 6, distributedLateHalfUnit i = 496125 / 4 := by
  norm_num [distributedLateHalfUnit, Fin.prod_univ_succ]

/-- The distributed late defect survives the same `501/500` overhead at all six steps. -/
theorem distributedLateHalfUnit_robust_margin :
    robustWickScale ^ 6 * (∏ i : Fin 6, distributedLateHalfUnit i) <
      injectiveCoefficient := by
  rw [distributedLateHalfUnit_product]
  norm_num [robustWickScale, injectiveCoefficient]

/-- Pointwise product consumer for the distributed late half-unit profile. -/
theorem product_lt_injectiveCoefficient_of_distributedLateHalfUnit
    (c : Fin 6 → ℚ) (hc0 : ∀ i, 0 ≤ c i)
    (hc : ∀ i, c i ≤ robustWickScale * distributedLateHalfUnit i) :
    ∏ i : Fin 6, c i < injectiveCoefficient := by
  have hprod : (∏ i : Fin 6, c i) ≤
      ∏ i : Fin 6, robustWickScale * distributedLateHalfUnit i :=
    Finset.prod_le_prod (fun i _ => hc0 i) (fun i _ => hc i)
  calc
    (∏ i : Fin 6, c i) ≤
        robustWickScale ^ 6 * ∏ i : Fin 6, distributedLateHalfUnit i := by
      simpa [Finset.prod_mul_distrib] using hprod
    _ < injectiveCoefficient := distributedLateHalfUnit_robust_margin

/-- Exact compact ledger for the robust `10.5` cap at `5 -> 6`. -/
theorem robust_halfUnit_five_iff (D : Nat → Int) :
    RationalTransitionAt productionN 5 (21 * 501) 1000 D ↔
      (1000 : Int) * productionN * 36 * D 6 ≤
        10521 * (productionN - 5 : Int) ^ 2 * D 5 := by
  rw [rationalTransitionAt_iff_compact productionN D
    (by norm_num [productionN]) (by norm_num)]
  norm_num [CompactTransitionLedger]

/-- Exact compact ledger for the robust `12.5` cap at `6 -> 7`. -/
theorem robust_halfUnit_six_iff (D : Nat → Int) :
    RationalTransitionAt productionN 6 (25 * 501) 1000 D ↔
      (1000 : Int) * productionN * 49 * D 7 ≤
        12525 * (productionN - 6 : Int) ^ 2 * D 6 := by
  rw [rationalTransitionAt_iff_compact productionN D
    (by norm_num [productionN]) (by norm_num)]
  norm_num [CompactTransitionLedger]

end ArkLib.ProximityGap.Frontier.BGKLaterTransitionDefectLedgers

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.BGKLaterTransitionDefectLedgers.rationalTransitionAt_iff_compact
#print axioms
  ArkLib.ProximityGap.Frontier.BGKLaterTransitionDefectLedgers.production_birthday_crossover
#print axioms
  ArkLib.ProximityGap.Frontier.BGKLaterTransitionDefectLedgers.product_lt_injectiveCoefficient_of_distributedLateHalfUnit
#print axioms
  ArkLib.ProximityGap.Frontier.BGKLaterTransitionDefectLedgers.robust_halfUnit_five_iff
#print axioms
  ArkLib.ProximityGap.Frontier.BGKLaterTransitionDefectLedgers.robust_halfUnit_six_iff
