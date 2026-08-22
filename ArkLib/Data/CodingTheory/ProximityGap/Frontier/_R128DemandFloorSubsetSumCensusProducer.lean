/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R125DemandFloorMaximalOrbitProducer
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CensusLaw

/-!
# Subset-sum census route to the maximal demand-tail allowance

The KKH26 exact census law identifies a monomial-pair bad-scalar set with the image of the
`r`-subset-sum map.  This file proves the elementary counting bridge from such an image over a
`2g`-point set into the R125 maximal allowance

`(4g) * C(2g,r-1) + 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.R128DemandFloorSubsetSumCensusProducer

open ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer

variable {F : Type*} [Field F] [DecidableEq F]

/-- A one-step binomial cap: `C(m,r) ≤ m * C(m,r-1)` for positive `r`. -/
theorem choose_le_mul_choose_pred (m r : ℕ) (hr : 1 ≤ r) :
    m.choose r ≤ m * m.choose (r - 1) := by
  have hself : m.choose r ≤ m.choose r * r := by
    calc
      m.choose r = m.choose r * 1 := by rw [mul_one]
      _ ≤ m.choose r * r := Nat.mul_le_mul_left _ hr
  have hch : m.choose r * r = m.choose (r - 1) * (m - (r - 1)) := by
    have hr' : r - 1 + 1 = r := Nat.succ_pred_eq_of_pos hr
    simpa [hr'] using Nat.choose_succ_right_eq m (r - 1)
  calc
    m.choose r ≤ m.choose r * r := hself
    _ = m.choose (r - 1) * (m - (r - 1)) := hch
    _ ≤ m.choose (r - 1) * m := by
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = m * m.choose (r - 1) := by rw [Nat.mul_comm]

/-- Any image of `r`-subsets of a `2g`-point set fits the R125 maximal allowance. -/
theorem subset_image_card_le_maximal_allowance
    (H : Finset F) (f : Finset F → F) (g r : ℕ)
    (hH : H.card = 2 * g)
    (hr : 1 ≤ r) :
    ((H.powersetCard r).image f).card ≤ (4 * g) * maximalTailOP g r + 1 := by
  have himage : ((H.powersetCard r).image f).card ≤ (H.powersetCard r).card :=
    Finset.card_image_le
  have hchoose : (H.powersetCard r).card = (2 * g).choose r := by
    rw [Finset.card_powersetCard, hH]
  have hbinom : (2 * g).choose r ≤ (4 * g) * maximalTailOP g r := by
    calc
      (2 * g).choose r ≤ (2 * g) * (2 * g).choose (r - 1) :=
        choose_le_mul_choose_pred (2 * g) r hr
      _ ≤ (4 * g) * (2 * g).choose (r - 1) := by
        exact Nat.mul_le_mul_right _ (by omega)
      _ = (4 * g) * maximalTailOP g r := by rw [maximalTailOP]
  exact le_trans (le_trans himage (by simpa [hchoose] using hbinom)) (Nat.le_succ _)

open Classical in
/-- KKH26 exact bad-scalar census counts fit the R125 maximal allowance on a `2g`-point domain. -/
theorem kkh26_badScalar_census_card_le_maximal_allowance
    [Fintype F]
    (H : Finset F) (g r : ℕ)
    (hH : H.card = 2 * g)
    (hr2 : 2 ≤ r) :
    (Finset.univ.filter (fun lam : F =>
        ∃ q : Polynomial F, q.natDegree ≤ r - 2 ∧
          r ≤ (ArkLib.ProximityGap.KKH26.lineAgreeSet H r lam q).card)).card
      ≤ (4 * g) * maximalTailOP g r + 1 := by
  rw [ArkLib.ProximityGap.KKH26.badScalar_census_card H hr2]
  exact subset_image_card_le_maximal_allowance H (fun T => -∑ a ∈ T, a) g r hH (by omega)

end ArkLib.ProximityGap.Frontier.R128DemandFloorSubsetSumCensusProducer

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R128DemandFloorSubsetSumCensusProducer.choose_le_mul_choose_pred
#print axioms
  ArkLib.ProximityGap.Frontier.R128DemandFloorSubsetSumCensusProducer.subset_image_card_le_maximal_allowance
#print axioms
  ArkLib.ProximityGap.Frontier.R128DemandFloorSubsetSumCensusProducer.kkh26_badScalar_census_card_le_maximal_allowance
