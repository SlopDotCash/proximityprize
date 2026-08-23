/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKCosetAmplification

/-!
# The raw depth-seven flatness residual is false at production scale

The DC frequency contributes `|G|^14` to the full fourteenth Gauss-period moment. Thus

`|G|^14 ≤ q * rEnergy G 7`.

At `|G| = 2^30` and `q ≤ 2^159`, the proposed raw bound
`rEnergy G 7 ≤ 2^18 * |G|^7` would instead give `q * rEnergy G 7 ≤ 2^387`, contradicting
`|G|^14 = 2^420`.

The corrected object is the DC-subtracted quantity

`q * rEnergy G 7 - |G|^14 = Σ_{b ≠ 0} |η_b|^14`.

Coset amplification needs this off-zero moment to be at most
`|G| * (2^51)^7`. The scale-uniform coefficient-`2^18` formulation below is slightly stronger
under the production bounds and has exactly the same numerical budget `2^387`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1024

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw
open ArkLib.ProximityGap.Frontier.BGKCosetAmplification
open ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity
open ArkLib.ProximityGap.Frontier.BGKNineBitGap

namespace ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidualRefuted

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The BGK lane's own depth-seven moment identity, with the zero-frequency contribution removed
exactly.  Stating this directly avoids confusing the lane-local `rEnergy` representation with the
older library representation of the same collision census. -/
theorem offZero_fourteenthMoment_eq_dcExcess
    {psi : AddChar F ℂ} (hpsi : psi.IsPrimitive) (G : Finset F) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta psi G b‖ ^ 14
      = (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) - (G.card : ℝ) ^ 14 := by
  have hlaw : ∑ b : F, ‖eta psi G b‖ ^ 14
      = (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) := by
    simpa using moment_eq_card_energy hpsi G 7
  have hsplit : ∑ b : F, ‖eta psi G b‖ ^ 14
      = ‖eta psi G 0‖ ^ 14 +
        ∑ b ∈ Finset.univ.erase (0 : F), ‖eta psi G b‖ ^ 14 := by
    simpa using
      (Finset.add_sum_erase _ (fun b : F => ‖eta psi G b‖ ^ 14) (Finset.mem_univ 0)).symm
  have hzero : ‖eta psi G (0 : F)‖ ^ 14 = (G.card : ℝ) ^ 14 := by
    simpa using eta_zero_pow psi G 7
  rw [hsplit, hzero] at hlaw
  linarith

/-- The raw residual proposed in `_BGKDepthSevenFlatnessResidual`. -/
def RawDepthSevenFlatnessResidual (G : Finset F) : Prop :=
  rEnergy G 7 ≤ 2 ^ 18 * G.card ^ 7

/-- **Refutation of the raw depth-seven residual at production scale.** The contradiction is the
`2^420` DC floor versus the proposed `2^387` full-moment ceiling. -/
theorem production_rawDepthSevenFlatnessResidual_false
    {psi : AddChar F ℂ} (hpsi : psi.IsPrimitive) {G : Finset F}
    (hcard : G.card = 2 ^ 30) (hqu : Fintype.card F ≤ 2 ^ 159) :
    ¬ RawDepthSevenFlatnessResidual G := by
  intro hraw
  have hoff := offZero_fourteenthMoment_eq_dcExcess hpsi G
  have hoff_nonneg :
      0 ≤ ∑ b ∈ Finset.univ.erase (0 : F), ‖eta psi G b‖ ^ 14 := by
    exact Finset.sum_nonneg fun b _ => by positivity
  rw [hoff] at hoff_nonneg
  have hlower : (G.card : ℝ) ^ 14 ≤
      (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) := by
    linarith
  have hlower' : (2 : ℝ) ^ 420 ≤
      (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) := by
    calc
      (2 : ℝ) ^ 420 = (G.card : ℝ) ^ 14 := by
        rw [hcard]
        norm_num [← pow_mul]
      _ ≤ (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) := hlower
  have hqR : (Fintype.card F : ℝ) ≤ (2 : ℝ) ^ 159 := by
    exact_mod_cast hqu
  have hER : (rEnergy G 7 : ℝ) ≤ (2 : ℝ) ^ 18 * ((2 : ℝ) ^ 30) ^ 7 := by
    have hrawR : (rEnergy G 7 : ℝ) ≤
        (2 : ℝ) ^ 18 * (G.card : ℝ) ^ 7 := by
      exact_mod_cast hraw
    rwa [hcard, Nat.cast_pow, Nat.cast_ofNat] at hrawR
  have hupper : (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) ≤ (2 : ℝ) ^ 387 := by
    calc
      (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ)
          ≤ (2 : ℝ) ^ 159 * ((2 : ℝ) ^ 18 * ((2 : ℝ) ^ 30) ^ 7) := by
            exact mul_le_mul hqR hER (by positivity) (by positivity)
      _ = (2 : ℝ) ^ 387 := by norm_num [← pow_mul, ← pow_add]
  have : (2 : ℝ) ^ 420 ≤ (2 : ℝ) ^ 387 := hlower'.trans hupper
  norm_num at this

/-- The corrected coefficient-`2^18` residual: bound the DC-subtracted/off-zero moment, not the
full energy. By `sum_nonzero_moment`, the left side is exactly `Σ_{b≠0} |η_b|^14`. -/
def DepthSevenOffZeroFlatnessResidual (G : Finset F) : Prop :=
  (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) - (G.card : ℝ) ^ 14
    ≤ (Fintype.card F : ℝ) * ((2 : ℝ) ^ 18 * (G.card : ℝ) ^ 7)

/-- The exact DC-subtracted budget needed by the production coset-amplification consumer. -/
def DepthSevenCosetBudgetResidual (G : Finset F) : Prop :=
  (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) - (G.card : ℝ) ^ 14
    ≤ (G.card : ℝ) * ((2 : ℝ) ^ 51) ^ 7

/-- At the production parameters the corrected residual gives exactly the budget required by
coset amplification: `Σ_{b≠0} |η_b|^14 ≤ |G| * (2^51)^7 = 2^387`. -/
theorem offZero_budget_of_depthSevenFlatness
    {G : Finset F} (hcard : G.card = 2 ^ 30) (hqu : Fintype.card F ≤ 2 ^ 159)
    (hflat : DepthSevenOffZeroFlatnessResidual G) :
    DepthSevenCosetBudgetResidual G := by
  unfold DepthSevenCosetBudgetResidual
  calc
    (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) - (G.card : ℝ) ^ 14
        ≤ (Fintype.card F : ℝ) * ((2 : ℝ) ^ 18 * (G.card : ℝ) ^ 7) := hflat
    _ ≤ (2 : ℝ) ^ 159 * ((2 : ℝ) ^ 18 * ((2 : ℝ) ^ 30) ^ 7) := by
      have hqR : (Fintype.card F : ℝ) ≤ (2 : ℝ) ^ 159 := by exact_mod_cast hqu
      rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_right hqR (by positivity)
    _ = (G.card : ℝ) * ((2 : ℝ) ^ 51) ^ 7 := by
      rw [hcard]
      norm_num [← pow_mul, ← pow_add]

/-- The exact coset-budget residual closes the nine-bit worst-case target without discarding the
mandatory DC term. -/
theorem worstCase_of_depthSevenCosetBudget
    {psi : AddChar F ℂ} (hpsi : psi.IsPrimitive) {G : Finset F}
    (hG : MulClosed G) (hcard : G.card = 2 ^ 30)
    (hbudget : DepthSevenCosetBudgetResidual G) :
    WorstCaseIncompleteSumBound psi G (2 ^ 51) := by
  intro b hb
  have hamp := card_nsmul_le_offZero_moment hG psi hb 7
  have hamp14 : (G.card : ℝ) * ‖eta psi G b‖ ^ 14
      ≤ ∑ c ∈ Finset.univ.erase (0 : F), ‖eta psi G c‖ ^ 14 := by
    simpa using hamp
  rw [offZero_fourteenthMoment_eq_dcExcess hpsi G] at hamp14
  unfold DepthSevenCosetBudgetResidual at hbudget
  have hpow : (G.card : ℝ) * ‖eta psi G b‖ ^ 14
      ≤ (G.card : ℝ) * ((2 : ℝ) ^ 51) ^ 7 := by
    calc
      (G.card : ℝ) * ‖eta psi G b‖ ^ 14
          = (G.card : ℝ) * ‖eta psi G b‖ ^ (2 * 7) := by norm_num
      _ ≤ (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) - (G.card : ℝ) ^ (2 * 7) := by
        simpa using hamp14
      _ = (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) - (G.card : ℝ) ^ 14 := by norm_num
      _ ≤ (G.card : ℝ) * ((2 : ℝ) ^ 51) ^ 7 := hbudget
  have hcardPos : (0 : ℝ) < G.card := by rw [hcard]; positivity
  have hpow' : (‖eta psi G b‖ ^ 2) ^ 7 ≤ ((2 : ℝ) ^ 51) ^ 7 := by
    have hcancel : ‖eta psi G b‖ ^ 14 ≤ ((2 : ℝ) ^ 51) ^ 7 :=
      le_of_mul_le_mul_left hpow hcardPos
    rw [← pow_mul]
    exact hcancel
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow'

/-- The coefficient-`2^18` off-zero flatness residual implies the exact coset budget, and hence
closes the same nine-bit target. -/
theorem worstCase_of_depthSevenOffZeroFlatness
    {psi : AddChar F ℂ} (hpsi : psi.IsPrimitive) {G : Finset F}
    (hG : MulClosed G) (hcard : G.card = 2 ^ 30)
    (hqu : Fintype.card F ≤ 2 ^ 159)
    (hflat : DepthSevenOffZeroFlatnessResidual G) :
    WorstCaseIncompleteSumBound psi G (2 ^ 51) :=
  worstCase_of_depthSevenCosetBudget hpsi hG hcard
    (offZero_budget_of_depthSevenFlatness hcard hqu hflat)

/-- End-to-end corrected consumer: the off-zero residual delivers the production depth-five
collision ceiling through the existing nine-bit weld. -/
theorem production_ceiling_of_depthSevenOffZeroFlatness
    {psi : AddChar F ℂ} (hpsi : psi.IsPrimitive) {G : Finset F}
    (hG : MulClosed G) (hcard : G.card = 2 ^ 30)
    (hq : (2 : ℝ) ^ 158 ≤ (Fintype.card F : ℝ))
    (hqu : Fintype.card F ≤ 2 ^ 159)
    (hflat : DepthSevenOffZeroFlatnessResidual G) :
    rEnergy G 5 ≤ productionCollisionCeiling :=
  rEnergy_le_production_ceiling_sharp hpsi G (by positivity) le_rfl
    (worstCase_of_depthSevenOffZeroFlatness hpsi hG hcard hqu hflat) hcard hq

end ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidualRefuted

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidualRefuted.production_rawDepthSevenFlatnessResidual_false
#print axioms
  ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidualRefuted.offZero_budget_of_depthSevenFlatness
#print axioms
  ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidualRefuted.worstCase_of_depthSevenCosetBudget
#print axioms
  ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidualRefuted.worstCase_of_depthSevenOffZeroFlatness
#print axioms
  ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidualRefuted.production_ceiling_of_depthSevenOffZeroFlatness
