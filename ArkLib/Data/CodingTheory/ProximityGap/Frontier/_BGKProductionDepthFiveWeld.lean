/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKDepthREnergyLaw
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G112FiberCollisionVarianceIdentity

/-!
# BGK at any scale `M ≤ 2⁴⁰` ⟹ the production depth-five envelope — #466

End-to-end weld at the literal prize numbers. Under the single named open Prop
`WorstCaseIncompleteSumBound ψ G M` with any `M ≤ 2⁴⁰` (the round-30 conjectured scale is
`M = C·n·log n ≈ 2³⁵ ≪ 2⁴⁰` at `n = 2³⁰`), on a production-sized instance
(`|G| = 2³⁰`, `q ≥ 2¹⁵⁸` — the prize field has `q = n·(2¹²⁸ + 192) + 1 > 2¹⁵⁸`):

* `rEnergy_le_production_ceiling` — the ordered depth-five energy fits the G112 collision
  ceiling: `E₅(G) ≤ 2²³⁵ = productionCollisionCeiling`. The margin is wide:
  `E₅ ≤ |G|¹⁰/q + M⁴·|G| ≤ 2¹⁴² + 2¹⁹⁰ ≪ 2²³⁵`.

* `bgk_production_depthFive_weld` — composed with the kernel-checked G112 arithmetic
  (`production_collisionCeiling_mul_base_le_wick`): the full depth-five envelope
  `E₅(G) · productionDepthFiveBase ≤ productionWick`.

Combined with `_BGKDepthREnergyLaw` and `_BGKSupBoundMomentTower`, the chain
"BGK sup-bound (round-30 scale) ⟹ depth-five collision ceiling ⟹ production Wick envelope"
is now a THEOREM; the only open content anywhere in the chain is the hypothesis
`WorstCaseIncompleteSumBound` itself. Nothing here discharges it. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 512
set_option maxRecDepth 8192
set_option linter.style.longLine false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw
open ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity

namespace ArkLib.ProximityGap.Frontier.BGKProductionDepthFiveWeld

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **BGK ⟹ the production collision ceiling.** At production scale (`|G| = 2³⁰`,
`q ≥ 2¹⁵⁸`), any BGK sup-bound `M ≤ 2⁴⁰` (round-30 scale is `≈ 2³⁵`) forces the ordered
depth-five energy under the G112 collision ceiling `2²³⁵`. -/
theorem rEnergy_le_production_ceiling {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ 2 ^ 40)
    (hwc : WorstCaseIncompleteSumBound ψ G M)
    (hG : G.card = 2 ^ 30) (hq : (2 : ℝ) ^ 158 ≤ (Fintype.card F : ℝ)) :
    rEnergy G 5 ≤ productionCollisionCeiling := by
  have h5 := rEnergy_five_le_of_worstCase hψ G hM0 hwc
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hq
  have hGR : (G.card : ℝ) = 2 ^ 30 := by rw [hG]; norm_num
  -- `M⁴ ≤ 2¹⁶⁰`.
  have hM4 : M ^ 4 ≤ (2 : ℝ) ^ 160 := by
    calc M ^ 4 ≤ ((2 : ℝ) ^ 40) ^ 4 := pow_le_pow_left₀ hM0 hM 4
      _ = (2 : ℝ) ^ 160 := by norm_num
  -- `q·E₅ ≤ 2³⁰⁰ + 2¹⁹⁰·q`.
  have hstep : q * (rEnergy G 5 : ℝ) ≤ (2 : ℝ) ^ 300 + (2 : ℝ) ^ 190 * q := by
    have hGpow : (G.card : ℝ) ^ 10 = (2 : ℝ) ^ 300 := by rw [hGR, ← pow_mul]
    have hMq : M ^ 4 * (q * (G.card : ℝ)) ≤ (2 : ℝ) ^ 190 * q := by
      rw [hGR]
      calc M ^ 4 * (q * 2 ^ 30) ≤ (2 : ℝ) ^ 160 * (q * 2 ^ 30) := by
            have hq30 : (0 : ℝ) ≤ q * 2 ^ 30 := by positivity
            exact mul_le_mul_of_nonneg_right hM4 hq30
        _ = (2 : ℝ) ^ 190 * q := by ring
    calc q * (rEnergy G 5 : ℝ)
        ≤ (G.card : ℝ) ^ 10 + M ^ 4 * (q * (G.card : ℝ)) := h5
      _ ≤ (2 : ℝ) ^ 300 + (2 : ℝ) ^ 190 * q := by rw [hGpow]; linarith
  -- `2³⁰⁰ ≤ 2²³⁴·q` (since `q ≥ 2¹⁵⁸ ≥ 2⁶⁶`), so `q·E₅ ≤ (2²³⁴ + 2¹⁹⁰)·q ≤ 2²³⁵·q`.
  have h66 : (2 : ℝ) ^ 66 ≤ q := by
    have : (2 : ℝ) ^ 66 ≤ (2 : ℝ) ^ 158 :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    linarith
  have h300 : (2 : ℝ) ^ 300 ≤ (2 : ℝ) ^ 234 * q := by
    have hsplit : (2 : ℝ) ^ 300 = (2 : ℝ) ^ 234 * (2 : ℝ) ^ 66 := by
      rw [← pow_add]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left h66 (by positivity)
  have hEq : q * (rEnergy G 5 : ℝ) ≤ q * (2 : ℝ) ^ 235 := by
    have hcoef : (2 : ℝ) ^ 234 + (2 : ℝ) ^ 190 ≤ (2 : ℝ) ^ 235 := by
      have h1 : (2 : ℝ) ^ 190 ≤ (2 : ℝ) ^ 234 :=
        pow_le_pow_right₀ (by norm_num) (by norm_num)
      have h2 : (2 : ℝ) ^ 234 + (2 : ℝ) ^ 234 = (2 : ℝ) ^ 235 := by
        rw [← two_mul, ← pow_succ']
      linarith
    have hqnn : (0 : ℝ) ≤ q := le_of_lt hq0
    calc q * (rEnergy G 5 : ℝ) ≤ (2 : ℝ) ^ 300 + (2 : ℝ) ^ 190 * q := hstep
      _ ≤ (2 : ℝ) ^ 234 * q + (2 : ℝ) ^ 190 * q := add_le_add h300 le_rfl
      _ = ((2 : ℝ) ^ 234 + (2 : ℝ) ^ 190) * q := by ring
      _ ≤ (2 : ℝ) ^ 235 * q := mul_le_mul_of_nonneg_right hcoef hqnn
      _ = q * (2 : ℝ) ^ 235 := by ring
  have hEreal : (rEnergy G 5 : ℝ) ≤ (2 : ℝ) ^ 235 :=
    le_of_mul_le_mul_left hEq hq0
  have hfinal : (rEnergy G 5 : ℝ) ≤ ((productionCollisionCeiling : ℕ) : ℝ) := by
    have hcast : ((productionCollisionCeiling : ℕ) : ℝ) = (2 : ℝ) ^ 235 := by
      norm_num [productionCollisionCeiling]
    rw [hcast]
    exact hEreal
  exact_mod_cast hfinal

/-- **BGK ⟹ the production depth-five Wick envelope, end to end.** Composing the collision
ceiling with the kernel-checked G112 arithmetic: at production scale, any BGK sup-bound
`M ≤ 2⁴⁰` forces `E₅(G) · productionDepthFiveBase ≤ productionWick`. The single open input
of the whole chain is `WorstCaseIncompleteSumBound`. -/
theorem bgk_production_depthFive_weld {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ 2 ^ 40)
    (hwc : WorstCaseIncompleteSumBound ψ G M)
    (hG : G.card = 2 ^ 30) (hq : (2 : ℝ) ^ 158 ≤ (Fintype.card F : ℝ)) :
    rEnergy G 5 * productionDepthFiveBase ≤ productionWick := by
  have hceil := rEnergy_le_production_ceiling hψ G hM0 hM hwc hG hq
  calc rEnergy G 5 * productionDepthFiveBase
      ≤ productionCollisionCeiling * productionDepthFiveBase :=
        Nat.mul_le_mul_right _ hceil
    _ ≤ productionWick := production_collisionCeiling_mul_base_le_wick

/-- The prize field cardinality clears the `2¹⁵⁸` hypothesis:
`productionQ = 2³⁰·(2¹²⁸ + 192) + 1 ≥ 2¹⁵⁸`. Kernel arithmetic. -/
theorem productionQ_ge : 2 ^ 158 ≤ productionQ := by
  norm_num [productionQ, productionN]

end ArkLib.ProximityGap.Frontier.BGKProductionDepthFiveWeld

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.BGKProductionDepthFiveWeld.rEnergy_le_production_ceiling
#print axioms
  ArkLib.ProximityGap.Frontier.BGKProductionDepthFiveWeld.bgk_production_depthFive_weld
#print axioms ArkLib.ProximityGap.Frontier.BGKProductionDepthFiveWeld.productionQ_ge
