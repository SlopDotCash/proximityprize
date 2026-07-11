/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKProductionDepthFiveWeld

/-!
# The nine-bit gap: how much of BGK the depth-five envelope actually needs — #466

Sharp localization of the open input on the depth-five lane. Two ends:

* `worstCase_trivial` — the **unconditional trivial anchor**: `‖η_b‖ ≤ |G|` (triangle
  inequality), so `WorstCaseIncompleteSumBound ψ G (|G|²)` holds with NO open input. At the
  production size `|G| = 2³⁰` this is `M = 2⁶⁰`.

* `rEnergy_le_production_ceiling_sharp` — the production weld's arithmetic sharpened to its
  true slack: the depth-five collision ceiling fires at any `M ≤ 2⁵¹` (not just `2⁴⁰`):
  `M⁴·q·|G| ≤ 2²⁰⁴·q·2³⁰ = 2²³⁴·q` and `|G|¹⁰ = 2³⁰⁰ ≤ 2²³⁴·q` at `q ≥ 2⁶⁶`, summing under
  `2²³⁵·q`.

**The gap statement.** The unconditional anchor sits at `M = 2⁶⁰`; the depth-five envelope
fires at `M ≤ 2⁵¹`. So the open content of the ENTIRE depth-five lane is exactly a `2⁹`
improvement of the worst-case sup-bound over trivial — on the sup-norm scale,
`‖η_b‖ ≤ 2²⁵·⁵ = |G|⁰·⁸⁵`, a saving factor of `2⁴·⁵ ≈ 23` over the trivial `‖η_b‖ ≤ 2³⁰`.
(For comparison, the conjectured BGK/round-30 scale `M ≈ 2³⁵` saves 25 bits — the lane needs
only 9 of them.) The round-31 moment ladder stops at `√q` and cannot deliver ANY per-frequency
saving in this regime; the 9 bits remain genuinely open. Nothing here discharges them.
Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 512
set_option maxRecDepth 8192

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw
open ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity
open ArkLib.ProximityGap.Frontier.BGKProductionDepthFiveWeld

namespace ArkLib.ProximityGap.Frontier.BGKNineBitGap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The unconditional trivial anchor**: `‖η_b‖ ≤ |G|` for every `b`, by the triangle
inequality — so the worst-case sup-bound holds at `M = |G|²` with no open input. -/
theorem worstCase_trivial (ψ : AddChar F ℂ) (G : Finset F) :
    WorstCaseIncompleteSumBound ψ G ((G.card : ℝ) ^ 2) := by
  intro b _
  have hnorm : ‖eta ψ G b‖ ≤ (G.card : ℝ) := by
    calc ‖eta ψ G b‖ ≤ ∑ y ∈ G, ‖ψ (b * y)‖ := norm_sum_le _ _
      _ = ∑ _y ∈ G, (1 : ℝ) := Finset.sum_congr rfl (fun y _ => ψ.norm_apply _)
      _ = (G.card : ℝ) := by simp
  calc ‖eta ψ G b‖ ^ 2 ≤ (G.card : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- **The sharpened production ceiling**: the depth-five collision ceiling fires at any
`M ≤ 2⁵¹` — the true slack of the weld arithmetic (9 bits below the trivial `2⁶⁰`). -/
theorem rEnergy_le_production_ceiling_sharp {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {M : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ 2 ^ 51)
    (hwc : WorstCaseIncompleteSumBound ψ G M)
    (hG : G.card = 2 ^ 30) (hq : (2 : ℝ) ^ 158 ≤ (Fintype.card F : ℝ)) :
    rEnergy G 5 ≤ productionCollisionCeiling := by
  have h5 := rEnergy_five_le_of_worstCase hψ G hM0 hwc
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by positivity) hq
  have hGR : (G.card : ℝ) = 2 ^ 30 := by rw [hG]; norm_num
  have hM4 : M ^ 4 ≤ (2 : ℝ) ^ 204 := by
    calc M ^ 4 ≤ ((2 : ℝ) ^ 51) ^ 4 := pow_le_pow_left₀ hM0 hM 4
      _ = (2 : ℝ) ^ 204 := by norm_num
  have hstep : q * (rEnergy G 5 : ℝ) ≤ (2 : ℝ) ^ 300 + (2 : ℝ) ^ 234 * q := by
    have hGpow : (G.card : ℝ) ^ 10 = (2 : ℝ) ^ 300 := by rw [hGR, ← pow_mul]
    have hMq : M ^ 4 * (q * (G.card : ℝ)) ≤ (2 : ℝ) ^ 234 * q := by
      rw [hGR]
      calc M ^ 4 * (q * 2 ^ 30) ≤ (2 : ℝ) ^ 204 * (q * 2 ^ 30) :=
            mul_le_mul_of_nonneg_right hM4 (by positivity)
        _ = (2 : ℝ) ^ 234 * q := by ring
    calc q * (rEnergy G 5 : ℝ)
        ≤ (G.card : ℝ) ^ 10 + M ^ 4 * (q * (G.card : ℝ)) := h5
      _ ≤ (2 : ℝ) ^ 300 + (2 : ℝ) ^ 234 * q := by rw [hGpow]; linarith
  have h66 : (2 : ℝ) ^ 66 ≤ q := by
    have : (2 : ℝ) ^ 66 ≤ (2 : ℝ) ^ 158 :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    linarith
  have h300 : (2 : ℝ) ^ 300 ≤ (2 : ℝ) ^ 234 * q := by
    have hsplit : (2 : ℝ) ^ 300 = (2 : ℝ) ^ 234 * (2 : ℝ) ^ 66 := by rw [← pow_add]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left h66 (by positivity)
  have hEq : q * (rEnergy G 5 : ℝ) ≤ q * (2 : ℝ) ^ 235 := by
    have h2 : (2 : ℝ) ^ 234 + (2 : ℝ) ^ 234 = (2 : ℝ) ^ 235 := by
      rw [← two_mul, ← pow_succ']
    calc q * (rEnergy G 5 : ℝ) ≤ (2 : ℝ) ^ 300 + (2 : ℝ) ^ 234 * q := hstep
      _ ≤ (2 : ℝ) ^ 234 * q + (2 : ℝ) ^ 234 * q := add_le_add h300 le_rfl
      _ = ((2 : ℝ) ^ 234 + (2 : ℝ) ^ 234) * q := by ring
      _ = (2 : ℝ) ^ 235 * q := by rw [h2]
      _ = q * (2 : ℝ) ^ 235 := by ring
  have hEreal : (rEnergy G 5 : ℝ) ≤ (2 : ℝ) ^ 235 := le_of_mul_le_mul_left hEq hq0
  have hfinal : (rEnergy G 5 : ℝ) ≤ ((productionCollisionCeiling : ℕ) : ℝ) := by
    have hcast : ((productionCollisionCeiling : ℕ) : ℝ) = (2 : ℝ) ^ 235 := by
      norm_num [productionCollisionCeiling]
    rw [hcast]; exact hEreal
  exact_mod_cast hfinal

/-- **The nine-bit gap, stated as one theorem.** Unconditionally, the trivial anchor delivers
the sup-bound at `M = 2⁶⁰` (production size); the sharpened weld consumes any `M ≤ 2⁵¹`. So
the entire open content of the depth-five lane is the 9-bit interval `2⁵¹ < M ≤ 2⁶⁰`: any
worst-case improvement of factor `2⁹` over trivial closes the lane. Both ends are proven;
the interior is the named open Prop. -/
theorem nineBitGap (ψ : AddChar F ℂ) (G : Finset F) (hG : G.card = 2 ^ 30) :
    WorstCaseIncompleteSumBound ψ G (2 ^ 60) ∧
      ((2 : ℝ) ^ 60) / ((2 : ℝ) ^ 51) = 2 ^ 9 := by
  constructor
  · have h := worstCase_trivial ψ G
    have hcast : ((G.card : ℝ)) ^ 2 = (2 : ℝ) ^ 60 := by
      rw [hG]
      norm_num
    rwa [hcast] at h
  · have h9 : (2 : ℝ) ^ 60 = (2 : ℝ) ^ 51 * (2 : ℝ) ^ 9 := by rw [← pow_add]
    rw [h9]
    field_simp

end ArkLib.ProximityGap.Frontier.BGKNineBitGap

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.BGKNineBitGap.worstCase_trivial
#print axioms
  ArkLib.ProximityGap.Frontier.BGKNineBitGap.rEnergy_le_production_ceiling_sharp
#print axioms ArkLib.ProximityGap.Frontier.BGKNineBitGap.nineBitGap
