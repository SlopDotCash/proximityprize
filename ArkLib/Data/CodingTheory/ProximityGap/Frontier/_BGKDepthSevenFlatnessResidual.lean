/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKCosetAmplification

/-!
# Historical raw depth-seven residual (refuted; use the DC-corrected successor) — #466

**Correction, 2026-07-11.**  The raw residual registered in this file is impossible at the
production scale because it includes the zero-frequency/DC mass.  Indeed, `|G| = 2^30` and
`q ≤ 2^159` force

`2^420 = |G|^14 ≤ q E₇`,

whereas `E₇ ≤ 2^18 |G|^7` would force `q E₇ ≤ 2^387`.  The axiom-clean refutation and the
correct replacement

`q E₇ - |G|^14 ≤ q * 2^18 * |G|^7`

are in `_BGKDepthSevenFlatnessResidualRefuted`.  The conditional consumers below remain logically
valid but have a false production antecedent; they are retained only as the audit trail for the
superseded interface.

Registers the 2026-07-10/11 BGK-lane endpoint as a strict census residual (`def …Residual :
Prop`), with its full consumer chain landed:

* `DepthSevenFlatnessResidual G` — the now-refuted raw statement
  `E₇(G) ≤ 2¹⁸·|G|⁷`.  The session's bracketing had treated it as the open core before the DC
  audit found the missing `|G|^14` term:
  - depth ≤ 6 is IMPOSSIBLE even coset-amplified (`depthSix_amplified_noGo`, Jensen floor);
  - depth 7 SUFFICES via coset amplification (`depthSeven_amplified_closes`);
  - the plain (unamplified) depth-7 route is IMPOSSIBLE (`depthSeven_moment_noGo`);
  - the Gauss-period route floors at `√q = 2⁷⁹ ≫ 2²⁵·⁵` (can never enter the regime);
  - the trivial anchor is 9 bits short (`nineBitGap`).

* `worstCase_of_depthSevenFlatness` — the residual yields the nine-bit sup-bound
  `WorstCaseIncompleteSumBound ψ G (2⁵¹)` (multiplicatively closed `G`, production size).

* `production_ceiling_of_depthSevenFlatness` — and hence the G112 production depth-five
  collision ceiling, end to end.

The small-scale numerics predate the DC audit and do not validate this raw production statement.
Use `probe_bgk_depth7_dc_centering.py` and the corrected successor instead. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1024
set_option maxRecDepth 16384

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw
open ArkLib.ProximityGap.Frontier.G112FiberCollisionVarianceIdentity
open ArkLib.ProximityGap.Frontier.BGKProductionDepthFiveWeld
open ArkLib.ProximityGap.Frontier.BGKNineBitGap
open ArkLib.ProximityGap.Frontier.BGKCosetAmplification

namespace ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidual

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Superseded raw residual.**  This proposition is false under the production hypotheses; see
`_BGKDepthSevenFlatnessResidualRefuted`. -/
def DepthSevenFlatnessResidual (G : Finset F) : Prop :=
  rEnergy G 7 ≤ 2 ^ 18 * G.card ^ 7

/-- The residual delivers the nine-bit sup-bound (production size, multiplicatively closed
`G`, `q ≤ 2¹⁵⁹`): `WorstCaseIncompleteSumBound ψ G (2⁵¹)`. -/
theorem worstCase_of_depthSevenFlatness {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hG : MulClosed G) (hcard : G.card = 2 ^ 30)
    (hqu : Fintype.card F ≤ 2 ^ 159)
    (hres : DepthSevenFlatnessResidual G) :
    WorstCaseIncompleteSumBound ψ G (2 ^ 51) :=
  depthSeven_amplified_closes hψ hG hcard hqu hres

/-- The residual delivers the G112 production depth-five collision ceiling, end to end. -/
theorem production_ceiling_of_depthSevenFlatness {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hG : MulClosed G) (hcard : G.card = 2 ^ 30)
    (hq : (2 : ℝ) ^ 158 ≤ (Fintype.card F : ℝ)) (hqu : Fintype.card F ≤ 2 ^ 159)
    (hres : DepthSevenFlatnessResidual G) :
    rEnergy G 5 ≤ productionCollisionCeiling :=
  rEnergy_le_production_ceiling_sharp hψ G (by positivity) le_rfl
    (worstCase_of_depthSevenFlatness hψ hG hcard hqu hres) hcard hq

/-- **Correction theorem for the exact named Prop.**  Under the production cardinality bounds the
raw residual is false: the zero-frequency floor is `2^420`, while the residual would cap the full
moment at `2^387`. -/
theorem production_depthSevenFlatnessResidual_false
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hcard : G.card = 2 ^ 30) (hqu : Fintype.card F ≤ 2 ^ 159) :
    ¬ DepthSevenFlatnessResidual G := by
  intro hres
  have hlaw : ∑ b : F, ‖eta ψ G b‖ ^ 14
      = (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) := by
    simpa using moment_eq_card_energy hψ G 7
  have hzero : ‖eta ψ G (0 : F)‖ ^ 14 = (G.card : ℝ) ^ 14 := by
    simpa using eta_zero_pow ψ G 7
  have hsingle : ‖eta ψ G (0 : F)‖ ^ 14
      ≤ ∑ b : F, ‖eta ψ G b‖ ^ 14 :=
    Finset.single_le_sum (f := fun b : F => ‖eta ψ G b‖ ^ 14)
      (fun b _ => by positivity) (Finset.mem_univ 0)
  rw [hlaw, hzero] at hsingle
  have hlower : (2 : ℝ) ^ 420 ≤
      (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) := by
    calc
      (2 : ℝ) ^ 420 = (G.card : ℝ) ^ 14 := by
        rw [hcard]
        norm_num [← pow_mul]
      _ ≤ (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) := hsingle
  have hqR : (Fintype.card F : ℝ) ≤ (2 : ℝ) ^ 159 := by
    exact_mod_cast hqu
  have hER : (rEnergy G 7 : ℝ) ≤ (2 : ℝ) ^ 18 * ((2 : ℝ) ^ 30) ^ 7 := by
    have hresR : (rEnergy G 7 : ℝ) ≤
        (2 : ℝ) ^ 18 * (G.card : ℝ) ^ 7 := by
      exact_mod_cast hres
    rwa [hcard, Nat.cast_pow, Nat.cast_ofNat] at hresR
  have hupper : (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) ≤ (2 : ℝ) ^ 387 := by
    calc
      (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ)
          ≤ (2 : ℝ) ^ 159 * ((2 : ℝ) ^ 18 * ((2 : ℝ) ^ 30) ^ 7) := by
            exact mul_le_mul hqR hER (by positivity) (by positivity)
      _ = (2 : ℝ) ^ 387 := by norm_num [← pow_mul, ← pow_add]
  have : (2 : ℝ) ^ 420 ≤ (2 : ℝ) ^ 387 := hlower.trans hupper
  norm_num at this

end ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidual

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidual.worstCase_of_depthSevenFlatness
#print axioms
  ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidual.production_ceiling_of_depthSevenFlatness
#print axioms
  ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidual.production_depthSevenFlatnessResidual_false
