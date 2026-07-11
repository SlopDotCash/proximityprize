/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKCosetAmplification

/-!
# The depth-seven flatness residual: the BGK lane's sharp named open core — #466

Registers the 2026-07-10/11 BGK-lane endpoint as a strict census residual (`def …Residual :
Prop`), with its full consumer chain landed:

* `DepthSevenFlatnessResidual G` — `E₇(G) ≤ 2¹⁸·|G|⁷`: seventh-moment flatness at `1.94×`
  the Wick constant `13‼`. THE open core of the depth-five production lane after this
  session's bracketing:
  - depth ≤ 6 is IMPOSSIBLE even coset-amplified (`depthSix_amplified_noGo`, Jensen floor);
  - depth 7 SUFFICES via coset amplification (`depthSeven_amplified_closes`);
  - the plain (unamplified) depth-7 route is IMPOSSIBLE (`depthSeven_moment_noGo`);
  - the Gauss-period route floors at `√q = 2⁷⁹ ≫ 2²⁵·⁵` (can never enter the regime);
  - the trivial anchor is 9 bits short (`nineBitGap`).

* `worstCase_of_depthSevenFlatness` — the residual yields the nine-bit sup-bound
  `WorstCaseIncompleteSumBound ψ G (2⁵¹)` (multiplicatively closed `G`, production size).

* `production_ceiling_of_depthSevenFlatness` — and hence the G112 production depth-five
  collision ceiling, end to end.

Numerics (`probe_bgk_depth9_wick_ratio.py`): the residual HOLDS at `n = 16` for `p/n² ≥ 4.5`
and trends toward holding at `n = 32`; the prize regime sits at `p/n² = 2⁹⁸`. It is the
per-frequency BGK/Paley-spectrum conjecture in its minimal formalized form; discharging it =
the prize wall. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

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

/-- **The depth-seven flatness residual** (strict census form): the ordered seventh additive
energy of `G` is within `2¹⁸ = 1.94×13‼` of the Wick scale. The sharp open core of the BGK
depth lane — see the module docstring for the two-sided bracketing that pins it. -/
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

end ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidual

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidual.worstCase_of_depthSevenFlatness
#print axioms
  ArkLib.ProximityGap.Frontier.BGKDepthSevenFlatnessResidual.production_ceiling_of_depthSevenFlatness
