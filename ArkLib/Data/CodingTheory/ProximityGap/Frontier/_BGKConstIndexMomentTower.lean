/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ConstantIndexGaussSumBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKDepthREnergyLaw

/-!
# UNCONDITIONAL every-depth moment tower + energy law for constant-index subgroups — #466

The in-tree Gauss-period route (`ConstantIndexGaussSumBound.lean`) discharges the BGK Prop
`WorstCaseIncompleteSumBound` for every constant-index subgroup `G_χ` (`m = orderOf χ ≥ 2`) at
`M_m = (((m−1)√q + 1)/m)²` — but its consumer stops at depth 2 (`addEnergy_constIndex_le`).
Composing with the landed tower (`_BGKSupBoundMomentTower` / `_BGKDepthREnergyLaw`) upgrades it
to EVERY depth, unconditionally:

* `etaMomentTower_constIndex` — `∑_{b≠0} ‖η_b(G_χ)‖^{2r} ≤ M_m^{r−1}·(q·|G_χ| − |G_χ|²)`
  for every `r ≥ 1`. Zero open inputs.
* `rEnergy_constIndex_le` — `q·E_r(G_χ) ≤ |G_χ|^{2r} + M_m^{r−1}·q·|G_χ|` for every `r ≥ 1`.
  At `r = 2` this recovers (and at `r ≥ 3` strictly extends) the in-tree depth-2 result: the
  FIRST unconditional depth-arbitrary energy law for any nontrivial subgroup family in-tree.

**Honesty note.** `M_m ≈ q` as `m` grows, so at the prize index `m = 2¹²⁸` these bounds are
far above the nine-bit target — the constant-index family is the PROVEN low end of the
instance ladder, not the deep regime. The value: the entire depth-arbitrary pipeline is now
exercised unconditionally on a genuinely infinite family with real cancellation, and any
future improvement of `M_m` (for any subgroup family) inherits every depth instantly.
Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.ConstantIndexGaussSum
open ArkLib.ProximityGap.Frontier.BGKSupBoundMomentTower
open ArkLib.ProximityGap.Frontier.BGKDepthREnergyLaw

namespace ArkLib.ProximityGap.Frontier.BGKConstIndexMomentTower

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The constant-index worst-case scale `M_m = (((m−1)√q + 1)/m)²`. -/
noncomputable def constIndexScale (χ : MulChar F ℂ) : ℝ :=
  (((orderOf χ - 1 : ℝ) * Real.sqrt (Fintype.card F : ℝ) + 1) / (orderOf χ : ℝ)) ^ 2

theorem constIndexScale_nonneg (χ : MulChar F ℂ) : 0 ≤ constIndexScale χ :=
  sq_nonneg _

/-- **UNCONDITIONAL every-depth moment tower for constant-index subgroups**: for `m ≥ 2` and
every `r ≥ 1`, `∑_{b≠0} ‖η_b(G_χ)‖^{2r} ≤ M_m^{r−1}·(q·|G_χ| − |G_χ|²)`. No open inputs. -/
theorem etaMomentTower_constIndex {χ : MulChar F ℂ} {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (hm : 2 ≤ orderOf χ) {r : ℕ} (hr : 1 ≤ r) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ (Gchi χ) b‖ ^ (2 * r)
      ≤ constIndexScale χ ^ (r - 1)
        * ((Fintype.card F : ℝ) * (Gchi χ).card - ((Gchi χ).card : ℝ) ^ 2) :=
  etaMomentTower_of_worstCase hψ (Gchi χ) (constIndexScale_nonneg χ)
    (worstCaseIncompleteSumBound_constIndex hψ hm) hr

/-- **UNCONDITIONAL depth-`r` energy law for constant-index subgroups**: for `m ≥ 2` and every
`r ≥ 1`, `q·E_r(G_χ) ≤ |G_χ|^{2r} + M_m^{r−1}·q·|G_χ|`. Extends the in-tree depth-2
`addEnergy_constIndex_le` to arbitrary depth with zero open inputs. -/
theorem rEnergy_constIndex_le {χ : MulChar F ℂ} {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (hm : 2 ≤ orderOf χ) {r : ℕ} (hr : 1 ≤ r) :
    (Fintype.card F : ℝ) * rEnergy (Gchi χ) r
      ≤ ((Gchi χ).card : ℝ) ^ (2 * r)
        + constIndexScale χ ^ (r - 1) * ((Fintype.card F : ℝ) * (Gchi χ).card) :=
  rEnergy_le_of_worstCase hψ (Gchi χ) (constIndexScale_nonneg χ)
    (worstCaseIncompleteSumBound_constIndex hψ hm) hr

end ArkLib.ProximityGap.Frontier.BGKConstIndexMomentTower

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms
  ArkLib.ProximityGap.Frontier.BGKConstIndexMomentTower.etaMomentTower_constIndex
#print axioms ArkLib.ProximityGap.Frontier.BGKConstIndexMomentTower.rEnergy_constIndex_le
