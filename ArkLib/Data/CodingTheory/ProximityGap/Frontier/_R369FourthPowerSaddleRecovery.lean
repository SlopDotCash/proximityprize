/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCOptimized

/-!
# R369: the fourth-power saddle-moment conjecture

The stronger assertion that every DC-subtracted moment is sub-Wick is false above
`|G|^4`: the `n=32`, `p=21523361` cell violates it at shallow depths.  The violation
recovers before the optimized depth `ceil(log p)`.  This file states only that surviving
single-rung conjecture and checks its direct prize-scale spectral consequence.

No theorem below proves the conjecture.  It is a named `Prop`, not an axiom.
-/

set_option autoImplicit false

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.DCOptimized
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.R369FourthPowerSaddleRecovery

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The surviving R369 hypothesis: once the field has at least fourth-power size,
the single optimized DC-subtracted moment is sub-Wick. -/
def FourthPowerSaddleDCEnergy (G : Finset F) : Prop :=
  G.card ^ 4 ≤ Fintype.card F →
    DCEnergyBound G ⌈Real.log (Fintype.card F : ℝ)⌉₊

/-- R369's conjecture gives the optimized square-root-scale period bound immediately.
This is the precise endpoint for which the numerical prove/refute loop supplies evidence. -/
theorem eta_sq_le_of_fourthPowerSaddle
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hsize : G.card ^ 4 ≤ Fintype.card F)
    (hsaddle : FourthPowerSaddleDCEnergy G) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2 ≤
      2 * Real.exp 1 * (G.card : ℝ) *
        (⌈Real.log (Fintype.card F : ℝ)⌉₊ : ℝ) := by
  let r : ℕ := ⌈Real.log (Fintype.card F : ℝ)⌉₊
  have hq : (1 : ℝ) < Fintype.card F := by
    exact_mod_cast (Fintype.one_lt_card (α := F))
  have hlogpos : 0 < Real.log (Fintype.card F : ℝ) := Real.log_pos hq
  have hr : 1 ≤ r := by
    exact Nat.ceil_pos.mpr hlogpos
  have hrq : Real.log (Fintype.card F : ℝ) ≤ r := Nat.le_ceil _
  have hdc : DCEnergyBound G r := hsaddle hsize
  simpa only [r] using eta_sq_le_dcOptimized hψ hr hrq hdc hb

end ArkLib.ProximityGap.Frontier.R369FourthPowerSaddleRecovery

#print axioms
  ArkLib.ProximityGap.Frontier.R369FourthPowerSaddleRecovery.eta_sq_le_of_fourthPowerSaddle
