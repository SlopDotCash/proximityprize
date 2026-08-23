/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodMomentBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The rooted moment-method sup-norm bound on the worst subgroup period (#389)

`worst_period_moment_le` lands the per-frequency inequality `‖η_b‖^{2r} ≤ q·E_r(G) − |G|^{2r}`.
This file takes the `2r`-th root, landing the form the prize δ* reduction actually consumes — the
sup-norm bound on the worst Gaussian period directly on the in-tree `eta` object:

> `worst_period_le_root` :  for `b ≠ 0`, `r ≥ 1`,  `‖η_b‖ ≤ (q·E_r(G) − |G|^{2r})^{1/(2r)}`.

This is the concrete capstone wiring the abstract `MomentSupNormBridge` (`ℓ^∞ ≤ ℓ^{2r}`) to the
real moment ladder. Combined with the clean-range identity (`E_r = E_r^{(0)}` Gaussian for
`q > (2r)^{φ(n)}`, `CleanRangeNorm`) it gives the proven low-`r` bound; combined with the OPEN
high-`r` halo non-concentration bound `E_r ≤ (1+o(1))·E_r^{(0)}` at `r ≈ ⌈ln q⌉` it gives the prize
sup-norm `B(μ_n) ≤ (1+o(1))√(e·n·ln q)`. The bridge here is unconditional; the open input is the
moment bound (Bourgain–Shkredov wall).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

namespace ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The rooted moment-method sup-norm bound.** For every nontrivial frequency `b ≠ 0` and every
`r ≥ 1`, the worst Gaussian period is bounded by the `2r`-th root of the trimmed `2r`-th moment:
`‖η_b‖ ≤ (q·E_r(G) − |G|^{2r})^{1/(2r)}`.  Concrete in-tree capstone of the moment→sup-norm bridge. -/
theorem worst_period_le_root {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {r : ℕ}
    (hr : 1 ≤ r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ≤ ((Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) := by
  have hmom : ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r) :=
    worst_period_moment_le hψ G r hb
  have hbound_nonneg : 0 ≤ (Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r) :=
    le_trans (by positivity) hmom
  -- take 2r-th roots of `‖η_b‖^{2r} ≤ RHS`
  have hroot : (‖eta ψ G b‖ ^ (2 * r)) ^ ((1 : ℝ) / (2 * r))
      ≤ ((Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) :=
    Real.rpow_le_rpow (by positivity) hmom (by positivity)
  -- the LHS root simplifies to `‖η_b‖`
  have hlhs : (‖eta ψ G b‖ ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) = ‖eta ψ G b‖ := by
    rw [one_div, show (2 * (r : ℝ)) = ((2 * r : ℕ) : ℝ) by push_cast; ring]
    exact Real.pow_rpow_inv_natCast (norm_nonneg _) (by omega)
  rwa [hlhs] at hroot

end ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentLadder.worst_period_le_root
