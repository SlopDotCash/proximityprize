/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MomentOptimizedSupNorm
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._WallCapstone

/-!
# LANE M wiring check (#466 R13): the moment-optimized sup-norm IS the capstone's `B`/`hB`

This tiny file machine-verifies the round-13 claim that LANE M removes caveat (a) of
`_WallCapstone`: it composes `MomentOptimizedSupNorm.supNorm_le_of_wallHolds` (which produces the
closed-form sup-norm bound `B := √(2e·n·(ln q+1))` FROM `WallHolds` alone) into
`WallCapstone.wall_capstone`'s `B`/`hB0`/`hB` slots — closing the previously-parametric gap
end-to-end.

The result `wall_capstone_moment_closed` is `_WallCapstone.wall_capstone` with its `B` and `hB`
supplied by the wall itself (no free sup-norm parameter); the ONLY remaining hypotheses are

* `hwall : WallHolds G` — the wall (the one open analytic Prop), and
* `hglue : RealizedIncidenceBudget …` — the SECOND, distinct named glue (the `√q·B` hyperplane
  cancellation, proven THIS round to not follow from `WallHolds`; see the round-13 kb note).

So the capstone's caveat (a) is discharged: `WallHolds` now supplies BOTH the per-rung moment inputs
AND the optimized sup-norm `B`. The residual is exactly the two-Prop localization
`WallHolds ∧ RealizedIncidenceBudget`, with the second Prop irreducibly distinct.

Note the two `WallHolds` defs (`MomentOptimizedSupNorm.WallHolds` and `WallCapstone.WallHolds`) are
DEFINITIONALLY EQUAL (`∀ r, DCEnergyBound G r`), so the composition type-checks with no glue lemma —
`wall_capstone` accepts the `MomentOptimizedSupNorm` `WallHolds` directly.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 13, LANE M.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal
open ProximityGap Code
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier
open ArkLib.ProximityGap.Frontier.WallCapstone

namespace ArkLib.ProximityGap.Frontier.MomentWallWiring

/-- **Caveat (a) discharged: the capstone with `B` supplied by the wall itself.**  For a smooth
subgroup `G = μ_n`, primitive `ψ`, `q = |F| ≥ e`, and the two open Props `WallHolds G` and
`RealizedIncidenceBudget` (with `B` = the wall's own optimized sup-norm `√(2e·n·(ln q+1))`), the
capstone conclusion holds — with NO free sup-norm parameter.  Compare `_WallCapstone.wall_capstone`,
which took `B`/`hB` as unproven inputs; here they are `supNorm_le_of_wallHolds` from `hwall`.

The remaining hypotheses are exactly the TWO distinct open Props:
`hwall` (the wall) and `hglue` (the `√q·B` hyperplane-cancellation glue, proven this round to be a
genuinely separate input). -/
theorem wall_capstone_moment_closed
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : Set (ι → A)) (εstar : ℝ≥0∞) (δ : ℝ≥0)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ))
    (hwall : WallHolds G)
    (s₀ s₁ : WordStack A (Fin 2) ι → F)
    (hglue : RealizedIncidenceBudget C εstar δ G
      (Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1))) s₀ s₁)
    (hδ1 : δ ≤ 1) :
    (∀ (r : ℕ) (b : F), b ≠ 0 →
        ‖eta ψ G b‖ ^ (2 * r)
          ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
      ∧ δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C εstar :=
  wall_capstone C εstar δ hψ G hwall
    (MomentOptimizedSupNorm.sqrt_floor_nonneg G)
    (MomentOptimizedSupNorm.supNorm_le_of_wallHolds hψ G hq hwall) s₀ s₁ hglue hδ1

end ArkLib.ProximityGap.Frontier.MomentWallWiring

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.Frontier.MomentWallWiring.wall_capstone_moment_closed
