/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PrizeRadiusCompletionCeiling

/-!
# The open prize predicate is CONFINED to the thin regime `q > 2d·log q` (#444)

`PrizeStructuralConstant.DepthLogSubGaussian ψ G := prizeRadiusSq ψ G ≤ 2·|G|·log q` is the
single 25-year-open prize predicate (the `√(log q)` ceiling above the proven `√n` Parseval
floor).  Its ONLY in-tree producer is `depthLogSubGaussian_of_nearRamanujan`, conditional on
the open near-Ramanujan hypothesis.

This file records the complementary UNCONDITIONAL producer in the *thick* regime, using the
O219 ceiling `prizeRadiusSq (torsion F d) < q`:

* **`depthLogSubGaussian_torsion_of_card_le`** — whenever `q ≤ 2·d·log q` (the thick /
  sub-Johnson regime, `d = |torsion F d|`), the open predicate `DepthLogSubGaussian ψ
  (torsion F d)` holds **unconditionally** — the trivial `√q` ceiling already beats the
  `√(2d·log q)` target, so there is nothing open there.

Consequence (recorded in the docstring of the companion `not_thin_of_depthLog_open`):
the genuinely-open content of `DepthLogSubGaussian` lives ENTIRELY in the **thin** regime
`q > 2·d·log q` — i.e. `d < q/(2 log q)`, exactly the prize window `q = d^β` with `β` large.
This is the in-tree confinement of the open prize content to thin subgroups (rule 3): the
predicate is only a real obstruction where the subgroup is thin.

NOTE (honest scope).  This DELIMITS where the open content lives; it does NOT prove CORE.
The thin-regime instance `q > 2d·log q` (the prize window) stays fully OPEN — only the thick
complement is discharged.  No `δ*`/capacity/beyond-Johnson claim; cliff-at-`n/2` not
referenced.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.PrizeStructuralConstant

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The thick-regime unconditional producer of the open prize predicate.**  When the field
is small enough relative to the subgroup that the trivial bound already suffices,
`q ≤ 2·d·log q`, the O219 ceiling `prizeRadiusSq (torsion F d) < q` discharges
`DepthLogSubGaussian` with NO open hypothesis. -/
theorem depthLogSubGaussian_torsion_of_card_le {d : ℕ} (hd : d ∣ Fintype.card F - 1)
    (hd0 : 0 < d) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hthick : (Fintype.card F : ℝ) ≤ 2 * (d : ℝ) * Real.log (Fintype.card F)) :
    DepthLogSubGaussian ψ (torsion F d) := by
  unfold DepthLogSubGaussian
  -- rewrite `|torsion F d| = d`
  rw [card_torsion hd hd0]
  -- `prizeRadiusSq < q ≤ 2·d·log q`
  have hceil : prizeRadiusSq ψ (torsion F d) < (Fintype.card F : ℝ) :=
    prizeRadiusSq_torsion_lt_card hd hd0 hψ
  linarith

/-- **The contrapositive confinement.**  If the open predicate is genuinely an obstruction at
`torsion F d` (i.e. `DepthLogSubGaussian` FAILS), then the subgroup is necessarily **thin**:
`q > 2·d·log q`.  So all open prize content lives in the thin regime. -/
theorem not_thick_of_depthLogSubGaussian_torsion_fails {d : ℕ} (hd : d ∣ Fintype.card F - 1)
    (hd0 : 0 < d) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hfail : ¬ DepthLogSubGaussian ψ (torsion F d)) :
    2 * (d : ℝ) * Real.log (Fintype.card F) < (Fintype.card F : ℝ) := by
  by_contra hle
  push Not at hle
  exact hfail (depthLogSubGaussian_torsion_of_card_le hd hd0 hψ hle)

end ArkLib.ProximityGap.PrizeStructuralConstant

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.PrizeStructuralConstant.depthLogSubGaussian_torsion_of_card_le
#print axioms
  ArkLib.ProximityGap.PrizeStructuralConstant.not_thick_of_depthLogSubGaussian_torsion_fails
