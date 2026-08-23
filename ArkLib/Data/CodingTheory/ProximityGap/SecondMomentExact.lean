/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The exact DC-subtracted second moment (#407)

The `r = 1` base case of the moment ladder is exact and unconditional (no energy conjecture). From the
Parseval identity `∑_b ‖η_b‖² = q·|G|` (`subgroup_gaussSum_secondMoment`), removing the DC term
`‖η_0‖² = |G|²` gives

> **`sum_nonzero_sq`** — `∑_{b≠0} ‖η_b‖² = q·|G| − |G|²`.

Hence `A_1 = (1/q)∑_{b≠0}‖η_b‖² = |G| − |G|²/q < |G| = Wick(1)`, so the prize bound `A_r ≤ (2r−1)‼·|G|^r`
holds **exactly and unconditionally at `r = 1`** — the base case the moment method anchors on. The open
content is `r ≥ 2` (where the Lam–Leung char-0 floor plus the char-p anomaly enter).

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

namespace ArkLib.ProximityGap.SecondMomentExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Exact DC-subtracted second moment.** `∑_{b≠0} ‖η_b‖² = q·|G| − |G|²` — Parseval minus the DC
(`b=0`) term `‖η_0‖² = |G|²`. Unconditional; the `r=1` anchor of the moment ladder. -/
theorem sum_nonzero_sq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * (G.card : ℝ) - (G.card : ℝ) ^ 2 := by
  have hfull := subgroup_gaussSum_secondMoment hψ G
  have hdc : ‖eta ψ G 0‖ ^ 2 = (G.card : ℝ) ^ 2 := by rw [eta_zero]; simp
  have hsplit : ∑ b : F, ‖eta ψ G b‖ ^ 2
      = ‖eta ψ G 0‖ ^ 2 + ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 :=
    (Finset.add_sum_erase univ _ (Finset.mem_univ 0)).symm
  rw [hfull, hdc] at hsplit
  linarith [hsplit]

end ArkLib.ProximityGap.SecondMomentExact

#print axioms ArkLib.ProximityGap.SecondMomentExact.sum_nonzero_sq
