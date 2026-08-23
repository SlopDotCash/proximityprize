/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# The DC-subtracted Gauss-period moment (#407)

The full `2r`-th moment is `∑_{b∈F} ‖η_b‖^{2r} = q·E_r(G)` (`subgroup_gaussSum_moment`). The prize
object is the NON-trivial part `A_r := (1/q)∑_{b≠0} ‖η_b‖^{2r}` — the `b=0` (DC) term `‖η_0‖^{2r} =
|G|^{2r}` must be removed, since `M(n)=max_{b≠0}‖η_b‖` and `M^{2r} ≤ ∑_{b≠0}‖η_b‖^{2r}`.

> **`sum_nonzero_moment`** — `∑_{b≠0} ‖η_b‖^{2r} = q·E_r(G) − |G|^{2r}`.

This is the exact identity separating the char-free energy from the anomaly: dividing by `q`,
`A_r = E_r(G) − |G|^{2r}/q`, and the open prize bound `A_r ≤ (2r−1)‼·|G|^r` ⟺ `Anom_r ≤ |G|^{2r}/q`.

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.DCSubtractedMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The DC (`b=0`) Gauss period is exactly `|G|`: `η_0 = ∑_{y∈G} ψ(0) = |G|`. -/
theorem eta_zero (ψ : AddChar F ℂ) (G : Finset F) : eta ψ G 0 = (G.card : ℂ) := by
  simp [eta]

/-- **DC-subtracted moment identity.** `∑_{b≠0} ‖η_b‖^{2r} = q·E_r(G) − |G|^{2r}`. Removing the DC term
isolates the prize object `A_r = (1/q)∑_{b≠0}‖η_b‖^{2r}` that controls `M(n)=max_{b≠0}‖η_b‖`. -/
theorem sum_nonzero_moment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
      = (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
  have hfull : ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) = (Fintype.card F : ℝ) * (rEnergy G r : ℝ) :=
    subgroup_gaussSum_moment hψ G r
  have hdc : ‖eta ψ G 0‖ ^ (2 * r) = (G.card : ℝ) ^ (2 * r) := by
    rw [eta_zero]; simp
  have hsplit : ∑ b : F, ‖eta ψ G b‖ ^ (2 * r)
      = ‖eta ψ G 0‖ ^ (2 * r) + ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) :=
    (Finset.add_sum_erase univ _ (Finset.mem_univ 0)).symm
  rw [hfull, hdc] at hsplit
  linarith [hsplit]

end ArkLib.ProximityGap.DCSubtractedMoment

#print axioms ArkLib.ProximityGap.DCSubtractedMoment.sum_nonzero_moment
