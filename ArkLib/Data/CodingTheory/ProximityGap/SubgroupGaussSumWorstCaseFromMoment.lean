/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# The worst-case subgroup character sum is bounded by every moment (#389)

The dual direction to `SubgroupGaussSumMomentBound.rEnergy_le`: since `‖η_b‖^{2r}` is one nonneg
term of `∑_{b'} ‖η_{b'}‖^{2r} = q·E_r(G)` (`SubgroupGaussSumMoment`),

> **`eta_pow_le_moment`** — for every `b`, `‖η_b‖^{2r} ≤ q · E_r(G)`.

Hence `max_b ‖η_b‖ ≤ (q·E_r)^{1/2r}`: the worst-case incomplete character sum (the δ\* interior
residual) is controlled by *any* band's energy. Together with `rEnergy_le` (energy bounded by the
worst case), this pins the equivalence `max_{b≠0}|η_b| ≤ C√|G| ⟺ E_r = O(|G|^r)` — the Bourgain
bound and the all-bands supply bound are the same open object. Axiom-clean. Issue #389.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumWorstCase2

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The worst case is bounded by every moment.** `‖η_b‖^{2r} ≤ q · E_r(G)` for all `b`. -/
theorem eta_pow_le_moment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (b : F) (r : ℕ) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * rEnergy G r := by
  rw [← subgroup_gaussSum_moment hψ G r]
  exact Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * r))
    (fun i _ => by positivity) (Finset.mem_univ b)

end ArkLib.ProximityGap.SubgroupGaussSumWorstCase2

#print axioms ArkLib.ProximityGap.SubgroupGaussSumWorstCase2.eta_pow_le_moment
