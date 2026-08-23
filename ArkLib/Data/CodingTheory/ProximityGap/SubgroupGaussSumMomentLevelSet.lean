/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# All-moments frequency concentration for the subgroup Gauss sum (#389)

Generalizes `SubgroupGaussSumLevelSet` (the `r=1` second-moment Markov bound) to every band, using
the moment bridge `∑_b ‖η_b‖^{2r} = q·E_r(G)` (`SubgroupGaussSumMoment`):

> **`card_high_frequency_moment_le`** — `#{b : ‖η_b‖^{2r} ≥ T} · T ≤ q · E_r(G)`.

So at most `q·E_r/T` frequencies have `‖η_b‖^{2r} ≥ T`. With `T = λ·|G|^r` and `E_r = O(|G|^r)` (the
all-bands supply bound), this says all but a `q/λ`-fraction of frequencies obey `|η_b| ≤ (λ)^{1/2r}√|G|`
— and higher bands `r` give sharper tail control of the worst-case incomplete sum (the δ\* interior
residual). Axiom-clean. Issue #389.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumMomentLevelSet

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **All-moments Markov level-set bound.** At most `q·E_r/T` frequencies have `‖η_b‖^{2r} ≥ T`. -/
theorem card_high_frequency_moment_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (r : ℕ) (T : ℝ) :
    ((Finset.univ.filter (fun b => T ≤ ‖eta ψ G b‖ ^ (2 * r))).card : ℝ) * T
      ≤ (Fintype.card F : ℝ) * rEnergy G r := by
  set S := Finset.univ.filter (fun b => T ≤ ‖eta ψ G b‖ ^ (2 * r)) with hS
  have h1 : (S.card : ℝ) * T = ∑ _b ∈ S, T := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ _b ∈ S, T ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * r) :=
    Finset.sum_le_sum (fun b hb => (Finset.mem_filter.mp hb).2)
  have h3 : ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * r) ≤ ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b _ _ => by positivity)
  rw [h1]
  calc ∑ _b ∈ S, T
      ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * r) := h2
    _ ≤ ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) := h3
    _ = (Fintype.card F : ℝ) * rEnergy G r := subgroup_gaussSum_moment hψ G r

end ArkLib.ProximityGap.SubgroupGaussSumMomentLevelSet

#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentLevelSet.card_high_frequency_moment_le
