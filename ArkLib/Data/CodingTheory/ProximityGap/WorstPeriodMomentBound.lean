/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMomentLadder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option linter.style.longLine false

/-!
# The moment-method sup-norm bound on the worst subgroup Gaussian period (#389)

The exact handle the moment ladder gives on the WORST (sup-norm) Gaussian period. From
`subgroup_gaussSum_moment` (`∑_b ‖η_b‖^{2r} = q·E_r(G)`) peel off the trivial frequency
`b=0` (where `η_0 = |G|`, so `‖η_0‖^{2r} = |G|^{2r}`); every other single term is bounded by the
remaining sum:

> `worst_period_moment_le` :  for `b ≠ 0`,  `‖η_b‖^{2r} ≤ q·E_r(G) − |G|^{2r}`.

Taking `2r`-th roots, `max_{b≠0} ‖η_b‖ ≤ (q·E_r(G) − |G|^{2r})^{1/(2r)}` — the moment-method upper
bound on the sup-norm of the periods, valid for every `r ≥ 1`. With the exact `E_r` (char-0 walk
count, available for `q > (2r)^{φ(n)}` via the resultant lift) this is the route to the dyadic
square-root-cancellation bound; here we land the exact per-frequency inequality, which holds for ALL
`q` and any finite domain `G`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

namespace ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- The trivial frequency: `η_0 = ∑_{y∈G} ψ(0) = |G|`. -/
theorem eta_zero_eq_card (ψ : AddChar F ℂ) (G : Finset F) :
    eta ψ G 0 = (G.card : ℂ) := by
  simp [eta, AddChar.map_zero_eq_one]

/-- **The moment-method per-frequency bound.** For every nontrivial frequency `b ≠ 0` and every
`r`, the `2r`-th power of the Gaussian period is bounded by the total `2r`-th moment minus the
trivial term: `‖η_b‖^{2r} ≤ q·E_r(G) − |G|^{2r}`. (Hence `max_{b≠0}‖η_b‖ ≤ (q·E_r − |G|^{2r})^{1/2r}`,
the moment-method sup-norm bound on the worst subgroup period.) -/
theorem worst_period_moment_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r) := by
  classical
  have hmoment := subgroup_gaussSum_moment hψ G r
  -- the trivial term contributes |G|^{2r}
  have h0 : ‖eta ψ G (0 : F)‖ ^ (2 * r) = (G.card : ℝ) ^ (2 * r) := by
    rw [eta_zero_eq_card]; rw [Complex.norm_natCast]
  -- {b, 0} ⊆ univ and the summand is nonnegative, so ‖η_b‖^{2r} + ‖η_0‖^{2r} ≤ ∑_b ‖η_b‖^{2r}
  have hpair : ‖eta ψ G b‖ ^ (2 * r) + ‖eta ψ G (0 : F)‖ ^ (2 * r)
      ≤ ∑ x : F, ‖eta ψ G x‖ ^ (2 * r) := by
    have hsub : ({b, 0} : Finset F) ⊆ Finset.univ := Finset.subset_univ _
    have hle : ∑ x ∈ ({b, 0} : Finset F), ‖eta ψ G x‖ ^ (2 * r)
        ≤ ∑ x : F, ‖eta ψ G x‖ ^ (2 * r) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by positivity)
    rwa [Finset.sum_pair hb] at hle
  rw [hmoment] at hpair
  rw [h0] at hpair
  linarith
end ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentLadder.worst_period_moment_le
