/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentPairCount

/-!
# Distance-dependent shell bound for the ball-intersection count (toward T4.17, #82)

The CS25 breakdown's far/coverage half needs a `ballInterCount(r, v)` bound that *decreases* with the
pair distance `wt(v)` — the in-tree bounds being only the vanishing `wt(v) > 2r ⇒ 0`
(`ballInterCount_eq_zero_of_lt`) and the loose `≤ V` (`ballInterCount_le`), which make the second
moment as loose as the first moment.

This file proves the first genuinely distance-dependent bound: the two-ball intersection lies inside
a **shell**. Any `x ∈ B(0,r) ∩ B(v,r)` has `dist(x,0) ≥ wt(v) − r` (triangle inequality:
`wt(v) = dist(0,v) ≤ dist(0,x) + dist(x,v) ≤ dist(x,0) + r`), so

  `ballInterCount(r, v) ≤ #{x : dist(x,0) ≤ r ∧ wt(v) ≤ dist(x,0) + r}`,

i.e. the intersection is confined to the Hamming shell `wt(v) − r ≤ dist(x,0) ≤ r`. The shell
bound is **nonincreasing** in `wt(v)`, but not strictly: for every `wt(v) ≤ r` the condition
`wt(v) ≤ dist(x,0) + r` holds for all `x ∈ B(0,r)`, so the shell is the entire ball and the bound
equals the loose `V`. Only for `r < wt(v)` does it drop below `V` (the point `x = 0` is excluded),
and as `wt(v)` grows toward `2r` the inner radius `wt(v) − r` rises to `r`, thinning the shell to
a sphere. This weak distance dependence is an input to, not a proof of, the tight second-moment
estimate (and CS25's `√`-deviation term), which still needs the quantitative shell/enumerator
analysis.
-/

open scoped BigOperators

namespace ArkLib.CS25

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Shell containment of the ball intersection.** `B(0,r) ∩ B(v,r)` lies in the Hamming shell
`wt(v) − r ≤ dist(·,0) ≤ r`, so `ballInterCount(r,v) ≤ #{x : dist(x,0) ≤ r ∧ wt(v) ≤ dist(x,0)+r}`. -/
theorem ballInterCount_le_shell (r : ℕ) (v : ι → F) :
    ballInterCount r v
      ≤ (Finset.univ.filter (fun x : ι → F =>
          hammingDist x 0 ≤ r ∧ hammingDist (0 : ι → F) v ≤ hammingDist x 0 + r)).card := by
  unfold ballInterCount
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨h0, hv⟩ := hx
  refine ⟨h0, ?_⟩
  calc hammingDist (0 : ι → F) v
      ≤ hammingDist (0 : ι → F) x + hammingDist x v := hammingDist_triangle _ _ _
    _ = hammingDist x 0 + hammingDist x v := by rw [hammingDist_comm]
    _ ≤ hammingDist x 0 + r := by omega

/-- **Explicit distance dependence.** The ball-intersection count plus the *inner-exclusion* count
`#{x ∈ B(0,r) : dist(x,0) + r < wt(v)}` is at most the full ball volume `V = #B(0,r)`. The
inner-exclusion count is nondecreasing in `wt(v)` (`innerExclusionMonotonicity`), so this exhibits
`ballInterCount(r,v) ≤ V − (nondecreasing-in-wt(v))`, a weakly sharper replacement for the loose
`ballInterCount ≤ V`. It is not strictly decreasing: the exclusion count is `0` for all
`wt(v) ≤ r` (e.g. `n = 2`, `r = 1` over `F₂`: centers of weight `0` and `1` both give exclusion
`0` and bound `3 = V`), and it improves on `V` only once `wt(v) > r`. -/
theorem ballInterCount_add_inner_le_ball (r : ℕ) (v : ι → F) :
    ballInterCount r v
      + ((Finset.univ.filter (fun x : ι → F => hammingDist x 0 ≤ r)).filter
          (fun x : ι → F => ¬ hammingDist (0 : ι → F) v ≤ hammingDist x 0 + r)).card
      ≤ (Finset.univ.filter (fun x : ι → F => hammingDist x 0 ≤ r)).card := by
  have hshell := ballInterCount_le_shell r v
  have hpart := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun x : ι → F => hammingDist x 0 ≤ r))
    (p := fun x : ι → F => hammingDist (0 : ι → F) v ≤ hammingDist x 0 + r)
  have hshell' : ballInterCount r v
      ≤ ((Finset.univ.filter (fun x : ι → F => hammingDist x 0 ≤ r)).filter
          (fun x : ι → F => hammingDist (0 : ι → F) v ≤ hammingDist x 0 + r)).card := by
    refine hshell.trans (le_of_eq ?_)
    rw [Finset.filter_filter]
  omega

end ArkLib.CS25
