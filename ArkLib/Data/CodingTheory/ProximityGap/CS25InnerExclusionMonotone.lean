/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallInterShell

/-!
# Monotonicity of the inner-exclusion count (#389, CS25 second-moment lane)

`ballInterCount_add_inner_le_ball` exhibits `ballInterCount(r,v) ≤ V − (inner-exclusion count)`,
where the inner-exclusion count is `#{x ∈ B(0,r) : dist(x,0)+r < wt(v)}`.  This file names that count
(`innerExclusionCount`) and proves it is **monotone increasing in the center weight** `wt(v)`:
as the two centers separate, more of the ball is excluded.  This is the strictly decreasing
distance dependence the tight second-moment estimate needs, replacing the loose `ballInterCount ≤ V`.
-/

set_option linter.unusedSectionVars false


open scoped BigOperators

namespace ArkLib.CS25

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- The inner-exclusion count `#{x ∈ B(0,r) : dist(x,0)+r < wt(v)}` appearing in
`ballInterCount_add_inner_le_ball`. -/
def innerExclusionCount (r : ℕ) (v : ι → F) : ℕ :=
  ((Finset.univ.filter (fun x : ι → F => hammingDist x 0 ≤ r)).filter
    (fun x : ι → F => ¬ hammingDist (0 : ι → F) v ≤ hammingDist x 0 + r)).card

/-- **Monotonicity of the inner-exclusion count in the center weight.** As `wt(v)` grows, more of
the ball `B(0,r)` is excluded, so `innerExclusionCount` increases — the strictly decreasing distance
dependence the tight second-moment estimate needs. -/
theorem innerExclusionMonotonicity (r : ℕ) (v₁ v₂ : ι → F)
    (hw : hammingDist (0 : ι → F) v₁ ≤ hammingDist (0 : ι → F) v₂) :
    innerExclusionCount r v₁ ≤ innerExclusionCount r v₂ := by
  unfold innerExclusionCount
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨h0, hv⟩ := hx
  exact ⟨h0, by omega⟩

end ArkLib.CS25
