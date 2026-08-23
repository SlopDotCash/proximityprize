/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# CS25 #82, deliverable 2 (a): the second moment as `|RS|·∑_e I(e)`

The joint `δ`-cover count of two centers `c, c'`,
`jointCoverCount δ c c' = #{w : δᵣ(w,c) ≤ δ ∧ δᵣ(w,c') ≤ δ} = |B(c,δ) ∩ B(c',δ)|`,
is **translation invariant**: it depends only on `c' - c`.  Hence summed over a linear code's pairs
it collapses to `|RS| · ∑_{e ∈ RS} I(e)` with `I(e) = jointCoverCount δ 0 e` — the ball-intersection
form of the CS25 second moment `E[N²]`.
-/

open scoped BigOperators ENNReal NNReal

namespace ArkLib.CS25

open Code

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- Hamming distance is invariant under a common translation of both arguments. -/
theorem hammingDist_sub_sub (w c c' : ι → F) :
    hammingDist (w - c) (c' - c) = hammingDist w c' := by
  unfold hammingDist
  congr 1
  ext i
  simp [Pi.sub_apply, sub_left_inj]

/-- Relative Hamming distance is invariant under a common translation. -/
theorem relHammingDist_sub_sub (w c c' : ι → F) :
    relHammingDist (w - c) (c' - c) = relHammingDist w c' := by
  unfold relHammingDist
  rw [hammingDist_sub_sub]

/-- The joint `δ`-cover count of two centers: `|B(c,δ) ∩ B(c',δ)|`. -/
noncomputable def jointCoverCount (δ : ℝ≥0) (c c' : ι → F) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w : ι → F =>
    (relHammingDist w c : ENNReal) ≤ (δ : ENNReal)
      ∧ (relHammingDist w c' : ENNReal) ≤ (δ : ENNReal))).card

/-- **Translation invariance.** The joint cover count depends only on the difference `c' - c`. -/
theorem jointCoverCount_translation (δ : ℝ≥0) (c c' : ι → F) :
    jointCoverCount δ c c' = jointCoverCount δ 0 (c' - c) := by
  classical
  unfold jointCoverCount
  refine Finset.card_bij (fun w _ => w - c) ?_ ?_ ?_
  · -- maps into the (0, c'-c) ball
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have h : relHammingDist (w - c) (0 : ι → F) = relHammingDist w c := by
        rw [← relHammingDist_sub_sub w c c, sub_self]
      rw [h]; exact hw.2.1
    · rw [relHammingDist_sub_sub w c c']; exact hw.2.2
  · -- injective
    intro a _ b _ hab
    exact sub_left_inj.mp hab
  · -- surjective
    intro v hv
    rw [Finset.mem_filter] at hv
    refine ⟨v + c, ?_, by abel⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have h : relHammingDist (v + c) c = relHammingDist v (0 : ι → F) := by
        rw [← relHammingDist_sub_sub (v + c) c c]; congr 1 <;> abel
      rw [h]; exact hv.2.1
    · have h : relHammingDist (v + c) c' = relHammingDist v (c' - c) := by
        rw [← relHammingDist_sub_sub (v + c) c c']; congr 1 <;> abel
      rw [h]; exact hv.2.2

end ArkLib.CS25
