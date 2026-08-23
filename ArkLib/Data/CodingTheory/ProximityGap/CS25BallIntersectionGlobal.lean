/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersection

/-!
# CS25 #82, deliverable 2 (b/d): the global ball-intersection sum

`∑_{e} I(e) = V²` — the total ball-intersection over **all** difference vectors equals the squared
ball volume `V = #{w : δᵣ(w,0) ≤ δ}`.  (Fubini: `∑_e #{w : w,w-e both δ-close to 0}` =
`∑_{w δ-close} #{e : w δ-close to e}` = `∑_{w δ-close} V` by translation.)

This is the *global normalization* of the second moment: the Reed–Solomon restriction
`∑_{e∈RS} I(e)` is compared against this total — equidistribution `∑_{e∈RS} I(e) ≈ (|RS|/|F^ι|)·V²`
is exactly the CS25 concentration that the entropy band [d] controls.
-/

open scoped BigOperators ENNReal NNReal

namespace ArkLib.CS25

open Code Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- `δᵣ(a,b) = δᵣ(a-b, 0)`. -/
theorem relHammingDist_eq_sub (a b : ι → F) :
    relHammingDist a b = relHammingDist (a - b) (0 : ι → F) := by
  rw [← relHammingDist_sub_sub a b b, sub_self]

/-- The `δ`-ball around any center `w` has the same size as the ball around `0`. -/
theorem card_rball_eq (w : ι → F) (δ : ℝ≥0) :
    (univ.filter (fun e : ι → F => (relHammingDist w e : ENNReal) ≤ (δ : ENNReal))).card
      = (univ.filter (fun f : ι → F =>
          (relHammingDist f (0 : ι → F) : ENNReal) ≤ (δ : ENNReal))).card := by
  classical
  refine Finset.card_bij' (fun e _ => w - e) (fun f _ => w - f) ?_ ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    refine ⟨mem_univ _, ?_⟩
    have h : relHammingDist (w - e) (0 : ι → F) = relHammingDist w e :=
      (relHammingDist_eq_sub w e).symm
    rw [h]; exact he.2
  · intro f hf
    rw [Finset.mem_filter] at hf ⊢
    refine ⟨mem_univ _, ?_⟩
    have h : relHammingDist w (w - f) = relHammingDist f (0 : ι → F) := by
      rw [relHammingDist_eq_sub w (w - f)]; congr 1; abel
    rw [h]; exact hf.2
  · intro e _; simp
  · intro f _; simp

/-- **Global ball-intersection sum.** `∑_{e} I(e) = V²` with `V = #{w : δᵣ(w,0) ≤ δ}`. -/
theorem sum_jointCoverCount_eq_volume_sq (δ : ℝ≥0) :
    (∑ e : ι → F, jointCoverCount δ (0 : ι → F) e)
      = (univ.filter (fun w : ι → F =>
            (relHammingDist w (0 : ι → F) : ENNReal) ≤ (δ : ENNReal))).card
        * (univ.filter (fun w : ι → F =>
            (relHammingDist w (0 : ι → F) : ENNReal) ≤ (δ : ENNReal))).card := by
  classical
  have hcc : ∀ e : ι → F, jointCoverCount δ (0 : ι → F) e
      = ∑ w : ι → F, (if (relHammingDist w (0 : ι → F) : ENNReal) ≤ (δ : ENNReal)
            ∧ (relHammingDist w e : ENNReal) ≤ (δ : ENNReal) then 1 else 0) := by
    intro e; rw [jointCoverCount, Finset.card_filter]
  simp_rw [hcc]
  rw [Finset.sum_comm]
  -- ∑_w ∑_e (if P w ∧ Q w e then 1 else 0)
  have hpt : ∀ w : ι → F,
      (∑ e : ι → F, if (relHammingDist w (0 : ι → F) : ENNReal) ≤ (δ : ENNReal)
            ∧ (relHammingDist w e : ENNReal) ≤ (δ : ENNReal) then 1 else 0)
        = if (relHammingDist w (0 : ι → F) : ENNReal) ≤ (δ : ENNReal)
            then (univ.filter (fun f : ι → F =>
                (relHammingDist f (0 : ι → F) : ENNReal) ≤ (δ : ENNReal))).card else 0 := by
    intro w
    by_cases hP : (relHammingDist w (0 : ι → F) : ENNReal) ≤ (δ : ENNReal)
    · simp only [hP, true_and, if_true]
      rw [← Finset.card_filter, card_rball_eq w δ]
    · simp [hP]
  simp_rw [hpt]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

end ArkLib.CS25
