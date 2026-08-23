/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersectionGlobal

/-!
# CS25 #82, deliverable 2 (b/d): the coset identity

The Fourier/MacWilliams route to the second-moment tail.  The total ball-intersection over the code

  `T = ∑_{c∈C} I(c) = ∑_{c∈C} |B(0,δ) ∩ B(c,δ)|`

equals the number of **pairs in the ball whose difference lies in the code**:

  `T = #{(w,f) ∈ B(0,δ)² : w - f ∈ C}`,

via the reindexing `(c, w) ↦ (w, w - c)` together with `δᵣ(w, w - f) = δᵣ(f, 0)`.  This is the entry
point to `T = ∑_κ |B(0,δ) ∩ κ|²` (cosets) and the dual-code Fourier bound — the elegant replacement
for the ball-intersection multinomial.
-/

open scoped BigOperators ENNReal NNReal

namespace ArkLib.CS25

open Code Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- `δᵣ(w, w - f) = δᵣ(f, 0)`: the relative distance from `w` to `w - f` is the relative weight
of `f`. -/
theorem relHammingDist_self_sub (w f : ι → F) :
    relHammingDist w (w - f) = relHammingDist f (0 : ι → F) := by
  rw [relHammingDist_eq_sub w (w - f)]
  congr 1
  abel

/-- **Coset identity.** For a finite code `C`, the total ball-intersection `∑_{c∈C} I(c)` equals the
number of pairs of ball points whose difference lies in `C`. -/
theorem sum_jointCoverCount_eq_pairs (C : Finset (ι → F)) (δ : ℝ≥0) :
    (∑ c ∈ C, jointCoverCount δ (0 : ι → F) c)
      = ((Finset.univ ×ˢ Finset.univ).filter
          (fun wf : (ι → F) × (ι → F) =>
            (relHammingDist wf.1 (0 : ι → F) : ENNReal) ≤ (δ : ENNReal)
              ∧ (relHammingDist wf.2 (0 : ι → F) : ENNReal) ≤ (δ : ENNReal)
              ∧ wf.1 - wf.2 ∈ C)).card := by
  classical
  -- LHS = #{(c,w) : c ∈ C ∧ δᵣ(w,0) ≤ δ ∧ δᵣ(w,c) ≤ δ}
  have hLHS :
      (∑ c ∈ C, jointCoverCount δ (0 : ι → F) c)
        = ((C ×ˢ Finset.univ).filter
            (fun cw : (ι → F) × (ι → F) =>
              (relHammingDist cw.2 (0 : ι → F) : ENNReal) ≤ (δ : ENNReal)
                ∧ (relHammingDist cw.2 cw.1 : ENNReal) ≤ (δ : ENNReal))).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    unfold jointCoverCount
    rw [Finset.card_filter]
  rw [hLHS]
  -- reindex (c,w) ↦ (w, w - c)
  refine Finset.card_bij' (fun cw _ => (cw.2, cw.2 - cw.1)) (fun wf _ => (wf.1 - wf.2, wf.1))
    ?_ ?_ ?_ ?_
  · intro cw hcw
    rw [Finset.mem_filter, Finset.mem_product] at hcw
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨mem_univ _, mem_univ _⟩, hcw.2.1, ?_, ?_⟩
    · rw [← relHammingDist_eq_sub]; exact hcw.2.2
    · simpa using hcw.1.1
  · intro wf hwf
    rw [Finset.mem_filter, Finset.mem_product] at hwf
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hwf.2.2.2, mem_univ _⟩, hwf.2.1, ?_⟩
    · rw [relHammingDist_self_sub]; exact hwf.2.2.1
  · intro cw _; simp
  · intro wf _; simp

end ArkLib.CS25
