/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds
import ArkLib.Data.CodingTheory.ProximityGap.CoveringFromFarCount

/-!
# CS25 #82: the complete breakdown from the single-word far count

`rs_epsCA_breakdown_cs25_of_counts` (CapacityBounds.lean) discharges the CS25 T4.17 residual
`ε_ca(RS, δ) = 1` from the *stack*-level count budget
`(∑_u #{γ : far}) + #{u : jointProx} < #stacks`.

This file re-expresses that budget in the **single-word** form the CS25 covering argument actually
targets, using the proven double count `sum_card_far_eq`
(`∑_u #{γ : far γ} = |F| · |ι→F| · |{w : δᵣ(w,C) > δ}|`):

  `|F| · |ι→F| · |{w : δᵣ(w, RS) > δ}| + #{u : jointProx} < #stacks  ⟹  ε_ca(RS, δ) = 1`.

The remaining mathematical input is now a statement purely about *words*: the δ-neighbourhood of the
Reed–Solomon code covers all but a `< 1/|F|` fraction of `(ι → F)` in the CS25 entropy band — the
genuine second-moment / covering content (`E[N²]` via the MDS ball-intersection analysis), which the
covered-set machinery (`SupportSqBound`, `CS25SecondMomentReduction`, `RSVanishingDim`) feeds.
-/

open scoped NNReal ProbabilityTheory BigOperators

namespace CodingTheory

open ProximityGap Code Finset

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **CS25 complete breakdown from the single-word far count.** If the number of words beyond
relative distance `δ` from the Reed–Solomon code, scaled by `|F| · |ι→F|`, plus the number of
jointly-`δ`-close stacks, is below the stack count, then `ε_ca(RS, δ) = 1`. -/
theorem rs_epsCA_breakdown_cs25_of_far_count
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hfar :
      Fintype.card F *
          (Fintype.card (ι → F) *
            (univ.filter (fun w : ι → F =>
              ¬ δᵣ(w, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ)).card)
        + (univ.filter (fun u : Code.WordStack F (Fin 2) ι =>
            Code.jointProximity (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ)).card
      < Fintype.card (Code.WordStack F (Fin 2) ι)) :
    rs_epsCA_breakdown_cs25 domain k δ hq_ge hδ_lo hδ_hi := by
  refine rs_epsCA_breakdown_cs25_of_counts domain k δ hq_ge hδ_lo hδ_hi ?_
  rw [sum_card_far_eq]
  exact hfar

end CodingTheory
