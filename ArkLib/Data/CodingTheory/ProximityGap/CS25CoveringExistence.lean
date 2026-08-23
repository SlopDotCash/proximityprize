/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CoveringFromFarCount

/-!
# CS25 #82 covering existence: a covered, non-jointly-close stack from the count budget

The proven reduction `ProximityGap.one_le_epsCA_of_line_covered` needs a stack `u` that is BOTH
*line-covered* (`∀ γ, δᵣ(u 0 + γ • u 1, C) ≤ δ`) AND *not jointly `δ`-close*
(`¬ jointProximity C u δ`).  `exists_line_covered_stack_of_sum_far_lt` only delivers the first.

This file closes that gap with a combined pigeonhole: if the total far-line count plus the number
of jointly-close stacks is below the stack count, then a covered non-jointly-close stack exists,
hence `1 ≤ ε_ca(C, δ)`.  Combined with the double count `sum_card_far_eq`
(`∑_u #far γ = |F| · |ι → F| · |far|`), this reduces the CS25 T4.17 (#82) breakdown to the two
*band* counting inputs:

* the δ-neighbourhood-complement bound `|{w : δᵣ(w,C) > δ}|` (small in the entropy band), and
* the jointly-close-stack bound `|{u : jointProximity C u δ}|` (small in the entropy band).

These two remaining inputs are the genuine CS25 second-moment content (the `√((H_q(δ)-δ)/n)` term
of the band hypotheses); everything mechanical around them is now discharged here.
-/

open scoped NNReal ENNReal BigOperators

namespace ProximityGap

open Code Finset

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
omit [Nonempty ι] [DecidableEq F] in
/-- **Combined covering existence.** If the total number of "far" `γ` across all stacks plus the
number of jointly-`δ`-close stacks is strictly below the stack count, then some stack is *both*
line-covered and not jointly `δ`-close. -/
theorem exists_covered_not_jointProx_stack_of_counts (C : Set (ι → A)) (δ : ℝ≥0)
    (hsum :
      (∑ u : WordStack A (Fin 2) ι,
          (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ)).card)
        + (univ.filter (fun u : WordStack A (Fin 2) ι => jointProximity C u δ)).card
      < Fintype.card (WordStack A (Fin 2) ι)) :
    ∃ u : WordStack A (Fin 2) ι,
      (∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ δ) ∧ ¬ jointProximity C u δ := by
  classical
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ u, (∀ γ, δᵣ(u 0 + γ • u 1, C) ≤ δ) → jointProximity C u δ`
  set far : WordStack A (Fin 2) ι → ℕ :=
    fun u => (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ)).card with hfar
  -- partition the stacks into fully covered (`far = 0`) and the rest
  have hsplit :
      Fintype.card (WordStack A (Fin 2) ι)
        = (univ.filter (fun u : WordStack A (Fin 2) ι => far u = 0)).card
          + (univ.filter (fun u : WordStack A (Fin 2) ι => ¬ far u = 0)).card := by
    have h :=
      Finset.card_filter_add_card_filter_not
        (s := (univ : Finset (WordStack A (Fin 2) ι))) (p := fun u => far u = 0)
    simpa [Finset.card_univ] using h.symm
  -- the non-covered stacks contribute at least `1` each to `∑ far`
  have hfar_le :
      (univ.filter (fun u : WordStack A (Fin 2) ι => ¬ far u = 0)).card
        ≤ ∑ u : WordStack A (Fin 2) ι, far u := by
    rw [Finset.card_eq_sum_ones]
    refine le_trans (Finset.sum_le_sum (fun u hu => ?_))
      (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
    exact Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hu).2
  -- a fully-covered stack is jointly close (by `hcon`)
  have hcov_le :
      (univ.filter (fun u : WordStack A (Fin 2) ι => far u = 0)).card
        ≤ (univ.filter (fun u : WordStack A (Fin 2) ι => jointProximity C u δ)).card := by
    apply Finset.card_le_card
    intro u hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨hu.1, hcon u (fun γ => ?_)⟩
    have hempty : (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ)) = ∅ :=
      Finset.card_eq_zero.mp hu.2
    by_contra hγ
    exact (Finset.eq_empty_iff_forall_notMem.mp hempty γ)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ γ, hγ⟩)
  have hsum' :
      (∑ u : WordStack A (Fin 2) ι, far u)
        + (univ.filter (fun u : WordStack A (Fin 2) ι => jointProximity C u δ)).card
      < Fintype.card (WordStack A (Fin 2) ι) := by
    simpa [far] using hsum
  omega

open Classical in
/-- **`1 ≤ ε_ca` from the covering count budget (CS25 #82).** Wires the combined existence into
`one_le_epsCA_of_line_covered`. -/
theorem one_le_epsCA_of_counts (C : Set (ι → A)) (δ : ℝ≥0)
    (hsum :
      (∑ u : WordStack A (Fin 2) ι,
          (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ)).card)
        + (univ.filter (fun u : WordStack A (Fin 2) ι => jointProximity C u δ)).card
      < Fintype.card (WordStack A (Fin 2) ι)) :
    1 ≤ epsCA (F := F) C δ δ := by
  obtain ⟨u, hcov, hnj⟩ := exists_covered_not_jointProx_stack_of_counts C δ hsum
  exact one_le_epsCA_of_line_covered C δ δ u hnj hcov

end ProximityGap
