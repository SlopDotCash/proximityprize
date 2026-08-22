/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25CoveringCount

/-!
# CS25 covered-stack existence from the few-far-words budget (toward T4.17, #82)

Composes the proven pigeonhole `exists_line_covered_stack_of_sum_far_lt` with the covering
double-count `sum_far_card_eq` to obtain a single clean reduction: a fully line-covered stack
exists once `|F| · #{w far from C} < |ι → A|`. This is the crisp remaining target for the CS25
complete-CA-breakdown lower bound — the genuine open content is now exactly the "few far words"
budget `#{w far} < |A|^n / |F|`, which the qEntropy/RS-ball-count argument must supply.
-/

open scoped NNReal
open Finset

set_option linter.unusedSectionVars false

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Covered bad-line stack from the "few far words" budget.** If `|F| · #{w far from C} < |ι → A|`
then some stack `u` has its whole affine line `u 0 + γ • u 1` within distance `δ` of `C`. -/
theorem exists_line_covered_stack_of_far_lt (C : Set (ι → A)) (δ : ℝ≥0)
    (hbudget : Fintype.card F * (univ.filter (fun w : ι → A => ¬ δᵣ(w, C) ≤ δ)).card
        < Fintype.card (ι → A)) :
    ∃ u : Matrix (Fin 2) ι A, ∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ δ := by
  classical
  have hpos : 0 < Fintype.card (ι → A) :=
    Fintype.card_pos_iff.mpr (⟨fun _ => 0⟩ : Nonempty (ι → A))
  have hcard : Fintype.card (Matrix (Fin 2) ι A)
      = Fintype.card (ι → A) * Fintype.card (ι → A) :=
    (Fintype.card_congr (finTwoArrowEquiv (ι → A))).trans (Fintype.card_prod _ _)
  have hsum : (∑ u : Matrix (Fin 2) ι A,
      (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ)).card)
      < Fintype.card (Matrix (Fin 2) ι A) := by
    rw [sum_far_card_eq, hcard]
    calc Fintype.card F * Fintype.card (ι → A)
            * (univ.filter (fun w : ι → A => ¬ δᵣ(w, C) ≤ δ)).card
        = (Fintype.card F * (univ.filter (fun w : ι → A => ¬ δᵣ(w, C) ≤ δ)).card)
            * Fintype.card (ι → A) := by ring
      _ < Fintype.card (ι → A) * Fintype.card (ι → A) :=
          mul_lt_mul_of_pos_right hbudget hpos
  exact exists_line_covered_stack_of_sum_far_lt C δ hsum

open Classical in
/-- **Far = total − close.** Far and close words partition `ι → A`, so the far count is the
complement of the coverage count. This is the bridge that turns a coverage *lower* bound
`#{close} ≥ B` (the CS25 second-moment / entropy covered-fraction line, `card_close_ge_card_mul_vol`
/ `CS25CoveredFractionEntropy`) into the far *upper* bound `#{far} ≤ |ι→A| − B` that the `hfar`
budget (`exists_line_covered_stack_of_far_lt`) consumes — i.e. ingredient (a) of the CS25 breakdown
count. -/
theorem card_far_eq_card_sub_card_close (C : Set (ι → A)) (δ : ℝ≥0) :
    (Finset.univ.filter (fun w : ι → A => ¬ δᵣ(w, C) ≤ δ)).card
      = Fintype.card (ι → A)
        - (Finset.univ.filter (fun w : ι → A => δᵣ(w, C) ≤ δ)).card := by
  classical
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (ι → A))) (p := fun w : ι → A => δᵣ(w, C) ≤ δ)
  rw [Finset.card_univ] at h
  omega

/-- **Few-far-words budget from a coverage lower bound.** If the coverage `#{close} ≥ B` is large
enough that `|F| · (|ι→A| − B) < |ι→A|`, then some stack has a fully `δ`-covered affine line —
combining `card_far_eq_card_sub_card_close` with `exists_line_covered_stack_of_far_lt`. The CS25
entropy covered-fraction bound supplies such a `B` in the breakdown band. -/
theorem exists_line_covered_stack_of_close_ge (C : Set (ι → A)) (δ : ℝ≥0) (B : ℕ)
    (hclose : B ≤ (Finset.univ.filter (fun w : ι → A => δᵣ(w, C) ≤ δ)).card)
    (hbudget : Fintype.card F * (Fintype.card (ι → A) - B) < Fintype.card (ι → A)) :
    ∃ u : Matrix (Fin 2) ι A, ∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ δ := by
  refine exists_line_covered_stack_of_far_lt C δ (lt_of_le_of_lt ?_ hbudget)
  rw [card_far_eq_card_sub_card_close]
  exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hclose _)

open Classical in
/-- **CS25 count budget from coverage `B` and jointProx bound `J`.** Both ingredients of the CS25
breakdown count, assembled: given coverage `#{close} ≥ B` (ingredient a, the entropy
covered-fraction bound) and a jointly-close bound `#{jointProx} ≤ J` (ingredient b,
`card_jointProximity_le…`), the count budget `hsum` of
`rs_epsCA_breakdown_cs25_entropyBallLowerWitness_of_counts` follows from the single explicit numeric
inequality `|F|·|ι→A|·(|ι→A| − B) + J < #stacks`. This reduces the remaining T4.17 open math to that
one inequality (satisfiable on the sub-band `H_{q²}(δ) < 1−ρ`; see `CS25JointProxBound`). -/
theorem sum_far_plus_jointProx_lt_of_close_ge (C : Set (ι → A)) (δ : ℝ≥0) (B J : ℕ)
    (hclose : B ≤ (Finset.univ.filter (fun w : ι → A => δᵣ(w, C) ≤ δ)).card)
    (hjp : (Finset.univ.filter (fun u : Matrix (Fin 2) ι A =>
        Code.jointProximity (C := C) (u := u) δ)).card ≤ J)
    (hbudget : Fintype.card F * Fintype.card (ι → A) * (Fintype.card (ι → A) - B) + J
        < Fintype.card (Matrix (Fin 2) ι A)) :
    (∑ u : Matrix (Fin 2) ι A,
        (Finset.univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ)).card)
      + (Finset.univ.filter (fun u : Matrix (Fin 2) ι A =>
          Code.jointProximity (C := C) (u := u) δ)).card
      < Fintype.card (Matrix (Fin 2) ι A) := by
  rw [sum_far_card_eq, card_far_eq_card_sub_card_close]
  refine lt_of_le_of_lt (Nat.add_le_add ?_ hjp) hbudget
  exact mul_le_mul_left' (Nat.sub_le_sub_left hclose _) _

end ProximityGap
