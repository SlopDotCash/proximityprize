/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# CS25 covering double-count (toward T4.17, issue #82)

`exists_line_covered_stack_of_sum_far_lt` (Errors.lean) reduces the CS25 complete-CA-breakdown
lower bound to the inequality `∑_u #{γ : line far} < #stacks`. This file proves the exact
double-count its docstring identifies as the remaining combinatorial content:

  `∑_{u : Fin 2 → ι → A} #{γ : Δᵣ(u 0 + γ • u 1, C) > δ}
      = |F| · |ι → A| · #{w : Δᵣ(w, C) > δ}`.

The proof is a Fubini swap plus, for each fixed `γ`, the *shear* bijection
`u ↦ (u 0 + γ • u 1, u 1)` on stacks (which carries the `γ`-line to the first row), followed by
the product split `∑_v g (v 0) = |ι → A| · ∑_w g w`.

Combined with `exists_line_covered_stack_of_sum_far_lt`, this turns the covering hypothesis into
the clean "few far words" budget `|F| · #{w far} < |ι → A|`, i.e. `#{w far} < |A|^n / |F|` — the
form the CS25 entropy/ball-count input must establish.
-/

open scoped NNReal
open Finset

set_option linter.unusedSectionVars false

namespace ProximityGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type*} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **CS25 covering double-count.** The total number of `(stack, γ)` pairs whose `γ`-line
`u 0 + γ • u 1` is *far* from `C` equals `|F| · |ι → A| · #{w far from C}`.
(`WordStack A (Fin 2) ι` is `Matrix (Fin 2) ι A`.) -/
theorem sum_far_card_eq (C : Set (ι → A)) (δ : ℝ≥0) :
    (∑ u : Matrix (Fin 2) ι A,
        (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ)).card)
      = Fintype.card F * Fintype.card (ι → A)
          * (univ.filter (fun w : ι → A => ¬ δᵣ(w, C) ≤ δ)).card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have key : ∀ γ : F,
      (∑ u : Matrix (Fin 2) ι A, if ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ then (1 : ℕ) else 0)
        = Fintype.card (ι → A)
            * (univ.filter (fun w : ι → A => ¬ δᵣ(w, C) ≤ δ)).card := by
    intro γ
    -- the shear bijection `u ↦ (u 0 + γ • u 1, u 1)`, carrying the `γ`-line to row 0
    let e : Matrix (Fin 2) ι A ≃ Matrix (Fin 2) ι A :=
      { toFun := fun u => ![u 0 + γ • u 1, u 1]
        invFun := fun v => ![v 0 - γ • v 1, v 1]
        left_inv := fun u => by funext i; fin_cases i <;> simp
        right_inv := fun v => by funext i; fin_cases i <;> simp }
    calc (∑ u : Matrix (Fin 2) ι A, if ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ then (1 : ℕ) else 0)
        = ∑ v : Matrix (Fin 2) ι A, if ¬ δᵣ(v 0, C) ≤ δ then (1 : ℕ) else 0 :=
          Equiv.sum_comp e (fun v => if ¬ δᵣ(v 0, C) ≤ δ then (1 : ℕ) else 0)
      _ = ∑ p : (ι → A) × (ι → A), if ¬ δᵣ(p.1, C) ≤ δ then (1 : ℕ) else 0 :=
          Fintype.sum_equiv (finTwoArrowEquiv (ι → A))
            (fun v => if ¬ δᵣ(v 0, C) ≤ δ then (1 : ℕ) else 0)
            (fun p => if ¬ δᵣ(p.1, C) ≤ δ then (1 : ℕ) else 0) (fun v => rfl)
      _ = Fintype.card (ι → A)
            * (univ.filter (fun w : ι → A => ¬ δᵣ(w, C) ≤ δ)).card := by
          rw [Finset.card_filter, Finset.mul_sum, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun x _ => ?_
          change (∑ _y : ι → A, if ¬ δᵣ(x, C) ≤ δ then (1 : ℕ) else 0)
            = Fintype.card (ι → A) * (if ¬ δᵣ(x, C) ≤ δ then (1 : ℕ) else 0)
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun γ _ => key γ), Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Finset.card_filter, mul_assoc]

/-! Combined with `exists_line_covered_stack_of_sum_far_lt`, `sum_far_card_eq` turns the pigeonhole
threshold `∑_u #{far γ} < |stacks| = |ι → A|²` into the clean budget `|F| · #{w far} < |ι → A|`
(i.e. `#{w far} < |A|^n / |F|`) — the exact "few far words" bound the CS25 entropy/ball-count
argument must supply for the T4.17 complete-breakdown lower bound. -/

end ProximityGap
