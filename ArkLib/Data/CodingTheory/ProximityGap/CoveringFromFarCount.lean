/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-! # Double-count for the CS25 #82 covering averaging

`∑_u #{γ : Δᵣ(u 0 + γ • u 1, C) > δ} = |F| · |ι → F| · |far|`, via the per-`γ` shift equiv
`u ↦ (u 0 + γ • u 1, u 1)`.  Uses `Fintype.sum_equiv` (whose hypothesis is `rfl`, avoiding any
membership-iff) rather than a card bijection.  Combined with
`exists_line_covered_stack_of_sum_far_lt` this reduces #82's covering to the δ-neighbourhood
bound `|F| · |far| < |F|^{|ι|}`. -/

open scoped NNReal BigOperators

namespace ProximityGap

open Code Finset

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Shift equiv on stacks: `u ↦ (u 0 + γ • u 1, u 1)`. -/
def shiftEquiv (γ : F) : WordStack F (Fin 2) ι ≃ (ι → F) × (ι → F) where
  toFun u := (u 0 + γ • u 1, u 1)
  invFun p := ![p.1 - γ • p.2, p.2]
  left_inv u := by
    funext i
    fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, add_sub_cancel_right]
  right_inv p := by
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sub_add_cancel]

/-- For fixed `γ`: `#{u : far line point} = |far| · |ι → F|` (sum-based, via `shiftEquiv`). -/
theorem card_far_stacks_fixed_gamma (C : Set (ι → F)) (δ : ℝ≥0) (γ : F) :
    (univ.filter (fun u : WordStack F (Fin 2) ι => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ)).card
      = (univ.filter (fun w : ι → F => ¬ δᵣ(w, C) ≤ δ)).card * Fintype.card (ι → F) := by
  classical
  rw [card_filter]
  rw [Fintype.sum_equiv (shiftEquiv γ)
        (fun u => if ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ then (1 : ℕ) else 0)
        (fun p => if ¬ δᵣ(p.1, C) ≤ δ then (1 : ℕ) else 0) (fun u => rfl)]
  rw [Fintype.sum_prod_type]
  have hb : ∀ a : ι → F,
      (∑ _b : ι → F, if ¬ δᵣ(a, C) ≤ δ then (1 : ℕ) else 0)
        = (if ¬ δᵣ(a, C) ≤ δ then (1 : ℕ) else 0) * Fintype.card (ι → F) := by
    intro a
    rw [Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul, mul_comm]
  simp_rw [hb]
  rw [← Finset.sum_mul, ← card_filter]

/-- Double-count: `∑_u #{far γ} = |F| · |ι → F| · |far|`. -/
theorem sum_card_far_eq (C : Set (ι → F)) (δ : ℝ≥0) :
    (∑ u : WordStack F (Fin 2) ι,
        (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ)).card)
      = Fintype.card F *
          (Fintype.card (ι → F) * (univ.filter (fun w : ι → F => ¬ δᵣ(w, C) ≤ δ)).card) := by
  classical
  simp only [card_filter]
  rw [Finset.sum_comm]
  have h : ∀ γ : F,
      (∑ u : WordStack F (Fin 2) ι, if ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ then 1 else 0)
        = (univ.filter (fun w : ι → F => ¬ δᵣ(w, C) ≤ δ)).card * Fintype.card (ι → F) := by
    intro γ
    rw [← card_far_stacks_fixed_gamma C δ γ, card_filter]
  simp_rw [h]
  rw [Finset.sum_const, card_univ]
  simp [nsmul_eq_mul, mul_comm, mul_assoc]

end ProximityGap
