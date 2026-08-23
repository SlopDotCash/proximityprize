/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Non-degenerate covering pigeonhole (toward T4.17, #82)

`exists_line_covered_stack_of_sum_far_lt` (Errors.lean) produces a fully line-covered stack from a
"few far γ" budget, but says nothing about joint proximity — and `one_le_epsCA_of_line_covered`
needs a covered stack that is *also not jointly close*.

This file proves the refined pigeonhole that supplies exactly that: if the far-`γ` count plus the
number of jointly-`δ_int`-close stacks together stay below the stack count, then some stack is
**covered and not jointly close**:

  `(∑_u #{far γ}) + #{u : jointProximity u δ_int} < #stacks
      → ∃ u, ¬ jointProximity u δ_int ∧ (∀ γ, Δᵣ(u 0 + γ • u 1, C) ≤ δ_fld)`.

Combined with the CS25 second-moment coverage lower bound (`#{far} small`, the
`CS25SecondMomentHighDist` / `CS25RSCoveredFraction` line) and an upper bound on the
jointly-close count (coverage of the interleaved code `C^⋈`), this is the final assembly step that
discharges the CS25 complete-CA-breakdown lower bound `1 ≤ ε_ca` (T4.17) via
`one_le_epsCA_of_line_covered`.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **Refined covering pigeonhole.** If the total number of far `(stack, γ)` pairs plus the number
of jointly-`δ_int`-close stacks is strictly below the stack count, then some stack `u` is both not
jointly `δ_int`-close to `C` and has its whole affine line `u 0 + γ • u 1` within `δ_fld` of `C`. -/
theorem exists_line_covered_not_jointly_close_of_counts (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0)
    (h : (∑ u : Matrix (Fin 2) ι A,
            (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ_fld)).card)
          + (univ.filter (fun u : Matrix (Fin 2) ι A =>
              Code.jointProximity (C := C) (u := u) δ_int)).card
          < Fintype.card (Matrix (Fin 2) ι A)) :
    ∃ u : Matrix (Fin 2) ι A,
      ¬ Code.jointProximity (C := C) (u := u) δ_int
        ∧ ∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ δ_fld := by
  classical
  by_contra hcon
  push_neg at hcon
  -- every stack is jointly close or carries a far `γ`
  have key : ∀ u : Matrix (Fin 2) ι A,
      (1 : ℕ) ≤ (if Code.jointProximity (C := C) (u := u) δ_int then 1 else 0)
        + (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ_fld)).card := by
    intro u
    by_cases hJP : Code.jointProximity (C := C) (u := u) δ_int
    · rw [if_pos hJP]; omega
    · obtain ⟨γ, hγ⟩ := hcon u hJP
      have hpos : 1 ≤ (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ_fld)).card := by
        refine Finset.card_pos.mpr ⟨γ, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact not_le.mpr hγ
      omega
  have hsum :
      (∑ u : Matrix (Fin 2) ι A,
          ((if Code.jointProximity (C := C) (u := u) δ_int then 1 else 0)
            + (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ_fld)).card))
        = (univ.filter (fun u : Matrix (Fin 2) ι A =>
              Code.jointProximity (C := C) (u := u) δ_int)).card
          + ∑ u : Matrix (Fin 2) ι A,
              (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ_fld)).card := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.card_filter]
  have hge : Fintype.card (Matrix (Fin 2) ι A)
      ≤ ∑ u : Matrix (Fin 2) ι A,
          ((if Code.jointProximity (C := C) (u := u) δ_int then 1 else 0)
            + (univ.filter (fun γ : F => ¬ δᵣ(u 0 + γ • u 1, C) ≤ δ_fld)).card) := by
    rw [Fintype.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun u _ => key u)
  rw [hsum] at hge
  omega

end ProximityGap
