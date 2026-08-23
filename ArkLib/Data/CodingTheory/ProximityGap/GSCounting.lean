/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Push

/-! # Heavy-coordinate pigeonhole (consumable for GS / Johnson list-decoding)

Double-counting + averaging: if each of `|κ|` rows of an incidence relation `M`
has at least `a` marked columns, some column is marked by at least the average
`a·|κ|/|ι|` rows — i.e. `|κ|·a ≤ |ι|·(that column's count)`. This is the
"heavy coordinate" step behind the matching-coverage / Johnson list-size counting:
many codewords agreeing with a word on `≥a` positions each force a position where
many of them coincide. Mathlib-only, fully general. -/

namespace GSCounting

open Finset

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- **Row–column double counting.** The total over rows of per-row marked-column
counts equals the total over columns of per-column marked-row counts. -/
theorem sum_rows_eq_sum_cols (M : κ → ι → Prop) [∀ k x, Decidable (M k x)] :
    ∑ k : κ, (Finset.univ.filter (fun x => M k x)).card
      = ∑ x : ι, (Finset.univ.filter (fun k => M k x)).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

/-- **Heavy coordinate.** If every row has `≥ a` marked columns, some column `x`
satisfies `|κ| · a ≤ |ι| · (#rows marking x)`. -/
theorem exists_heavy_coordinate (M : κ → ι → Prop) [∀ k x, Decidable (M k x)]
    {a : ℕ} (hrow : ∀ k, a ≤ (Finset.univ.filter (fun x => M k x)).card)
    (hι : 0 < Fintype.card ι) :
    ∃ x : ι, Fintype.card κ * a ≤
      Fintype.card ι * (Finset.univ.filter (fun k => M k x)).card := by
  classical
  -- total column count ≥ |κ|·a
  have htot : Fintype.card κ * a ≤ ∑ x : ι, (Finset.univ.filter (fun k => M k x)).card := by
    rw [← sum_rows_eq_sum_cols]
    calc Fintype.card κ * a = ∑ _k : κ, a := by
            rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
      _ ≤ ∑ k : κ, (Finset.univ.filter (fun x => M k x)).card :=
        Finset.sum_le_sum (fun k _ => hrow k)
  -- averaging: some column ≥ average, i.e. |ι|·(col x) ≥ Σ ≥ |κ|·a
  by_contra hcon
  push Not at hcon
  -- every column has |ι|·count < |κ|·a, so the sum is < |ι|·(|κ|·a)... derive contradiction
  have hbound : ∀ x : ι, Fintype.card ι * (Finset.univ.filter (fun k => M k x)).card
      < Fintype.card κ * a := hcon
  have hsum_lt : Fintype.card ι * (∑ x : ι, (Finset.univ.filter (fun k => M k x)).card)
      < Fintype.card ι * (Fintype.card κ * a) := by
    rw [Finset.mul_sum]
    calc ∑ x : ι, Fintype.card ι * (Finset.univ.filter (fun k => M k x)).card
        < ∑ _x : ι, Fintype.card κ * a := by
          apply Finset.sum_lt_sum_of_nonempty
          · exact Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hι)
          · intro x _; exact hbound x
      _ = Fintype.card ι * (Fintype.card κ * a) := by
          rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  have : Fintype.card ι * (Fintype.card κ * a)
      ≤ Fintype.card ι * (∑ x : ι, (Finset.univ.filter (fun k => M k x)).card) :=
    Nat.mul_le_mul_left _ htot
  omega

end GSCounting
