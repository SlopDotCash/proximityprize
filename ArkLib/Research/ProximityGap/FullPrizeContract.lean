/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-! Candidate statement for review of the operational version of the two grand challenges.
This module defines a specification. It supplies no answer functions or universal proof. -/
set_option autoImplicit false

namespace FullPrizeReview
open Code ProximityGap CoreDefinitions
open scoped NNReal ENNReal

/-- `some e` gives the first failing error count. With `none` every grid point passes. -/
abbrev Boundary (n : ℕ) := Option (Fin (n + 1))

/-- A predicted boundary specifies the entire closed-ball security predicate on [0,1]. -/
def correctBoundary (n : ℕ) (answer : Boundary n) (safe : ℝ≥0 → Prop) : Prop :=
  ∀ δ : ℝ≥0, δ ≤ 1 →
    (safe δ ↔ match answer with
      | none => True
      | some e => δ < (e.val : ℝ≥0) / n)

/-- A code can realize one of the requested rates even if its length is below sixteen. -/
def hasPrizeRate (n k : ℕ) : Prop :=
  2 * k = n ∨ 4 * k = n ∨ 8 * k = n ∨ 16 * k = n

/-- Correctness obligation for two proposed answers on a supplied smooth code domain.
The caller chooses the field, smooth domain, tolerance, and the two predictions from those inputs.
A complete result must exhibit and justify the predictions for its entire claimed input regime. -/
def correctForDomain {F ι : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (D : ι ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0)
    (mcaAnswer : ℕ → Boundary (Fintype.card ι))
    (listAnswer : ℕ → ℕ → Boundary (Fintype.card ι)) : Prop :=
  ∀ k : ℕ, hasPrizeRate (Fintype.card ι) k →
    correctBoundary (Fintype.card ι) (mcaAnswer k) (fun δ =>
      mcaError (AffineLineGenerator F) (ReedSolomon.code D k) (δ : ℝ) ≤ (ε : ENNReal)) ∧
    ∀ m : ℕ, 0 < m →
      correctBoundary (Fintype.card ι) (listAnswer k m) (fun δ =>
        (Code.Lambda (interleavedCodeSet (κ := Fin m)
          (ReedSolomon.code D k : Set (ι → F))) (δ : ℝ) : ENNReal) ≤
          (ε : ENNReal) * (Fintype.card F : ENNReal))

/-- The safe radii through one uniquely determine the boundary of a positive-length code. -/
theorem correctBoundary_unique {n : ℕ} (hn : 0 < n) {a b : Boundary n} {safe : ℝ≥0 → Prop}
    (ha : correctBoundary n a safe) (hb : correctBoundary n b safe) : a = b := by
  have hpos : 0 < (n : ℝ≥0) := by exact_mod_cast hn
  have hgrid (e : Fin (n + 1)) : (e.val : ℝ≥0) / n ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast Nat.le_of_lt_succ e.isLt) (by positivity)
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j =>
      have hs := (ha _ (hgrid j)).mpr trivial
      exact False.elim ((lt_irrefl _) ((hb _ (hgrid j)).mp hs))
  | some i =>
    cases b with
    | none =>
      have hs := (hb _ (hgrid i)).mpr trivial
      exact False.elim ((lt_irrefl _) ((ha _ (hgrid i)).mp hs))
    | some j =>
      congr 1
      apply le_antisymm
      · by_contra! h
        have hlt : (j.val : ℝ≥0) / n < (i.val : ℝ≥0) / n :=
          (div_lt_div_iff_of_pos_right hpos).mpr (by exact_mod_cast h)
        have hs := (ha _ (hgrid j)).mpr hlt
        exact (lt_irrefl _) ((hb _ (hgrid j)).mp hs)
      · by_contra! h
        have hlt : (i.val : ℝ≥0) / n < (j.val : ℝ≥0) / n :=
          (div_lt_div_iff_of_pos_right hpos).mpr (by exact_mod_cast h)
        have hs := (hb _ (hgrid i)).mpr hlt
        exact (lt_irrefl _) ((ha _ (hgrid i)).mp hs)

end FullPrizeReview
