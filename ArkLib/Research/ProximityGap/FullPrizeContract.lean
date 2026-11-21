/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
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

end FullPrizeReview
