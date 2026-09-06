/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R266 index-window split socket)
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

/-!
# R266 (#466): index-window split socket

R266 suggests splitting the micro-band theorem into a finite medium-index branch
and a softer large-index branch.  This file packages the propositional
accounting: if both branches imply the same direct micro-band cap, then the cap
holds unconditionally for every index.
-/

namespace ArkLib.ProximityGap.Frontier.R266IndexWindowSplitSocket

variable {ι : Type*} [DecidableEq ι]

noncomputable section

/-- Survivor count at threshold `θ`. -/
def SurvivorCount (s : Finset ι) (t : ι → ℝ) (θ : ℝ) : ℝ :=
  ((s.filter (fun i => θ ≤ t i)).card : ℝ)

/-- The direct micro-band cap at `τ`. -/
def DirectMicroBandCap (s : Finset ι) (t : ι → ℝ) (τ A : ℝ) : Prop :=
  SurvivorCount s t τ ≤ A * (s.card : ℝ)

/-- Branch predicate for a quotient index `M` with cutoff `M₀`. -/
def InFiniteWindow (M M₀ : ℕ) : Prop := M < M₀

/-- Case split for the direct micro-band cap across an index cutoff. -/
theorem directMicroBandCap_of_indexWindow_split
    (s : Finset ι) (t : ι → ℝ) (τ A : ℝ) (M M₀ : ℕ)
    (hFinite : InFiniteWindow M M₀ → DirectMicroBandCap s t τ A)
    (hLarge : M₀ ≤ M → DirectMicroBandCap s t τ A) :
    DirectMicroBandCap s t τ A := by
  by_cases h : M < M₀
  · exact hFinite h
  · exact hLarge (Nat.le_of_not_gt h)

end

end ArkLib.ProximityGap.Frontier.R266IndexWindowSplitSocket

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R266IndexWindowSplitSocket.directMicroBandCap_of_indexWindow_split
