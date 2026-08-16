/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

set_option autoImplicit false

/-!
# D4 MacMahon/margin-encoding gate

Issue #464 flagged arXiv:2606.27323 as a possible route through amplified zeta moments: encode
moment constants as weighted counts of matrix pairs with prescribed margins, then port the
MacMahon/constant-term machinery to the finite-field wraparound defect.

This file records the logical gate.  A margin encoding can be useful, but by itself it is only a
reindexing of the same nonnegative count.  To bound the prize statistic it must supply a genuine
budget for the sum of margin fiber masses, or sufficiently strong uniform fiber caps.  Coarse
information such as "few occupied margins" does not control total mass: one margin can carry an
arbitrarily large fiber.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.D4MacMahonMarginEncodingGate

/-- An exact margin encoding of a statistic `stat`: all quantitative content is in the margin
fiber masses `fiberMass`. -/
def EncodesByMargins {M : Type*} [Fintype M] (stat : ℝ) (fiberMass : M → ℝ) : Prop :=
  stat = ∑ m, fiberMass m

/-- A margin encoding transfers to a prize bound exactly when the margin-side total is bounded. -/
theorem bound_of_margin_encoding_and_budget
    {M : Type*} [Fintype M] {stat B : ℝ} {fiberMass : M → ℝ}
    (henc : EncodesByMargins stat fiberMass)
    (hbudget : ∑ m, fiberMass m ≤ B) :
    stat ≤ B := by
  rw [henc]
  exact hbudget

/-- Uniform per-margin fiber caps imply only the corresponding cardinality-times-cap total bound.
Thus a MacMahon margin decomposition is useful only if the cap and number of margins fit the prize
budget. -/
theorem total_bound_of_uniform_margin_cap
    {M : Type*} [Fintype M] (fiberMass : M → ℝ) (C : ℝ)
    (hcap : ∀ m, fiberMass m ≤ C) :
    ∑ m, fiberMass m ≤ (Fintype.card M : ℝ) * C := by
  calc
    ∑ m, fiberMass m ≤ ∑ _ : M, C := sum_le_sum (by intro m _; exact hcap m)
    _ = (Fintype.card M : ℝ) * C := by simp [Finset.card_univ]

/-- **One-heavy-margin countermodel.**  Even with a single occupied margin, the total margin mass
can exceed any proposed bound if no fiber-mass cap is supplied. -/
theorem one_heavy_margin_refutes_support_only (B : ℝ) :
    ∃ fiberMass : PUnit → ℝ, B < ∑ m, fiberMass m := by
  refine ⟨fun _ => B + 1, ?_⟩
  simp

/-- A fixed finite margin index set is compatible with both a bounded statistic and an arbitrarily
large statistic.  The index set or polytope alone therefore cannot decide the prize floor; the
load-bearing input is the actual fiber-mass inequality. -/
theorem same_margin_shape_allows_bound_and_spike (B : ℝ) :
    ∃ low high : PUnit → ℝ,
      (∑ m, low m ≤ B) ∧ B < ∑ m, high m := by
  refine ⟨fun _ => B - 1, fun _ => B + 1, ?_, ?_⟩
  · simp
  · simp

/-! ## Axiom audit. -/
#print axioms bound_of_margin_encoding_and_budget
#print axioms total_bound_of_uniform_margin_cap
#print axioms one_heavy_margin_refutes_support_only
#print axioms same_margin_shape_allows_bound_and_spike

end ArkLib.ProximityGap.Frontier.D4MacMahonMarginEncodingGate
