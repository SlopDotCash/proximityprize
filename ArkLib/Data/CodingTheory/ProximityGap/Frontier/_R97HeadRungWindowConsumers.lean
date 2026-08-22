/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R21HeadRungDichotomy

/-!
# LANE B2 (#466 round 97): head-rung windows from `AwaySupBound`

R21 proves the one-rung automatic side of the head-rung dichotomy:

`AwaySupBound C` and `C ≤ 2r+1` imply `HeadRungSubWick r`.

This file packages the interval form.  A single threshold at `r₀` gives every later head rung,
and the r = 3 threshold is the concrete constant `7`.  This is the reusable surface for the
current normal form: below the threshold the head rungs are phase-deep; above it they are just
shadows of `AwaySupBound`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R97HeadRungWindowConsumers

open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Exact-budget one-rung form: `AwaySupBound` at the Wick budget `C = 2r+1`
is precisely enough to force the named head-rung sub-Wick inequality. -/
theorem headRungSubWick_of_awaySupBound_at_wickBudget
    (ψ : AddChar F ℂ) (G H D : Finset F) (r : ℕ)
    (hAway : AwaySupBound ψ G H D (2 * (r : ℝ) + 1)) :
    HeadRungSubWick ψ G H D r :=
  headRungSubWick_of_awaySupBound ψ G H D r le_rfl hAway

/-- If `AwaySupBound C` reaches the threshold at `r₀`, then every later head rung is automatic. -/
theorem headRungSubWick_window_of_awaySupBound
    (ψ : AddChar F ℂ) (G H D : Finset F) {C : ℝ} (r₀ : ℕ)
    (hC : C ≤ (2 * r₀ + 1 : ℝ))
    (hAway : AwaySupBound ψ G H D C) :
    ∀ r : ℕ, r₀ ≤ r → HeadRungSubWick ψ G H D r := by
  intro r hr
  have hrReal : (r₀ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hCr : C ≤ (2 * r + 1 : ℝ) := by
    nlinarith
  exact headRungSubWick_of_awaySupBound ψ G H D r hCr hAway

/-- Concrete r = 3 window: `AwaySupBound C` with `C ≤ 7` gives all head rungs from `3` on. -/
theorem headRungSubWick_from_three_of_awaySupBound
    (ψ : AddChar F ℂ) (G H D : Finset F) {C : ℝ}
    (hC : C ≤ (7 : ℝ))
    (hAway : AwaySupBound ψ G H D C) :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G H D r := by
  have hC' : C ≤ (2 * (3 : ℕ) + 1 : ℝ) := by
    norm_num
    exact hC
  simpa using
    headRungSubWick_window_of_awaySupBound ψ G H D (r₀ := 3) hC' hAway

/-- A failure at any rung at or beyond `r₀` refutes the corresponding thresholded
`AwaySupBound` window. -/
theorem not_awaySupBound_of_headRung_window_failure
    (ψ : AddChar F ℂ) (G H D : Finset F) {C : ℝ} {r₀ r : ℕ}
    (hr : r₀ ≤ r)
    (hC : C ≤ (2 * r₀ + 1 : ℝ))
    (hfail : ¬ HeadRungSubWick ψ G H D r) :
    ¬ AwaySupBound ψ G H D C := by
  intro hAway
  exact hfail (headRungSubWick_window_of_awaySupBound ψ G H D r₀ hC hAway r hr)

/-- Exact-budget contrapositive: failure of the rung-`r` sub-Wick inequality refutes
`AwaySupBound` at the matching Wick budget `C = 2r+1`. -/
theorem not_awaySupBound_at_wickBudget_of_headRung_failure
    (ψ : AddChar F ℂ) (G H D : Finset F) {r : ℕ}
    (hfail : ¬ HeadRungSubWick ψ G H D r) :
    ¬ AwaySupBound ψ G H D (2 * (r : ℝ) + 1) := by
  intro hAway
  exact hfail (headRungSubWick_of_awaySupBound_at_wickBudget ψ G H D r hAway)

/-- Concrete r = 3 failure form: any failed head rung at depth at least `3` rules out
`AwaySupBound C` for every `C ≤ 7`. -/
theorem not_awaySupBound_le_seven_of_headRung_failure
    (ψ : AddChar F ℂ) (G H D : Finset F) {C : ℝ} {r : ℕ}
    (hr : 3 ≤ r)
    (hC : C ≤ (7 : ℝ))
    (hfail : ¬ HeadRungSubWick ψ G H D r) :
    ¬ AwaySupBound ψ G H D C := by
  have hC' : C ≤ (2 * (3 : ℕ) + 1 : ℝ) := by
    norm_num
    exact hC
  exact not_awaySupBound_of_headRung_window_failure ψ G H D hr hC' hfail

end ArkLib.ProximityGap.Frontier.R97HeadRungWindowConsumers

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R97HeadRungWindowConsumers.headRungSubWick_of_awaySupBound_at_wickBudget
#print axioms
  ArkLib.ProximityGap.Frontier.R97HeadRungWindowConsumers.headRungSubWick_window_of_awaySupBound
#print axioms
  ArkLib.ProximityGap.Frontier.R97HeadRungWindowConsumers.headRungSubWick_from_three_of_awaySupBound
#print axioms
  ArkLib.ProximityGap.Frontier.R97HeadRungWindowConsumers.not_awaySupBound_of_headRung_window_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R97HeadRungWindowConsumers.not_awaySupBound_at_wickBudget_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R97HeadRungWindowConsumers.not_awaySupBound_le_seven_of_headRung_failure
