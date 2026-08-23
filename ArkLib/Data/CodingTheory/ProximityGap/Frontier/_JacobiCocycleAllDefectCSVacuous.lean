/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleKDefectQuantDeficit
import Mathlib.Tactic

/-!
# The Cauchy–Schwarz deficit floor is VACUOUS in the all-defect regime (Lane 3 constraint lemma)

**Door (iv), Lane 3 — a PROVEN constraint lemma backing Shaw's Lever-B (additive-energy/L²) refutation.**

`_JacobiCocycleKDefectQuantDeficit` proved the additive-in-defect first-power floor
`M − ‖∑γ‖ ≥ (M − k)·D / M` (`D = ∑_{i∈S}(1 − Re w_i)`, `k = #S`). The prize regime is the ADVERSARIAL
worst coset, where EVERY one of the `M` phases is off-aligned (`k = M`, `D = Θ(M)`). This file records
the exact, kernel-checked fact that the Cauchy–Schwarz / L²-budget floor DEGENERATES there:

  **at `k = #S = M` the floor `(M − k)·D/M = 0`** — the bound becomes the vacuous `0 ≤ M − ‖∑γ‖`.

So the entire Cauchy–Schwarz route (`(∑ Im)² ≤ k∑ Im²`, `D² ≤ k∑ d²`, the L²-budget collapse
`D² + (∑ Im)² ≤ 2kD`) certifies NO cancellation in the regime the prize actually needs: its only output
is `‖∑γ‖ ≤ M`, the trivial ceiling. The deficit-from-below it provides is `0`. This is the precise
mechanism behind Shaw's Lever-B refutation: an additive-energy/L² lower bound on the deficit cannot
reach the `√(n log m)` prize scale, because at full defect cardinality it reaches `0`.

## HONEST SCOPE
This is a CONSTRAINT/refutation lemma: it does not prove CORE; it precisely locks WHY the CS/L²-budget
deficit lever is structurally incapable of proving CORE (vacuous at `k = M`). A real prize bound must
exploit the ARITHMETIC phase structure of `{b·x^m}` (the open door-(iv) anti-concentration), not the
metric Cauchy–Schwarz budget. NO CORE / cancellation / completion / anti-concentration / moment-saving
/ capacity claim. Prize CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace ArkLib.ProximityGap.Frontier.JacobiCocycleAllDefectCSVacuous

open Finset Complex
open ProximityGap.Frontier.DyadicJacobiCocycleNonContraction
open ProximityGap.Frontier.JacobiCocycleKDefectQuantDeficit

/-- **The k-defect CS floor vanishes at full cardinality.** When the defect set is everything
(`S = univ`, so `#S = M`), the floor `(M − #S)·D/M` is exactly `0`, for ANY phases `w` and `M`. -/
theorem kDefect_floor_eq_zero_of_full (M : ℕ) (w : Fin M → ℂ) :
    ((M : ℝ) - (univ : Finset (Fin M)).card) * (∑ i ∈ (univ : Finset (Fin M)), (1 - (w i).re))
      / (M : ℝ) = 0 := by
  rw [Finset.card_univ, Fintype.card_fin]
  simp

/-- **All-defect vacuity (the constraint).** At `k = M` the k-defect deficit bound degrades to the
content-free `0 ≤ M − ‖∑γ‖` — i.e. the only consequence of the Cauchy–Schwarz / L²-budget route in the
adversarial all-defect regime is the trivial ceiling `‖∑γ‖ ≤ M`, NOT any prize-scale cancellation. -/
theorem allDefect_cs_floor_vacuous (M : ℕ) (hM : 1 ≤ M) (w : Fin M → ℂ)
    (hunit : ∀ i, ‖w i‖ = 1) :
    ((M : ℝ) - (univ : Finset (Fin M)).card)
        * (∑ i ∈ (univ : Finset (Fin M)), (1 - (w i).re)) / (M : ℝ) = 0
      ∧ ‖phaseSum (kDefectFamily (univ : Finset (Fin M)) w)‖ ≤ (M : ℝ) := by
  refine ⟨kDefect_floor_eq_zero_of_full M w, ?_⟩
  -- the trivial ceiling: it is exactly the (vanishing-floor) instance of kDefect_deficit_ge
  have hk : (univ : Finset (Fin M)).card ≤ M := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hfloor := kDefect_floor_eq_zero_of_full M w
  have hge := kDefect_deficit_ge (univ : Finset (Fin M)) w hM hk (fun i _ => hunit i)
  rw [hfloor] at hge
  linarith [hge]

end ArkLib.ProximityGap.Frontier.JacobiCocycleAllDefectCSVacuous

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleAllDefectCSVacuous.kDefect_floor_eq_zero_of_full
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleAllDefectCSVacuous.allDefect_cs_floor_vacuous
