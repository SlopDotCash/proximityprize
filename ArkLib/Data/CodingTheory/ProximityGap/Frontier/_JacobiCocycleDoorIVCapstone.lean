/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleCancellationGap
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleAlignmentMechanism
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleFermatCornerExclusion

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Door-(iv) Jacobi-cocycle CAPSTONE: the three faces of the localized gap, bundled

**Door (iv), Lane 2 — the citable capstone unifying three proven faces.**

The Door-IV gap, after Shaw's tetrachotomy, is localized to ONE object: the dispersion of the
Jacobi-cocycle phase sum. This file does NOT prove that dispersion (the open `JacobiCocycleDispersion`).
It bundles the three *proven, axiom-clean* faces of the gap — already landed in this lane — into a
single kernel-checked conjunction, so "the Jacobi-cocycle gap is exactly characterized (size, mechanism,
and closed-form exclusion)" is one citable statement rather than three scattered files:

* **SIZE** (`_JacobiCocycleCancellationGap.baseline_div_target_eq_factor`): the cocycle must induce a
  cancellation factor `(1/C)·√(n/log m)` off the trivial baseline `n` — the full `√n` Paley/BGK
  cancellation up to the logarithmic thinness factor.
* **MECHANISM** (`_JacobiCocycleAlignmentMechanism.flat_target_forces_non_alignment`): meeting the flat
  prize budget forces phase non-alignment — any prize-meeting cocycle is genuinely dispersed.
* **EXCLUSION** (`_JacobiCocycleFermatCornerExclusion.prizeRegime_not_fermat_corner`): the prize regime
  is disjoint from the Fermat corner, so no closed-form 2-power Gauss-sum evaluation route exists — the
  genuinely-new dispersion estimate is the only door.

## HONEST SCOPE
A bundling capstone of already-proven facts. It proves NOTHING new toward CORE; the open object is
`JacobiCocycleDispersion`, untouched. NO CORE / cancellation / completion / anti-concentration /
moment-saving / capacity claim. Prize CORE stays OPEN.
-/

namespace ArkLib.ProximityGap.Frontier.JacobiCocycleDoorIVCapstone

open ProximityGap.Frontier.DyadicJacobiCocycleNonContraction

/-- **Door-(iv) Jacobi-cocycle characterization (citable capstone).** Under the prize-regime data
(`0 < C`, `0 < n`, `1 < m`; arithmetic factorization `pSub = nNat · mNat`, `nNat = 2^a`, an odd prime
factor `r ∣ mNat` with `1 < r`; a unit-phase configuration `γ` meeting the flat budget below the
baseline `M`), the three proven faces hold SIMULTANEOUSLY:

1. **SIZE** — the required cancellation factor equals `(1/C)·√(n/log m)` exactly.
2. **MECHANISM** — the budget-meeting configuration has NO common unit phase (forced dispersion).
3. **EXCLUSION** — `pSub = p − 1` is not a 2-power, so `p` is not a Fermat prime (no closed-form route).

This is the bundled door-(iv) statement: the gap's size, its mechanism, and the unavailability of the
closed-form corner, all kernel-checked together. It does NOT close the gap. -/
theorem jacobiCocycle_doorIV_characterization
    {C n m : ℝ} (hC : 0 < C) (hn : 0 < n) (hm : 1 < m)
    {pSub nNat mNat r a : ℕ}
    (hfac : pSub = nNat * mNat) (hnNat : nNat = 2 ^ a)
    (hr_odd : Odd r) (hr1 : 1 < r) (hr_dvd : r ∣ mNat)
    {M : ℕ} {γ : Fin M → ℂ}
    (hbudget : ‖phaseSum γ‖ ≤ C * Real.sqrt ((M : ℝ) * Real.log M))
    (hgap : C * Real.sqrt ((M : ℝ) * Real.log M) < (M : ℝ)) :
    -- 1. SIZE
    n / (C * Real.sqrt (n * Real.log m))
        = JacobiCocycleCancellationGap.requiredCancellationFactor C n m
    -- 2. MECHANISM
    ∧ (¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ j, γ j = ζ)
    -- 3. EXCLUSION
    ∧ (∀ k, pSub ≠ 2 ^ k) := by
  refine ⟨?_, ?_, ?_⟩
  · exact JacobiCocycleCancellationGap.baseline_div_target_eq_factor hC hn hm
  · exact JacobiCocycleAlignmentMechanism.flat_target_forces_non_alignment hbudget hgap
  · exact JacobiCocycleFermatCornerExclusion.prizeRegime_not_fermat_corner
      hfac hnNat hr_odd hr1 hr_dvd

end ArkLib.ProximityGap.Frontier.JacobiCocycleDoorIVCapstone

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleDoorIVCapstone.jacobiCocycle_doorIV_characterization
