/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleAllDefectCSVacuous
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Near-all-defect CS floor is only complement-size

**Door (iv), Lane 3 — strengthens the CS/L²-budget refutation near the adversarial regime.**

`_JacobiCocycleAllDefectCSVacuous` proved that the k-defect Cauchy–Schwarz floor

`((M - k) · D) / M`, where `D = ∑_{i∈S}(1 - Re w_i)`, is exactly zero at full defect cardinality
`k=M`. This file records the nearby quantitative obstruction: even when the defect set misses `r=M-k`
indices, the CS floor is bounded by `2r`. Thus the Cauchy–Schwarz/L² route only gives an
`O(complement-size)` certificate near the all-defect regime, not a prize-scale dispersion theorem.

Probe: `scripts/probes/probe_dooriv_near_all_defect_floor.py` checked `M=1..256` and every `k`; the
worst ratio approaches `1` as `k/M → 1`, so the `2(M-k)` ceiling is sharp up to the endpoint factor.

## HONEST SCOPE
This is a constraint lemma for the k-defect CS floor, not a CORE bound. It explains why the floor that is
useful for sparse defects cannot survive the adversarial all/near-all-defect phase configuration. Any real
Door-IV crack still needs arithmetic anti-concentration of the monomial phases, not this L² budget. No CORE,
cancellation, completion, moment-saving, anti-concentration, or capacity claim.
-/

namespace ArkLib.ProximityGap.Frontier.JacobiCocycleNearAllDefectFloor

open Finset Complex
open ProximityGap.Frontier.DyadicJacobiCocycleNonContraction
open ProximityGap.Frontier.JacobiCocycleKDefectQuantDeficit
open ProximityGap.Frontier.JacobiCocycleAllDefectCSVacuous

variable {M : ℕ} (S : Finset (Fin M)) (w : Fin M → ℂ)

/-- **The k-defect CS floor is at most twice the complement size.** For unit defect phases and
`#S ≤ M`, the floor from `_JacobiCocycleKDefectQuantDeficit`,
`((M - #S) * D) / M`, is bounded by `2*(M-#S)`. Near the all-defect regime this is only
`O(M-#S)`, and at `S=univ` it recovers the exact zero floor. -/
theorem kDefect_floor_le_twice_complement (hM : 1 ≤ M) (hk : S.card ≤ M)
    (hunit : ∀ i ∈ S, ‖w i‖ = 1) :
    ((M : ℝ) - S.card) * (∑ i ∈ S, (1 - (w i).re)) / (M : ℝ)
      ≤ 2 * ((M : ℝ) - S.card) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hkM : (S.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk
  obtain ⟨_hD0, hD2⟩ := kDefect_D_bounds S w hunit
  have hDleM : (∑ i ∈ S, (1 - (w i).re)) ≤ 2 * (M : ℝ) := by
    nlinarith [hD2, hkM]
  apply (div_le_iff₀ hM0).mpr
  nlinarith [hkM, hDleM]

/-- **Near-all-defect corollary.** If the complement size `M-#S` is at most `R`, then the k-defect CS
floor is at most `2R`. A small complement cannot yield more than a small absolute floor from this route. -/
theorem kDefect_floor_le_of_complement_le {R : ℝ} (hM : 1 ≤ M) (hk : S.card ≤ M)
    (hunit : ∀ i ∈ S, ‖w i‖ = 1) (hR : (M : ℝ) - S.card ≤ R) :
    ((M : ℝ) - S.card) * (∑ i ∈ S, (1 - (w i).re)) / (M : ℝ) ≤ 2 * R := by
  have hfloor := kDefect_floor_le_twice_complement S w hM hk hunit
  nlinarith [hfloor, hR]

/-- **Inverse spend obligation for near-all-defect CS floors.** Any claimed lower certificate `T` from the
k-defect CS floor forces at least `T/2` missing indices outside the defect set. Thus a prize-sized floor
cannot be hidden in a near-all-defect configuration unless the complement itself is prize-sized. -/
theorem complement_ge_half_floor_of_floor_ge {T : ℝ} (hM : 1 ≤ M) (hk : S.card ≤ M)
    (hunit : ∀ i ∈ S, ‖w i‖ = 1)
    (hT : T ≤ ((M : ℝ) - S.card) * (∑ i ∈ S, (1 - (w i).re)) / (M : ℝ)) :
    T / 2 ≤ (M : ℝ) - S.card := by
  have hfloor := kDefect_floor_le_twice_complement S w hM hk hunit
  nlinarith

/-- **Strict inverse spend obligation.** If a target `T` is larger than twice the complement size, then the
k-defect CS floor is strictly below `T`; the Cauchy–Schwarz route cannot certify that target. -/
theorem kDefect_floor_lt_of_twice_complement_lt {T : ℝ} (hM : 1 ≤ M) (hk : S.card ≤ M)
    (hunit : ∀ i ∈ S, ‖w i‖ = 1) (hT : 2 * ((M : ℝ) - S.card) < T) :
    ((M : ℝ) - S.card) * (∑ i ∈ S, (1 - (w i).re)) / (M : ℝ) < T := by
  have hfloor := kDefect_floor_le_twice_complement S w hM hk hunit
  nlinarith

/-- **Normalized near-all-defect obstruction.** Dividing the CS floor by `M`, the certificate is bounded
by twice the missing-index fraction `(M-#S)/M`. Hence if the complement is `o(M)`, this entire normalized
Cauchy–Schwarz budget vanishes; any fixed normalized saving needs a fixed complement fraction. -/
theorem normalized_floor_le_twice_complement_fraction (hM : 1 ≤ M) (hk : S.card ≤ M)
    (hunit : ∀ i ∈ S, ‖w i‖ = 1) :
    (((M : ℝ) - S.card) * (∑ i ∈ S, (1 - (w i).re)) / (M : ℝ)) / (M : ℝ)
      ≤ 2 * (((M : ℝ) - S.card) / (M : ℝ)) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hfloor := kDefect_floor_le_twice_complement S w hM hk hunit
  exact (div_le_div_of_nonneg_right hfloor (le_of_lt hM0)).trans_eq (by ring)

/-- **Fractional target spend.** A normalized floor target `eps` forces the complement fraction to be at
least `eps/2`. This is the scale-free version of the near-all-defect obstruction. -/
theorem complement_fraction_ge_half_of_normalized_floor_ge {eps : ℝ} (hM : 1 ≤ M)
    (hk : S.card ≤ M) (hunit : ∀ i ∈ S, ‖w i‖ = 1)
    (hfloor : eps ≤ (((M : ℝ) - S.card) * (∑ i ∈ S, (1 - (w i).re)) / (M : ℝ)) / (M : ℝ)) :
    eps / 2 ≤ ((M : ℝ) - S.card) / (M : ℝ) := by
  have hnorm := normalized_floor_le_twice_complement_fraction S w hM hk hunit
  nlinarith

end ArkLib.ProximityGap.Frontier.JacobiCocycleNearAllDefectFloor

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleNearAllDefectFloor.kDefect_floor_le_twice_complement
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleNearAllDefectFloor.kDefect_floor_le_of_complement_le
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleNearAllDefectFloor.complement_ge_half_floor_of_floor_ge
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleNearAllDefectFloor.kDefect_floor_lt_of_twice_complement_lt
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleNearAllDefectFloor.normalized_floor_le_twice_complement_fraction
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleNearAllDefectFloor.complement_fraction_ge_half_of_normalized_floor_ge
