/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound

/-!
# P1 predecessor radius versus the in-tree BCIKS20 error bound (bivariate lane)

The P1 predecessor residual (`CanonicalUniformPredecessorBadCount`) demands at most
`N = 2^30` bad scalars at radius `deltaPred = 480946858 / 2^30 ≈ 0.44792` for the
rate-quarter code `ReedSolomon.code canonicalDomain k`, `k = 2^28`.

Since `deltaPred < 1/2 = 1 - sqrt(rate)`, one might hope the in-tree BCIKS20
Johnson-regime machinery (`proximity_gap_RSCodes`, `RS_correlatedAgreement_affineLines*`)
already discharges the residual.  This file machine-checks why it cannot:

* `udr_lt_deltaPred` / `deltaPred_lt_johnson`: the predecessor radius lies strictly
  inside the **Johnson branch** `((1-ρ)/2, 1-√ρ) = (3/8, 1/2)` of
  `ProximityGap.errorBound` — the unique-decoding branch, whose error `n/q` is exactly
  pin strength, is out of reach by an absolute radius margin of `0.0729`.
* `errorBound_eval`: on the Johnson branch the in-tree error evaluates **exactly** to
  `ε = deg² / ((2m)^7 · q)` with `m = min(1-√ρ-δ, √ρ/20) = 1/40`, i.e.
  `ε · q = 2^56 · 20^7 = 2^63 · 10^7 = 92233720368547758080000000 ≈ 2^86.25`
  bad scalars — exceeding the required budget `N = 2^30` by the exact factor
  `2^33 · 10^7` (`scalarBudget_eq_N_mul_gap`).
* `ratio_le_errorBound_of_le_budget`: consequently the `Pr > ε` firing condition of
  every in-tree correlated-agreement front door is unsatisfiable by any bad-scalar
  family of at most `2^63·10^7` elements; the guarded P1 extraction concerns families
  of `N + 1 ≈ 2^30` (56 binary orders below the threshold).
* `errorBound_lt_one_P1` (over the literal prize field `ZMod P`, `P ≈ 2^158`):
  `ε < 1`, so the in-tree theorems are non-vacuous at P1 — they are simply
  quantitatively `2^56.25`-fold too weak for the predecessor pin.

`deltaPred` here equals
`RateQuarterPredecessorFourPencilReduction.P1.predecessorDelta` by that file's
`predecessor_radius_numerator_value` (`predecessorRadiusNumerator = 480946858`,
`N = 1073741824`); the numerals are kept literal to avoid importing an unbuilt lane.

Verdict content: a machine-checked **barrier** for the "in-tree list-decoding substrate
discharges the predecessor pin" route.  The pin asks for unique-decoding-strength error
(`n/q`, BCIKS20 Conjecture 1.5 / ABF26-MCA strength) at a radius where the formalized
(and literature) bound is `deg²/((2m)^7 q)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic

/-- The P1 predecessor radius `(N - T)/N = 480946858/2^30` as literal numerals. -/
noncomputable def deltaPred : ℝ≥0 := (480946858 : ℝ≥0) / (1073741824 : ℝ≥0)

/-- The exact bad-scalar budget of the in-tree Johnson-branch error bound at the P1
predecessor point: `ε · q = deg² · 20^7 = 2^63 · 10^7`. -/
abbrev scalarBudget : ℕ := 92233720368547758080000000

theorem scalarBudget_eq_pow : scalarBudget = 2 ^ 63 * 10 ^ 7 := by norm_num

/-- The Johnson-branch budget exceeds the pin target `N` by exactly `2^33 · 10^7`. -/
theorem scalarBudget_eq_N_mul_gap : scalarBudget = N * (2 ^ 33 * 10 ^ 7) := by norm_num

/-- The predecessor radius numerator agrees with the four-pencil lane's
`predecessorRadiusNumerator = N - predecessorThreshold`. -/
theorem deltaPred_eq_pred_ratio :
    deltaPred = ((N - 592794966 : ℕ) : ℝ≥0) / ((N : ℕ) : ℝ≥0) := by
  unfold deltaPred
  norm_num

section Generic

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq Fq]
variable (domain : Fin N ↪ Fq)

/-- The rate of the P1-shaped code is exactly `1/4`. -/
theorem rate_eval :
    ((LinearCode.rate (ReedSolomon.code domain k) : ℚ≥0) : ℝ≥0) = 1 / 4 := by
  have h := congrArg (fun x : ℚ≥0 => (x : ℝ≥0))
    (ReedSolomon.rateOfLinearCode_eq_div' (F := Fq) (α := domain) (n := k)
      (by simp [Fintype.card_fin]; norm_num))
  simp only [NNRat.cast_div, NNRat.cast_natCast, Fintype.card_fin] at h
  rw [h, ← NNReal.coe_inj]
  push_cast
  norm_num

/-- The square-root rate of the P1-shaped code is exactly `1/2`. -/
theorem sqrtRate_eval : ReedSolomon.sqrtRate k domain = 1 / 2 := by
  unfold ReedSolomon.sqrtRate
  rw [rate_eval]
  have h : (1 / 4 : ℝ≥0) = (1 / 2 : ℝ≥0) ^ 2 := by
    rw [← NNReal.coe_inj]
    push_cast
    norm_num
  rw [h, NNReal.sqrt_sq]

theorem one_sub_quarter : (1 : ℝ≥0) - 1 / 4 = 3 / 4 := by
  apply tsub_eq_of_eq_add
  rw [← NNReal.coe_inj]
  push_cast
  norm_num

theorem one_sub_half : (1 : ℝ≥0) - 1 / 2 = 1 / 2 := by
  apply tsub_eq_of_eq_add
  rw [← NNReal.coe_inj]
  push_cast
  norm_num

/-- The unique-decoding threshold `(1-ρ)/2 = 3/8` is strictly below the predecessor
radius: the `n/q`-error branch of `errorBound` cannot fire at the P1 predecessor. -/
theorem udr_lt_deltaPred : ((1 : ℝ≥0) - 1 / 4) / 2 < deltaPred := by
  rw [one_sub_quarter]
  unfold deltaPred
  rw [← NNReal.coe_lt_coe]
  push_cast
  norm_num

/-- The predecessor radius is strictly below the Johnson radius `1 - √ρ = 1/2`. -/
theorem deltaPred_lt_half : deltaPred < (1 : ℝ≥0) - 1 / 2 := by
  rw [one_sub_half]
  unfold deltaPred
  rw [← NNReal.coe_lt_coe]
  push_cast
  norm_num

/-- Radius-margin term of the Johnson-branch error at the predecessor point. -/
theorem one_sub_half_sub_deltaPred :
    (1 : ℝ≥0) - 1 / 2 - deltaPred = (55924054 : ℝ≥0) / 1073741824 := by
  rw [one_sub_half]
  apply tsub_eq_of_eq_add
  unfold deltaPred
  rw [← NNReal.coe_inj]
  push_cast
  norm_num

/-- The min in the Johnson-branch error is pinned at `√ρ/20 = 1/40`. -/
theorem min_eval :
    min ((1 : ℝ≥0) - 1 / 2 - deltaPred) ((1 / 2 : ℝ≥0) / 20) = 1 / 40 := by
  have h40 : ((1 / 2 : ℝ≥0)) / 20 = 1 / 40 := by
    rw [← NNReal.coe_inj]
    push_cast
    norm_num
  rw [one_sub_half_sub_deltaPred, h40, min_eq_right]
  rw [← NNReal.coe_le_coe]
  push_cast
  norm_num

/-- **Exact evaluation of the in-tree BCIKS20 error bound at the P1 predecessor
point.**  The Johnson branch fires and its value is `2^63·10^7 / q`. -/
theorem errorBound_eval :
    errorBound deltaPred k domain =
      (scalarBudget : ℝ≥0) / ((Fintype.card Fq : ℕ) : ℝ≥0) := by
  have hqpos : (0 : ℝ) < (Fintype.card Fq : ℝ) := by
    exact_mod_cast Fintype.card_pos
  unfold errorBound
  simp only [rate_eval]
  have hsqrt : NNReal.sqrt (1 / 4 : ℝ≥0) = 1 / 2 := by
    have h : (1 / 4 : ℝ≥0) = (1 / 2 : ℝ≥0) ^ 2 := by
      rw [← NNReal.coe_inj]; push_cast; norm_num
    rw [h, NNReal.sqrt_sq]
  simp only [hsqrt]
  rw [if_neg (by
    intro hmem
    exact absurd hmem.2 (not_le.mpr udr_lt_deltaPred))]
  rw [if_pos ⟨udr_lt_deltaPred, deltaPred_lt_half⟩]
  have hq : ((Fintype.card Fq : ℕ) : ℝ) ≠ 0 := ne_of_gt hqpos
  apply NNReal.coe_injective
  show (((k : ℝ≥0) ^ 2 : ℝ≥0) : ℝ) /
      ((2 * ((min ((1 : ℝ≥0) - 1 / 2 - deltaPred) ((1 / 2 : ℝ≥0) / 20) : ℝ≥0) : ℝ)) ^ 7 *
        ((Fintype.card Fq : ℕ) : ℝ)) =
    (((scalarBudget : ℝ≥0) / ((Fintype.card Fq : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)
  rw [min_eval, NNReal.coe_div]
  push_cast
  field_simp
  ring_nf

/-- Cleared form: the in-tree Johnson error times the field size is exactly the
`2^63·10^7` scalar budget — independent of the field. -/
theorem errorBound_mul_card :
    errorBound deltaPred k domain * ((Fintype.card Fq : ℕ) : ℝ≥0) =
      (scalarBudget : ℝ≥0) := by
  rw [errorBound_eval, div_mul_cancel₀]
  exact_mod_cast Fintype.card_ne_zero

/-- **Blocking hypothesis, machine-checked.**  Any bad-scalar family of size at most
the `2^63·10^7` budget has normalized mass at most the in-tree error bound, so the
`Pr > ε` firing condition of the in-tree correlated-agreement front doors
(`proximity_gap_RSCodes`, `RS_correlatedAgreement_affineLines*`) is unsatisfiable for
it.  The guarded P1 predecessor extraction concerns families of `N + 1 = 2^30 + 1`. -/
theorem ratio_le_errorBound_of_le_budget (c : ℕ) (hc : c ≤ scalarBudget) :
    (c : ℝ≥0) / ((Fintype.card Fq : ℕ) : ℝ≥0) ≤ errorBound deltaPred k domain := by
  rw [errorBound_eval]
  have hc' : (c : ℝ≥0) ≤ (scalarBudget : ℝ≥0) := by exact_mod_cast hc
  gcongr

/-- The pin-scale family is inside the budget by a factor `2^33·10^7`. -/
theorem pin_scale_le_budget : N + 1 ≤ scalarBudget := by norm_num

end Generic

section P1

local instance localInstance_FSME_BivariateJohnsonErrorFloor_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_FSME_BivariateJohnsonErrorFloor_2 : NeZero P := ⟨prime_P.ne_zero⟩

/-- Over the literal P1 prize field, the error bound is exactly `2^63·10^7 / P`. -/
theorem errorBound_eval_P1 (domain : Fin N ↪ F) :
    errorBound deltaPred k domain = (scalarBudget : ℝ≥0) / ((P : ℕ) : ℝ≥0) := by
  rw [errorBound_eval, ZMod.card]

/-- The in-tree bound is non-vacuous at P1 (`ε < 1`): the barrier is quantitative
(`2^56.25`-fold), not a domain-of-applicability failure. -/
theorem errorBound_lt_one_P1 (domain : Fin N ↪ F) :
    errorBound deltaPred k domain < 1 := by
  rw [errorBound_eval_P1]
  rw [div_lt_one (by
    rw [← NNReal.coe_lt_coe]
    push_cast
    norm_num [P])]
  rw [← NNReal.coe_lt_coe]
  push_cast
  norm_num [P]

end P1

#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.scalarBudget_eq_pow
#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.scalarBudget_eq_N_mul_gap
#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.deltaPred_eq_pred_ratio
#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.rate_eval
#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.sqrtRate_eval
#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.udr_lt_deltaPred
#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.deltaPred_lt_half
#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.min_eval
#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.errorBound_eval
#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.errorBound_mul_card
#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.ratio_le_errorBound_of_le_budget
#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.pin_scale_le_budget
#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.errorBound_eval_P1
#print axioms ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor.errorBound_lt_one_P1

end ArkLib.ProximityGap.Frontier.FSMEBivariateJohnsonErrorFloor
