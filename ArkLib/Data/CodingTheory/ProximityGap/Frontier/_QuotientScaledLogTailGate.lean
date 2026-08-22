/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._QuotientTailSupConsumer
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Scaled-log quotient tail gate

The exponential quotient-tail gate says that an estimate

`quotientTailMass Y T <= A * exp(-rate)`

turns into a pulled-back pointwise theorem exactly past the logarithmic threshold

`log #Q + log A < rate`.

This file records the constant-form bridge used at the prize threshold.  If the quotient has size
`m` and the analytic theorem gives `rate = κ * log m`, then the useful side of the gate is

`1 + log A / log m < κ`.

At the opposite inequality, `κ <= 1 + log A / log m`, the exponential tail budget is still
compatible with one bad quotient atom.  This isolates the constant pressure in subgaussian attempts:
for `T^2 = C^2 * n * log m` and rate `c*T^2/V`, the scaled-log constant is
`κ = c*C^2*n/V`.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.QuotientScaledLogTailGate

open ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer

variable {α Q : Type} [Fintype Q]

/-! ## Pure logarithmic arithmetic -/

/-- If the exponential rate is strictly larger than `log N + log A`, then the exponential budget
`A * exp(-rate)` has total mass below one atom count `N`. -/
theorem mul_exponentialTail_lt_one_of_log_budget
    {N A rate : ℝ} (hN : 0 < N) (hA : 0 < A)
    (hlog : Real.log N + Real.log A < rate) :
    N * (A * Real.exp (-rate)) < 1 := by
  have hneg : Real.log N + Real.log A - rate < 0 := by linarith
  have hexp : Real.exp (Real.log N + Real.log A - rate) < Real.exp 0 :=
    Real.exp_lt_exp.mpr hneg
  have hrw :
      Real.exp (Real.log N + Real.log A - rate) = N * (A * Real.exp (-rate)) := by
    rw [show Real.log N + Real.log A - rate = Real.log N + Real.log A + (-rate) by ring,
      Real.exp_add, Real.exp_add, Real.exp_log hN, Real.exp_log hA]
    ring
  simpa [hrw] using hexp

/-- If the exponential rate is no larger than `log N + log A`, then the exponential budget can pay
for at least one atom count `N`. -/
theorem one_le_mul_exponentialTail_of_log_budget_le
    {N A rate : ℝ} (hN : 0 < N) (hA : 0 < A)
    (hlog : rate ≤ Real.log N + Real.log A) :
    1 ≤ N * (A * Real.exp (-rate)) := by
  have hnonneg : 0 ≤ Real.log N + Real.log A - rate := by linarith
  have hexp : Real.exp 0 ≤ Real.exp (Real.log N + Real.log A - rate) :=
    Real.exp_le_exp.mpr hnonneg
  have hrw :
      Real.exp (Real.log N + Real.log A - rate) = N * (A * Real.exp (-rate)) := by
    rw [show Real.log N + Real.log A - rate = Real.log N + Real.log A + (-rate) by ring,
      Real.exp_add, Real.exp_add, Real.exp_log hN, Real.exp_log hA]
    ring
  simpa [hrw] using hexp

/-- Multiplying the strict scaled-log margin by `log m > 0` gives the logarithmic union-budget
margin. -/
theorem log_add_lt_scaled_log_of_one_add_div_lt
    {m A κ : ℝ} (hlogm : 0 < Real.log m)
    (hκ : 1 + Real.log A / Real.log m < κ) :
    Real.log m + Real.log A < κ * Real.log m := by
  have hmul :
      (1 + Real.log A / Real.log m) * Real.log m < κ * Real.log m :=
    mul_lt_mul_of_pos_right hκ hlogm
  calc
    Real.log m + Real.log A = (1 + Real.log A / Real.log m) * Real.log m := by
      field_simp [ne_of_gt hlogm]
    _ < κ * Real.log m := hmul

/-- The non-strict opposite scaled-log inequality is exactly the one-atom obstruction side of the
logarithmic gate. -/
theorem scaled_log_le_log_add_of_le_one_add_div
    {m A κ : ℝ} (hlogm : 0 < Real.log m)
    (hκ : κ ≤ 1 + Real.log A / Real.log m) :
    κ * Real.log m ≤ Real.log m + Real.log A := by
  have hmul :
      κ * Real.log m ≤ (1 + Real.log A / Real.log m) * Real.log m :=
    mul_le_mul_of_nonneg_right hκ (le_of_lt hlogm)
  calc
    κ * Real.log m ≤ (1 + Real.log A / Real.log m) * Real.log m := hmul
    _ = Real.log m + Real.log A := by
      field_simp [ne_of_gt hlogm]

/-- Quotient-cardinality specialization of the strict scaled-log margin. -/
theorem quotient_logBudget_of_scaledLog_margin [Nonempty Q]
    {m A κ : ℝ}
    (hcard : (Fintype.card Q : ℝ) = m)
    (hlogm : 0 < Real.log m)
    (hκ : 1 + Real.log A / Real.log m < κ) :
    Real.log (Fintype.card Q : ℝ) + Real.log A < κ * Real.log m := by
  simpa [hcard] using log_add_lt_scaled_log_of_one_add_div_lt hlogm hκ

/-- Quotient-cardinality specialization of the non-strict scaled-log obstruction. -/
theorem quotient_logBudget_obstruction_of_scaledLog_le [Nonempty Q]
    {m A κ : ℝ}
    (hcard : (Fintype.card Q : ℝ) = m)
    (hlogm : 0 < Real.log m)
    (hκ : κ ≤ 1 + Real.log A / Real.log m) :
    κ * Real.log m ≤ Real.log (Fintype.card Q : ℝ) + Real.log A := by
  simpa [hcard] using scaled_log_le_log_add_of_le_one_add_div hlogm hκ

/-! ## Consuming tails with rate `κ * log m` -/

/-- A quotient-tail estimate with rate `κ * log m` gives the pulled-back pointwise bound once
`κ` beats `1 + log A / log m`. -/
theorem pulledBack_forall_le_of_scaledLogTail [Nonempty Q]
    (quot : α -> Q) {Y : Q -> ℝ} {T m A κ : ℝ}
    (hcard : (Fintype.card Q : ℝ) = m)
    (hlogm : 0 < Real.log m)
    (hA : 0 < A)
    (hmass : quotientTailMass Y T ≤ A * Real.exp (-(κ * Real.log m)))
    (hκ : 1 + Real.log A / Real.log m < κ) :
    ∀ a : α, Y (quot a) ≤ T := by
  have hcard_pos : (0 : ℝ) < (Fintype.card Q : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty Q))
  have hbudget : (Fintype.card Q : ℝ) * (A * Real.exp (-(κ * Real.log m))) < 1 :=
    mul_exponentialTail_lt_one_of_log_budget hcard_pos hA
      (quotient_logBudget_of_scaledLog_margin (Q := Q) hcard hlogm hκ)
  exact pulledBack_forall_le_of_quotientTailMass_bound_card_mul_lt_one
    (Q := Q) quot (Y := Y) (T := T) (U := A * Real.exp (-(κ * Real.log m)))
    hmass hbudget

/-- If `κ <= 1 + log A / log m`, the scaled-log quotient-tail budget is still compatible with one
bad pulled-back atom. -/
theorem scaledLogTail_budget_allows_pulledBack_spike_of_constant_le
    [Nonempty α] [Nonempty Q] [DecidableEq Q]
    (quot : α -> Q) {T m A κ : ℝ}
    (hcard : (Fintype.card Q : ℝ) = m)
    (hlogm : 0 < Real.log m)
    (hA : 0 < A)
    (hκ : κ ≤ 1 + Real.log A / Real.log m) :
    ∃ Y : Q -> ℝ,
      quotientTailMass Y T ≤ A * Real.exp (-(κ * Real.log m)) ∧
        ∃ a : α, T < Y (quot a) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card Q : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty Q))
  have hbudget : 1 ≤ (Fintype.card Q : ℝ) * (A * Real.exp (-(κ * Real.log m))) :=
    one_le_mul_exponentialTail_of_log_budget_le hcard_pos hA
      (quotient_logBudget_obstruction_of_scaledLog_le (Q := Q) hcard hlogm hκ)
  exact quotientTail_budget_allows_pulledBack_spike_of_one_le_card_mul
    (Q := Q) quot (T := T) (U := A * Real.exp (-(κ * Real.log m))) hbudget

/-! ## Subgaussian prize-threshold packaging -/

/-- If `T^2 = C^2 * n * log m` and `κ = c*C^2*n/V`, then the subgaussian exponent
`c*T^2/V` is exactly `κ * log m`. -/
theorem subGaussian_rate_eq_scaled_log_of_sq_threshold
    {T m c C n V κ : ℝ}
    (hT : T ^ 2 = C ^ 2 * n * Real.log m)
    (hκ : κ = c * C ^ 2 * n / V) :
    c * T ^ 2 / V = κ * Real.log m := by
  rw [hT, hκ]
  ring

/-- Prize-threshold subgaussian consumer.  Once the exponent has the scaled-log form
`c*T^2/V = κ*log m`, the constant condition is `1 + log A / log m < κ`. -/
theorem pulledBack_forall_le_of_prizeSubGaussianRate [Nonempty Q]
    (quot : α -> Q) {Y : Q -> ℝ} {T m A c V κ : ℝ}
    (hcard : (Fintype.card Q : ℝ) = m)
    (hlogm : 0 < Real.log m)
    (hA : 0 < A)
    (hrate : c * T ^ 2 / V = κ * Real.log m)
    (hmass : quotientTailMass Y T ≤ A * Real.exp (-(c * T ^ 2 / V)))
    (hκ : 1 + Real.log A / Real.log m < κ) :
    ∀ a : α, Y (quot a) ≤ T := by
  have hmass' : quotientTailMass Y T ≤ A * Real.exp (-(κ * Real.log m)) := by
    simpa [hrate] using hmass
  exact pulledBack_forall_le_of_scaledLogTail (Q := Q) quot
    (Y := Y) (T := T) (m := m) (A := A) (κ := κ) hcard hlogm hA hmass' hκ

/-- Prize-threshold subgaussian obstruction.  If the scaled-log constant is at or below
`1 + log A / log m`, the subgaussian-looking budget still admits one bad quotient atom. -/
theorem prizeSubGaussian_budget_allows_spike_of_constant_le
    [Nonempty α] [Nonempty Q] [DecidableEq Q]
    (quot : α -> Q) {T m A c V κ : ℝ}
    (hcard : (Fintype.card Q : ℝ) = m)
    (hlogm : 0 < Real.log m)
    (hA : 0 < A)
    (hrate : c * T ^ 2 / V = κ * Real.log m)
    (hκ : κ ≤ 1 + Real.log A / Real.log m) :
    ∃ Y : Q -> ℝ,
      quotientTailMass Y T ≤ A * Real.exp (-(c * T ^ 2 / V)) ∧
        ∃ a : α, T < Y (quot a) := by
  rcases scaledLogTail_budget_allows_pulledBack_spike_of_constant_le (Q := Q) quot
      (T := T) (m := m) (A := A) (κ := κ) hcard hlogm hA hκ with
    ⟨Y, hmass, hspike⟩
  refine ⟨Y, ?_, hspike⟩
  simpa [hrate] using hmass

/-- Convenience consumer using the squared prize-threshold identity
`T^2 = C^2*n*log m`. -/
theorem pulledBack_forall_le_of_prizeSquaredSubGaussianTail [Nonempty Q]
    (quot : α -> Q) {Y : Q -> ℝ} {T m A c C n V κ : ℝ}
    (hcard : (Fintype.card Q : ℝ) = m)
    (hlogm : 0 < Real.log m)
    (hA : 0 < A)
    (hT : T ^ 2 = C ^ 2 * n * Real.log m)
    (hκdef : κ = c * C ^ 2 * n / V)
    (hmass : quotientTailMass Y T ≤ A * Real.exp (-(c * T ^ 2 / V)))
    (hκ : 1 + Real.log A / Real.log m < κ) :
    ∀ a : α, Y (quot a) ≤ T :=
  pulledBack_forall_le_of_prizeSubGaussianRate (Q := Q) quot
    (Y := Y) (T := T) (m := m) (A := A) (c := c) (V := V) (κ := κ)
    hcard hlogm hA (subGaussian_rate_eq_scaled_log_of_sq_threshold hT hκdef) hmass hκ

end ArkLib.ProximityGap.Frontier.QuotientScaledLogTailGate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.QuotientScaledLogTailGate.mul_exponentialTail_lt_one_of_log_budget
#print axioms ArkLib.ProximityGap.Frontier.QuotientScaledLogTailGate.one_le_mul_exponentialTail_of_log_budget_le
#print axioms ArkLib.ProximityGap.Frontier.QuotientScaledLogTailGate.log_add_lt_scaled_log_of_one_add_div_lt
#print axioms ArkLib.ProximityGap.Frontier.QuotientScaledLogTailGate.scaled_log_le_log_add_of_le_one_add_div
#print axioms ArkLib.ProximityGap.Frontier.QuotientScaledLogTailGate.quotient_logBudget_of_scaledLog_margin
#print axioms ArkLib.ProximityGap.Frontier.QuotientScaledLogTailGate.pulledBack_forall_le_of_scaledLogTail
#print axioms ArkLib.ProximityGap.Frontier.QuotientScaledLogTailGate.scaledLogTail_budget_allows_pulledBack_spike_of_constant_le
#print axioms ArkLib.ProximityGap.Frontier.QuotientScaledLogTailGate.subGaussian_rate_eq_scaled_log_of_sq_threshold
#print axioms ArkLib.ProximityGap.Frontier.QuotientScaledLogTailGate.pulledBack_forall_le_of_prizeSubGaussianRate
#print axioms ArkLib.ProximityGap.Frontier.QuotientScaledLogTailGate.prizeSubGaussian_budget_allows_spike_of_constant_le
#print axioms ArkLib.ProximityGap.Frontier.QuotientScaledLogTailGate.pulledBack_forall_le_of_prizeSquaredSubGaussianTail
