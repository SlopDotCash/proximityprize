/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._QuotientTailSupConsumer
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Exponential quotient-tail gate

`_QuotientTailSupConsumer` records the exact finite atom gate:

`quotientTailMass Y T <= U` proves `Y (quot a) <= T` for every pulled-back atom once
`#Q * U < 1`, and a one-quotient-atom spike remains compatible when `1 <= #Q * U`.

This file packages that gate in the exponential form used by subgaussian, large-deviation, and
Lamzouri-style tail estimates.  A tail estimate

`quotientTailMass Y T <= A * exp(-rate)`

becomes a pointwise theorem only after the rate beats the quotient entropy plus prefactor:

`log #Q + log A < rate`.

Conversely, if `rate <= log #Q + log A`, the same exponential budget is still large enough for one
bad quotient atom.  Thus the missing analytic input for the issue #464 floor is not merely a tail
shape; it must cross this strict quotient-union threshold at the prize value of `T`.
-/

namespace ArkLib.ProximityGap.Frontier.QuotientExponentialTailGate

open ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer

variable {α Q : Type} [Fintype Q]

/-! ## Exponential budgets versus logarithmic rate margins -/

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

/-- Quotient-cardinality specialization of the strict logarithmic rate margin. -/
theorem quotient_card_mul_exponentialTail_lt_one_of_log_budget [Nonempty Q]
    {A rate : ℝ} (hA : 0 < A)
    (hlog : Real.log (Fintype.card Q : ℝ) + Real.log A < rate) :
    (Fintype.card Q : ℝ) * (A * Real.exp (-rate)) < 1 := by
  have hcard_pos : (0 : ℝ) < (Fintype.card Q : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty Q))
  exact mul_exponentialTail_lt_one_of_log_budget hcard_pos hA hlog

/-- Quotient-cardinality specialization of the non-strict logarithmic obstruction. -/
theorem one_le_quotient_card_mul_exponentialTail_of_log_budget_le [Nonempty Q]
    {A rate : ℝ} (hA : 0 < A)
    (hlog : rate ≤ Real.log (Fintype.card Q : ℝ) + Real.log A) :
    1 ≤ (Fintype.card Q : ℝ) * (A * Real.exp (-rate)) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card Q : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty Q))
  exact one_le_mul_exponentialTail_of_log_budget_le hcard_pos hA hlog

/-! ## Consuming exponential quotient tails -/

/-- Exponential-tail consumer in operational form.  A quotient-tail estimate of size
`A * exp(-rate)` proves the pulled-back pointwise bound once the total quotient budget is below one.
-/
theorem pulledBack_forall_le_of_exponentialTail [Nonempty Q]
    (quot : α -> Q) {Y : Q -> ℝ} {T A rate : ℝ}
    (hmass : quotientTailMass Y T ≤ A * Real.exp (-rate))
    (hbudget : (Fintype.card Q : ℝ) * (A * Real.exp (-rate)) < 1) :
    ∀ a : α, Y (quot a) ≤ T :=
  pulledBack_forall_le_of_quotientTailMass_bound_card_mul_lt_one
    (Q := Q) quot (Y := Y) (T := T) (U := A * Real.exp (-rate)) hmass hbudget

/-- Exponential-tail consumer in logarithmic form: the analytic rate must beat
`log #Q + log A`. -/
theorem pulledBack_forall_le_of_exponentialTail_logBudget [Nonempty Q]
    (quot : α -> Q) {Y : Q -> ℝ} {T A rate : ℝ}
    (hA : 0 < A)
    (hmass : quotientTailMass Y T ≤ A * Real.exp (-rate))
    (hlog : Real.log (Fintype.card Q : ℝ) + Real.log A < rate) :
    ∀ a : α, Y (quot a) ≤ T :=
  pulledBack_forall_le_of_exponentialTail (Q := Q) quot (Y := Y) (T := T)
    hmass (quotient_card_mul_exponentialTail_lt_one_of_log_budget (Q := Q) hA hlog)

/-- Subgaussian quotient-tail consumer in operational form.  The threshold `T` proves a pulled-back
pointwise bound once `#Q * A * exp(-(c*T^2/V)) < 1`. -/
theorem pulledBack_forall_le_of_subGaussianTail [Nonempty Q]
    (quot : α -> Q) {Y : Q -> ℝ} {T A c V : ℝ}
    (hmass : quotientTailMass Y T ≤ A * Real.exp (-(c * T ^ 2 / V)))
    (hbudget : (Fintype.card Q : ℝ) * (A * Real.exp (-(c * T ^ 2 / V))) < 1) :
    ∀ a : α, Y (quot a) ≤ T :=
  pulledBack_forall_le_of_exponentialTail (Q := Q) quot
    (Y := Y) (T := T) (A := A) (rate := c * T ^ 2 / V) hmass hbudget

/-- Subgaussian quotient-tail consumer in logarithmic form.  At threshold `T`, the useful analytic
target is `log #Q + log A < c*T^2/V`. -/
theorem pulledBack_forall_le_of_subGaussianTail_logBudget [Nonempty Q]
    (quot : α -> Q) {Y : Q -> ℝ} {T A c V : ℝ}
    (hA : 0 < A)
    (hmass : quotientTailMass Y T ≤ A * Real.exp (-(c * T ^ 2 / V)))
    (hlog : Real.log (Fintype.card Q : ℝ) + Real.log A < c * T ^ 2 / V) :
    ∀ a : α, Y (quot a) ≤ T :=
  pulledBack_forall_le_of_exponentialTail_logBudget (Q := Q) quot
    (Y := Y) (T := T) (A := A) (rate := c * T ^ 2 / V) hA hmass hlog

/-! ## One-atom obstruction at the logarithmic boundary -/

/-- If the exponential quotient-tail budget is at least one quotient atom, a pulled-back spike above
threshold remains compatible with the estimate. -/
theorem exponentialTail_budget_allows_pulledBack_spike_of_one_le_card_mul
    [Nonempty α] [Nonempty Q] [DecidableEq Q]
    (quot : α -> Q) {T A rate : ℝ}
    (hbudget : 1 ≤ (Fintype.card Q : ℝ) * (A * Real.exp (-rate))) :
    ∃ Y : Q -> ℝ,
      quotientTailMass Y T ≤ A * Real.exp (-rate) ∧ ∃ a : α, T < Y (quot a) :=
  quotientTail_budget_allows_pulledBack_spike_of_one_le_card_mul
    (Q := Q) quot (T := T) (U := A * Real.exp (-rate)) hbudget

/-- Logarithmic obstruction form: if `rate <= log #Q + log A`, an exponential quotient-tail
estimate with prefactor `A` is still compatible with one bad pulled-back atom. -/
theorem exponentialTail_budget_allows_pulledBack_spike_of_log_budget_le
    [Nonempty α] [Nonempty Q] [DecidableEq Q]
    (quot : α -> Q) {T A rate : ℝ}
    (hA : 0 < A)
    (hlog : rate ≤ Real.log (Fintype.card Q : ℝ) + Real.log A) :
    ∃ Y : Q -> ℝ,
      quotientTailMass Y T ≤ A * Real.exp (-rate) ∧ ∃ a : α, T < Y (quot a) :=
  exponentialTail_budget_allows_pulledBack_spike_of_one_le_card_mul (Q := Q) quot
    (T := T) (A := A) (rate := rate)
    (one_le_quotient_card_mul_exponentialTail_of_log_budget_le (Q := Q) hA hlog)

/-- Subgaussian obstruction form.  If `c*T^2/V <= log #Q + log A`, the subgaussian-looking
quotient-tail budget has not crossed the one-atom scale. -/
theorem subGaussianTail_budget_allows_pulledBack_spike_of_log_budget_le
    [Nonempty α] [Nonempty Q] [DecidableEq Q]
    (quot : α -> Q) {T A c V : ℝ}
    (hA : 0 < A)
    (hlog : c * T ^ 2 / V ≤ Real.log (Fintype.card Q : ℝ) + Real.log A) :
    ∃ Y : Q -> ℝ,
      quotientTailMass Y T ≤ A * Real.exp (-(c * T ^ 2 / V)) ∧
        ∃ a : α, T < Y (quot a) :=
  exponentialTail_budget_allows_pulledBack_spike_of_log_budget_le (Q := Q) quot
    (T := T) (A := A) (rate := c * T ^ 2 / V) hA hlog

/-- Two-sided exponential quotient-tail gate: the strict budget gives the consumer, while the
opposite one-atom budget gives a spike model. -/
theorem exponentialQuotientTailGate [Nonempty α] [Nonempty Q] [DecidableEq Q]
    (quot : α -> Q) {T A rate : ℝ} :
    ((Fintype.card Q : ℝ) * (A * Real.exp (-rate)) < 1 ->
        ∀ Y : Q -> ℝ,
          quotientTailMass Y T ≤ A * Real.exp (-rate) ->
          ∀ a : α, Y (quot a) ≤ T)
      ∧
      (1 ≤ (Fintype.card Q : ℝ) * (A * Real.exp (-rate)) ->
        ∃ Y : Q -> ℝ,
          quotientTailMass Y T ≤ A * Real.exp (-rate) ∧
            ∃ a : α, T < Y (quot a)) := by
  constructor
  · intro hbudget Y hmass
    exact pulledBack_forall_le_of_exponentialTail (Q := Q) quot
      (Y := Y) (T := T) (A := A) (rate := rate) hmass hbudget
  · intro hbudget
    exact exponentialTail_budget_allows_pulledBack_spike_of_one_le_card_mul
      (Q := Q) quot (T := T) (A := A) (rate := rate) hbudget

end ArkLib.ProximityGap.Frontier.QuotientExponentialTailGate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.QuotientExponentialTailGate.mul_exponentialTail_lt_one_of_log_budget
#print axioms ArkLib.ProximityGap.Frontier.QuotientExponentialTailGate.one_le_mul_exponentialTail_of_log_budget_le
#print axioms ArkLib.ProximityGap.Frontier.QuotientExponentialTailGate.quotient_card_mul_exponentialTail_lt_one_of_log_budget
#print axioms ArkLib.ProximityGap.Frontier.QuotientExponentialTailGate.pulledBack_forall_le_of_exponentialTail
#print axioms ArkLib.ProximityGap.Frontier.QuotientExponentialTailGate.pulledBack_forall_le_of_exponentialTail_logBudget
#print axioms ArkLib.ProximityGap.Frontier.QuotientExponentialTailGate.pulledBack_forall_le_of_subGaussianTail
#print axioms ArkLib.ProximityGap.Frontier.QuotientExponentialTailGate.pulledBack_forall_le_of_subGaussianTail_logBudget
#print axioms ArkLib.ProximityGap.Frontier.QuotientExponentialTailGate.exponentialTail_budget_allows_pulledBack_spike_of_one_le_card_mul
#print axioms ArkLib.ProximityGap.Frontier.QuotientExponentialTailGate.exponentialTail_budget_allows_pulledBack_spike_of_log_budget_le
#print axioms ArkLib.ProximityGap.Frontier.QuotientExponentialTailGate.subGaussianTail_budget_allows_pulledBack_spike_of_log_budget_le
#print axioms ArkLib.ProximityGap.Frontier.QuotientExponentialTailGate.exponentialQuotientTailGate
