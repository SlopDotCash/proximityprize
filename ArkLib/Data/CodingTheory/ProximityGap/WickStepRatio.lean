/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-!
# Wick step-ratio telescoping (#444)

This file records the elementary algebra behind the corrected W3 framing in the proximity-prize notes:
for a nonnegative moment/energy sequence, the pointwise step inequality

`E_{r+1} ≤ (2r+1) n E_r`

telescopes from the base `E_1 ≤ n` to the Wick envelope

`E_r ≤ (2r-1)!! n^r`.

Honest scope: this is only a consumer bridge. It does not prove the char-`p` step inequality for Gauss
period energies, hence does not close CORE. It is the precise algebraic reduction target surfaced by the
latest probes: prove the step ratio, and Wick follows; fail the step ratio, and this bridge gives no help.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.WickStepRatio

/-- The Wick/Gaussian even-moment envelope `(2r-1)!! n^r`, as a natural number. -/
def wickEnvelope (n r : ℕ) : ℕ := Nat.doubleFactorial (2 * r - 1) * n ^ r

/-- The Wick envelope obeys the exact Gaussian step recurrence
`W_{r+1} = (2r+1) n W_r` for `r ≥ 1`. -/
theorem wickEnvelope_succ_eq (n r : ℕ) (hr : 1 ≤ r) :
    wickEnvelope n (r + 1) = (2 * r + 1) * n * wickEnvelope n r := by
  unfold wickEnvelope
  have hidx : 2 * (r + 1) - 1 = (2 * r - 1) + 2 := by omega
  rw [hidx, Nat.doubleFactorial_add_two, pow_succ]
  have hcoef : 2 * r - 1 + 2 = 2 * r + 1 := by omega
  rw [hcoef]
  ring

/-- **Step-ratio telescopes to Wick.** If a nonnegative sequence `E` satisfies the base bound
`E 1 ≤ n` and every step up to `r` obeys `E_{k+1} ≤ (2k+1)n E_k`, then `E r` is bounded by the
Wick envelope `(2r-1)!! n^r`.

This is the clean formal bridge for the corrected W3 target in #444. It is deliberately conditional:
the hard open input is the step inequality for the actual char-`p` energy sequence. -/
theorem le_wickEnvelope_of_step_ratio {E : ℕ → ℕ} {n r : ℕ} (hr : 1 ≤ r) (hbase : E 1 ≤ n)
    (hstep : ∀ k, 1 ≤ k → k < r → E (k + 1) ≤ (2 * k + 1) * n * E k) :
    E r ≤ wickEnvelope n r := by
  induction r, hr using Nat.le_induction with
  | base =>
      simpa [wickEnvelope] using hbase
  | succ r hr ih =>
      have hstep_r : E (r + 1) ≤ (2 * r + 1) * n * E r := hstep r hr (Nat.lt_succ_self r)
      have ih' : E r ≤ wickEnvelope n r := ih (fun k hk1 hkr =>
        hstep k hk1 (lt_trans hkr (Nat.lt_succ_self r)))
      have hmul : (2 * r + 1) * n * E r ≤ (2 * r + 1) * n * wickEnvelope n r := by
        exact Nat.mul_le_mul_left ((2 * r + 1) * n) ih'
      calc
        E (r + 1) ≤ (2 * r + 1) * n * E r := hstep_r
        _ ≤ (2 * r + 1) * n * wickEnvelope n r := hmul
        _ = wickEnvelope n (r + 1) := (wickEnvelope_succ_eq n r hr).symm

/-- Contrapositive witness form: if `E r` exceeds the Wick envelope despite `E 1 ≤ n`, then at least
one intermediate step ratio must fail. This pins any Wick failure to a concrete local step failure rather
than a vague global moment deficit. -/
theorem exists_step_ratio_failure_of_wick_failure {E : ℕ → ℕ} {n r : ℕ} (hr : 1 ≤ r)
    (hbase : E 1 ≤ n) (hfail : wickEnvelope n r < E r) :
    ∃ k, 1 ≤ k ∧ k < r ∧ (2 * k + 1) * n * E k < E (k + 1) := by
  by_contra hnone
  have hstep : ∀ k, 1 ≤ k → k < r → E (k + 1) ≤ (2 * k + 1) * n * E k := by
    intro k hk1 hkr
    by_contra hkfail
    have hklt : (2 * k + 1) * n * E k < E (k + 1) := Nat.lt_of_not_ge hkfail
    exact hnone ⟨k, hk1, hkr, hklt⟩
  have hwick := le_wickEnvelope_of_step_ratio hr hbase hstep
  exact not_lt_of_ge hwick hfail

#print axioms wickEnvelope_succ_eq
#print axioms le_wickEnvelope_of_step_ratio
#print axioms exists_step_ratio_failure_of_wick_failure

end ArkLib.ProximityGap.WickStepRatio
