/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSecondMoment

/-!
# The closed-form deep-band failure count: the (L, V) instantiation

Issue #389, route-2 capstone. The second-moment machine
(`DeepBandSecondMoment.lean`: exact moments → integer Cauchy–Schwarz → pigeonhole →
`deep_band_badSet_card_of_moments`, with the numeric reduction `budget_of_numeric` and the
deep-pair count `deepPairs_card_le`) is closed-form but parametric in `(L, V)`. This file
runs the optimization: with

* `Λ := P / q^(m+1) + C' + 2` (ℕ-division), where `P := C(n, k+m+1)` is the core count
  and `C' := C(k+m+1, k+1)·C(n−(k+1), m)` the deep-pair degree, and
* `V := P·Λ / q^m`,

the moment budget clears **unconditionally** (`closedForm_budget`), and therefore at every
band radius, with no side conditions:

> **`deep_band_failure_closed_form`** — `∃ Q₀ : P·Λ/q^m ≤ #badSet(Q₀, x^k) · Λ²`,

the unconditional deep-band failure count `badSet ≳ P/(q^m·Λ)` with
`Λ ≈ max(P/q^(m+1), C')`. In the bandwidth zone (`P ≥ C'·q^(m+1)`) this recovers the
`q/2`-failure of the capacity-failure bandwidth law; **below it the failure count stays
proportional to the witness mass divided by `q^m·C'` at every band** — the first
unconditional quantitative failure bound covering the whole deep band, and a proven
calibration floor for the open supply wall: any positive supply route must beat the
effective constant `2(C'+2)`.

Probe: `scripts/probes/probe_budget_instantiation.py` — budget verified integer-exactly
against TRUE deep-pair counts (not the `deepPairs_card_le` bound) on six parameter tuples.

## References

* Issue #389; `DeepBandSecondMoment.lean` (the machine), `DeepBandCoherence.lean`
  (the witness-mass law this quantifies).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The closed-form budget**: the optimized `(Λ, V)` choice clears the numeric moment
budget unconditionally. -/
theorem closedForm_budget (dom : Fin n ↪ F) (k m : ℕ) {M : ℕ}
    (hM : 2 * (k + m + 1) ≤ M) :
    ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2
          * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
            (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card
          + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card)
          * (Fintype.card F) ^ (M - m)
        + (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
            * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
                / (Fintype.card F) ^ (m + 1)
              + (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2)
            / (Fintype.card F) ^ m)
          * (Fintype.card F) ^ M
      ≤ 2 * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
            / (Fintype.card F) ^ (m + 1)
          + (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2)
        * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
          * (Fintype.card F) ^ (M - m)) := by
  classical
  set P : ℕ := ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card with hP
  set q : ℕ := Fintype.card F with hq
  set C' : ℕ := (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m with hC'
  set D : ℕ := (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter
      (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card) with hD
  set Λ : ℕ := P / q ^ (m + 1) + C' + 2 with hΛ
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hqm : 0 < q ^ m := pow_pos Fintype.card_pos m
  have hqm1 : 0 < q ^ (m + 1) := pow_pos Fintype.card_pos (m + 1)
  -- exponent bookkeeping: M − (2m+1) + (m+1) = M − m, and M = m + (M − m)
  have hexp1 : (m + 1) + (M - (2 * m + 1)) = M - m := by omega
  have hexp2 : m + (M - m) = M := by omega
  -- term 1: P²·q^(M−2m−1) ≤ (P/q^(m+1) + 1)·P·q^(M−m)
  have ht1 : P ^ 2 * q ^ (M - (2 * m + 1))
      ≤ (P / q ^ (m + 1) + 1) * P * q ^ (M - m) := by
    have hdiv : P < (P / q ^ (m + 1) + 1) * q ^ (m + 1) := by
      calc P = q ^ (m + 1) * (P / q ^ (m + 1)) + P % q ^ (m + 1) :=
            (Nat.div_add_mod _ _).symm
        _ < q ^ (m + 1) * (P / q ^ (m + 1)) + q ^ (m + 1) :=
            Nat.add_lt_add_left (Nat.mod_lt _ hqm1) _
        _ = (P / q ^ (m + 1) + 1) * q ^ (m + 1) := by ring
    calc P ^ 2 * q ^ (M - (2 * m + 1))
        = P * (P * q ^ (M - (2 * m + 1))) := by ring
      _ ≤ P * (((P / q ^ (m + 1) + 1) * q ^ (m + 1)) * q ^ (M - (2 * m + 1))) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (le_of_lt hdiv))
      _ = (P / q ^ (m + 1) + 1) * P * (q ^ (m + 1) * q ^ (M - (2 * m + 1))) := by ring
      _ = (P / q ^ (m + 1) + 1) * P * q ^ (M - m) := by
          rw [← pow_add, hexp1]
  -- term 2: (D + P)·q^(M−m) ≤ (C' + 1)·P·q^(M−m)
  have hDle : D ≤ P * C' := by
    have h := deepPairs_card_le (n := n) k m
    rw [hD, hP, hC']
    exact h
  have ht2 : (D + P) * q ^ (M - m) ≤ (C' + 1) * P * q ^ (M - m) := by
    have : D + P ≤ (C' + 1) * P := by
      calc D + P ≤ P * C' + P := by omega
        _ = (C' + 1) * P := by ring
    exact Nat.mul_le_mul_right _ this
  -- term 3: V·q^M ≤ Λ·P·q^(M−m), since V = P·Λ/q^m
  have ht3 : (P * Λ / q ^ m) * q ^ M ≤ Λ * P * q ^ (M - m) := by
    calc (P * Λ / q ^ m) * q ^ M
        = (P * Λ / q ^ m) * (q ^ m * q ^ (M - m)) := by rw [← pow_add, hexp2]
      _ = ((P * Λ / q ^ m) * q ^ m) * q ^ (M - m) := by ring
      _ ≤ (P * Λ) * q ^ (M - m) :=
          Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
      _ = Λ * P * q ^ (M - m) := by ring
  -- assemble: the three allocations sum to (2Λ)·P·q^(M−m) exactly
  have hsum : (P / q ^ (m + 1) + 1) + (C' + 1) + Λ = 2 * Λ := by
    rw [hΛ]
    ring
  calc P ^ 2 * q ^ (M - (2 * m + 1)) + (D + P) * q ^ (M - m)
        + (P * Λ / q ^ m) * q ^ M
      ≤ (P / q ^ (m + 1) + 1) * P * q ^ (M - m) + (C' + 1) * P * q ^ (M - m)
        + Λ * P * q ^ (M - m) := by
        exact Nat.add_le_add (Nat.add_le_add ht1 ht2) ht3
    _ = ((P / q ^ (m + 1) + 1) + (C' + 1) + Λ) * (P * q ^ (M - m)) := by ring
    _ = 2 * Λ * (P * q ^ (M - m)) := by rw [hsum]

open Classical in
/-- **THE CLOSED-FORM DEEP-BAND FAILURE COUNT.**  At every band radius
(`(1−δ)n ≤ k+m+1`), with `P := C(n, k+m+1)`, `C' := C(k+m+1,k+1)·C(n−(k+1),m)`, and
`Λ := P/q^(m+1) + C' + 2`, some stack of the generated family has at least
`(P·Λ/q^m) / Λ²` bad scalars — unconditionally:

  `∃ Q₀ : P·Λ/q^m ≤ #badSet(Q₀, x^k) · Λ²`.

In the bandwidth zone (`P ≥ C'·q^(m+1)`) this is the `≳ q/2` failure; below it the
failure count stays `≳ P/(2·q^m·(C'+2))` — proportional to the witness mass at every
band, with no side conditions. -/
theorem deep_band_failure_closed_form (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0)) :
    ∃ Q₀ : F[X],
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
          * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
              / (Fintype.card F) ^ (m + 1)
            + (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2)
          / (Fintype.card F) ^ m)
        ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
              ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
              (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
            * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
                / (Fintype.card F) ^ (m + 1)
              + (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2) ^ 2 := by
  classical
  exact deep_band_badSet_card_of_moments dom hk hhi
    (M := 2 * (k + m + 1)) le_rfl
    (budget_of_numeric dom k m le_rfl (closedForm_budget dom k m le_rfl))

/-! ## Source audit -/

#print axioms closedForm_budget
#print axioms deep_band_failure_closed_form

end ProximityGap.PairRank
