/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSecondMomentSharp
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandFailureClosedForm

/-!
# The SHARP closed-form deep-band failure count (#389)

Re-instantiates `deep_band_failure_closed_form` through the sharp moment chain
(`sum_N2_le_sharp` → `deep_band_badSet_card_of_moments_sharp`): with

  `Λ' := P/q^(m+1) + C'/q + 3`   (ℕ-division; `C' := C(k+m+1,k+1)·C(n−(k+1),m)`)

the sharp budget clears unconditionally (`closedForm_budget_sharp` — the four-way
allocation `(P/q^(m+1)+1) + (C'/q+1) + 1 + Λ' = 2Λ'`; the diagonal costs its own unit,
which is why `+3`: probe `probe_sharp_budget_instantiation.py` records the `+2` variant
failing exactly at `(13,9,2,1)` where the deep bucket has zero slack), giving

> **`deep_band_failure_closed_form_sharp`** — `∃ Q₀ : P·Λ'/q^m ≤ #badSet(Q₀,xᵏ)·Λ'²`
> at every band radius, no side conditions — **badSet ≳ P/(q^m·Λ')** with
> `Λ' ≈ max(P/q^(m+1), C'/q)`: a full factor `q` below the landed
> `Λ ≈ max(P/q^(m+1), C')` wherever `C'` dominates (the sub-bandwidth regime).

Probe: budget integer-exact vs TRUE deep-pair counts at six tuples; the sharp floor
dominates the landed floor everywhere measured (e.g. `4` vs `0` at `(131,16,2,1)`).

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

set_option linter.style.longLine false

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- `budget_of_numeric` for the sharp strata shape. -/
theorem budget_of_numeric_sharp (dom : Fin n ↪ F) (k m : ℕ) {M : ℕ}
    (hM : 2 * (k + m + 1) ≤ M) {L V : ℕ}
    (hnum : ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2 * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card) * (Fintype.card F) ^ (M - (m + 1))
        + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (Fintype.card F) ^ (M - m))) :
    ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2 * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card) * (Fintype.card F) ^ (M - (m + 1))
        + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (Fintype.card F) ^ (M - m)
        + V * (Fintype.card F) ^ M
      ≤ 2 * L * (∑ c : Fin M → F,
          (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter (fun T => IsCoherent dom k m T (genPoly c))).card) := by
  classical
  refine le_trans hnum (Nat.mul_le_mul_left _ ?_)
  have h := sum_N1_eq dom k m (M := M) (by omega)
  have hqm : (Fintype.card F) ^ M
      = (Fintype.card F) ^ (M - m) * (Fintype.card F) ^ m := by
    rw [← pow_add]
    congr 1
    omega
  rw [hqm, ← mul_assoc] at h
  have := Nat.eq_of_mul_eq_mul_right (pow_pos Fintype.card_pos m) h
  omega

open Classical in
/-- **The sharp closed-form budget**: the `(Λ', V)` choice clears the SHARP moment
budget unconditionally — four-way allocation, the diagonal on its own unit. -/
theorem closedForm_budget_sharp (dom : Fin n ↪ F) (k m : ℕ) {M : ℕ}
    (hM : 2 * (k + m + 1) ≤ M) :
    ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card ^ 2 * (Fintype.card F) ^ (M - (2 * m + 1))
        + (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card) * (Fintype.card F) ^ (M - (m + 1))
        + ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (Fintype.card F) ^ (M - m)
        + (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card / (Fintype.card F) ^ (m + 1) + ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m) / (Fintype.card F) + 3) / (Fintype.card F) ^ m) * (Fintype.card F) ^ M
      ≤ 2 * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card / (Fintype.card F) ^ (m + 1) + ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m) / (Fintype.card F) + 3) * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (Fintype.card F) ^ (M - m)) := by
  classical
  set P : ℕ := ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card with hP
  set q : ℕ := Fintype.card F with hq
  set C' : ℕ := (k + m + 1).choose (k + 1) * (n - (k + 1)).choose m with hC'
  set D : ℕ := (((((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)) ×ˢ (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)))).filter (fun p => p.1 ≠ p.2 ∧ k < (p.1 ∩ p.2).card)).card) with hD
  set Λ : ℕ := P / q ^ (m + 1) + C' / q + 3 with hΛ
  have hq1 : 0 < q := Fintype.card_pos
  have hqm : 0 < q ^ m := pow_pos Fintype.card_pos m
  have hqm1 : 0 < q ^ (m + 1) := pow_pos Fintype.card_pos (m + 1)
  have hexp1 : (m + 1) + (M - (2 * m + 1)) = M - m := by omega
  have hexp2 : m + (M - m) = M := by omega
  have hexp3 : (M - (m + 1)) + 1 = M - m := by omega
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
  -- term 2 (SHARP): D·q^(M−(m+1)) ≤ (C'/q + 1)·P·q^(M−m)
  have hDle : D ≤ P * C' := by
    have h := deepPairs_card_le (n := n) k m
    rw [hD, hP, hC']
    exact h
  have ht2 : D * q ^ (M - (m + 1)) ≤ (C' / q + 1) * P * q ^ (M - m) := by
    have hCdiv : C' < (C' / q + 1) * q := by
      calc C' = q * (C' / q) + C' % q := (Nat.div_add_mod _ _).symm
        _ < q * (C' / q) + q := Nat.add_lt_add_left (Nat.mod_lt _ hq1) _
        _ = (C' / q + 1) * q := by ring
    calc D * q ^ (M - (m + 1))
        ≤ (P * C') * q ^ (M - (m + 1)) := Nat.mul_le_mul_right _ hDle
      _ ≤ (P * ((C' / q + 1) * q)) * q ^ (M - (m + 1)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (le_of_lt hCdiv))
      _ = (C' / q + 1) * P * (q ^ (M - (m + 1)) * q ^ 1) := by ring
      _ = (C' / q + 1) * P * q ^ (M - m) := by
          rw [← pow_add, hexp3]
  -- term 3 (diagonal): P·q^(M−m) ≤ 1·P·q^(M−m)
  have ht_diag : P * q ^ (M - m) ≤ 1 * P * q ^ (M - m) := by
    rw [one_mul]
  -- term 4: V·q^M ≤ Λ·P·q^(M−m)
  have ht3 : (P * Λ / q ^ m) * q ^ M ≤ Λ * P * q ^ (M - m) := by
    calc (P * Λ / q ^ m) * q ^ M
        = (P * Λ / q ^ m) * (q ^ m * q ^ (M - m)) := by rw [← pow_add, hexp2]
      _ = ((P * Λ / q ^ m) * q ^ m) * q ^ (M - m) := by ring
      _ ≤ (P * Λ) * q ^ (M - m) :=
          Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
      _ = Λ * P * q ^ (M - m) := by ring
  have hsum : (P / q ^ (m + 1) + 1) + (C' / q + 1) + 1 + Λ = 2 * Λ := by
    rw [hΛ]
    ring
  calc P ^ 2 * q ^ (M - (2 * m + 1)) + D * q ^ (M - (m + 1))
        + P * q ^ (M - m) + (P * Λ / q ^ m) * q ^ M
      ≤ (P / q ^ (m + 1) + 1) * P * q ^ (M - m)
        + (C' / q + 1) * P * q ^ (M - m)
        + 1 * P * q ^ (M - m)
        + Λ * P * q ^ (M - m) := by
        exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ht1 ht2) ht_diag) ht3
    _ = ((P / q ^ (m + 1) + 1) + (C' / q + 1) + 1 + Λ) * (P * q ^ (M - m)) := by ring
    _ = 2 * Λ * (P * q ^ (M - m)) := by rw [hsum]

open Classical in
/-- **THE SHARP CLOSED-FORM DEEP-BAND FAILURE COUNT.**  At every band radius, with
`Λ' := P/q^(m+1) + C'/q + 3`:  `∃ Q₀ : P·Λ'/q^m ≤ #badSet(Q₀, x^k)·Λ'²` — the failure
floor `badSet ≳ P/(q^m·Λ')` with `Λ' ≈ max(P/q^(m+1), C'/q)`, a full factor `q` below
the landed closed form wherever `C'` dominates. -/
theorem deep_band_failure_closed_form_sharp (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0)) :
    ∃ Q₀ : F[X],
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card / (Fintype.card F) ^ (m + 1) + ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m) / (Fintype.card F) + 3) / (Fintype.card F) ^ m)
        ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
              ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
              (fun i => Q₀.eval (dom i)) (fun i => (dom i) ^ k) γ)).card
            * (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card / (Fintype.card F) ^ (m + 1) + ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m) / (Fintype.card F) + 3) ^ 2 := by
  classical
  exact deep_band_badSet_card_of_moments_sharp dom hk hhi
    (M := 2 * (k + m + 1)) le_rfl
    (budget_of_numeric_sharp dom k m le_rfl (closedForm_budget_sharp dom k m le_rfl))

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.budget_of_numeric_sharp
#print axioms ProximityGap.PairRank.closedForm_budget_sharp
#print axioms ProximityGap.PairRank.deep_band_failure_closed_form_sharp
