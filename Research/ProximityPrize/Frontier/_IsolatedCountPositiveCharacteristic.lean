/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE.
Authors: danghuy174
-/
import Research.ProximityPrize.Frontier._AntipodalEvenOddDescent
import Mathlib.Algebra.CharP.Defs

/-!
# `IsolatedCountResidual` fails in positive characteristic

The rational counterexample in `_IsolatedCountResidualRefuted.lean` uses the interpolant
`E(u) = -u²/6 + 7u/6` to produce three isolated roots `0, 1, 2` for `O = 1` at `k = 1`.
Because the denominator only involves the prime factors 2 and 3, this integer certificate
survives in every field where `(2 : F) ≠ 0` and `(3 : F) ≠ 0`.

Consequently, restricting to positive characteristic `p > 3` cannot repair the unrestricted
residual. Any genuine repair must impose the halved-subgroup domain restriction or degree/head
bounds on `E`.
-/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ProximityGap.Frontier.IsolatedCountPositiveCharacteristic

open AntipodalEvenOddDescent

/-- The interpolant `E(u) = -u²/6 + 7u/6` defined over any field where 6 is invertible. -/
def witnessE (F : Type*) [Field F] (inv6 : F) : F[X] :=
  C (-inv6) * X ^ 2 + C ((7 : F) * inv6) * X

theorem witnessE_eval_zero (F : Type*) [Field F] (inv6 : F) :
    (witnessE F inv6).eval 0 = 0 := by
  simp [witnessE]

theorem witnessE_eval_one (F : Type*) [Field F] (inv6 : F) (hinv : (6 : F) * inv6 = 1) :
    (witnessE F inv6).eval 1 = 1 := by
  simp only [witnessE, eval_add, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
  have : -(inv6) + (7 : F) * inv6 = (6 : F) * inv6 := by ring
  rw [this, hinv]

theorem witnessE_eval_four (F : Type*) [Field F] (inv6 : F) (hinv : (6 : F) * inv6 = 1) :
    (witnessE F inv6).eval 4 = 2 := by
  simp only [witnessE, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  have : -(inv6) * 4 ^ 2 + (7 : F) * inv6 * 4 = 2 * ((6 : F) * inv6) := by ring
  rw [this, hinv, mul_one]

open Classical in
/-- The three isolated roots `0, 1, 2` of `witnessE(X²) - X · 1`. -/
theorem witnessE_three_isolated_roots (F : Type*) [Field F] (inv6 : F)
    (hinv : (6 : F) * inv6 = 1) :
    (↑({0, 1, 2} : Finset F) : Set F) ⊆
      {x : F | ((witnessE F inv6).comp (X ^ 2) - X * (C (1 : F)).comp (X ^ 2)).IsRoot x ∧
        (C (1 : F)).eval (x ^ 2) ≠ 0} := by
  intro x hx
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  refine ⟨?_, by simp only [eval_C, ne_eq, one_ne_zero, not_false_eq_true]⟩
  rw [IsRoot.def, eval_sub, eval_mul, eval_X, eval_comp, eval_comp, eval_C]
  simp only [eval_pow, eval_X]
  rcases hx with rfl | rfl | rfl
  · have h0sq : (0 : F) ^ 2 = 0 := by ring
    rw [h0sq, witnessE_eval_zero]
    ring
  · have h1sq : (1 : F) ^ 2 = 1 := by ring
    rw [h1sq, witnessE_eval_one F inv6 hinv]
    ring
  · have h2sq : (2 : F) ^ 2 = 4 := by ring
    rw [h2sq, witnessE_eval_four F inv6 hinv]
    ring

open Classical in
/-- The set `{0, 1, 2}` has cardinality 3 in any field of characteristic `≠ 2`. -/
theorem card_zero_one_two (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    ({0, 1, 2} : Finset F).card = 3 := by
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  have h02 : (0 : F) ≠ 2 := Ne.symm h2
  have h12 : (1 : F) ≠ 2 := by
    intro h
    apply zero_ne_one (α := F)
    calc (0 : F) = 2 - 2 := (sub_self _).symm
         _ = 2 - 1 := by rw [← h]
         _ = 1 := by ring
  simp [h01, h02, h12]

/-- `IsolatedCountResidual F 1` is false in every field where 2 and 3 are nonzero. -/
theorem not_isolatedCountResidual_of_small_primes_ne_zero
    (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ¬ IsolatedCountResidual F 1 := by
  classical
  have h6 : (6 : F) ≠ 0 := by
    have : (6 : F) = (2 : F) * 3 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h3
  have hinv : (6 : F) * (6 : F)⁻¹ = 1 := mul_inv_cancel₀ h6
  intro h
  have hOdeg : (C (1 : F)).natDegree < 1 := by simp
  have hc := (h (witnessE F (6 : F)⁻¹) (C 1) hOdeg).2 {0, 1, 2}
    (witnessE_three_isolated_roots F (6 : F)⁻¹ hinv)
  rw [card_zero_one_two F h2] at hc
  omega

/-- Restricting `IsolatedCountResidual` to any prime characteristic above three cannot repair it. -/
theorem not_isolatedCountResidual_of_char_gt_three
    (F : Type*) [Field F] (p : ℕ) [CharP F p] (hp : 3 < p) :
    ¬ IsolatedCountResidual F 1 := by
  have hsmall (n : ℕ) (hn : 0 < n) (hlt : n < p) : (n : F) ≠ 0 := by
    intro h
    have hdiv := (CharP.cast_eq_zero_iff F p n).mp h
    have hle := Nat.le_of_dvd hn hdiv
    omega
  exact not_isolatedCountResidual_of_small_primes_ne_zero F
    (hsmall 2 (by norm_num) (by omega))
    (hsmall 3 (by norm_num) (by omega))

/-- In characteristic zero, `IsolatedCountResidual F 1` is false. -/
theorem not_isolatedCountResidual_of_char_zero
    (F : Type*) [Field F] [CharZero F] :
    ¬ IsolatedCountResidual F 1 := by
  exact not_isolatedCountResidual_of_small_primes_ne_zero F
    (by norm_num) (by norm_num)
end ProximityGap.Frontier.IsolatedCountPositiveCharacteristic

#print axioms ProximityGap.Frontier.IsolatedCountPositiveCharacteristic.witnessE_three_isolated_roots
#print axioms ProximityGap.Frontier.IsolatedCountPositiveCharacteristic.card_zero_one_two
#print axioms ProximityGap.Frontier.IsolatedCountPositiveCharacteristic.not_isolatedCountResidual_of_small_primes_ne_zero
#print axioms ProximityGap.Frontier.IsolatedCountPositiveCharacteristic.not_isolatedCountResidual_of_char_gt_three
#print axioms ProximityGap.Frontier.IsolatedCountPositiveCharacteristic.not_isolatedCountResidual_of_char_zero

