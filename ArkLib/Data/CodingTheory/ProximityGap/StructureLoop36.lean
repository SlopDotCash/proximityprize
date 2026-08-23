/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Loop 36 — amplified additive injections are still safe under constant blowup

Loops 31--35 isolated the multiplicative exponent-density danger. This file checks a richer
recurrence shape that often appears in protocol soundness accounting:

    T(j+1) ≤ a*T(j) + b.

The attempted disproof is that additive per-fold injections might be harmless locally but become
dangerous after later multiplicative amplification. The recurrence does amplify them, but if the
multiplicative blowup per fold is a constant factor `2^c` and the additive injection is bounded, the
whole affine recurrence is still absorbed by one extra final-domain power.

Thus the remaining dangerous case is not merely "additive terms are later amplified"; it requires
unbounded multiplicative exponent density or unbounded additive injections inside the actual
smooth-domain GS/proximity mechanism. See `DISPROOF_LOG.md` (Loop36).
-/

namespace ArkLib.ProximityGap.StructureLoop36

/-- **The fold depth is bounded by the final smooth-domain size.** -/
theorem fold_depth_le_domain_pow (m : ℕ) : (m : ℝ) ≤ (2 : ℝ) ^ m := by
  exact_mod_cast (Nat.lt_two_pow_self (n := m)).le

/-- **Affine recurrence with constant factor.** If `T(j+1)≤a*T(j)+b`, with `a≥1` and `b≥0`, then
the additive injections are amplified by at most the final factor `a^m`, giving
`T(m)≤a^m*T(0)+m*b*a^m`. -/
theorem affine_recursion_amplified
    (T : ℕ → ℝ) {a b : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hstep : ∀ j, T (j + 1) ≤ a * T j + b) :
    ∀ m, T m ≤ a ^ m * T 0 + (m : ℝ) * b * a ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
      have ha0 : 0 ≤ a := le_trans (by norm_num : (0 : ℝ) ≤ 1) ha
      have hapow : 1 ≤ a ^ (n + 1) := one_le_pow₀ ha
      have hb_amp : b ≤ b * a ^ (n + 1) := by
        calc
          b = b * 1 := by ring
          _ ≤ b * a ^ (n + 1) := mul_le_mul_of_nonneg_left hapow hb
      have hmul : a * T n ≤ a * (a ^ n * T 0 + (n : ℝ) * b * a ^ n) :=
        mul_le_mul_of_nonneg_left ih ha0
      calc
        T (n + 1) ≤ a * T n + b := hstep n
        _ ≤ a * (a ^ n * T 0 + (n : ℝ) * b * a ^ n) + b := by linarith
        _ = a ^ (n + 1) * T 0 + (n : ℝ) * b * a ^ (n + 1) + b := by ring
        _ ≤ a ^ (n + 1) * T 0 + (n : ℝ) * b * a ^ (n + 1) + b * a ^ (n + 1) := by
          linarith
        _ = a ^ (n + 1) * T 0 + ((n + 1 : ℕ) : ℝ) * b * a ^ (n + 1) := by
          norm_num [Nat.cast_add, Nat.cast_one]
          ring

/-- **Constant per-fold factor matches a final-domain power.** -/
theorem pow_const_factor_eq_domain_pow (c m : ℕ) :
    ((2 : ℝ) ^ c) ^ m = ((2 : ℝ) ^ m) ^ c := by
  rw [← pow_mul, ← pow_mul]
  ring_nf

/-- **Affine recurrence under factor `2^c`.** With per-fold multiplicative factor exactly `2^c`,
the final amplification is the degree-`c` polynomial in the final domain size. -/
theorem affine_recursion_exact_constant_factor
    (T : ℕ → ℝ) {b : ℝ} (c : ℕ) (hb : 0 ≤ b)
    (hstep : ∀ j, T (j + 1) ≤ ((2 : ℝ) ^ c) * T j + b) :
    ∀ m, T m ≤ ((2 : ℝ) ^ m) ^ c * T 0 + (m : ℝ) * b * ((2 : ℝ) ^ m) ^ c := by
  intro m
  have h := affine_recursion_amplified T (a := (2 : ℝ) ^ c) (b := b)
    (by exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hb hstep m
  rwa [pow_const_factor_eq_domain_pow c m] at h

/-- **Bounded additive injections are absorbed by one extra final-domain power.** If the per-fold
factor is `2^c`, the base is nonnegative, and the additive injection is bounded by a nonnegative
constant `b`, then the whole affine recurrence is bounded by a degree-`c+1` final-domain polynomial
times the harmless coefficient `T(0)+b`. -/
theorem affine_recursion_constant_factor_absorbed
    (T : ℕ → ℝ) {b : ℝ} (c : ℕ) (hT0 : 0 ≤ T 0) (hb : 0 ≤ b)
    (hstep : ∀ j, T (j + 1) ≤ ((2 : ℝ) ^ c) * T j + b) :
    ∀ m, T m ≤ (T 0 + b) * ((2 : ℝ) ^ m) ^ (c + 1) := by
  intro m
  have hmain := affine_recursion_exact_constant_factor T c hb hstep m
  have hpow_nonneg : 0 ≤ ((2 : ℝ) ^ m) ^ c := by positivity
  have hdomain_ge_one : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hP_le_next : ((2 : ℝ) ^ m) ^ c ≤ ((2 : ℝ) ^ m) ^ (c + 1) := by
    exact pow_le_pow_right₀ hdomain_ge_one (Nat.le_succ c)
  have hm_le : (m : ℝ) ≤ (2 : ℝ) ^ m := fold_depth_le_domain_pow m
  have hterm0 : ((2 : ℝ) ^ m) ^ c * T 0 ≤ ((2 : ℝ) ^ m) ^ (c + 1) * T 0 := by
    exact mul_le_mul_of_nonneg_right hP_le_next hT0
  have htermb : (m : ℝ) * b * ((2 : ℝ) ^ m) ^ c ≤ ((2 : ℝ) ^ m) ^ (c + 1) * b := by
    calc
      (m : ℝ) * b * ((2 : ℝ) ^ m) ^ c ≤ ((2 : ℝ) ^ m) * b * ((2 : ℝ) ^ m) ^ c := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm_le hb) hpow_nonneg
      _ = ((2 : ℝ) ^ m) ^ (c + 1) * b := by ring
  calc
    T m ≤ ((2 : ℝ) ^ m) ^ c * T 0 + (m : ℝ) * b * ((2 : ℝ) ^ m) ^ c := hmain
    _ ≤ ((2 : ℝ) ^ m) ^ (c + 1) * T 0 + ((2 : ℝ) ^ m) ^ (c + 1) * b :=
      add_le_add hterm0 htermb
    _ = (T 0 + b) * ((2 : ℝ) ^ m) ^ (c + 1) := by ring

end ArkLib.ProximityGap.StructureLoop36

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop36.fold_depth_le_domain_pow
#print axioms ArkLib.ProximityGap.StructureLoop36.affine_recursion_amplified
#print axioms ArkLib.ProximityGap.StructureLoop36.pow_const_factor_eq_domain_pow
#print axioms ArkLib.ProximityGap.StructureLoop36.affine_recursion_exact_constant_factor
#print axioms ArkLib.ProximityGap.StructureLoop36.affine_recursion_constant_factor_absorbed
