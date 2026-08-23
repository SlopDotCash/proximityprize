/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G129FullDescentBudget

/-!
# G130 (= G129 part 2b core): uniform per-rung budget lemmas

The tower induction needs the G128/G129 budget analysis at EVERY rung `t ≤ 110`, not just
`110`.  Kernel-checking one hundred gates is infeasible; this file replaces them with four
uniform lemmas whose proofs are clean inductions with enormous slack:

1. `factorial_sq_le` — `2^163 · (t!)² ≤ 2^(30t)` for `7 ≤ t ≤ 110` (induction; step factor
   `(t+1)² ≤ 2^30`): the depth-`0` term fits an eighth of the rung-`t` DC mass at every rung.
2. `shallow_head_gate` — `16 · 2^160 · (110)_9² ≤ 2^300`: ONE kernel gate covering the
   geometric shallow tail at every rung, by `(t)_9 ≤ (110)_9`.
3. `deep_dc_gate` — `64 · (110)_k² ≤ 2^(30k)` for `1 ≤ k ≤ 8`: the deep terms' pure-DC parts,
   monotone in `t`.
4. `deep_wick_le` — `2^166 · (110)_8² · (2t−1)!! ≤ 2^(30t)` for `11 ≤ t ≤ 110` (induction;
   step factor `2t+1 ≤ 2^8`): the deep terms' Wick parts.

Together these make the per-rung descent budget provable uniformly for `11 ≤ t ≤ 110` — the
assembly into per-rung tower steps and the strong induction is the sequel.  The rungs
`t ≤ 10` are outside this machinery (crossover regime; the in-tree rung-2 anchor and small-rung
analysis live elsewhere).

**Honest scope.**  Arithmetic infrastructure only.  CORE remains OPEN.  Issue #466 (G129/G130).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G130UniformRungBudgets

/-- **Uniform depth-0 budget.**  `2^163 · (t!)² ≤ 2^(30t)` for all `7 ≤ t` (stated without an
upper bound on `t`: the induction step `(t+1)² ≤ 2^30` holds whenever `t + 1 ≤ 2^15`, and we
only ever instantiate `t ≤ 110`). -/
theorem factorial_sq_le : ∀ t, 7 ≤ t → t ≤ 110 →
    2 ^ 163 * (Nat.factorial t) ^ 2 ≤ 2 ^ (30 * t) := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ t ih =>
      intro h7 h110
      rcases Nat.lt_or_ge t 7 with hlt | hge
      · -- base case t + 1 = 7
        have : t = 6 := by omega
        subst this
        norm_num [Nat.factorial]
      · have ht110 : t ≤ 110 := by omega
        have hstep : (t + 1) ^ 2 ≤ 2 ^ 30 := by
          have : t + 1 ≤ 111 := by omega
          calc
            (t + 1) ^ 2 ≤ 111 ^ 2 := Nat.pow_le_pow_left this 2
            _ ≤ 2 ^ 30 := by norm_num
        have hprev := ih hge ht110
        calc
          2 ^ 163 * (Nat.factorial (t + 1)) ^ 2
              = (2 ^ 163 * (Nat.factorial t) ^ 2) * (t + 1) ^ 2 := by
            rw [Nat.factorial_succ]
            ring
          _ ≤ 2 ^ (30 * t) * 2 ^ 30 := Nat.mul_le_mul hprev hstep
          _ = 2 ^ (30 * (t + 1)) := by
            rw [← pow_add]
            congr 1

/-- **Uniform shallow-head gate**: one kernel inequality covers the geometric shallow tail at
every rung, via `(t)_9 ≤ (110)_9`. -/
theorem shallow_head_gate :
    16 * (2 ^ 160 * (Nat.descFactorial 110 9) ^ 2) ≤ 2 ^ 300 := by
  norm_num [Nat.descFactorial]
  decide

/-- Descending factorials are monotone in the base. -/
theorem descFactorial_mono_base {a b k : ℕ} (h : a ≤ b) :
    Nat.descFactorial a k ≤ Nat.descFactorial b k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
      exact Nat.mul_le_mul (by omega) ih

/-- **Uniform deep-DC gates**: `64 · (110)_k² ≤ 2^(30k)` for `1 ≤ k ≤ 8`. -/
theorem deep_dc_gate : ∀ k, 1 ≤ k → k ≤ 8 →
    64 * (Nat.descFactorial 110 k) ^ 2 ≤ 2 ^ (30 * k) := by
  intro k h1 h8
  interval_cases k <;> norm_num [Nat.descFactorial]

/-- **Uniform deep-Wick budget.**  `2^166 · (110)_8² · (2t−1)!! ≤ 2^(30t)` for
`11 ≤ t ≤ 110` (induction; step factor `2t + 1 ≤ 2^8`). -/
theorem deep_wick_le : ∀ t, 11 ≤ t → t ≤ 110 →
    2 ^ 166 * (Nat.descFactorial 110 8) ^ 2 * Nat.doubleFactorial (2 * t - 1)
      ≤ 2 ^ (30 * t) := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ t ih =>
      intro h11 h110
      rcases Nat.lt_or_ge t 11 with hlt | hge
      · -- base case t + 1 = 11
        have : t = 10 := by omega
        subst this
        norm_num [Nat.descFactorial, Nat.doubleFactorial]
        decide
      · have ht110 : t ≤ 110 := by omega
        have harg : 2 * (t + 1) - 1 = (2 * t - 1) + 2 := by omega
        have hdf : Nat.doubleFactorial (2 * (t + 1) - 1)
            = (2 * t + 1) * Nat.doubleFactorial (2 * t - 1) := by
          rw [harg, Nat.doubleFactorial_add_two]
          congr 1
          omega
        have hstep : 2 * t + 1 ≤ 2 ^ 30 := by
          have : t ≤ 110 := ht110
          omega
        have hprev := ih hge ht110
        calc
          2 ^ 166 * (Nat.descFactorial 110 8) ^ 2 *
              Nat.doubleFactorial (2 * (t + 1) - 1)
              = (2 ^ 166 * (Nat.descFactorial 110 8) ^ 2 *
                  Nat.doubleFactorial (2 * t - 1)) * (2 * t + 1) := by
            rw [hdf]
            ring
          _ ≤ 2 ^ (30 * t) * 2 ^ 30 := Nat.mul_le_mul hprev hstep
          _ = 2 ^ (30 * (t + 1)) := by
            rw [← pow_add]
            congr 1

end ArkLib.ProximityGap.Frontier.G130UniformRungBudgets

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G130UniformRungBudgets.factorial_sq_le
#print axioms ArkLib.ProximityGap.Frontier.G130UniformRungBudgets.shallow_head_gate
#print axioms
  ArkLib.ProximityGap.Frontier.G130UniformRungBudgets.descFactorial_mono_base
#print axioms ArkLib.ProximityGap.Frontier.G130UniformRungBudgets.deep_dc_gate
#print axioms ArkLib.ProximityGap.Frontier.G130UniformRungBudgets.deep_wick_le
