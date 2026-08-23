/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.LogRatioTowerBoundedIncrement

/-!
# The un-logged exponential form of the bounded-increment tower bound (#444)

`LogRatioTowerBoundedIncrement.logTower_le_card_mul_log2` proved the LOG-side bounded-increment sum
`log(Mtow a) − log(Mtow 0) ≤ a·log 2`. This file exponentiates it to the directly-usable
multiplicative form `Mtow a ≤ 2^a · Mtow 0` (the trivial `M(μ_{2^a}) ≤ 2^a = n` bound the Liu–Zhou
recursion gives when iterated), without going through logs at the point of use. This is the honest
"iterating the recursion gives only the trivial bound, `√n` short of the prize" statement, in the
form a downstream argument actually consumes.

## What is landed (axiom-clean: `propext`, `Classical.choice`, `Quot.sound`)
* `tower_le_two_pow_mul` : from the per-step doubling `Mtow (i+1) ≤ 2·Mtow i` alone (no logs, no
  positivity), `Mtow a ≤ 2^a · Mtow 0`. Direct induction on `a` (cleaner than exponentiating).
* `tower_le_two_pow_mul_of_log` : the same conclusion DERIVED from the landed log-side lemma
  `logTower_le_card_mul_log2` by exponentiating, exhibiting the equivalence of the two routes
  (requires positivity to invert the log).

## HONEST SCOPE (rules 1, 3, 4, 6 + the asymptotic guard). Same wall as
`LogRatioTowerBoundedIncrement`: this is the THICKNESS-BLIND trivial bound (the Liu–Zhou doubling
holds in the thick `β≈2.3` window where the prize is FALSE), so by rule 3 it cannot prove the prize.
`2^a = n` is `√n` above the prize `C√(n·log(p/n))`. NON-MOMENT, EXTEND-proven on the landed
bounded-increment tower. No capacity/beyond-Johnson claim; cliff-at-n/2 untouched. CORE
`M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

namespace ProximityGap.Frontier.LogRatioTowerExpForm

open ProximityGap.Frontier.LogRatioTowerBoundedIncrement

variable {Mtow : ℕ → ℝ}

/-- **The un-logged trivial bound (direct).** If the tower at most doubles each step
(`Mtow (i+1) ≤ 2·Mtow i`, the Liu–Zhou recursion), then `Mtow a ≤ 2^a · Mtow 0`. This is the trivial
`M(μ_{2^a}) ≤ 2^a = n` bound, `√n` short of the prize. Direct induction, no logs needed. -/
theorem tower_le_two_pow_mul (a : ℕ)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i) :
    Mtow a ≤ 2 ^ a * Mtow 0 := by
  induction a with
  | zero => simp
  | succ n ih =>
    calc Mtow (n + 1)
        ≤ 2 * Mtow n := hdouble n
      _ ≤ 2 * (2 ^ n * Mtow 0) := by
          have : (0 : ℝ) ≤ 2 := by norm_num
          exact mul_le_mul_of_nonneg_left ih this
      _ = 2 ^ (n + 1) * Mtow 0 := by ring

/-- **Exponentiated excess form.** If the log-tower has only `R` excess above the square-root
baseline, `log(Mtow a) − log(Mtow 0) ≤ (a log 2)/2 + R`, then the tower itself satisfies
`Mtow a ≤ exp((a log 2)/2 + R) · Mtow 0`. This is the multiplicative form of the exact wall mapped
by `logTower_excess_eq`: the prize would require `R = O(log log(p/2^a))`, not just bounded
increments. -/
theorem tower_le_exp_sqrtBaseline_mul (a : ℕ) (R : ℝ)
    (hpos : ∀ i, 0 < Mtow i)
    (hlog : Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * (Real.log 2 / 2) + R) :
    Mtow a ≤ Real.exp ((a : ℝ) * (Real.log 2 / 2) + R) * Mtow 0 := by
  have hRHSpos : 0 < Real.exp ((a : ℝ) * (Real.log 2 / 2) + R) * Mtow 0 := by
    exact mul_pos (Real.exp_pos _) (hpos 0)
  have hlog2 : Real.log (Mtow a) ≤
      Real.log (Real.exp ((a : ℝ) * (Real.log 2 / 2) + R) * Mtow 0) := by
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (hpos 0)), Real.log_exp]
    linarith
  exact (Real.log_le_log_iff (hpos a) hRHSpos).mp hlog2

/-- **Exponentiated excess-sum form.** Combining `logTower_excess_eq` with
`tower_le_exp_sqrtBaseline_mul`: a direct bound on the centered increment sum gives the
multiplicative square-root-baseline tower bound. This is a packaging lemma only; bounding this sum
sublinearly is exactly the open mean-drift / char-p transfer wall. -/
theorem tower_le_exp_sqrtBaseline_mul_of_excess_sum (a : ℕ) (R : ℝ)
    (hpos : ∀ i, 0 < Mtow i)
    (hexcess : (∑ i ∈ Finset.range a,
        ((Real.log (Mtow (i + 1)) - Real.log (Mtow i)) - Real.log 2 / 2)) ≤ R) :
    Mtow a ≤ Real.exp ((a : ℝ) * (Real.log 2 / 2) + R) * Mtow 0 := by
  exact tower_le_exp_sqrtBaseline_mul a R hpos ((logTower_excess_eq (Mtow := Mtow) a R).mpr hexcess)

/-- **Linear-excess exponentiation recovers the trivial exponential bound.** Combining the
centered-excess wall `Σ(Δ_i - ½log2) ≤ (a/2)log2` with the square-root-baseline exponential form
collapses to `Mtow a ≤ exp(a log2) · Mtow 0`. This is the square-root-baseline bookkeeping version
of the same wall: bounded increments leave LINEAR excess, hence recover only the trivial `2^a`
scale rather than the prize-scale `2^(a/2)·polylog`. -/
theorem tower_le_exp_linearExcess_mul (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i) :
    Mtow a ≤ Real.exp ((a : ℝ) * Real.log 2) * Mtow 0 := by
  have hexcess := logTower_excess_le_half_card_mul_log2 (Mtow := Mtow) a hpos hdouble
  have h := tower_le_exp_sqrtBaseline_mul_of_excess_sum (Mtow := Mtow) a
    ((a : ℝ) * (Real.log 2 / 2)) hpos hexcess
  have harg : (a : ℝ) * (Real.log 2 / 2) + (a : ℝ) * (Real.log 2 / 2)
      = (a : ℝ) * Real.log 2 := by ring
  simpa [harg] using h

/-- **The un-logged trivial bound, DERIVED from the log-side lemma.** Exponentiating
`LogRatioTowerBoundedIncrement.logTower_le_card_mul_log2` (which gives
`log(Mtow a) − log(Mtow 0) ≤ a·log 2`) recovers `Mtow a ≤ 2^a · Mtow 0`, given positivity to invert
the log. This exhibits that the direct induction and the log-side bounded-increment route agree. -/
theorem tower_le_two_pow_mul_of_log (a : ℕ)
    (hpos : ∀ i, 0 < Mtow i)
    (hdouble : ∀ i, Mtow (i + 1) ≤ 2 * Mtow i) :
    Mtow a ≤ 2 ^ a * Mtow 0 := by
  have hlog : Real.log (Mtow a) - Real.log (Mtow 0) ≤ (a : ℝ) * Real.log 2 :=
    logTower_le_card_mul_log2 a hpos hdouble
  -- log (Mtow a) ≤ log (Mtow 0) + a log 2 = log (Mtow 0 * 2^a) = log (2^a * Mtow 0)
  have hRHSpos : (0 : ℝ) < 2 ^ a * Mtow 0 := by
    have := hpos 0
    positivity
  have hlog2 : Real.log (Mtow a) ≤ Real.log (2 ^ a * Mtow 0) := by
    rw [Real.log_mul (by positivity) (ne_of_gt (hpos 0)), Real.log_pow]
    linarith
  -- invert log (both sides positive)
  exact (Real.log_le_log_iff (hpos a) hRHSpos).mp hlog2

end ProximityGap.Frontier.LogRatioTowerExpForm

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.LogRatioTowerExpForm.tower_le_exp_sqrtBaseline_mul
#print axioms ProximityGap.Frontier.LogRatioTowerExpForm.tower_le_exp_sqrtBaseline_mul_of_excess_sum
#print axioms ProximityGap.Frontier.LogRatioTowerExpForm.tower_le_exp_linearExcess_mul
