/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiFinitePrefixTurnoverGate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Local slope bounds do not prove Jacobi turnover

The Form-D/Jacobi route to issue #464 asks for a global recurrence-coefficient ceiling after the
Hermite-like prefix.  `_JacobiFinitePrefixTurnoverGate` records that a finite checked prefix is not
enough.  This file records the adjacent guardrail: adding a local one-step rise bound is still not
enough unless the allowed slope is zero, the horizon is bounded, or one proves an independent tail
turnover theorem.

The exact consumer is the linear envelope:

`b (K+t) <= B + t*s`

from a prefix bound `b K <= B` and one-step rise bound `b (k+1) <= b k + s`.  This is sharp: the
delayed ramp `b k = B + s * (k-K)` after the prefix satisfies the local rule and exceeds the global
ceiling as soon as `s > 0`.
-/

namespace ArkLib.ProximityGap.Frontier.JacobiLocalSlopeTurnoverGate

open ArkLib.ProximityGap.Frontier.JacobiFinitePrefixTurnoverGate

/-- One-step local rise bound.  This abstracts local smoothness/Toda-step information. -/
def OneStepRiseBound (b : Nat -> ℝ) (s : ℝ) : Prop :=
  forall k : Nat, b (k + 1) <= b k + s

/-- A prefix bound and a one-step rise bound give only a linear envelope after the prefix. -/
theorem bound_after_prefix_by_step
    {b : Nat -> ℝ} {K : Nat} {B s : ℝ}
    (hPrefix : PrefixBound b K B)
    (hStep : OneStepRiseBound b s) :
    forall t : Nat, b (K + t) <= B + (t : ℝ) * s := by
  intro t
  induction t with
  | zero =>
      simpa using hPrefix K le_rfl
  | succ t ih =>
      have hnext : b (K + (t + 1)) <= b (K + t) + s := by
        simpa [Nat.add_assoc, Nat.succ_eq_add_one] using hStep (K + t)
      calc
        b (K + (t + 1)) <= b (K + t) + s := hnext
        _ <= B + (t : ℝ) * s + s := by linarith
        _ = B + ((t + 1 : Nat) : ℝ) * s := by
          norm_num [Nat.cast_add, Nat.cast_one]
          ring

/-- The delayed ramp beginning at prefix value `B`: after `K`, it rises with slope `s`. -/
def delayedRamp (K : Nat) (B s : ℝ) : Nat -> ℝ :=
  fun k : Nat => B + s * ((k - K : Nat) : ℝ)

/-- On the checked prefix, the delayed ramp is exactly `B`. -/
theorem delayedRamp_eq_prefix_value_of_le {K k : Nat} {B s : ℝ} (hk : k <= K) :
    delayedRamp K B s k = B := by
  have hsub : k - K = 0 := Nat.sub_eq_zero_of_le hk
  simp [delayedRamp, hsub]

/-- Hence the delayed ramp obeys the prefix ceiling. -/
theorem delayedRamp_prefixBound (K : Nat) (B s : ℝ) :
    PrefixBound (delayedRamp K B s) K B := by
  intro k hk
  rw [delayedRamp_eq_prefix_value_of_le hk]

/-- The delayed ramp obeys the one-step rise bound with slope `s`. -/
theorem delayedRamp_oneStepRiseBound {K : Nat} {B s : ℝ} (hs : 0 <= s) :
    OneStepRiseBound (delayedRamp K B s) s := by
  intro k
  have hnat : (k + 1) - K <= (k - K) + 1 := by omega
  have hcast : (((k + 1) - K : Nat) : ℝ) <= ((k - K : Nat) : ℝ) + 1 := by
    exact_mod_cast hnat
  have hmul : s * (((k + 1) - K : Nat) : ℝ) <= s * (((k - K : Nat) : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hcast hs
  unfold delayedRamp
  nlinarith

/-- The delayed ramp is sharp for the linear envelope. -/
theorem delayedRamp_prefix_plus (K t : Nat) (B s : ℝ) :
    delayedRamp K B s (K + t) = B + (t : ℝ) * s := by
  have hsub : K + t - K = t := by omega
  simp [delayedRamp, hsub, mul_comm]

/-- With any positive allowed slope, the delayed ramp violates the global ceiling immediately after
the checked prefix. -/
theorem not_globalBound_delayedRamp {K : Nat} {B s : ℝ} (hs : 0 < s) :
    ¬ GlobalBound (delayedRamp K B s) B := by
  intro hGlobal
  have h := hGlobal (K + 1)
  rw [delayedRamp_prefix_plus K 1 B s] at h
  norm_num at h
  linarith

/-- Local one-step regularity plus finite-prefix verification cannot force a global turnover
ceiling.  The counterexample is the delayed ramp. -/
theorem localSlope_not_force_global {K : Nat} {B s : ℝ} (hs : 0 < s) :
    exists b : Nat -> ℝ,
      PrefixBound b K B ∧ OneStepRiseBound b s ∧ ¬ GlobalBound b B := by
  refine ⟨delayedRamp K B s, delayedRamp_prefixBound K B s,
    delayedRamp_oneStepRiseBound (le_of_lt hs), not_globalBound_delayedRamp hs⟩

/-- Bundled gate: the linear envelope is the real output of prefix plus local slope, and the
delayed-ramp model shows that this output is sharp and does not imply the global ceiling. -/
theorem localSlopeTurnoverGate {K : Nat} {B s : ℝ} (hs : 0 < s) :
    (forall b : Nat -> ℝ,
        PrefixBound b K B -> OneStepRiseBound b s ->
          forall t : Nat, b (K + t) <= B + (t : ℝ) * s)
      ∧ exists b : Nat -> ℝ,
          PrefixBound b K B ∧ OneStepRiseBound b s ∧ ¬ GlobalBound b B := by
  exact ⟨fun b hPrefix hStep => bound_after_prefix_by_step hPrefix hStep,
    localSlope_not_force_global hs⟩

end ArkLib.ProximityGap.Frontier.JacobiLocalSlopeTurnoverGate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiLocalSlopeTurnoverGate.bound_after_prefix_by_step
#print axioms ArkLib.ProximityGap.Frontier.JacobiLocalSlopeTurnoverGate.delayedRamp_prefixBound
#print axioms ArkLib.ProximityGap.Frontier.JacobiLocalSlopeTurnoverGate.delayedRamp_oneStepRiseBound
#print axioms ArkLib.ProximityGap.Frontier.JacobiLocalSlopeTurnoverGate.delayedRamp_prefix_plus
#print axioms ArkLib.ProximityGap.Frontier.JacobiLocalSlopeTurnoverGate.not_globalBound_delayedRamp
#print axioms ArkLib.ProximityGap.Frontier.JacobiLocalSlopeTurnoverGate.localSlope_not_force_global
#print axioms ArkLib.ProximityGap.Frontier.JacobiLocalSlopeTurnoverGate.localSlopeTurnoverGate
