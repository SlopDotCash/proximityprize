/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/

import ProximityPrize.Compatibility.PMFTotalVariation
import ToMathlib.Topology.Algebra.InfiniteSum.Option

/-!
# Coupling completed discrete distributions with explicit failure mass

A distribution on `Option α` records failure at `none`. These pure PMF facts preserve the
former SPMF coupling statements, including countably infinite supports. Total variation comes
from the canonical measure API through `PMFTotalVariation`; no computation interpreter or
probability-semantics instance is installed.
-/

open MeasureTheory
open scoped ENNReal

namespace ProximityPrize.Compatibility.CompletedPMFCoupling

noncomputable section

variable {α : Type*}

/-- The canonical measure of successful outcomes satisfying the event. -/
def successfulEventMass (p : PMF (Option α)) (b : α → Prop) : ENNReal :=
  @PMF.toMeasure (Option α) ⊤ p {o | o.elim False b}

open Classical in
/-- Successful event mass is the sum of its successful point masses. -/
theorem successfulEventMass_eq_tsum (p : PMF (Option α)) (b : α → Prop) :
    successfulEventMass p b = ∑' x, if b x then p (some x) else 0 := by
  classical
  let : MeasurableSpace (Option α) := ⊤
  rw [successfulEventMass, PMF.toMeasure_apply_eq_tsum, tsum_option _ ENNReal.summable]
  have hnone : ({o : Option α | o.elim False b}.indicator p) none = 0 :=
    Set.indicator_of_notMem (by simp) _
  rw [hnone, zero_add]
  apply tsum_congr
  intro x
  by_cases hx : b x
  · rw [Set.indicator_of_mem (show some x ∈ {o : Option α | o.elim False b} from hx),
      ite_eq_left hx]
  · rw [Set.indicator_of_notMem
      (show some x ∉ {o : Option α | o.elim False b} from hx), ite_eq_right hx]

/-- A successful event has finite mass because the completed distribution is a probability. -/
theorem successfulEventMass_ne_top (p : PMF (Option α)) (b : α → Prop) :
    successfulEventMass p b ≠ ⊤ := by
  let : MeasurableSpace (Option α) := ⊤
  exact measure_ne_top p.toMeasure _

/-- Equal failure mass and agreement off a bad event bound completed-distribution TV. -/
theorem tvDist_le_eventMass_of_identicalOffBad
    (p q : PMF (Option α)) (b : α → Prop)
    (h_eq : ∀ x, ¬ b x → p (some x) = q (some x))
    (h_bad : successfulEventMass p b = successfulEventMass q b)
    (h_fail : p none = q none) :
    PMFTotalVariation.tvDist p q ≤ (successfulEventMass p b).toReal := by
  classical
  rw [PMFTotalVariation.tvDist]
  refine ENNReal.toReal_mono (successfulEventMass_ne_top p b) ?_
  rw [PMFTotalVariation.etvDist_eq_half_tsum, tsum_option _ ENNReal.summable,
    h_fail, ENNReal.absDiff_self, zero_add]
  calc
    (∑' x, ENNReal.absDiff (p (some x)) (q (some x))) / 2
        ≤ (∑' x, if b x then p (some x) + q (some x) else 0) / 2 :=
      ENNReal.div_le_div_right (ENNReal.tsum_le_tsum fun x => by
        by_cases hx : b x
        · simpa only [hx, ite_true] using
            ENNReal.absDiff_le_add (p (some x)) (q (some x))
        · simp only [hx, ite_false, h_eq x hx, ENNReal.absDiff_self, le_refl]) _
    _ = (successfulEventMass p b + successfulEventMass q b) / 2 := by
      rw [successfulEventMass_eq_tsum, successfulEventMass_eq_tsum]
      congr 1
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro x
      by_cases hx : b x <;> simp [hx]
    _ = (successfulEventMass p b + successfulEventMass p b) / 2 := by rw [← h_bad]
    _ = successfulEventMass p b := by
      rw [← two_mul, mul_div_assoc]
      simp [ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- Mapping a successful Boolean flag identifies its true point mass with the flag event. -/
theorem map_some_true_eq_eventMass (p : PMF (Option α)) (f : α → Bool) :
    p.map (Option.map f) (some true) = successfulEventMass p (fun x => f x = true) := by
  classical
  rw [PMF.map_apply, successfulEventMass_eq_tsum, tsum_option _ ENNReal.summable]
  simp only [Option.map_none, reduceCtorEq, ite_false, zero_add, Option.map_some,
    Option.some.injEq]
  exact tsum_congr fun x => by simp only [eq_comm]

/-- Boolean-flag form, still observing failure as the `none` point of the completed PMF. -/
theorem tvDist_le_trueMass_of_identicalOffFlag
    (p q : PMF (Option α)) (f : α → Bool)
    (h_eq : ∀ x, f x = false → p (some x) = q (some x))
    (h_flag : p.map (Option.map f) (some true) = q.map (Option.map f) (some true))
    (h_fail : p none = q none) :
    PMFTotalVariation.tvDist p q ≤ (p.map (Option.map f) (some true)).toReal := by
  rw [map_some_true_eq_eventMass]
  refine tvDist_le_eventMass_of_identicalOffBad p q (fun x => f x = true) ?_ ?_ h_fail
  · intro x hx
    exact h_eq x (by simpa using hx)
  · simpa only [map_some_true_eq_eventMass] using h_flag

#print axioms tvDist_le_eventMass_of_identicalOffBad
#print axioms tvDist_le_trueMass_of_identicalOffFlag

end

end ProximityPrize.Compatibility.CompletedPMFCoupling
