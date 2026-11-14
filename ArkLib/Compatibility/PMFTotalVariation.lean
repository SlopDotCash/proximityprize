/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ToMathlib.MeasureTheory.Measure.TotalVariation.Variation

/-!
# Discrete PMF total variation through the canonical measure API

These compatibility functions evaluate PMFs on the discrete sigma algebra and delegate to
VCVio's native measure total variation. The half-L1 formula is a proved bridge for retained
point-mass arguments. The metric instance is scoped to this compatibility surface.
-/

open MeasureTheory ENNReal

namespace ProximityPrize.Compatibility.PMFTotalVariation

noncomputable section

variable {α : Type*}

/-- A PMF viewed as its canonical measure on the discrete sigma algebra. -/
abbrev toDiscreteMeasure (p : PMF α) : @Measure α ⊤ := @PMF.toMeasure α ⊤ p

/-- Extended total variation supplied by the canonical measure implementation. -/
def etvDist (p q : PMF α) : ENNReal :=
  @Measure.etvDist α ⊤ (toDiscreteMeasure p) (toDiscreteMeasure q)

/-- Real total variation supplied by the canonical measure implementation. -/
def tvDist (p q : PMF α) : ℝ := (etvDist p q).toReal

@[simp] theorem etvDist_self (p : PMF α) : etvDist p p = 0 := by
  let : MeasurableSpace α := ⊤
  exact Measure.etvDist_self p.toMeasure

theorem etvDist_comm (p q : PMF α) : etvDist p q = etvDist q p := by
  let : MeasurableSpace α := ⊤
  exact Measure.etvDist_comm p.toMeasure q.toMeasure

theorem etvDist_ne_top (p q : PMF α) : etvDist p q ≠ ⊤ := by
  let : MeasurableSpace α := ⊤
  exact Measure.etvDist_ne_top p.toMeasure q.toMeasure (by simp) (by simp)

@[simp] theorem tvDist_self (p : PMF α) : tvDist p p = 0 := by simp [tvDist]

theorem tvDist_nonneg (p q : PMF α) : 0 ≤ tvDist p q := ENNReal.toReal_nonneg

theorem tvDist_comm (p q : PMF α) : tvDist p q = tvDist q p := by
  simp only [tvDist, etvDist_comm]

theorem tvDist_triangle (p q r : PMF α) : tvDist p r ≤ tvDist p q + tvDist q r := by
  let : MeasurableSpace α := ⊤
  exact Measure.tvDist_triangle p.toMeasure q.toMeasure r.toMeasure (by simp) (by simp) (by simp)

theorem tvDist_eq_zero_iff (p q : PMF α) : tvDist p q = 0 ↔ p = q := by
  let : MeasurableSpace α := ⊤
  change p.toMeasure.tvDist q.toMeasure = 0 ↔ p = q
  rw [Measure.tvDist_eq_zero_iff _ _ (by simp) (by simp), PMF.toMeasure_inj]

scoped instance : MetricSpace (PMF α) where
  dist := tvDist
  edist := etvDist
  dist_self := tvDist_self
  dist_comm := tvDist_comm
  dist_triangle := tvDist_triangle
  eq_of_dist_eq_zero h := (tvDist_eq_zero_iff _ _).mp h
  edist_dist p q := (ENNReal.ofReal_toReal (etvDist_ne_top p q)).symm

private theorem tsum_tsub_of_le {f g : α → ENNReal} (hg : (∑' x, g x) ≠ ⊤)
    (h : ∀ x, g x ≤ f x) :
    (∑' x, (f x - g x)) = (∑' x, f x) - (∑' x, g x) := by
  apply ENNReal.eq_sub_of_add_eq hg
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun x => tsub_add_cancel_of_le (h x)

/-- The half-L1 point-mass formula agrees with canonical native total variation. -/
theorem etvDist_eq_half_tsum (p q : PMF α) :
    etvDist p q = (∑' x, ENNReal.absDiff (p x) (q x)) / 2 := by
  classical
  let : MeasurableSpace α := ⊤
  let s : Set α := {x | p x ≤ q x}
  have hH : IsHahnDecomposition p.toMeasure q.toMeasure s := by
    refine ⟨MeasurableSet.of_discrete, ?_, ?_⟩
    · rw [Measure.le_iff]
      intro t ht
      rw [Measure.restrict_apply ht, Measure.restrict_apply ht,
        PMF.toMeasure_apply_eq_tsum, PMF.toMeasure_apply_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hx : x ∈ t ∩ s
      · simp only [Set.indicator_of_mem hx]
        exact hx.2
      · simp only [Set.indicator_of_notMem hx, le_refl]
    · rw [Measure.le_iff]
      intro t ht
      rw [Measure.restrict_apply ht, Measure.restrict_apply ht,
        PMF.toMeasure_apply_eq_tsum, PMF.toMeasure_apply_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hx : x ∈ t ∩ sᶜ
      · simp only [Set.indicator_of_mem hx]
        exact le_of_not_ge hx.2
      · simp only [Set.indicator_of_notMem hx, le_refl]
  have hpfinite (t : Set α) : (∑' x, t.indicator p x) ≠ ⊤ := by
    rw [← PMF.toMeasure_apply_eq_tsum]
    exact measure_ne_top _ _
  have hqfinite (t : Set α) : (∑' x, t.indicator q x) ≠ ⊤ := by
    rw [← PMF.toMeasure_apply_eq_tsum]
    exact measure_ne_top _ _
  have hle : ∀ x, s.indicator p x ≤ s.indicator q x := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact hx
    · simp only [Set.indicator_of_notMem hx, le_refl]
  have hge : ∀ x, sᶜ.indicator q x ≤ sᶜ.indicator p x := by
    intro x
    by_cases hx : p x ≤ q x
    · simp [s, hx]
    · have hxc : x ∈ sᶜ := hx
      rw [Set.indicator_of_mem hxc, Set.indicator_of_mem hxc]
      exact le_of_not_ge hx
  have hpoint (x : α) : ENNReal.absDiff (p x) (q x) =
      (s.indicator q x - s.indicator p x) +
        (sᶜ.indicator p x - sᶜ.indicator q x) := by
    by_cases hx : p x ≤ q x
    · simp [s, hx, ENNReal.absDiff, tsub_eq_zero_of_le hx]
    · simp [s, hx, ENNReal.absDiff, tsub_eq_zero_of_le (le_of_not_ge hx)]
  have hsum : (∑' x, ENNReal.absDiff (p x) (q x)) =
      MeasureTheory.etvDist p.toMeasure q.toMeasure := by
    simp_rw [hpoint]
    rw [ENNReal.tsum_add, tsum_tsub_of_le (hpfinite s) hle,
      tsum_tsub_of_le (hqfinite sᶜ) hge, hH.etvDist_eq,
      PMF.toMeasure_apply_eq_tsum, PMF.toMeasure_apply_eq_tsum,
      PMF.toMeasure_apply_eq_tsum, PMF.toMeasure_apply_eq_tsum]
  rw [hsum, MeasureTheory.etvDist_eq_two_mul_etvDist]
  change _ = 2 * etvDist p q / 2
  rw [mul_comm (2 : ENNReal), ENNReal.mul_div_cancel_right two_ne_zero ofNat_ne_top]

end

end ProximityPrize.Compatibility.PMFTotalVariation
