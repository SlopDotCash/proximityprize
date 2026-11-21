/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.RateHalfApolarBudget
import ArkLib.Research.ProximityGap.Frontier._PrizeShapeRateHalfBracket
import ArkLib.Data.CodingTheory.ProximityGap.MCAStepFunction
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-!
# Rate-half threshold from the predecessor count

The geometric input is stated solely in terms of the actual bad scalars of
each received pair. The bisimplex endpoint, the Hamming grid, the field
budget and the real-radius equivalence are discharged here.
-/

set_option autoImplicit false
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.RateHalfApolarThreshold

private abbrev n : ℕ := 1073741824
private abbrev h : ℕ := 268435456
noncomputable abbrev code {p : ℕ} [Fact p.Prime] (g : ZMod p) :=
  evalCode g n 536870911

open Classical in
/-- The finite counting statement proved by the apolar argument on a smooth domain. -/
def PredecessorCap {p : ℕ} [Fact p.Prime] (g : ZMod p) : Prop :=
  ∀ u : Code.WordStack (ZMod p) (Fin 2) (Fin n),
    (Finset.univ.filter (fun γ : ZMod p =>
      mcaEvent (code g) ((268435455:ℝ≥0)/n) (u 0) (u 1) γ)).card ≤ 268435458

private theorem lower_mass {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = n) :
    (536870914:ℝ≥0∞)/(p:ℝ≥0∞) ≤ epsMCA (F := ZMod p) (code g) (1/4) := by
  have h0 := BadFamilyCensus.bisimplex_epsMCA_lower_bound (d := 536870911) (e := h)
    hg (by decide) (by decide) (by decide) (by decide)
  have hr : (1:ℝ≥0) - (805306368:ℝ≥0)/1073741824 = 1/4 := tsub_eq_of_eq_add (by norm_num)
  change (536870914:ℝ≥0∞)/(p:ℝ≥0∞) ≤
    epsMCA (F := ZMod p) (code g) (1-(805306368:ℝ≥0)/1073741824) at h0
  rwa [hr] at h0

/-- The upper endpoint follows for the entire budget interval without using the cap. -/
theorem endpoint_bad {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = n)
    (hb : p / 2^128 ≤ 536870913) :
    (epsStar:ℝ≥0∞) < epsMCA (F := ZMod p) (code g) (1/4) := by
  rw [epsStar_coe_eq_natCast_inv]
  apply lt_of_lt_of_le _ (lower_mass hg)
  have hp : (p:ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fact.out (p := p.Prime)).ne_zero
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp) (Or.inl (ENNReal.natCast_ne_top p)),
    ← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (ENNReal.natCast_ne_top _))]
  have hi := (Nat.lt_mul_div_succ p (by decide : 0<2^128)).trans_le
    (Nat.mul_le_mul_left _ (show p / 2^128 + 1 ≤ 536870914 by omega))
  exact_mod_cast (by simpa only [Nat.mul_comm] using hi)

/-- The first bad Hamming index is exactly h, for every prime in the budget window. -/
theorem threshold {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = n)
    (hb : 268435458 ≤ p / 2^128) (hu : p / 2^128 ≤ 536870913) (cap : PredecessorCap g) :
    mcaDeltaStar (F := ZMod p) (code g) (epsStar:ℝ≥0∞) = 1/4 := by
  apply le_antisymm
  · exact mcaDeltaStar_le_of_bad _ _ (endpoint_bad hg hu)
  · have hf := epsMCA_le_of_badCount_le (code g) ((268435455:ℝ≥0)/n) 268435458 cap
    rw [ZMod.card] at hf
    have good := hf.trans (natCast_div_le_inv_of_mul_le (Q := 2^128) (by decide)
      (Fact.out (p := p.Prime)).pos ((Nat.mul_le_mul_right _ hb).trans (Nat.div_mul_le_self ..)))
    rw [← epsStar_coe_eq_natCast_inv] at good
    have hδ := latticeBoundary_le_mcaDeltaStar_of_predecessor_good (a := h) (by decide)
      (by decide : h≤n) (code g) (epsStar:ℝ≥0∞) good
    rwa [show (h:ℝ≥0)/(n:ℝ≥0) = 1/4 by norm_num [h,n]] at hδ

/-- The full actual good-radius predicate for arbitrary real nonnegative radii. -/
theorem good_iff {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = n)
    (hb : 268435458 ≤ p / 2^128) (hu : p / 2^128 ≤ 536870913) (cap : PredecessorCap g)
    (δ : ℝ≥0) : epsMCA (F := ZMod p) (code g) δ ≤ (epsStar:ℝ≥0∞) ↔ δ < 1/4 := by
  constructor
  · intro good
    by_contra! he
    exact (endpoint_bad hg hu).not_ge ((epsMCA_mono _ he).trans good)
  · intro small
    by_contra! bad
    have bound := mcaDeltaStar_le_of_bad _ _ bad
    rw [threshold hg hb hu cap] at bound
    exact small.not_ge bound

/-- A concrete production field in the admissible budget interval. -/
theorem budget_plus_three (cap : PredecessorCap RateHalfApolarBudget.generator) :
    mcaDeltaStar (F := ZMod RateHalfApolarBudget.P) (code RateHalfApolarBudget.generator)
      (epsStar:ℝ≥0∞) = 1/4 :=
  threshold RateHalfApolarBudget.generator_order (by rw [RateHalfApolarBudget.budget]; decide)
    (by rw [RateHalfApolarBudget.budget]; decide) cap

/-- The lower endpoint of the proven field-budget interval. -/
theorem boundary_prime (cap : PredecessorCap RateHalfApolarBudget.Boundary.generator) :
    mcaDeltaStar (F := ZMod RateHalfApolarBudget.Boundary.P) (code RateHalfApolarBudget.Boundary.generator)
      (epsStar:ℝ≥0∞) = 1/4 :=
  threshold RateHalfApolarBudget.Boundary.generator_order RateHalfApolarBudget.Boundary.budget.ge
    (by rw [RateHalfApolarBudget.Boundary.budget]; decide) cap

/-- Positive interleaving widths preserve the same good-radius interval. -/
theorem interleaved_good_iff {p : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = n)
    (hb : 268435458 ≤ p / 2^128) (hu : p / 2^128 ≤ 536870913) (cap : PredecessorCap g)
    (width : ℕ) [NeZero width] (δ : ℝ≥0) :
    epsMCA (F := ZMod p) (A := Fin width → ZMod p) ((code g) ^⋈ (Fin width)) δ ≤
      (epsStar:ℝ≥0∞) ↔ δ < 1/4 := by
  have hc := Ownership.evalCode_pred_eq_rsCode hg (by decide : 0 < 536870912)
  change evalCode g n 536870911 = _ at hc
  unfold code
  rw [hc, epsMCA_interleaved_eq, ← hc]
  exact good_iff hg hb hu cap δ

#print axioms endpoint_bad
#print axioms threshold
#print axioms boundary_prime
#print axioms budget_plus_three
#print axioms interleaved_good_iff

end ArkLib.ProximityGap.Frontier.RateHalfApolarThreshold
