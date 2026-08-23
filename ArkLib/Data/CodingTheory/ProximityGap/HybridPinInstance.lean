/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MonomialDominationKilled
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarExactPoint

/-!
# The v4 hybrid pin is non-vacuous: a fully unconditional instantiation

After three red-team kills the surviving extremality surface is the hybrid two-family
max (`HybridDomination`, `MonomialDominationKilled.lean`). This file closes the loop on
the repair by instantiating the v4 pin **with every hypothesis discharged as a
theorem** at the R1 instance `RS[F₅, μ₄, 2]`, `ε* = 2/5`:

* the hybrid surface holds *unconditionally* here (`hybridDomination_F5`): the only
  grid agreement above the crossing is `a = 4 = n`, where the staircase term
  `(n − a + 1)/|F| = 1/5` alone absorbs the exact sub-granularity value
  `ε_mca(C, 0) = 1/5` — no monomial bound needed;
* the numerics clear `ε*` (`hybridNumerics_F5`), and the crossing is bad by the landed
  R1 fact `ε_mca(C, 1/4) ≥ 4/5 > 2/5`;
* hence `mcaDeltaStar_F5_via_hybrid : mcaDeltaStar(C, 2/5) = 1/4` — the v4 engine
  reproduces the first exact δ\* value **with zero open inputs**, in agreement with the
  direct pin (`mcaDeltaStar_rs_F5_eq_quarter`).

The surface lineage thus ends in a consistent state: the hybrid surface is (i) exactly
what every probe and theorem supports, (ii) falsifier-tested where its predecessors
died, and (iii) non-vacuously pluggable into the δ\*-engine — the gap between the
theorem stack and the conditional production answer is now *only* the three named
analytic cores (window sup-extremality ≡ the CS25 wall, `s ≥ 256` counts, the
beyond-Johnson floor).

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357; `MonomialDominationKilled.lean` (the v4 surface and pin),
  `MCADeltaStarExactPoint.lean` (the R1 facts consumed).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.HybridPinInstance

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAThresholdLedger
open ProximityGap.CensusConditionalPin
open ProximityGap.MonomialDominationPin
open ProximityGap.MonomialDominationKilled
open ProximityGap.MCADeltaStarExactPoint

/-- The single above-crossing grid radius is `a = 4`, i.e. `δ = 0`. -/
theorem grid4_eq_zero : (1 - ((4 : ℕ) : ℝ≥0) / ((4 : ℕ) : ℝ≥0) : ℝ≥0) = 0 := by
  have h4 : ((4 : ℕ) : ℝ≥0) / ((4 : ℕ) : ℝ≥0) = 1 := by
    rw [div_self]
    norm_num
  rw [h4, tsub_self]

/-- **The hybrid surface holds unconditionally at the R1 instance:** at the only
above-crossing agreement (`a = 4`), the staircase term alone absorbs the exact
sub-granularity value. -/
theorem hybridDomination_F5 :
    HybridDomination gdom (rsC : Set (Fin 4 → F5)) 3 := by
  intro a ha3 ha4
  interval_cases a
  -- a = 4: ε_mca(C, 0) = 1/5 ≤ max(monomialEps, (4 − 4 + 1)/5)
  rw [grid4_eq_zero]
  have hexact : epsMCA (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) 0
      = 1 / (Fintype.card F5 : ℝ≥0∞) := by
    refine epsMCA_rs_eq_fifth_of_small ?_
    rw [zero_mul]
    norm_num
  rw [hexact]
  refine le_max_of_le_right ?_
  have hF : (Fintype.card F5 : ℝ≥0∞) = 5 := by rw [ZMod.card]; norm_num
  rw [hF]
  norm_num

/-- The hybrid numerics clear `ε* = 2/5` above the crossing. -/
theorem hybridNumerics_F5 : ∀ a : ℕ, 3 < a → a ≤ 4 →
    max (monomialEps gdom (rsC : Set (Fin 4 → F5))
          (1 - (a : ℝ≥0) / ((4 : ℕ) : ℝ≥0)))
        (((4 - a + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F5 : ℝ≥0∞)) ≤ (2/5 : ℝ≥0∞) := by
  intro a ha3 ha4
  interval_cases a
  refine max_le ?_ ?_
  · -- monomialEps ≤ ε_mca = 1/5 ≤ 2/5
    refine le_trans (monomialEps_le_epsMCA gdom _ _) ?_
    have hg : (1 - ((4 : ℕ) : ℝ≥0) / ((4 : ℕ) : ℝ≥0) : ℝ≥0) = 0 := grid4_eq_zero
    rw [hg]
    have hexact : epsMCA (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) 0
        = 1 / (Fintype.card F5 : ℝ≥0∞) := by
      refine epsMCA_rs_eq_fifth_of_small ?_
      rw [zero_mul]
      norm_num
    rw [hexact, ZMod.card]
    simp only [Nat.cast_ofNat]
    gcongr
    norm_num
  · -- staircase term (4 − 4 + 1)/5 = 1/5 ≤ 2/5
    have hF : (Fintype.card F5 : ℝ≥0∞) = 5 := by rw [ZMod.card]; norm_num
    rw [hF]
    have hone : ((4 - 4 + 1 : ℕ) : ℝ≥0∞) = 1 := by norm_num
    rw [hone]
    gcongr
    norm_num

/-- **The unconditional v4 pin:** `mcaDeltaStar(RS[F₅, μ₄, 2], 2/5) = 1/4` through the
hybrid engine — every hypothesis a theorem, in agreement with the direct R1 pin. -/
theorem mcaDeltaStar_F5_via_hybrid :
    mcaDeltaStar (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) (2/5 : ℝ≥0∞)
      = 1 - ((3 : ℕ) : ℝ≥0) / ((4 : ℕ) : ℝ≥0) := by
  refine mcaDeltaStar_eq_of_hybridCrossing gdom (rsC : Set (Fin 4 → F5))
    (2/5 : ℝ≥0∞) hybridDomination_F5 hybridNumerics_F5 ?_
  -- the crossing is bad: ε_mca(C, 1/4) ≥ 4/5 > 2/5 (the landed R1 fact)
  have hg : (1 - ((3 : ℕ) : ℝ≥0) / ((4 : ℕ) : ℝ≥0) : ℝ≥0) = 1/4 := by
    have h34 : ((3 : ℕ) : ℝ≥0) / ((4 : ℕ) : ℝ≥0) ≤ 1 := by
      rw [div_le_one (by norm_num : (0 : ℝ≥0) < ((4 : ℕ) : ℝ≥0))]
      exact_mod_cast (by norm_num : (3 : ℕ) ≤ 4)
    apply NNReal.coe_injective
    rw [NNReal.coe_sub h34]
    push_cast
    norm_num
  rw [hg]
  refine lt_of_lt_of_le ?_ epsMCA_rs_quarter_ge
  rw [ENNReal.div_lt_iff (by norm_num) (by norm_num),
    ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  norm_num

/-! ## Source audit -/

#print axioms hybridDomination_F5
#print axioms mcaDeltaStar_F5_via_hybrid

end ProximityGap.HybridPinInstance
