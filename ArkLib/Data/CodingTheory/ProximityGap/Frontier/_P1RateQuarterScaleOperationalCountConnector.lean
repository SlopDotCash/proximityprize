/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# Operational connector for the prize-scale rate-quarter count

This module isolates the final analytic handoff from the evolving concrete construction.  A
literal `N+2` lower bound on one stack's bad-event filter implies mass strictly above `2^-128`
over the first prize prime, and therefore caps the operational MCA threshold at
`delta = 23/48 - 2/(3N)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterScaleOperationalCountConnector

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
attribute [local instance] Classical.propDecidable

variable {I : Type} [Fintype I] [Nonempty I]

private theorem inv_natCast_lt_natCast_div {Q p W : ℕ}
    (hQ : 0 < Q) (hp : 0 < p) (hsmall : p < Q * W) :
    ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) < (W : ℝ≥0∞) / (p : ℝ≥0∞) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hpTop : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp0) (Or.inl hpTop)]
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hQTop : (Q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top Q
  rw [← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (Or.inl hQ0) (Or.inl hQTop)]
  exact_mod_cast (by simpa [Nat.mul_comm] using hsmall)

/-- The explicit `N+2` mass is strictly larger than the prize error `2^-128`. -/
theorem prizeEpsilon_lt_N_add_two_div_P :
    ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) <
      ((N + 2 : ℕ) : ℝ≥0∞) / (P : ℝ≥0∞) := by
  apply inv_natCast_lt_natCast_div (by norm_num) prime_P.pos
  norm_num [P, N]

/-- A literal `N+2` bad-filter count for one stack supplies the normalized MCA mass. -/
theorem epsMCA_ge_N_add_two_div_P_of_badScalar_filter_card
    (C : Set (I → F)) (v : WordStack F (Fin 2) I)
    (hcount : N + 2 ≤ (Finset.univ.filter fun gamma : F =>
      mcaEvent C delta (v 0) (v 1) gamma).card) :
    ((N + 2 : ℕ) : ℝ≥0∞) / (P : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) C delta := by
  classical
  let bad : Finset F := Finset.univ.filter fun gamma : F =>
    mcaEvent C delta (v 0) (v 1) gamma
  have hbad : ∀ gamma ∈ bad, mcaEvent C delta (v 0) (v 1) gamma := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (F := F) C delta v bad hbad
  rw [ZMod.card] at hengine
  refine le_trans ?_ hengine
  apply ENNReal.div_le_div_right
  exact_mod_cast hcount

/-- The same literal count closes the operational upper ledger at `delta`. -/
theorem mcaDeltaStar_le_rateQuarter_of_badScalar_filter_card
    (C : Set (I → F)) (v : WordStack F (Fin 2) I)
    (hcount : N + 2 ≤ (Finset.univ.filter fun gamma : F =>
      mcaEvent C delta (v 0) (v 1) gamma).card) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F) C
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤
      delta := by
  apply ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_bad
  exact prizeEpsilon_lt_N_add_two_div_P.trans_le
    (epsMCA_ge_N_add_two_div_P_of_badScalar_filter_card C v hcount)

/-- Advertised-radius form of the operational connector. -/
theorem mcaDeltaStar_le_twentyThree_over_fortyEight_correction_of_badScalar_filter_card
    (C : Set (I → F)) (v : WordStack F (Fin 2) I)
    (hcount : N + 2 ≤ (Finset.univ.filter fun gamma : F =>
      mcaEvent C delta (v 0) (v 1) gamma).card) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F) C
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤
      (23 / 48 : ℝ≥0) - 2 / (3 * N : ℕ) := by
  rw [← delta_eq_twentyThree_over_fortyEight_correction]
  exact mcaDeltaStar_le_rateQuarter_of_badScalar_filter_card C v hcount

#print axioms epsMCA_ge_N_add_two_div_P_of_badScalar_filter_card
#print axioms mcaDeltaStar_le_twentyThree_over_fortyEight_correction_of_badScalar_filter_card

end ArkLib.ProximityGap.Frontier.P1RateQuarterScaleOperationalCountConnector
