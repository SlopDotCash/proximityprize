/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MCAAdjacentFloorExactPin
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorCanonicalBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RateQuarterPredecessorFourPencilReduction
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# Conditional exact P1 pin from large-family four-pencil extraction

The common-factor construction makes the literal P1 rate-quarter code bad at

`480946859 / 2^30 = 43/96 + 1/(3 * 2^30)`.

The immediately preceding Hamming-lattice radius is
`480946858 / 2^30`.  At that predecessor,
`_RateQuarterPredecessorFourPencilReduction` proves a per-stack bad-scalar
bound of `N`, conditional on a favorable choice of decoded rich points covered
by four pencils whose source cores leave two fresh coordinates before the
agreement threshold.  No saturated lower bound on those cores is needed.

This module names the guarded geometric certificate: every two-row stack on
`canonicalDomain` whose bad-scalar count exceeds `N` has some favorable
rich-point witness family with such a cover.  Locally this is a strict
relaxation of saturated extraction: the source cores may have any size at most
the two-fresh cutoff.  Globally, because such a cover already forces the count
back below `N`, the guarded statement remains equivalent to the uniform count
target; it records a weaker geometric certificate, not an independently weaker
logical residual.  Under that single explicit hypothesis,
a case split gives the uniform count `<= N`; the field-size budget then gives
`epsMCA <= N/P <= 2^-128`.  The adjacent-floor connector and the unconditional
common-factor upper bound pin `mcaDeltaStar` exactly at the next lattice point.
No four-pencil extraction is asserted here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 800000
set_option maxRecDepth 500000

open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterFourPencilExactPin

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.KKH26
open P1RateQuarterScaleArithmetic
open P1RateQuarterCanonicalCodeBridge
open P1RateQuarterCommonFactorArithmetic
open P1RateQuarterCommonFactorCanonicalBridge
open RateQuarterPredecessorFourPencilReduction
open MCAAdjacentFloorExactPin

local instance localInstance_P1RateQuarterFourPencilExactPin_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterFourPencilExactPin_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

local notation "epsilonP1" =>
  ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞)
local notation "deltaCommon" => P1RateQuarterCommonFactorArithmetic.delta
local notation "deltaPredecessor" =>
  RateQuarterPredecessorFourPencilReduction.P1.predecessorDelta

/-! ## The guarded geometric residual -/

/-- **Named geometric certificate.** Every received two-row stack on the
canonical P1 domain whose predecessor bad-scalar count exceeds `N` admits a
favorable decoded rich-point family covered by four pencils whose source cores
leave at least two coordinates before the agreement threshold.  There is no
saturated lower bound on the four core sizes. -/
def CanonicalLargeBadFourPencilExtraction : Prop :=
  ∀ u : WordStack F (Fin 2) (Fin N),
    N < mcaBadCount (F := F) canonicalCode deltaPredecessor (u 0) (u 1) →
      RateQuarterPredecessorFourPencilReduction.P1.FavorableFourTwoFreshPencilExtraction
        canonicalDomain u

/-- Large-family extraction gives the literal per-stack bad-scalar count
`<= N` on the canonical code.  Stacks already within budget need no cover. -/
theorem canonical_mcaBadCount_le_N_of_largeBad_fourPencil
    (hextract : CanonicalLargeBadFourPencilExtraction)
    (u : WordStack F (Fin 2) (Fin N)) :
    mcaBadCount (F := F) canonicalCode deltaPredecessor
      (u 0) (u 1) ≤ N := by
  by_contra hnot
  have hlarge :
      N < mcaBadCount (F := F) canonicalCode deltaPredecessor
        (u 0) (u 1) := Nat.lt_of_not_ge hnot
  apply hnot
  simpa only [canonicalCode] using
    (RateQuarterPredecessorFourPencilReduction.P1.mcaBadCount_le_N_of_favorableFourTwoFreshPencilExtraction
      canonicalDomain u (by simp only [Fintype.card_fin]) (hextract u hlarge))

/-- The guarded extraction certificate is logically equivalent to the literal
uniform predecessor bad-count target.  The equivalence is a consequence of
the large-family guard; the certificate demanded in its forward direction is
nevertheless strictly weaker than saturated four-pencil extraction. -/
theorem canonicalLargeBadFourPencilExtraction_iff_uniform_badCount :
    CanonicalLargeBadFourPencilExtraction ↔
      ∀ u : WordStack F (Fin 2) (Fin N),
        mcaBadCount (F := F) canonicalCode deltaPredecessor
          (u 0) (u 1) ≤ N := by
  constructor
  · exact canonical_mcaBadCount_le_N_of_largeBad_fourPencil
  · intro hcount u hlarge
    exact (Nat.not_lt_of_ge (hcount u) hlarge).elim

/-! ## Prize-budget handoff -/

private theorem natCast_div_le_inv_of_mul_le {E Q p : ℕ}
    (hQ : 0 < Q) (hp : 0 < p) (hbudget : E * Q ≤ p) :
    (E : ℝ≥0∞) / (p : ℝ≥0∞) ≤ ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hpTop : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  rw [ENNReal.div_le_iff hp0 hpTop]
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hQTop : (Q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top Q
  calc
    (E : ℝ≥0∞) ≤ (E : ℝ≥0∞) * Q * (Q : ℝ≥0∞)⁻¹ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hQ0 hQTop, mul_one]
    _ ≤ (p : ℝ≥0∞) * (Q : ℝ≥0∞)⁻¹ := by
      gcongr
      exact_mod_cast hbudget
    _ = (Q : ℝ≥0∞)⁻¹ * (p : ℝ≥0∞) := mul_comm _ _

theorem N_div_P_le_prizeEpsilon :
    (N : ℝ≥0∞) / (P : ℝ≥0∞) ≤ epsilonP1 := by
  apply natCast_div_le_inv_of_mul_le (by norm_num) prime_P.pos
  norm_num [P1RateQuarterScaleArithmetic.N,
    ArkLib.ProximityGap.PrizeShapePrimeP30.P]

/-- Guarded large-family four-pencil extraction makes the immediate
predecessor good at the literal prize error. -/
theorem canonical_epsMCA_predecessor_le_prizeEpsilon_of_largeBad_fourPencil
    (hextract : CanonicalLargeBadFourPencilExtraction) :
    epsMCA (F := F) (A := F) canonicalCode deltaPredecessor ≤ epsilonP1 := by
  refine (epsMCA_le_of_badCount_le canonicalCode deltaPredecessor N
    (fun u ↦ ?_)).trans ?_
  · simpa only [mcaBadCount] using
      canonical_mcaBadCount_le_N_of_largeBad_fourPencil hextract u
  · simpa only [F, ZMod.card] using N_div_P_le_prizeEpsilon

/-! ## Adjacent-floor exact pin -/

/-- The common-factor endpoint is the Hamming-lattice point with numerator
`480946859`. -/
theorem common_delta_eq_latticeRadius :
    deltaCommon = latticeRadius N radiusNumerator := by
  rfl

/-- The four-pencil predecessor is exactly the Hamming-lattice point
immediately before the common-factor endpoint. -/
theorem fourPencil_predecessor_delta_eq_predecessorRadius :
    deltaPredecessor = predecessorRadius N radiusNumerator := by
  apply NNReal.coe_injective
  push_cast
  norm_num [RateQuarterPredecessorFourPencilReduction.P1.predecessorDelta,
    RateQuarterPredecessorFourPencilReduction.P1.predecessorRadiusNumerator,
    RateQuarterPredecessorFourPencilReduction.P1.predecessorThreshold,
    predecessorRadius, radiusNumerator, amplifiedThreshold, amplifiedCore,
    N, m, r, d]

/-- Guarded large-family extraction supplies goodness in the exact radius
form consumed by the adjacent-floor theorem. -/
theorem canonical_predecessor_good_of_largeBad_fourPencil
    (hextract : CanonicalLargeBadFourPencilExtraction) :
    epsMCA (F := F) (A := F) canonicalCode
        (predecessorRadius N radiusNumerator) ≤ epsilonP1 := by
  rw [← fourPencil_predecessor_delta_eq_predecessorRadius]
  exact canonical_epsMCA_predecessor_le_prizeEpsilon_of_largeBad_fourPencil
    hextract

/-- The unconditional common-factor construction gives the matching upper
ledger on the canonical code. -/
theorem canonical_mcaDeltaStar_le_common_delta :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) canonicalCode epsilonP1 ≤ deltaCommon := by
  rw [← evalCode_eq_canonicalCode]
  exact evalCode_commonFactor_mcaDeltaStar_le

/-- **Conditional exact P1 pin on the canonical Reed--Solomon code.** The only
hypothesis is guarded large-family extraction at the immediate predecessor. -/
theorem canonical_mcaDeltaStar_eq_common_delta_of_largeBad_fourPencil
    (hextract : CanonicalLargeBadFourPencilExtraction) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) canonicalCode epsilonP1 = deltaCommon := by
  rw [common_delta_eq_latticeRadius]
  apply mcaDeltaStar_eq_latticeRadius_of_predecessor_good_of_upper
      (F := F) (A := F) (a := radiusNumerator)
  · norm_num [radiusNumerator, amplifiedThreshold, amplifiedCore, m, r, d]
  · norm_num [radiusNumerator, amplifiedThreshold, amplifiedCore, N, m, r, d]
  · exact canonical_predecessor_good_of_largeBad_fourPencil hextract
  · rw [← common_delta_eq_latticeRadius]
    exact canonical_mcaDeltaStar_le_common_delta

/-- Literal `evalCode` form of the conditional exact pin. -/
theorem evalCode_rateQuarter_mcaDeltaStar_eq_common_delta_of_largeBad_fourPencil
    (hextract : CanonicalLargeBadFourPencilExtraction) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) (evalCode g N (k - 1)) epsilonP1 = deltaCommon := by
  rw [evalCode_eq_canonicalCode]
  exact canonical_mcaDeltaStar_eq_common_delta_of_largeBad_fourPencil hextract

/-- Closed-form literal-code statement of the conditional exact pin. -/
theorem evalCode_rateQuarter_mcaDeltaStar_eq_advertised_of_largeBad_fourPencil
    (hextract : CanonicalLargeBadFourPencilExtraction) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) (evalCode g N (k - 1)) epsilonP1 =
      (43 / 96 : ℝ≥0) + 1 / (3 * N : ℕ) := by
  rw [← delta_eq_fortyThree_over_ninetySix_correction]
  exact evalCode_rateQuarter_mcaDeltaStar_eq_common_delta_of_largeBad_fourPencil
    hextract

end ArkLib.ProximityGap.Frontier.P1RateQuarterFourPencilExactPin

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterFourPencilExactPin
#print axioms canonical_mcaBadCount_le_N_of_largeBad_fourPencil
#print axioms canonicalLargeBadFourPencilExtraction_iff_uniform_badCount
#print axioms canonical_epsMCA_predecessor_le_prizeEpsilon_of_largeBad_fourPencil
#print axioms fourPencil_predecessor_delta_eq_predecessorRadius
#print axioms canonical_mcaDeltaStar_eq_common_delta_of_largeBad_fourPencil
#print axioms evalCode_rateQuarter_mcaDeltaStar_eq_advertised_of_largeBad_fourPencil
