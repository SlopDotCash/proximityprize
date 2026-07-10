/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAFloorFactorization
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorArithmetic

/-!
# Generic far/structured split at the P1 rate-quarter predecessor

At the lattice predecessor of the common-factor construction, the agreement
floor is `592794966`.  Decoupled Johnson controls every stack whose direction
word agrees with each codeword on at most `327272220` coordinates: its exact
bad-scalar cap is `909522485`, below the required budget `N = 2^30`.

The remaining near-direction case is kept as the explicit named proposition
`PredecessorStructuredFloorResidual`.  Assuming it, the generic factorization
gives the uniform count `#bad <= N`, hence `epsMCA <= N/P <= 2^-128` and the
corresponding conditional lower bound on `mcaDeltaStar`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

open Finset
open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterPredecessorGenericSplit

attribute [local instance] Classical.propDecidable

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic
open P1RateQuarterCommonFactorArithmetic
open ArkLib.ProximityGap.MCAFloorFactorization

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
local instance : NeZero k := ⟨by norm_num [k]⟩

/-- One lattice step below the common-factor bad construction. -/
abbrev predecessorThreshold : ℕ := amplifiedThreshold + 1

abbrev predecessorRadiusNumerator : ℕ := N - predecessorThreshold

noncomputable abbrev predecessorDelta : ℝ≥0 :=
  predecessorRadiusNumerator / N

/-- Largest integral direction-agreement threshold for which the proven far
term is still at most `N`. -/
abbrev A1star : ℕ := 327272220

theorem predecessorThreshold_eq : predecessorThreshold = 592794966 := by
  norm_num [predecessorThreshold, amplifiedThreshold, amplifiedCore, m, r, d]

theorem predecessorRadiusNumerator_eq :
    predecessorRadiusNumerator = 480946858 := by
  norm_num [predecessorRadiusNumerator, predecessorThreshold,
    amplifiedThreshold, amplifiedCore, N, m, r, d]

theorem predecessorDelta_le_one : predecessorDelta ≤ 1 := by
  norm_num [predecessorDelta, predecessorRadiusNumerator,
    predecessorThreshold, amplifiedThreshold, amplifiedCore, N, m, r, d]
  rw [div_le_one] <;> norm_num

theorem agreement_mass_eq_predecessorThreshold :
    (1 - predecessorDelta) * (N : ℝ≥0) = predecessorThreshold := by
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_sub predecessorDelta_le_one]
  push_cast
  norm_num [predecessorDelta, predecessorRadiusNumerator,
    predecessorThreshold, amplifiedThreshold, amplifiedCore, N, m, r, d]

theorem agreement_ceiling_eq_predecessorThreshold :
    ⌈(1 - predecessorDelta) * (N : ℝ≥0)⌉₊ = predecessorThreshold := by
  rw [agreement_mass_eq_predecessorThreshold, Nat.ceil_natCast]

/-! ## Exact decoupled-Johnson arithmetic -/

theorem decoupled_gap : N * A1star < predecessorThreshold ^ 2 := by
  norm_num [A1star, predecessorThreshold, amplifiedThreshold, amplifiedCore, N, m, r, d]

theorem far_denominator_eq :
    predecessorThreshold ^ 2 - N * A1star = 1267611876 := by
  norm_num [A1star, predecessorThreshold, amplifiedThreshold, amplifiedCore, N, m, r, d]

theorem far_term_eq :
    N ^ 2 / (predecessorThreshold ^ 2 - N * A1star) = 909522485 := by
  norm_num [far_denominator_eq, N]

/-- The concrete arithmetic input to
`badScalars_le_of_structuredFloor_dominant` with `B = N`. -/
theorem far_term_dominated_by_N :
    N ^ 2 ≤ N * (predecessorThreshold ^ 2 - N * A1star) := by
  norm_num [far_denominator_eq, N]

/-! ## The explicit remaining structured residual -/

noncomputable abbrev predecessorCode (dom : Fin N ↪ F) : Submodule F (Fin N → F) :=
  ReedSolomon.code dom k

/-- **Named residual.** Near-direction stacks, namely those whose direction
agrees with some codeword on more than `A1star` coordinates, have at most `N`
bad scalars at the predecessor radius.  The far-direction complement is
already discharged by `decoupled_gap` and `far_term_dominated_by_N`. -/
def PredecessorStructuredFloorResidual (dom : Fin N ↪ F) : Prop :=
  StructuredFloorBound (predecessorCode dom) predecessorDelta A1star N

/-- Per-stack count consumer under the single explicit structured residual. -/
theorem badCount_le_N_of_structuredFloor
    (dom : Fin N ↪ F) (u0 u1 : Fin N → F)
    (hstructured : PredecessorStructuredFloorResidual dom) :
    badCount (predecessorCode dom) predecessorDelta u0 u1 ≤ N := by
  apply badScalars_le_of_structuredFloor_dominant
      (predecessorCode dom) predecessorDelta u0 u1
      predecessorThreshold A1star N
  · rw [Fintype.card_fin, agreement_mass_eq_predecessorThreshold]
  · simpa only [Fintype.card_fin] using decoupled_gap
  · simpa only [Fintype.card_fin] using far_term_dominated_by_N
  · exact hstructured

/-- Uniform bad-count form consumed by the `epsMCA` bridge. -/
theorem all_badCount_le_N_of_structuredFloor
    (dom : Fin N ↪ F)
    (hstructured : PredecessorStructuredFloorResidual dom)
    (u : WordStack F (Fin 2) (Fin N)) :
    (Finset.univ.filter fun gamma : F =>
      mcaEvent (predecessorCode dom : Set (Fin N → F)) predecessorDelta
        (u 0) (u 1) gamma).card ≤ N := by
  change badCount (predecessorCode dom) predecessorDelta (u 0) (u 1) ≤ N
  exact badCount_le_N_of_structuredFloor dom (u 0) (u 1) hstructured

/-! ## Prize-budget consumers -/

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
    (N : ℝ≥0∞) / (P : ℝ≥0∞) ≤
      ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  apply natCast_div_le_inv_of_mul_le (by norm_num) prime_P.pos
  norm_num [N, P]

theorem epsMCA_predecessor_le_prizeEpsilon
    (dom : Fin N ↪ F)
    (hstructured : PredecessorStructuredFloorResidual dom) :
    epsMCA (F := F) (A := F) (predecessorCode dom : Set (Fin N → F))
        predecessorDelta ≤
      ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  refine (epsMCA_le_of_badCount_le
    (predecessorCode dom : Set (Fin N → F)) predecessorDelta N
    (all_badCount_le_N_of_structuredFloor dom hstructured)).trans ?_
  simpa only [F, ZMod.card] using N_div_P_le_prizeEpsilon

theorem predecessorDelta_le_mcaDeltaStar
    (dom : Fin N ↪ F)
    (hstructured : PredecessorStructuredFloorResidual dom) :
    predecessorDelta ≤
      ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        (predecessorCode dom : Set (Fin N → F))
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
  exact ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good
    _ _ predecessorDelta_le_one
    (epsMCA_predecessor_le_prizeEpsilon dom hstructured)

end ArkLib.ProximityGap.Frontier.P1RateQuarterPredecessorGenericSplit

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterPredecessorGenericSplit
#print axioms agreement_ceiling_eq_predecessorThreshold
#print axioms far_term_eq
#print axioms badCount_le_N_of_structuredFloor
#print axioms epsMCA_predecessor_le_prizeEpsilon
#print axioms predecessorDelta_le_mcaDeltaStar
