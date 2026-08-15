/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MCAReindexEquiv
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleFinalConsumer

/-!
# The P1 rate-quarter certificate on the literal prize code

The fibre-indexed construction has exactly `N` coordinates and enumerates the
same power domain as `Fin N`.  This file upgrades its coordinate embedding to
an equivalence and transports every MCA event to the literal KKH26 code

`evalCode g N (k - 1)`.

Thus the operational upper ledger is a theorem about the prize's stated code,
not merely a Reed--Solomon code on an abstract isomorphic coordinate type.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset
open _root_.ProximityGap Code
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCanonicalCodeBridge

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.KKH26
open P1RateQuarterScaleArithmetic
open P1RateQuarterScaleConstruction
open P1RateQuarterScaleFinalConsumer
open P1RateQuarterScaleOperationalCountConnector
open MCAReindexEquiv

local instance localInstance_P1RateQuarterCanonicalCodeBridge_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterCanonicalCodeBridge_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-- The construction's injective enumeration is bijective because source and
target both have cardinality `N`. -/
noncomputable def coordEquiv : Coord ≃ Fin N :=
  Equiv.ofBijective (fun e : Coord => coordIndex e)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨
      coordIndex.injective,
      by rw [card_coord, Fintype.card_fin]⟩)

@[simp] theorem coordEquiv_apply (e : Coord) :
    coordEquiv e = coordIndex e := rfl

/-- The canonical `Fin N` power-domain embedding used by `evalCode`. -/
def canonicalDomain : Fin N ↪ F :=
  _root_.ProximityGap.KKH26RegimeSplit.powDomain g orderOf_g g_ne_zero

/-- The fibre enumeration and canonical enumeration select the same field
point coordinate by coordinate. -/
theorem domain_eq_canonicalDomain (e : Coord) :
    domain e = canonicalDomain (coordEquiv e) := rfl

/-- The literal prize Reed--Solomon code on `Fin N`. -/
abbrev canonicalCode : Set (Fin N → F) :=
  (ReedSolomon.code canonicalDomain k : Submodule F (Fin N → F))

/-- The KKH degree-`k-1` surface is exactly the canonical degree-`<k`
Reed--Solomon code. -/
theorem evalCode_eq_canonicalCode :
    evalCode g N (k - 1) = canonicalCode := by
  rw [_root_.ProximityGap.KKH26RegimeSplit.evalCode_eq_reedSolomon
    g orderOf_g g_ne_zero (k - 1)]
  norm_num [canonicalCode, canonicalDomain, k]

/-- Reindex the concrete two-row certificate onto `Fin N`. -/
noncomputable def canonicalStack : WordStack F (Fin 2) (Fin N) :=
  fun i => reindexWord coordEquiv (u i)

/-- Every scalar event for the literal prize code is equivalent to the
corresponding event in the fibre-indexed construction. -/
theorem canonical_mcaEvent_iff (gamma : F) :
    mcaEvent canonicalCode delta (canonicalStack 0) (canonicalStack 1) gamma ↔
      mcaEvent P1RateQuarterScaleFinalConsumer.certificateCode delta
        (u 0) (u 1) gamma := by
  simpa [canonicalCode, canonicalStack,
    P1RateQuarterScaleFinalConsumer.certificateCode] using
    (mcaEvent_reindex_reedSolomon_iff coordEquiv domain canonicalDomain
      domain_eq_canonicalDomain k delta (u 0) (u 1) gamma)

/-- The transported stack has the same literal bad-scalar filter, hence at
least `N+2` bad labels. -/
theorem canonical_badScalar_filter_card_ge_N_add_two :
    N + 2 ≤ (Finset.univ.filter fun gamma : F =>
      mcaEvent canonicalCode delta
        (canonicalStack 0) (canonicalStack 1) gamma).card := by
  have hfilter :
      (Finset.univ.filter fun gamma : F =>
        mcaEvent canonicalCode delta
          (canonicalStack 0) (canonicalStack 1) gamma) =
      (Finset.univ.filter fun gamma : F =>
        mcaEvent P1RateQuarterScaleFinalConsumer.certificateCode delta
          (u 0) (u 1) gamma) := by
    ext gamma
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact canonical_mcaEvent_iff gamma
  rw [hfilter]
  exact P1RateQuarterScaleBadCount.badScalar_filter_card_ge_N_add_two

/-- Operational upper bound for the literal prize code. -/
theorem evalCode_rateQuarter_mcaDeltaStar_le :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) (evalCode g N (k - 1))
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤ delta := by
  rw [evalCode_eq_canonicalCode]
  exact mcaDeltaStar_le_rateQuarter_of_badScalar_filter_card
    canonicalCode canonicalStack canonical_badScalar_filter_card_ge_N_add_two

/-- The literal prize-code threshold lies strictly below the rate-quarter
Johnson radius `1 - sqrt(1/4) = 1/2`. -/
theorem evalCode_rateQuarter_mcaDeltaStar_lt_half :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) (evalCode g N (k - 1))
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) <
      (1 / 2 : ℝ≥0) :=
  evalCode_rateQuarter_mcaDeltaStar_le.trans_lt delta_lt_half

/-- Advertised-radius form on the literal `evalCode` surface. -/
theorem evalCode_rateQuarter_mcaDeltaStar_le_advertised :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) (evalCode g N (k - 1))
        ((((2 : ℕ) ^ 128 : ℕ) : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤
      (23 / 48 : ℝ≥0) - 2 / (3 * N : ℕ) := by
  rw [← delta_eq_twentyThree_over_fortyEight_correction]
  exact evalCode_rateQuarter_mcaDeltaStar_le

end ArkLib.ProximityGap.Frontier.P1RateQuarterCanonicalCodeBridge

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterCanonicalCodeBridge
#print axioms coordEquiv
#print axioms domain_eq_canonicalDomain
#print axioms evalCode_eq_canonicalCode
#print axioms canonical_mcaEvent_iff
#print axioms canonical_badScalar_filter_card_ge_N_add_two
#print axioms evalCode_rateQuarter_mcaDeltaStar_lt_half
#print axioms evalCode_rateQuarter_mcaDeltaStar_le_advertised
