/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapeLowRateExactPins
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PackingBudgetFirstJump
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateSixteenthFullWiring
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._KKH26InteriorCeilingLatticeBridge
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConverse

/-!
# The real-valued Grand MCA predicate fails at the first prize-shaped prime

The operational good-radius set at rates `1/8` and `1/16` has supremum `1/2`, but
the endpoint `1/2` is bad at budget `2^-128`.  Consequently it has no largest
element.  This refutes the real-valued `GrandMCAResolution` / `mcaPrize` predicate
for the certified smooth domain.  The faithful lattice threshold is unaffected.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ProximityGap.GrandChallenges
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.PrizeShapeLowRateExactPins

namespace ArkLib.ProximityGap.Frontier.PrizeShapeGrandChallengeRefutation

local instance firstPrimeFact : Fact (Nat.Prime PrizeShapePrimeP30.P) :=
  ⟨PrizeShapePrimeP30.prime_P⟩

/-- A bad operational supremum cannot be represented by the attained-maximum
field of `GrandMCAResolution`. -/
theorem not_nonempty_resolution_of_bad_at_deltaStar
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} [NeZero n] (C : Set (Fin n → F)) (epsilonStar : ℝ≥0)
    (hbad : (epsilonStar : ENNReal) <
      epsMCA (F := F) (A := F) C
        (mcaDeltaStar (F := F) (A := F) C (epsilonStar : ENNReal))) :
    ¬ Nonempty (GrandMCAResolution C epsilonStar) := by
  rintro ⟨R⟩
  rcases lt_or_ge R.δStar
      (mcaDeltaStar (F := F) (A := F) C (epsilonStar : ENNReal)) with hlt | hge
  · obtain ⟨delta, hRdelta, hdeltaStar⟩ := exists_between hlt
    have hgood := ProximityGap.OpenCoreConverse.epsMCA_le_of_lt_mcaDeltaStar
      (F := F) (A := F) C (epsilonStar : ENNReal) hdeltaStar
    have hstarOne :
        mcaDeltaStar (F := F) (A := F) C (epsilonStar : ENNReal) ≤ 1 := by
      unfold mcaDeltaStar
      exact csSup_le' (fun _ hdelta' => hdelta'.1)
    have hdeltaOne : delta ≤ 1 := le_trans hdeltaStar.le hstarOne
    exact (not_lt_of_ge hgood) (R.maximal delta hRdelta hdeltaOne)
  · have hgood : epsMCA (F := F) (A := F) C
        (mcaDeltaStar (F := F) (A := F) C (epsilonStar : ENNReal)) ≤
        (epsilonStar : ENNReal) :=
      le_trans (epsMCA_mono C hge) R.bound
    exact (not_lt_of_ge hgood) hbad

/-- The canonical smooth power domain at the first certified prime. -/
noncomputable def firstPrimeDomain :
    Fin (2 ^ 30) ↪ ZMod PrizeShapePrimeP30.P :=
  ProximityGap.KKH26RegimeSplit.powDomain
    PrizeShapePrimeP30.g PrizeShapePrimeP30.orderOf_g
    (ProximityGap.KKH26RegimeSplit.ne_zero_of_orderOf_eq
      PrizeShapePrimeP30.orderOf_g)

/-- The literal rate-`1/16` count theorem closes the conditional exact-pin connector. -/
theorem firstPrime_rateSixteenth_deltaStar_eq_half_local :
    mcaDeltaStar
      (F := ZMod PrizeShapePrimeP30.P) (A := ZMod PrizeShapePrimeP30.P)
      (evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 26 - 1))
      (((2 ^ 128 : ℕ) : ENNReal)⁻¹ : ENNReal) = (1 / 2 : ℝ≥0) := by
  apply firstPrime_rateSixteenth_deltaStar_eq_half_of_badCount
  intro u
  letI : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩
  have hcount :=
    ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthFullWiring.halfPredecessor_badScalar_filter_card_le_length
      (F := ZMod PrizeShapePrimeP30.P) (n := 2 ^ 30) (h := 2 ^ 29) (k := 2 ^ 26)
      firstPrimeDomain (by norm_num) (by norm_num) (by norm_num) u
  have hcode :
      evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 26 - 1) =
        (ReedSolomon.code firstPrimeDomain (2 ^ 26) :
          Set (Fin (2 ^ 30) → ZMod PrizeShapePrimeP30.P)) := by
    simpa only [firstPrimeDomain, Nat.sub_add_cancel (by norm_num : 1 ≤ 2 ^ 26)] using
      (ProximityGap.KKH26RegimeSplit.evalCode_eq_reedSolomon
        PrizeShapePrimeP30.g PrizeShapePrimeP30.orderOf_g
        (ProximityGap.KKH26RegimeSplit.ne_zero_of_orderOf_eq
          PrizeShapePrimeP30.orderOf_g) (2 ^ 26 - 1))
  rw [← hcode] at hcount
  simpa only [halfPredecessorRadius,
    ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector.halfPredecessorRadius] using hcount

/-- At rate `1/16`, the same open-endpoint phenomenon forbids a witness. -/
theorem not_grandMCAChallengeRS_rateSixteenth :
    ¬ grandMCAChallengeRS firstPrimeDomain (2 ^ 26) epsStar := by
  intro h
  rcases h with ⟨delta, hdelta, hbound, hmax⟩
  apply not_nonempty_resolution_of_bad_at_deltaStar
    (C := (ReedSolomon.code firstPrimeDomain (2 ^ 26) :
      Set (Fin (2 ^ 30) → ZMod PrizeShapePrimeP30.P)))
    (epsilonStar := epsStar)
  · have hcode :
        (ReedSolomon.code firstPrimeDomain (2 ^ 26) :
            Set (Fin (2 ^ 30) → ZMod PrizeShapePrimeP30.P)) =
          evalCode PrizeShapePrimeP30.g (2 ^ 30) (2 ^ 26 - 1) := by
      symm
      simpa only [firstPrimeDomain, Nat.sub_add_cancel (by norm_num : 1 ≤ 2 ^ 26)] using
        (ProximityGap.KKH26RegimeSplit.evalCode_eq_reedSolomon
          PrizeShapePrimeP30.g PrizeShapePrimeP30.orderOf_g
          (ProximityGap.KKH26RegimeSplit.ne_zero_of_orderOf_eq
            PrizeShapePrimeP30.orderOf_g) (2 ^ 26 - 1))
    have heps : (epsStar : ENNReal) =
        (((2 ^ 128 : ℕ) : ENNReal)⁻¹ : ENNReal) := by
      norm_num [epsStar, div_eq_mul_inv]
    rw [heps, hcode, firstPrime_rateSixteenth_deltaStar_eq_half_local]
    exact
      (ArkLib.ProximityGap.PackingBudgetFirstJump.inv_lt_epsMCA_half_of_floor_eq_length
        PrizeShapePrimeP30.orderOf_g (by norm_num) (by norm_num) (by norm_num)
        PrizeShapePrimeP30.P_div_two_pow_128 (by norm_num) (by norm_num))
  · exact ⟨⟨delta, hdelta, hbound, hmax⟩⟩

/-- The fourth advertised prize rate gives dimension exactly `2^26` at length `2^30`. -/
theorem prizeRateSixteenth_floor :
    ⌊prizeRates (⟨3, by norm_num⟩ : Fin 4) *
      (Fintype.card (Fin (2 ^ 30)) : ℝ≥0)⌋₊ = 2 ^ 26 := by
  norm_num [prizeRates]

/-- **Formal prize verdict.**  The real-valued ABF26 MCA prize predicate is false
on the first certified smooth domain because its rate-`1/8` good-radius set has no
largest element. -/
theorem not_mcaPrize_firstPrimeDomain : ¬ mcaPrize firstPrimeDomain := by
  intro hprize
  have hrate := hprize (⟨3, by norm_num⟩ : Fin 4)
  apply not_grandMCAChallengeRS_rateSixteenth
  simpa only [grandMCAChallengeRSrate, prizeRateSixteenth_floor] using hrate

#print axioms not_nonempty_resolution_of_bad_at_deltaStar
#print axioms firstPrime_rateSixteenth_deltaStar_eq_half_local
#print axioms not_grandMCAChallengeRS_rateSixteenth
#print axioms prizeRateSixteenth_floor
#print axioms not_mcaPrize_firstPrimeDomain

end ArkLib.ProximityGap.Frontier.PrizeShapeGrandChallengeRefutation
