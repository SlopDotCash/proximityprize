/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKActualJointPeriodLaw

/-!
# The signed weighted-collision law at the injective transition `2 -> 3`

The ordered-injective cubic Fourier coefficient is Newton's polynomial

`J_3(b) = eta_b^3 - 3 eta_b eta_(2b) + 2 eta_(3b)`.

Expanding its full `L2` energy and applying the weighted mixed-moment Parseval theorem gives the
exact signed census

`q * (C_111,111 + 9 C_12,12 + 4 n
      - 6 C_111,12 + 4 C_111,3 - 12 C_12,3)`.

Every `C` is an actual weighted additive-collision count in `G`.  This is the first remaining
trajectory transition after the `1 -> 2` one-unit defect was excluded.  The file also removes the
zero frequency, obtaining the exact centered/injective energy, and rewrites a one-unit `2 -> 3`
Wick defect as a lower bound on the favorable signed correlation

`6 C_111,12 + 12 C_12,3`.

The term `C_12,12` is precisely the energy of the doubled weighted convolution isolated by G185;
G186's Young estimate controls this *positive* square term from above.  That estimate does not
control either favorable mixed correlation from below.  Dropping signs replaces the exact census
by an unsigned envelope and loses exactly

`6 C_111,12 + 12 C_12,3`.

Thus unsigned Young is a valid envelope but cannot itself certify the desired defect.  A survivor
must prove a lower correlation estimate for the actual subgroup, or move the defect to a denser
later transition.  The final arithmetic lemma records a robust alternative: half a Wick unit at
each of the last two transitions (`11 -> 21/2`, `13 -> 25/2`) still closes after a uniform
`501/500` overhead at all six steps.  No such arithmetic correlation estimate is asserted here.
Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 2048

open Finset AddChar
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKCubicSignedWeightedCollision

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.Frontier.BGKActualJointPeriodLaw

section CubicLaw

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Three unit weights, encoding `eta_b^3`. -/
def tripleUnitWeights : Fin 3 -> F := fun _ => 1

/-- Weights `(1,2)`, encoding `eta_b * eta_(2b)`. -/
def oneTwoWeights : Fin 2 -> F := ![1, 2]

/-- One tripled weight, encoding `eta_(3b)`. -/
def tripleTargetWeight : Fin 1 -> F := fun _ => 3

/-- The ordinary three-sum collision census `C_111,111`. -/
noncomputable def tripleSelfCollisionCount (G : Finset F) : Nat :=
  mixedDilationCollisionCount G tripleUnitWeights tripleUnitWeights

/-- The doubled weighted-convolution energy `C_12,12`. -/
noncomputable def oneTwoSelfCollisionCount (G : Finset F) : Nat :=
  mixedDilationCollisionCount G oneTwoWeights oneTwoWeights

/-- The first favorable mixed census `C_111,12`. -/
noncomputable def tripleToOneTwoCollisionCount (G : Finset F) : Nat :=
  mixedDilationCollisionCount G tripleUnitWeights oneTwoWeights

/-- The (positive-sign) triple-average resonance census `C_111,3`. -/
noncomputable def tripleToTripleTargetCollisionCount (G : Finset F) : Nat :=
  mixedDilationCollisionCount G tripleUnitWeights tripleTargetWeight

/-- The second favorable mixed census `C_12,3`. -/
noncomputable def oneTwoToTripleTargetCollisionCount (G : Finset F) : Nat :=
  mixedDilationCollisionCount G oneTwoWeights tripleTargetWeight

/-- The exact signed collision coefficient of the full cubic energy. -/
noncomputable def cubicSignedCollisionCombination (G : Finset F) : Int :=
  tripleSelfCollisionCount G + 9 * oneTwoSelfCollisionCount G + 4 * G.card -
    6 * tripleToOneTwoCollisionCount G +
    4 * tripleToTripleTargetCollisionCount G -
    12 * oneTwoToTripleTargetCollisionCount G

/-- The positive unsigned envelope obtained by deleting both favorable cross terms. -/
noncomputable def cubicUnsignedYoungEnvelope (G : Finset F) : Int :=
  tripleSelfCollisionCount G + 9 * oneTwoSelfCollisionCount G + 4 * G.card +
    4 * tripleToTripleTargetCollisionCount G

/-- The favorable correlation mass which unsigned Young discards. -/
noncomputable def cubicFavorableCorrelation (G : Finset F) : Int :=
  6 * tripleToOneTwoCollisionCount G +
    12 * oneTwoToTripleTargetCollisionCount G

/-- Exact signed/unsigned split.  This is the formal boundary of the G186 Young route. -/
theorem cubicSignedCollisionCombination_eq_unsigned_sub_favorable (G : Finset F) :
    cubicSignedCollisionCombination G =
      cubicUnsignedYoungEnvelope G - cubicFavorableCorrelation G := by
  unfold cubicSignedCollisionCombination cubicUnsignedYoungEnvelope cubicFavorableCorrelation
  ring

/-- The unsigned envelope is indeed an upper bound, but only because it drops the correlation
whose lower bound would create the desired saving. -/
theorem cubicSignedCollisionCombination_le_unsigned (G : Finset F) :
    cubicSignedCollisionCombination G <= cubicUnsignedYoungEnvelope G := by
  rw [cubicSignedCollisionCombination_eq_unsigned_sub_favorable]
  have hcorr : 0 <= cubicFavorableCorrelation G := by
    unfold cubicFavorableCorrelation
    positivity
  omega

/-- Ordered-injective depth-three Fourier coefficient. -/
noncomputable def orderedDistinctTriplePeriod
    (psi : AddChar F Complex) (G : Finset F) (b : F) : Complex :=
  eta psi G b ^ 3 -
    3 * eta psi G b * eta psi G ((2 : F) * b) +
    2 * eta psi G ((3 : F) * b)

private theorem prod_oneTwo_eta (psi : AddChar F Complex) (G : Finset F) (b : F) :
    (∏ i : Fin 2, eta psi G (oneTwoWeights i * b)) =
      eta psi G b * eta psi G ((2 : F) * b) := by
  simp [oneTwoWeights, Fin.prod_univ_succ]

/-- **Exact full cubic signed-collision law.** -/
theorem sum_orderedDistinctTriplePeriod_mul_conj_eq
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F)
    (h3 : (3 : F) ≠ 0) :
    (∑ b : F, orderedDistinctTriplePeriod psi G b *
      (starRingEnd Complex) (orderedDistinctTriplePeriod psi G b)) =
      (Fintype.card F : Complex) * (cubicSignedCollisionCombination G : Complex) := by
  have hAA : (∑ b : F, eta psi G b ^ 3 *
      (starRingEnd Complex) (eta psi G b ^ 3)) =
      (Fintype.card F : Complex) * tripleSelfCollisionCount G := by
    simpa [tripleUnitWeights, tripleSelfCollisionCount, Finset.prod_const] using
      (sum_prod_dilated_eta_mul_conj_eq_collisionCount
        (I := Fin 3) (J := Fin 3) hpsi G tripleUnitWeights tripleUnitWeights)
  have hBB : (∑ b : F,
      (eta psi G b * eta psi G ((2 : F) * b)) *
        (starRingEnd Complex) (eta psi G b * eta psi G ((2 : F) * b))) =
      (Fintype.card F : Complex) * oneTwoSelfCollisionCount G := by
    have hBBRaw := sum_prod_dilated_eta_mul_conj_eq_collisionCount
      (I := Fin 2) (J := Fin 2) hpsi G oneTwoWeights oneTwoWeights
    simp_rw [prod_oneTwo_eta] at hBBRaw
    simpa only [oneTwoSelfCollisionCount] using hBBRaw
  have hCC := sum_dilated_eta_mul_conj_eq_dilationCoincidenceCount
    hpsi G (3 : F) 3
  rw [dilationCoincidenceCount_same G 3 h3] at hCC
  have hAB : (∑ b : F, eta psi G b ^ 3 *
      (starRingEnd Complex)
        (eta psi G b * eta psi G ((2 : F) * b))) =
      (Fintype.card F : Complex) * tripleToOneTwoCollisionCount G := by
    have hABRaw := sum_prod_dilated_eta_mul_conj_eq_collisionCount
      (I := Fin 3) (J := Fin 2) hpsi G tripleUnitWeights oneTwoWeights
    simp_rw [prod_oneTwo_eta] at hABRaw
    simpa [tripleUnitWeights, tripleToOneTwoCollisionCount,
      Finset.prod_const] using hABRaw
  have hBARaw := sum_prod_dilated_eta_mul_conj_eq_collisionCount
    (I := Fin 2) (J := Fin 3) hpsi G oneTwoWeights tripleUnitWeights
  rw [mixedDilationCollisionCount_swap G oneTwoWeights tripleUnitWeights] at hBARaw
  simp_rw [prod_oneTwo_eta] at hBARaw
  have hBA : (∑ b : F,
      (eta psi G b * eta psi G ((2 : F) * b)) *
        (starRingEnd Complex) (eta psi G b ^ 3)) =
      (Fintype.card F : Complex) * tripleToOneTwoCollisionCount G := by
    simpa [tripleUnitWeights, tripleToOneTwoCollisionCount,
      Finset.prod_const] using hBARaw
  have hAC : (∑ b : F, eta psi G b ^ 3 *
      (starRingEnd Complex) (eta psi G ((3 : F) * b))) =
      (Fintype.card F : Complex) * tripleToTripleTargetCollisionCount G := by
    simpa [tripleUnitWeights, tripleTargetWeight,
      tripleToTripleTargetCollisionCount, Finset.prod_const] using
      (sum_prod_dilated_eta_mul_conj_eq_collisionCount
        (I := Fin 3) (J := Fin 1) hpsi G tripleUnitWeights tripleTargetWeight)
  have hCARaw := sum_prod_dilated_eta_mul_conj_eq_collisionCount
    (I := Fin 1) (J := Fin 3) hpsi G tripleTargetWeight tripleUnitWeights
  rw [mixedDilationCollisionCount_swap G tripleTargetWeight tripleUnitWeights] at hCARaw
  have hCA : (∑ b : F, eta psi G ((3 : F) * b) *
      (starRingEnd Complex) (eta psi G b ^ 3)) =
      (Fintype.card F : Complex) * tripleToTripleTargetCollisionCount G := by
    simpa [tripleUnitWeights, tripleTargetWeight,
      tripleToTripleTargetCollisionCount, Finset.prod_const] using hCARaw
  have hBC : (∑ b : F,
      (eta psi G b * eta psi G ((2 : F) * b)) *
        (starRingEnd Complex) (eta psi G ((3 : F) * b))) =
      (Fintype.card F : Complex) * oneTwoToTripleTargetCollisionCount G := by
    have hBCRaw := sum_prod_dilated_eta_mul_conj_eq_collisionCount
      (I := Fin 2) (J := Fin 1) hpsi G oneTwoWeights tripleTargetWeight
    simp_rw [prod_oneTwo_eta] at hBCRaw
    simpa [tripleTargetWeight, oneTwoToTripleTargetCollisionCount,
      Finset.prod_const] using hBCRaw
  have hCBRaw := sum_prod_dilated_eta_mul_conj_eq_collisionCount
    (I := Fin 1) (J := Fin 2) hpsi G tripleTargetWeight oneTwoWeights
  rw [mixedDilationCollisionCount_swap G tripleTargetWeight oneTwoWeights] at hCBRaw
  simp_rw [prod_oneTwo_eta] at hCBRaw
  have hCB : (∑ b : F, eta psi G ((3 : F) * b) *
      (starRingEnd Complex)
        (eta psi G b * eta psi G ((2 : F) * b))) =
      (Fintype.card F : Complex) * oneTwoToTripleTargetCollisionCount G := by
    simpa [tripleTargetWeight, oneTwoToTripleTargetCollisionCount,
      Finset.prod_const] using hCBRaw
  calc
    (∑ b : F, orderedDistinctTriplePeriod psi G b *
        (starRingEnd Complex) (orderedDistinctTriplePeriod psi G b)) =
        ∑ b : F, (
          eta psi G b ^ 3 * (starRingEnd Complex) (eta psi G b ^ 3) +
          9 * ((eta psi G b * eta psi G ((2 : F) * b)) *
            (starRingEnd Complex) (eta psi G b * eta psi G ((2 : F) * b))) +
          4 * (eta psi G ((3 : F) * b) *
            (starRingEnd Complex) (eta psi G ((3 : F) * b))) -
          3 * (eta psi G b ^ 3 *
            (starRingEnd Complex) (eta psi G b * eta psi G ((2 : F) * b))) -
          3 * ((eta psi G b * eta psi G ((2 : F) * b)) *
            (starRingEnd Complex) (eta psi G b ^ 3)) +
          2 * (eta psi G b ^ 3 *
            (starRingEnd Complex) (eta psi G ((3 : F) * b))) +
          2 * (eta psi G ((3 : F) * b) *
            (starRingEnd Complex) (eta psi G b ^ 3)) -
          6 * ((eta psi G b * eta psi G ((2 : F) * b)) *
            (starRingEnd Complex) (eta psi G ((3 : F) * b))) -
          6 * (eta psi G ((3 : F) * b) *
            (starRingEnd Complex) (eta psi G b * eta psi G ((2 : F) * b)))) := by
      apply Finset.sum_congr rfl
      intro b _hb
      unfold orderedDistinctTriplePeriod
      simp only [map_add, map_sub, map_mul, map_ofNat]
      ring
    _ = (∑ b : F, eta psi G b ^ 3 *
          (starRingEnd Complex) (eta psi G b ^ 3)) +
        9 * (∑ b : F, (eta psi G b * eta psi G ((2 : F) * b)) *
          (starRingEnd Complex) (eta psi G b * eta psi G ((2 : F) * b))) +
        4 * (∑ b : F, eta psi G ((3 : F) * b) *
          (starRingEnd Complex) (eta psi G ((3 : F) * b))) -
        3 * (∑ b : F, eta psi G b ^ 3 *
          (starRingEnd Complex) (eta psi G b * eta psi G ((2 : F) * b))) -
        3 * (∑ b : F, (eta psi G b * eta psi G ((2 : F) * b)) *
          (starRingEnd Complex) (eta psi G b ^ 3)) +
        2 * (∑ b : F, eta psi G b ^ 3 *
          (starRingEnd Complex) (eta psi G ((3 : F) * b))) +
        2 * (∑ b : F, eta psi G ((3 : F) * b) *
          (starRingEnd Complex) (eta psi G b ^ 3)) -
        6 * (∑ b : F, (eta psi G b * eta psi G ((2 : F) * b)) *
          (starRingEnd Complex) (eta psi G ((3 : F) * b))) -
        6 * (∑ b : F, eta psi G ((3 : F) * b) *
          (starRingEnd Complex) (eta psi G b * eta psi G ((2 : F) * b))) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = (Fintype.card F : Complex) * (cubicSignedCollisionCombination G : Complex) := by
      rw [hAA, hBB, hCC, hAB, hBA, hAC, hCA, hBC, hCB]
      unfold cubicSignedCollisionCombination
      push_cast
      ring

/-- Removing frequency zero subtracts the square of the ordered-injective mass
`(n*(n-1)*(n-2))^2`. -/
theorem sum_nonzero_orderedDistinctTriplePeriod_mul_conj_eq
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive) (G : Finset F)
    (h3 : (3 : F) ≠ 0) :
    (∑ b ∈ Finset.univ.erase (0 : F), orderedDistinctTriplePeriod psi G b *
      (starRingEnd Complex) (orderedDistinctTriplePeriod psi G b)) =
      (Fintype.card F : Complex) * (cubicSignedCollisionCombination G : Complex) -
        ((G.card : Complex) * (G.card - 1) * (G.card - 2)) ^ 2 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0),
    sum_orderedDistinctTriplePeriod_mul_conj_eq hpsi G h3]
  norm_num [orderedDistinctTriplePeriod, eta, AddChar.map_zero_eq_one]
  have hstar2 : (starRingEnd Complex) (2 : Complex) = 2 := by
    simp [starRingEnd_apply]
  have hstar3 : (starRingEnd Complex) (3 : Complex) = 3 := by
    simp [starRingEnd_apply]
  rw [hstar2, hstar3]
  ring

/-! ## Exact defect ledgers -/

/-- Integer numerator of the nonzero ordered-pair energy from the preceding transition. -/
noncomputable def orderedPairNonzeroEnergyLedger (G : Finset F) : Int :=
  Fintype.card F *
      (pairAdditiveCollisionCount G + G.card - 2 * midpointResonanceCount G : Int) -
    ((G.card : Int) * (G.card - 1)) ^ 2

/-- Integer numerator of the nonzero ordered-triple energy. -/
noncomputable def orderedTripleNonzeroEnergyLedger (G : Finset F) : Int :=
  Fintype.card F * cubicSignedCollisionCombination G -
    ((G.card : Int) * (G.card - 1) * (G.card - 2)) ^ 2

/-- A full one-unit Wick defect at `2 -> 3`: the normalized transition numerator is at most
`4` rather than its Wick baseline `5`.  Denominators have been cleared. -/
def SecondToThirdOneUnitDefectLedger (G : Finset F) : Prop :=
  (G.card : Int) * orderedTripleNonzeroEnergyLedger G <=
    4 * (G.card - 2 : Int) ^ 2 * orderedPairNonzeroEnergyLedger G

/-- The robust version selected by the `501/500` trajectory consumer: the normalized transition
numerator is at most `(501/500)*4`. -/
def SecondToThirdRobustDefectLedger (G : Finset F) : Prop :=
  500 * (G.card : Int) * orderedTripleNonzeroEnergyLedger G <=
    2004 * (G.card - 2 : Int) ^ 2 * orderedPairNonzeroEnergyLedger G

/-- The one-unit condition is exactly a lower threshold on the two favorable weighted
correlations.  This is the concrete arithmetic socket left at `2 -> 3`. -/
theorem secondToThirdOneUnitDefectLedger_iff_favorableThreshold (G : Finset F) :
    SecondToThirdOneUnitDefectLedger G <->
      (G.card : Int) * Fintype.card F * cubicUnsignedYoungEnvelope G -
          (G.card : Int) *
            ((G.card : Int) * (G.card - 1) * (G.card - 2)) ^ 2 -
          4 * (G.card - 2 : Int) ^ 2 * orderedPairNonzeroEnergyLedger G <=
        (G.card : Int) * Fintype.card F * cubicFavorableCorrelation G := by
  unfold SecondToThirdOneUnitDefectLedger orderedTripleNonzeroEnergyLedger
  rw [cubicSignedCollisionCombination_eq_unsigned_sub_favorable]
  constructor <;> intro h <;> nlinarith

/-- Robust `501/500` form of the same signed-correlation threshold. -/
theorem secondToThirdRobustDefectLedger_iff_favorableThreshold (G : Finset F) :
    SecondToThirdRobustDefectLedger G <->
      500 * (G.card : Int) * Fintype.card F * cubicUnsignedYoungEnvelope G -
          500 * (G.card : Int) *
            ((G.card : Int) * (G.card - 1) * (G.card - 2)) ^ 2 -
          2004 * (G.card - 2 : Int) ^ 2 * orderedPairNonzeroEnergyLedger G <=
        500 * (G.card : Int) * Fintype.card F * cubicFavorableCorrelation G := by
  unfold SecondToThirdRobustDefectLedger orderedTripleNonzeroEnergyLedger
  rw [cubicSignedCollisionCombination_eq_unsigned_sub_favorable]
  constructor <;> intro h <;> nlinarith

end CubicLaw

/-! ## A robust dense-late alternative -/

/-- A distributed profile which leaves the first four Wick numerators unchanged and saves half
a unit at each of the two densest transitions. -/
def twoLateHalfUnitProfile : Fin 6 -> Rat := ![3, 5, 7, 9, 21 / 2, 25 / 2]

theorem twoLateHalfUnitProfile_product :
    (∏ i : Fin 6, twoLateHalfUnitProfile i) = 496125 / 4 := by
  norm_num [Fin.prod_univ_succ, twoLateHalfUnitProfile]

/-- Even a uniform `501/500` overhead at every transition leaves this two-late half-unit profile
strictly below the injective coefficient `126871`. -/
theorem robust_twoLateHalfUnitProfile_closes :
    ((501 : Rat) / 500) ^ 6 * (∏ i : Fin 6, twoLateHalfUnitProfile i) < 126871 := by
  rw [twoLateHalfUnitProfile_product]
  norm_num

/-! ## Axiom audit -/

#print axioms cubicSignedCollisionCombination_eq_unsigned_sub_favorable
#print axioms sum_orderedDistinctTriplePeriod_mul_conj_eq
#print axioms sum_nonzero_orderedDistinctTriplePeriod_mul_conj_eq
#print axioms secondToThirdOneUnitDefectLedger_iff_favorableThreshold
#print axioms secondToThirdRobustDefectLedger_iff_favorableThreshold
#print axioms robust_twoLateHalfUnitProfile_closes

end ArkLib.ProximityGap.Frontier.BGKCubicSignedWeightedCollision
