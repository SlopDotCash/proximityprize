/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# First-collision covariance versus the two late BGK ledgers

G189 partitions the factorial repetition defect into disjoint first-collision strata and G190
polarizes the centered mass of their target profiles.  This file records the exact quantitative
consequence without importing either campaign branch:

`V(sum_i P_i) = sum_i V(P_i) + Cov_off(P)`.

At depth six there are `6 * 5 = 30` ordered collision colours.  To remove both copies of the
old pair-cover loss using a one-colour bound, it is enough that

`30 * Cov_off(P) <= -29 * sum_i V(P_i)`.

At depth seven the corresponding sharp coefficient is `41/42`.  These hypotheses imply the
robust half-unit `5 -> 6` and `6 -> 7` compact ledgers whenever the next collision defect is
itself the centered mass of the profile sum.

That last carrier hypothesis is deliberately explicit: the actual G189 sum is the *repetition*
defect, not the injective subset profile occurring in the BGK ledgers.  The second half of the
file gives the correct deletion identity.  If `J` is the factorial-scaled injective profile and
`P=sum_i P_i`, then

`V(J+P) = V(J) + [sum_i V(P_i) + Cov_off(P) + 2 Cov(J,P)]`.

Thus an internal upper bound making `Cov_off(P)` very negative does not by itself prove a late
ledger.  The bracketed deletion correction needs a *lower* bound.  A two-target nonnegative
counterprofile satisfies even the strongest internal cancellation (`V(P)=0`) while its injective
centered mass is positive and the `5 -> 6` compact ledger fails.  This isolates the remaining
sign input precisely: first-collision covariance removes the quartic norm loss, but a signed
injective--repetition covariance theorem is still required to transfer to the actual ledger.

There is also a separate coefficient obstruction.  The completed Newton enumeration reserves
only `138` for the entire repeated sector.  Making that sector free changes the injective
allocation from `126871` to `127009`, still `8126` below the Wick coefficient `135135`.
Consequently G190-type internal repeated-defect covariance cannot itself supply the main Wick
saving; that saving must occur in the raw/injective transition or Newton covariance.

Issue #466.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKFirstCollisionCovarianceLedgerBridge

/-! ## Exact local copy of the later-ledger interface -/

/-- Production subgroup size. -/
def productionN : Nat := 2 ^ 30

/-- Denominator-cleared transition ledger, definitionally identical to the interface in
`_BGKLaterTransitionDefectLedgers`.  It is duplicated so this scratch lane remains independently
iterable before that sibling scratch module has an olean. -/
def CompactTransitionLedger (n r capNumerator capDenominator : Nat)
    (D : Nat -> Int) : Prop :=
  (capDenominator : Int) * n * (r + 1 : Int) ^ 2 * D (r + 1) <=
    (capNumerator : Int) * (n - r : Int) ^ 2 * D r

/-! ## Standalone finite-profile polarization -/

/-- Unnormalized centered square mass on a finite target space. -/
def centeredMass {X : Type*} [Fintype X] (f : X -> Real) : Real :=
  (Fintype.card X : Real) * ∑ x, f x ^ 2 - (∑ x, f x) ^ 2

/-- Unnormalized centered inner product. -/
def centeredInner {X : Type*} [Fintype X] (f g : X -> Real) : Real :=
  (Fintype.card X : Real) * ∑ x, f x * g x - (∑ x, f x) * ∑ x, g x

/-- Sum of a finite family of target profiles. -/
def profileSum {I X : Type*} [DecidableEq I]
    (S : Finset I) (p : I -> X -> Real) : X -> Real :=
  fun x => ∑ i ∈ S, p i x

/-- Sum of the individual centered masses. -/
def stratumMass {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (p : I -> X -> Real) : Real :=
  ∑ i ∈ S, centeredMass (p i)

/-- Ordered off-diagonal aggregate centered covariance. -/
def aggregateCovariance {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (p : I -> X -> Real) : Real :=
  ∑ ij ∈ S.offDiag, centeredInner (p ij.1) (p ij.2)

theorem centeredMass_eq_inner {X : Type*} [Fintype X] (f : X -> Real) :
    centeredMass f = centeredInner f f := by
  unfold centeredMass centeredInner
  congr 1 <;> simp only [pow_two]

theorem centeredInner_comm {X : Type*} [Fintype X] (f g : X -> Real) :
    centeredInner f g = centeredInner g f := by
  unfold centeredInner
  simp_rw [mul_comm]

theorem centeredInner_profileSum_left {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (p : I -> X -> Real) (g : X -> Real) :
    centeredInner (profileSum S p) g = ∑ i ∈ S, centeredInner (p i) g := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [profileSum, centeredInner]
  | @insert i S hi ih =>
      rw [show profileSum (insert i S) p = fun x => p i x + profileSum S p x by
        funext x
        simp [profileSum, hi]]
      unfold centeredInner at ih ⊢
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [ih]
      simp [hi]
      ring

theorem centeredInner_profileSum_right {I X : Type*} [DecidableEq I] [Fintype X]
    (f : X -> Real) (S : Finset I) (p : I -> X -> Real) :
    centeredInner f (profileSum S p) = ∑ i ∈ S, centeredInner f (p i) := by
  rw [centeredInner_comm, centeredInner_profileSum_left]
  apply Finset.sum_congr rfl
  intro i hi
  exact centeredInner_comm _ _

/-- G190's finite-profile polarization, stated independently of the G189/G190 branch. -/
theorem centeredMass_profileSum {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (p : I -> X -> Real) :
    centeredMass (profileSum S p) = stratumMass S p + aggregateCovariance S p := by
  rw [centeredMass_eq_inner, centeredInner_profileSum_left]
  simp_rw [centeredInner_profileSum_right]
  rw [← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag S), Finset.sum_diag]
  simp_rw [← centeredMass_eq_inner]
  rfl

/-! ## Exact cancellation constants at depths six and seven -/

/-- With thirty collision colours, cancelling `29/30` of the summed stratum mass leaves one
colour's worth of centered mass. -/
theorem depthSix_cardinalityLoss_removed {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (p : I -> X -> Real)
    (hcov : 30 * aggregateCovariance S p <= -29 * stratumMass S p) :
    30 * centeredMass (profileSum S p) <= stratumMass S p := by
  rw [centeredMass_profileSum]
  linarith

/-- With forty-two collision colours, the corresponding threshold is `41/42`. -/
theorem depthSeven_cardinalityLoss_removed {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (p : I -> X -> Real)
    (hcov : 42 * aggregateCovariance S p <= -41 * stratumMass S p) :
    42 * centeredMass (profileSum S p) <= stratumMass S p := by
  rw [centeredMass_profileSum]
  linarith

/-- If the thirty individual strata cost at most thirty copies of one canonical budget, the
`29/30` covariance certificate removes the entire remaining cardinal factor. -/
theorem depthSix_oneColour_bound {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (p : I -> X -> Real) (B : Real)
    (hstrata : stratumMass S p <= 30 * B)
    (hcov : 30 * aggregateCovariance S p <= -29 * stratumMass S p) :
    centeredMass (profileSum S p) <= B := by
  have h := depthSix_cardinalityLoss_removed S p hcov
  linarith

/-- Depth-seven analogue: `41/42` aggregate cancellation converts forty-two stratum budgets to
one canonical budget. -/
theorem depthSeven_oneColour_bound {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (p : I -> X -> Real) (B : Real)
    (hstrata : stratumMass S p <= 42 * B)
    (hcov : 42 * aggregateCovariance S p <= -41 * stratumMass S p) :
    centeredMass (profileSum S p) <= B := by
  have h := depthSeven_cardinalityLoss_removed S p hcov
  linarith

/-- The two required cancellation fractions are strictly ordered: depth seven asks for the
stronger relative cancellation. -/
theorem required_cancellation_fractions :
    (29 : Rat) / 30 < 41 / 42 ∧ (41 : Rat) / 42 < 1 := by
  norm_num

/-! ## Direct-carrier consumers for the two exact compact ledgers -/

/-- **Direct-carrier `5 -> 6` bridge.**  If a depth-six collision defect is literally the
centered mass of a thirty-colour profile sum, the `29/30` aggregate-covariance certificate plus
the displayed stratum budget implies the exact robust half-unit compact ledger.

The actual G189 profile is not this carrier; see the deletion correction below. -/
theorem robust_halfUnit_five_of_directProfileCarrier
    {I X : Type*} [DecidableEq I] [Fintype X]
    (D : Nat -> Int) (S : Finset I) (p : I -> X -> Real)
    (hcarrier : (D 6 : Real) = centeredMass (profileSum S p))
    (hcov : 30 * aggregateCovariance S p <= -29 * stratumMass S p)
    (hstrata :
      (1000 : Real) * productionN * 36 * stratumMass S p <=
        30 * 10521 * (productionN - 5 : Real) ^ 2 * (D 5 : Real)) :
    CompactTransitionLedger productionN 5 10521 1000 D := by
  have hloss := depthSix_cardinalityLoss_removed S p hcov
  have hreal :
      (1000 : Real) * productionN * 36 * (D 6 : Real) <=
        10521 * (productionN - 5 : Real) ^ 2 * (D 5 : Real) := by
    rw [hcarrier]
    nlinarith
  unfold CompactTransitionLedger
  norm_num [productionN] at hreal ⊢
  exact_mod_cast hreal

/-- **Direct-carrier `6 -> 7` bridge.**  The exact depth-seven threshold is `41/42`. -/
theorem robust_halfUnit_six_of_directProfileCarrier
    {I X : Type*} [DecidableEq I] [Fintype X]
    (D : Nat -> Int) (S : Finset I) (p : I -> X -> Real)
    (hcarrier : (D 7 : Real) = centeredMass (profileSum S p))
    (hcov : 42 * aggregateCovariance S p <= -41 * stratumMass S p)
    (hstrata :
      (1000 : Real) * productionN * 49 * stratumMass S p <=
        42 * 12525 * (productionN - 6 : Real) ^ 2 * (D 6 : Real)) :
    CompactTransitionLedger productionN 6 12525 1000 D := by
  have hloss := depthSeven_cardinalityLoss_removed S p hcov
  have hreal :
      (1000 : Real) * productionN * 49 * (D 7 : Real) <=
        12525 * (productionN - 6 : Real) ^ 2 * (D 6 : Real) := by
    rw [hcarrier]
    nlinarith
  unfold CompactTransitionLedger
  norm_num [productionN] at hreal ⊢
  exact_mod_cast hreal

/-! ## The actual deletion correction -/

theorem centeredMass_add {X : Type*} [Fintype X] (f g : X -> Real) :
    centeredMass (fun x => f x + g x) =
      centeredMass f + centeredMass g + 2 * centeredInner f g := by
  unfold centeredMass centeredInner
  simp_rw [add_pow_two, Finset.sum_add_distrib, mul_add, add_mul]
  ring

/-- The complete signed correction between an all-tuples profile and its factorial-scaled
injective part.  The first two terms are G190's internal polarization; the last is G176's
injective--repetition covariance. -/
def deletionCorrection {I X : Type*} [DecidableEq I] [Fintype X]
    (J : X -> Real) (S : Finset I) (p : I -> X -> Real) : Real :=
  stratumMass S p + aggregateCovariance S p +
    2 * centeredInner J (profileSum S p)

/-- Exact two-covariance identity for the actual G189 carrier. -/
theorem centeredMass_allTuple_eq_injective_add_deletionCorrection
    {I X : Type*} [DecidableEq I] [Fintype X]
    (J : X -> Real) (S : Finset I) (p : I -> X -> Real) :
    centeredMass (fun x => J x + profileSum S p x) =
      centeredMass J + deletionCorrection J S p := by
  rw [centeredMass_add, centeredMass_profileSum]
  rfl

/-- Correct scaled deletion consumer for the robust half-unit `5 -> 6` ledger.  `U` is any
upper bound for the scaled all-tuples centered mass.  The second inequality says that the full
deletion correction, including injective--repetition covariance, absorbs the gap from `U` to the
desired injective budget. -/
theorem robust_halfUnit_five_of_deletionCorrection
    {I X : Type*} [DecidableEq I] [Fintype X]
    (D : Nat -> Int) (J : X -> Real) (S : Finset I) (p : I -> X -> Real) (U : Real)
    (hJ : centeredMass J = (Nat.factorial 6 : Real) ^ 2 * (D 6 : Real))
    (hall :
      (1000 : Real) * productionN * 36 *
          centeredMass (fun x => J x + profileSum S p x) <= U)
    (hcorrection :
      U <= (Nat.factorial 6 : Real) ^ 2 * 10521 *
          (productionN - 5 : Real) ^ 2 * (D 5 : Real) +
        (1000 : Real) * productionN * 36 * deletionCorrection J S p) :
    CompactTransitionLedger productionN 5 10521 1000 D := by
  have hid := centeredMass_allTuple_eq_injective_add_deletionCorrection J S p
  have hreal :
      (1000 : Real) * productionN * 36 * (D 6 : Real) <=
        10521 * (productionN - 5 : Real) ^ 2 * (D 5 : Real) := by
    rw [hid, hJ] at hall
    norm_num [Nat.factorial] at hall hcorrection ⊢
    nlinarith
  unfold CompactTransitionLedger
  norm_num [productionN] at hreal ⊢
  exact_mod_cast hreal

/-- Correct scaled deletion consumer for the robust half-unit `6 -> 7` ledger. -/
theorem robust_halfUnit_six_of_deletionCorrection
    {I X : Type*} [DecidableEq I] [Fintype X]
    (D : Nat -> Int) (J : X -> Real) (S : Finset I) (p : I -> X -> Real) (U : Real)
    (hJ : centeredMass J = (Nat.factorial 7 : Real) ^ 2 * (D 7 : Real))
    (hall :
      (1000 : Real) * productionN * 49 *
          centeredMass (fun x => J x + profileSum S p x) <= U)
    (hcorrection :
      U <= (Nat.factorial 7 : Real) ^ 2 * 12525 *
          (productionN - 6 : Real) ^ 2 * (D 6 : Real) +
        (1000 : Real) * productionN * 49 * deletionCorrection J S p) :
    CompactTransitionLedger productionN 6 12525 1000 D := by
  have hid := centeredMass_allTuple_eq_injective_add_deletionCorrection J S p
  have hreal :
      (1000 : Real) * productionN * 49 * (D 7 : Real) <=
        12525 * (productionN - 6 : Real) ^ 2 * (D 6 : Real) := by
    rw [hid, hJ] at hall
    norm_num [Nat.factorial] at hall hcorrection ⊢
    nlinarith
  unfold CompactTransitionLedger
  norm_num [productionN] at hreal ⊢
  exact_mod_cast hreal

/-! ## Calibrated no-go: internal cancellation alone is not a ledger transfer -/

/-- Two nonnegative strata supported at opposite targets. -/
def oppositeStrata (i x : Fin 2) : Real := if i = x then 1 else 0

/-- Their sum is constant, so its centered mass vanishes. -/
theorem oppositeStrata_profileSum_eq_one :
    profileSum (Finset.univ : Finset (Fin 2)) oppositeStrata = fun _ => 1 := by
  funext x
  fin_cases x <;> norm_num [profileSum, oppositeStrata, Fin.sum_univ_two]

theorem oppositeStrata_stratumMass :
    stratumMass (Finset.univ : Finset (Fin 2)) oppositeStrata = 2 := by
  norm_num [stratumMass, centeredMass, oppositeStrata, Fin.sum_univ_two]

/-- The ordered aggregate covariance is `-2`, exactly cancelling all individual mass. -/
theorem oppositeStrata_aggregateCovariance :
    aggregateCovariance (Finset.univ : Finset (Fin 2)) oppositeStrata = -2 := by
  norm_num [aggregateCovariance, centeredInner, oppositeStrata, Fin.sum_univ_two,
    Finset.offDiag]

theorem oppositeStrata_perfect_internal_cancellation :
    centeredMass (profileSum (Finset.univ : Finset (Fin 2)) oppositeStrata) = 0 ∧
      aggregateCovariance (Finset.univ : Finset (Fin 2)) oppositeStrata =
        -stratumMass (Finset.univ : Finset (Fin 2)) oppositeStrata := by
  rw [oppositeStrata_profileSum_eq_one, oppositeStrata_stratumMass,
    oppositeStrata_aggregateCovariance]
  norm_num [centeredMass, Fin.sum_univ_two]

/-- A unit injective profile, independent of the perfectly cancelling repetition strata. -/
def unitInjectiveProfile (x : Fin 2) : Real := if x = 0 then 1 else 0

theorem unitInjectiveProfile_centeredMass : centeredMass unitInjectiveProfile = 1 := by
  norm_num [centeredMass, unitInjectiveProfile, Fin.sum_univ_two]

/-- A signed defect ledger with zero depth-five defect and positive depth-six defect. -/
def counterDefect (r : Nat) : Int := if r = 6 then 1 else 0

theorem counterDefect_five : counterDefect 5 = 0 := by norm_num [counterDefect]

theorem counterDefect_six : counterDefect 6 = 1 := by norm_num [counterDefect]

/-- Even perfect internal first-collision cancellation does not imply the late ledger: the
injective profile can retain positive centered mass while the predecessor defect is zero. -/
theorem internal_covariance_alone_does_not_imply_fiveLedger :
    (30 * aggregateCovariance (Finset.univ : Finset (Fin 2)) oppositeStrata <=
        -29 * stratumMass (Finset.univ : Finset (Fin 2)) oppositeStrata) ∧
      ((counterDefect 6 : Real) = centeredMass unitInjectiveProfile) ∧
      ¬ CompactTransitionLedger productionN 5 10521 1000 counterDefect := by
  refine ⟨?_, ?_, ?_⟩
  · rw [oppositeStrata_aggregateCovariance, oppositeStrata_stratumMass]
    norm_num
  · rw [counterDefect_six, unitInjectiveProfile_centeredMass]
    norm_num
  · norm_num [CompactTransitionLedger, counterDefect, productionN]

/-- In the counterprofile the full deletion correction is zero: internal cancellation contributes
nothing, and a constant repetition sum has zero centered covariance with the injective profile.
This is the exact missing sign strength exposed by the no-go. -/
theorem counterprofile_deletionCorrection_eq_zero :
    deletionCorrection unitInjectiveProfile (Finset.univ : Finset (Fin 2))
      oppositeStrata = 0 := by
  rw [deletionCorrection, oppositeStrata_stratumMass,
    oppositeStrata_aggregateCovariance, oppositeStrata_profileSum_eq_one]
  norm_num [centeredInner, unitInjectiveProfile, Fin.sum_univ_two]

end ArkLib.ProximityGap.Frontier.BGKFirstCollisionCovarianceLedgerBridge

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.BGKFirstCollisionCovarianceLedgerBridge.centeredMass_profileSum
#print axioms
  ArkLib.ProximityGap.Frontier.BGKFirstCollisionCovarianceLedgerBridge.depthSix_cardinalityLoss_removed
#print axioms
  ArkLib.ProximityGap.Frontier.BGKFirstCollisionCovarianceLedgerBridge.robust_halfUnit_five_of_directProfileCarrier
#print axioms
  ArkLib.ProximityGap.Frontier.BGKFirstCollisionCovarianceLedgerBridge.robust_halfUnit_six_of_directProfileCarrier
#print axioms
  ArkLib.ProximityGap.Frontier.BGKFirstCollisionCovarianceLedgerBridge.centeredMass_allTuple_eq_injective_add_deletionCorrection
#print axioms
  ArkLib.ProximityGap.Frontier.BGKFirstCollisionCovarianceLedgerBridge.robust_halfUnit_five_of_deletionCorrection
#print axioms
  ArkLib.ProximityGap.Frontier.BGKFirstCollisionCovarianceLedgerBridge.robust_halfUnit_six_of_deletionCorrection
#print axioms
  ArkLib.ProximityGap.Frontier.BGKFirstCollisionCovarianceLedgerBridge.internal_covariance_alone_does_not_imply_fiveLedger
#print axioms
  ArkLib.ProximityGap.Frontier.BGKFirstCollisionCovarianceLedgerBridge.counterprofile_deletionCorrection_eq_zero
