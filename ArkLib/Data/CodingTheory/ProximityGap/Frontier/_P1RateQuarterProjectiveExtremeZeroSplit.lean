/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterProjectiveStructuredSplit
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterExtremeZeroJohnsonBand

/-!
# Projective extreme-zero split at the P1 rate-quarter predecessor

Projective nearness gives a codeword translate of every nonzero row-mix direction with support at
most `746469603`.  The two-tier extreme-zero estimate is stronger than its rounded `N`-budget
statement: its actual affine cap is `1013444618`.  Even after paying for the one projective slot
outside an affine chart, this is still strictly below `N`.

Consequently, for every invertible row mix of an over-budget stack and every nearby codeword
translate supplied by projective nearness, either the translated direction has support strictly
greater than `55920000`, or the translated affine line is zero-direction-unsafe.  The unsafe branch
is not left opaque: it is exactly a predecessor codeword agreeing with the mixed offset on at least
`predecessorThreshold` coordinates on which the chosen direction codeword agrees with the mixed
direction.  Invertibility transports this common joint agreement set back to the original rows.

No global residual is discharged here.  The result only removes the zero-safe extreme-support
endpoint from every projective chart.  All proofs contain no placeholders and are axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 800000
set_option maxRecDepth 500000

open Finset
open _root_.ProximityGap Code
open scoped NNReal

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterProjectiveExtremeZeroSplit

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.MCAFloorFactorization
open ProximityGap.MCAEquivariance
open ProximityGap.MCAProjectiveEquivariance
open ProximityGap.ProjectiveWorstCaseIncidence
open ProximityGap.Ownership
open P1RateQuarterScaleArithmetic
open P1RateQuarterPredecessorGenericSplit
open P1RateQuarterProjectiveStructuredSplit
open P1RateQuarterExtremeZeroJohnsonBand

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-! ## The unrounded two-tier budget -/

/-- The actual natural-number output of the two-tier Johnson calculation. -/
abbrev twoTierClosedBudget : Nat :=
  18 * twoTierSupportCap + 264793 * 26

theorem twoTierClosedBudget_eq : twoTierClosedBudget = 1013444618 := by
  norm_num [twoTierClosedBudget, twoTierSupportCap]

/-- The actual two-tier cap still fits after adding the one projective slot outside an affine
chart.  This slack is what makes the extreme-zero split uniform over arbitrary invertible row
mixes. -/
theorem twoTierClosedBudget_add_one_lt_N : twoTierClosedBudget + 1 < N := by
  norm_num [twoTierClosedBudget, twoTierSupportCap, N]

/-- Sharp, unrounded MCA-facing form of the two-tier extreme-zero estimate. -/
theorem predecessor_mcaEvent_filter_card_le_twoTierClosedBudget
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hsafe : ZeroDirectionSafeLine dom k predecessorThreshold u₀ u₁)
    (hsupport : (directionSupportSet u₁).card ≤ twoTierSupportCap) :
    (Finset.univ.filter (fun gamma : F =>
      mcaEvent (predecessorCode dom : Set (Fin N → F)) predecessorDelta
        u₀ u₁ gamma)).card ≤ twoTierClosedBudget := by
  have hallFit : twoTierAllAgreement + twoTierSupportCap ≤ predecessorThreshold := by
    rw [twoTierAllAgreement_eq, predecessorThreshold_eq]
    norm_num [twoTierSupportCap]
  have hhighEq : twoTierHighAgreement + twoTierDeficiencyCut = predecessorThreshold := by
    rw [twoTierHighAgreement_eq, predecessorThreshold_eq]
    norm_num [twoTierDeficiencyCut]
  have hweight :=
    ProximityGap.ExtremeZeroJohnsonBand.puncturedZeroStratifiedLineWeight_le_twoTierJohnson
      dom (k := k) (a := predecessorThreshold)
        (hAll := twoTierAllAgreement) (hHigh := twoTierHighAgreement)
        (d := twoTierDeficiencyCut) (s := twoTierSupportCap)
        (by norm_num [k]) u₀ u₁ hsupport hallFit hhighEq
        (by simpa only [Fintype.card_fin] using twoTierAll_gap)
        (by simpa only [Fintype.card_fin] using twoTierHigh_gap)
  rw [twoTierHigh_list_cap, twoTierAll_list_cap, twoTier_support_div] at hweight
  calc
    (Finset.univ.filter (fun gamma : F =>
        mcaEvent (predecessorCode dom : Set (Fin N → F)) predecessorDelta
          u₀ u₁ gamma)).card
        ≤ (lineBadScalars dom k predecessorThreshold u₀ u₁).card :=
      Finset.card_le_card
        (predecessor_mcaEvent_filter_subset_lineBadScalars dom u₀ u₁)
    _ ≤ ProximityGap.Ownership.puncturedZeroStratifiedLineWeight
          dom k predecessorThreshold u₀ u₁ :=
      lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
        dom k predecessorThreshold u₀ u₁ hsafe
    _ ≤ twoTierClosedBudget := by
      simpa only [twoTierClosedBudget] using hweight

/-! ## Count transport through translation and a projective chart -/

/-- Translating only the direction row by a codeword preserves the affine bad count. -/
theorem badCount_direction_sub_codeword
    (dom : Fin N ↪ F) (u₀ u₁ r : Fin N → F)
    (hr : r ∈ predecessorCode dom) :
    badCount (predecessorCode dom) predecessorDelta u₀ (u₁ - r) =
      badCount (predecessorCode dom) predecessorDelta u₀ u₁ := by
  classical
  apply congrArg Finset.card
  ext gamma
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simpa only [sub_eq_add_neg, add_zero] using
    (mcaEvent_translate (predecessorCode dom)
      (δ := predecessorDelta) (u₀ := u₀) (u₁ := u₁)
      (c₀ := 0) (c₁ := -r)
      (predecessorCode dom).zero_mem ((predecessorCode dom).neg_mem hr) gamma)

/-- An arbitrary invertible row mix can lose at most the one projective slot omitted by its affine
chart. -/
theorem badCount_le_rowMix_badCount_add_one
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    {a b c d : F} (hdet : a * d - b * c ≠ 0) :
    badCount (predecessorCode dom) predecessorDelta u₀ u₁ ≤
      badCount (predecessorCode dom) predecessorDelta
        (a • u₀ + b • u₁) (c • u₀ + d • u₁) + 1 := by
  calc
    badCount (predecessorCode dom) predecessorDelta u₀ u₁
        ≤ badSlotCount (F := F) (predecessorCode dom : Set (Fin N → F))
            predecessorDelta u₀ u₁ :=
      badCount_le_badSlotCount dom u₀ u₁
    _ = badSlotCount (F := F) (predecessorCode dom : Set (Fin N → F))
          predecessorDelta (a • u₀ + b • u₁) (c • u₀ + d • u₁) :=
      (badSlotCount_row_mix (predecessorCode dom) hdet predecessorDelta u₀ u₁).symm
    _ ≤ badCount (predecessorCode dom) predecessorDelta
          (a • u₀ + b • u₁) (c • u₀ + d • u₁) + 1 := by
      rw [badSlotCount_eq_affine_add_infty]
      simp only [badCount]
      split <;> omega

/-- A zero-safe small-support translate in any invertible chart forces the original affine count
strictly below the prize budget. -/
theorem badCount_lt_N_of_rowMix_direction_translate_safe
    (dom : Fin N ↪ F) (u₀ u₁ r : Fin N → F)
    {a b c d : F} (hdet : a * d - b * c ≠ 0)
    (hr : r ∈ predecessorCode dom)
    (hsafe : ZeroDirectionSafeLine dom k predecessorThreshold
      (a • u₀ + b • u₁) ((c • u₀ + d • u₁) - r))
    (hsupport :
      (directionSupportSet ((c • u₀ + d • u₁) - r)).card ≤ twoTierSupportCap) :
    badCount (predecessorCode dom) predecessorDelta u₀ u₁ < N := by
  calc
    badCount (predecessorCode dom) predecessorDelta u₀ u₁
        ≤ badCount (predecessorCode dom) predecessorDelta
            (a • u₀ + b • u₁) (c • u₀ + d • u₁) + 1 :=
      badCount_le_rowMix_badCount_add_one dom u₀ u₁ hdet
    _ = badCount (predecessorCode dom) predecessorDelta
          (a • u₀ + b • u₁) ((c • u₀ + d • u₁) - r) + 1 := by
      rw [badCount_direction_sub_codeword dom
        (a • u₀ + b • u₁) (c • u₀ + d • u₁) r hr]
    _ ≤ twoTierClosedBudget + 1 := Nat.add_le_add_right
      (predecessor_mcaEvent_filter_card_le_twoTierClosedBudget dom
        (a • u₀ + b • u₁) ((c • u₀ + d • u₁) - r)
        hsafe hsupport) 1
    _ < N := twoTierClosedBudget_add_one_lt_N

/-! ## The unsafe branch as a transported joint agreement -/

/-- The explicit witness hidden by zero-direction unsafety after translating the mixed direction
by `r`: a codeword agrees with the mixed offset on a threshold-size set on which `r` agrees with
the mixed direction. -/
def DirectionPinnedJointAgreement
    (dom : Fin N ↪ F) (v₀ v₁ r : Fin N → F) : Prop :=
  ∃ q ∈ predecessorCode dom, ∃ S : Finset (Fin N),
    predecessorThreshold ≤ S.card ∧
      ∀ i ∈ S, q i = v₀ i ∧ r i = v₁ i

/-- Zero-direction unsafety is exactly the direction-pinned common agreement witness. -/
theorem not_zeroDirectionSafeLine_iff_directionPinnedJointAgreement
    (dom : Fin N ↪ F) (v₀ v₁ r : Fin N → F) :
    ¬ ZeroDirectionSafeLine dom k predecessorThreshold v₀ (v₁ - r) ↔
      DirectionPinnedJointAgreement dom v₀ v₁ r := by
  classical
  constructor
  · intro hunsafe
    rw [ZeroDirectionSafeLine] at hunsafe
    push Not at hunsafe
    obtain ⟨q, hq, hcard⟩ := hunsafe
    refine ⟨q,
      (ProximityGap.ExtremeZeroJohnsonBand.mem_rsCode_iff_mem_reedSolomonCode
        dom k q).mp hq,
      directionZeroAgreementSet q v₀ (v₁ - r), hcard, ?_⟩
    intro i hi
    rw [directionZeroAgreementSet, Finset.mem_filter] at hi
    have hzero : (v₁ - r) i = 0 := by
      simpa only [directionZeroSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi.1
    exact ⟨hi.2, (sub_eq_zero.mp hzero).symm⟩
  · rintro ⟨q, hq, S, hcard, hagree⟩ hsafe
    have hq' : q ∈ (ProximityGap.SpikeFloor.rsCode dom k : Submodule F (Fin N → F)) :=
      (ProximityGap.ExtremeZeroJohnsonBand.mem_rsCode_iff_mem_reedSolomonCode
        dom k q).mpr hq
    have hsub : S ⊆ directionZeroAgreementSet q v₀ (v₁ - r) := by
      intro i hi
      rw [directionZeroAgreementSet, Finset.mem_filter]
      refine ⟨?_, (hagree i hi).1⟩
      rw [directionZeroSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [Pi.sub_apply, (hagree i hi).2, sub_self]
    have hge : predecessorThreshold ≤
        (directionZeroAgreementSet q v₀ (v₁ - r)).card :=
      hcard.trans (Finset.card_le_card hsub)
    exact (Nat.not_lt_of_ge hge) (hsafe q hq')

/-- The pinned witness jointly explains the mixed rows on the same threshold-size set. -/
theorem directionPinnedJointAgreement_implies_pairJointAgreesOn
    (dom : Fin N ↪ F) (v₀ v₁ r : Fin N → F)
    (hr : r ∈ predecessorCode dom)
    (hpinned : DirectionPinnedJointAgreement dom v₀ v₁ r) :
    ∃ S : Finset (Fin N), predecessorThreshold ≤ S.card ∧
      pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) S v₀ v₁ := by
  obtain ⟨q, hq, S, hcard, hagree⟩ := hpinned
  exact ⟨S, hcard, q, hq, r, hr, hagree⟩

/-- The unsafe common agreement set in the mixed chart transports to a joint explanation of the
original rows on exactly the same coordinates. -/
theorem directionPinnedJointAgreement_implies_original_pairJointAgreesOn
    (dom : Fin N ↪ F) (u₀ u₁ r : Fin N → F)
    {a b c d : F} (hdet : a * d - b * c ≠ 0)
    (hr : r ∈ predecessorCode dom)
    (hpinned : DirectionPinnedJointAgreement dom
      (a • u₀ + b • u₁) (c • u₀ + d • u₁) r) :
    ∃ S : Finset (Fin N), predecessorThreshold ≤ S.card ∧
      pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) S u₀ u₁ := by
  obtain ⟨S, hcard, hmixed⟩ :=
    directionPinnedJointAgreement_implies_pairJointAgreesOn dom
      (a • u₀ + b • u₁) (c • u₀ + d • u₁) r hr hpinned
  exact ⟨S, hcard,
    (pairJointAgreesOn_row_mix_iff (predecessorCode dom) hdet S u₀ u₁).mp hmixed⟩

/-! ## The projective extreme-zero dichotomy -/

/-- Every invertible chart of an over-budget stack admits a structured direction translate which
either remains outside the extreme-support endpoint or is zero-direction-unsafe. -/
theorem support_gt_twoTierCap_or_zeroDirectionUnsafe_of_N_lt_badCount_rowMix
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hover : N < badCount (predecessorCode dom) predecessorDelta u₀ u₁)
    {a b c d : F} (hdet : a * d - b * c ≠ 0) :
    ∃ r ∈ predecessorCode dom,
      (directionSupportSet ((c • u₀ + d • u₁) - r)).card ≤
          maxStructuredSupport ∧
        (twoTierSupportCap <
            (directionSupportSet ((c • u₀ + d • u₁) - r)).card ∨
          ¬ ZeroDirectionSafeLine dom k predecessorThreshold
            (a • u₀ + b • u₁) ((c • u₀ + d • u₁) - r)) := by
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra hzero
    push Not at hzero
    exact hdet (by rw [hzero.1, hzero.2]; simp)
  obtain ⟨r, hr, hstructuredSupport⟩ := projectivelyNear_exists_support_le
    dom u₀ u₁ (projectivelyNear_of_N_lt_badCount dom u₀ u₁ hover) c d hcd
  refine ⟨r, hr, hstructuredSupport, ?_⟩
  by_cases hlarge : twoTierSupportCap <
      (directionSupportSet ((c • u₀ + d • u₁) - r)).card
  · exact Or.inl hlarge
  · refine Or.inr ?_
    intro hsafe
    have hlt := badCount_lt_N_of_rowMix_direction_translate_safe
      dom u₀ u₁ r hdet hr hsafe (Nat.le_of_not_gt hlarge)
    omega

/-- Strong witness form of the same dichotomy.  In the unsafe branch the same threshold-size set
both pins the chosen mixed direction codeword and jointly explains the original stack. -/
theorem support_gt_twoTierCap_or_transported_jointAgreement_of_N_lt_badCount_rowMix
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hover : N < badCount (predecessorCode dom) predecessorDelta u₀ u₁)
    {a b c d : F} (hdet : a * d - b * c ≠ 0) :
    ∃ r ∈ predecessorCode dom,
      (directionSupportSet ((c • u₀ + d • u₁) - r)).card ≤
          maxStructuredSupport ∧
        (twoTierSupportCap <
            (directionSupportSet ((c • u₀ + d • u₁) - r)).card ∨
          (DirectionPinnedJointAgreement dom
              (a • u₀ + b • u₁) (c • u₀ + d • u₁) r ∧
            ∃ S : Finset (Fin N), predecessorThreshold ≤ S.card ∧
              pairJointAgreesOn (predecessorCode dom : Set (Fin N → F)) S u₀ u₁)) := by
  obtain ⟨r, hr, hsupport, hlarge | hunsafe⟩ :=
    support_gt_twoTierCap_or_zeroDirectionUnsafe_of_N_lt_badCount_rowMix
      dom u₀ u₁ hover hdet
  · exact ⟨r, hr, hsupport, Or.inl hlarge⟩
  · have hpinned :=
      (not_zeroDirectionSafeLine_iff_directionPinnedJointAgreement dom
        (a • u₀ + b • u₁) (c • u₀ + d • u₁) r).mp hunsafe
    exact ⟨r, hr, hsupport, Or.inr ⟨hpinned,
      directionPinnedJointAgreement_implies_original_pairJointAgreesOn
        dom u₀ u₁ r hdet hr hpinned⟩⟩

end ArkLib.ProximityGap.Frontier.P1RateQuarterProjectiveExtremeZeroSplit

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterProjectiveExtremeZeroSplit
#print axioms predecessor_mcaEvent_filter_card_le_twoTierClosedBudget
#print axioms badCount_direction_sub_codeword
#print axioms badCount_lt_N_of_rowMix_direction_translate_safe
#print axioms not_zeroDirectionSafeLine_iff_directionPinnedJointAgreement
#print axioms support_gt_twoTierCap_or_zeroDirectionUnsafe_of_N_lt_badCount_rowMix
#print axioms support_gt_twoTierCap_or_transported_jointAgreement_of_N_lt_badCount_rowMix
