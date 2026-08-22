/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ReedSolomonJohnson
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R2B_LargeZeroWitnessSplit
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterPredecessorGenericSplit

/-!
# Extreme-zero Johnson closure at the P1 rate-quarter predecessor

After translating a structured direction by a nearby Reed--Solomon codeword, its agreement set
becomes the zero set of the translated direction.  The existing large-zero split controls a safe
line by summing, over appearing codewords, the number of scalars supported outside that zero set.

This file closes the extreme end of that branch without a binomial coordinate-fiber census.  If
the moving support has size at most `s`, every appearing codeword agrees with the offset on at
least `a - s` coordinates.  Above the ordinary Johnson line there are few such codewords, while
zero-direction safety bounds each codeword's scalar fiber by the moving support size.  Thus

`#lineBadScalars <= (n^2 / ((a-s)^2 - n*(k-1))) * s`.

At the P1 predecessor, the one-tier specialization with `s = 28,000,000` gives a Johnson list cap
of `37`, hence `37 * 28,000,000 = 1,036,000,000 < 2^30`.  A sharper two-tier split at agreement
deficiency `2,072,000` raises the support endpoint to `55,920,000`: the high-agreement list has at
most `18` codewords, the whole tail has at most `264,793`, and the weighted scalar cap is
`1,013,444,618 < 2^30`.  Equivalently, the zero-safe branch is closed whenever the translated
direction has at least `1,017,821,824` zero coordinates.  This does not close the much wider
structured band; it removes its extreme-zero endpoint with no new residual.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 250000

open Finset Polynomial
open scoped NNReal

namespace ProximityGap.ExtremeZeroJohnsonBand

open ProximityGap SpikeFloor Ownership LargeZeroWitnessSplit
open ArkLib.CodingTheory.JohnsonSimplex
open ArkLib.CodingTheory.ReedSolomonJohnson

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The two Reed--Solomon submodule presentations used by the line-list and canonical-code APIs
have the same carrier. -/
theorem mem_rsCode_iff_mem_reedSolomonCode
    (dom : Fin n ↪ F) (k : ℕ) (w : Fin n → F) :
    w ∈ (rsCode dom k : Submodule F (Fin n → F)) ↔
      w ∈ ReedSolomon.code dom k := by
  rw [ReedSolomon.mem_code_iff_exists_polynomial]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, by funext i; rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, by funext i; rfl⟩

open Classical in
/-- Axiom-clean natural-number Johnson divisor bound for an arbitrary finite family of `rsCode`
codewords.  This is the local clean replacement for the legacy convenience path through
`JohnsonSplitSupply`. -/
theorem rsCodeFinset_card_le_johnson
    (dom : Fin n ↪ F) {k h : ℕ} (hk : 1 ≤ k) (u₀ : Fin n → F)
    (L : Finset (Fin n → F))
    (hcode : ∀ c ∈ L, c ∈ (rsCode dom k : Submodule F (Fin n → F)))
    (hagree : ∀ c ∈ L, h ≤ (agreeSet c u₀).card)
    (hgap : n * (k - 1) < h ^ 2) :
    L.card ≤ n ^ 2 / (h ^ 2 - n * (k - 1)) := by
  have hpoly : ∀ c ∈ L,
      ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (dom i) := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := hcode c hc
    refine ⟨p, ?_, rfl⟩
    by_cases hp0 : p = 0
    · rw [hp0, Polynomial.natDegree_zero]
      exact hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
  have hclose : ∀ c ∈ L,
      h ≤ ArkLib.CodingTheory.JohnsonSimplex.agree c u₀ := by
    intro c hc
    simpa [ArkLib.CodingTheory.JohnsonSimplex.agree, agreeSet] using hagree c hc
  have hreal := reedSolomon_johnson_list_bound dom k u₀ L h hpoly hclose
  have hden :
      ((h : ℝ) ^ 2 - (n : ℝ) * ((k - 1 : ℕ) : ℝ)) =
        ((h ^ 2 - n * (k - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hgap)]
    push_cast
    ring
  rw [Fintype.card_fin, hden] at hreal
  have hnat : L.card * (h ^ 2 - n * (k - 1)) ≤ n ^ 2 := by
    exact_mod_cast hreal
  exact (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hgap)).2 hnat

open Classical in
/-- Every appearing codeword belongs to one ordinary Johnson list around the offset.  The threshold
`h` only has to fit below the agreement forced onto the zero coordinates by the support bound. -/
theorem lineAppearingCodewords_card_le_johnson_of_support
    (dom : Fin n ↪ F) {k a h : ℕ} (hk : 1 ≤ k) (u₀ u₁ : Fin n → F)
    (hfit : h + (directionSupportSet u₁).card ≤ a)
    (hgap : n * (k - 1) < h ^ 2) :
    (lineAppearingCodewords dom k a u₀ u₁).card
      ≤ n ^ 2 / (h ^ 2 - n * (k - 1)) := by
  let L : Finset (Fin n → F) :=
    (Finset.univ : Finset (Fin n → F)).filter
      (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        h ≤ (agreeSet c u₀).card)
  have hsub : lineAppearingCodewords dom k a u₀ u₁ ⊆ L := by
    intro c hc
    have hforced :=
      sub_support_le_zeroAgreement_card_of_mem_lineAppearingCodewords
        dom k a u₀ u₁ hc
    have hcode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
      rw [lineAppearingCodewords, Finset.mem_filter] at hc
      exact hc.2.1
    have hzeroSub : directionZeroAgreementSet c u₀ u₁ ⊆ agreeSet c u₀ := by
      intro i hi
      rw [directionZeroAgreementSet, Finset.mem_filter] at hi
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hi.2⟩
    have hhzero : h ≤ (directionZeroAgreementSet c u₀ u₁).card := by
      omega
    change c ∈ (Finset.univ : Finset (Fin n → F)).filter
      (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        h ≤ (agreeSet c u₀).card)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hcode,
      hhzero.trans (Finset.card_le_card hzeroSub)⟩
  calc
    (lineAppearingCodewords dom k a u₀ u₁).card ≤ L.card :=
      Finset.card_le_card hsub
    _ ≤ n ^ 2 / (h ^ 2 - n * (k - 1)) := by
      exact rsCodeFinset_card_le_johnson dom hk u₀ L
        (fun c hc => (Finset.mem_filter.mp hc).2.1)
        (fun c hc => (Finset.mem_filter.mp hc).2.2) hgap

open Classical in
/-- The appearing codewords with at least `h` zero-coordinate agreements form an ordinary Johnson
list around the offset word. -/
theorem highZeroAgreementLineAppearing_card_le_johnson
    (dom : Fin n ↪ F) {k a h : ℕ} (hk : 1 ≤ k) (u₀ u₁ : Fin n → F)
    (hgap : n * (k - 1) < h ^ 2) :
    ((lineAppearingCodewords dom k a u₀ u₁).filter
      (fun c => h ≤ (directionZeroAgreementSet c u₀ u₁).card)).card
      ≤ n ^ 2 / (h ^ 2 - n * (k - 1)) := by
  let H := (lineAppearingCodewords dom k a u₀ u₁).filter
    (fun c => h ≤ (directionZeroAgreementSet c u₀ u₁).card)
  apply rsCodeFinset_card_le_johnson dom hk u₀ H
  · intro c hc
    have hcApp := (Finset.mem_filter.mp hc).1
    rw [lineAppearingCodewords, Finset.mem_filter] at hcApp
    exact hcApp.2.1
  · intro c hc
    have hzero := (Finset.mem_filter.mp hc).2
    refine hzero.trans (Finset.card_le_card ?_)
    intro i hi
    rw [directionZeroAgreementSet, Finset.mem_filter] at hi
    rw [agreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hi.2⟩
  · exact hgap

open Classical in
/-- On a zero-safe line, each appearing codeword contributes at most the whole moving support to
the punctured zero-stratified weight. -/
theorem puncturedZeroStratifiedLineWeight_le_lineList_mul_support
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    puncturedZeroStratifiedLineWeight dom k a u₀ u₁ ≤
      (lineAppearingCodewords dom k a u₀ u₁).card *
        (directionSupportSet u₁).card := by
  rw [puncturedZeroStratifiedLineWeight]
  calc
    ∑ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        (directionSupportSet u₁).card /
          (a - (directionZeroAgreementSet c u₀ u₁).card)
      ≤ ∑ _c ∈ lineAppearingCodewords dom k a u₀ u₁,
          (directionSupportSet u₁).card := by
        exact Finset.sum_le_sum fun _c _hc => Nat.div_le_self _ _
    _ = (lineAppearingCodewords dom k a u₀ u₁).card *
          (directionSupportSet u₁).card := by
        rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- Two-tier Johnson bound for the punctured line weight.  Codewords with at least `hHigh`
zero-coordinate agreements pay the tight high-list cap.  Every remaining codeword has denominator
at least `d+1`, while all appearing codewords are covered by the lower `hAll` Johnson list. -/
theorem puncturedZeroStratifiedLineWeight_le_twoTierJohnson
    (dom : Fin n ↪ F) {k a hAll hHigh d s : ℕ} (hk : 1 ≤ k)
    (u₀ u₁ : Fin n → F)
    (hsupport : (directionSupportSet u₁).card ≤ s)
    (hallFit : hAll + s ≤ a)
    (hhighEq : hHigh + d = a)
    (hgapAll : n * (k - 1) < hAll ^ 2)
    (hgapHigh : n * (k - 1) < hHigh ^ 2) :
    puncturedZeroStratifiedLineWeight dom k a u₀ u₁ ≤
      (n ^ 2 / (hHigh ^ 2 - n * (k - 1))) * s +
        (n ^ 2 / (hAll ^ 2 - n * (k - 1))) * (s / (d + 1)) := by
  let appC := lineAppearingCodewords dom k a u₀ u₁
  let high : (Fin n → F) → Prop :=
    fun c => hHigh ≤ (directionZeroAgreementSet c u₀ u₁).card
  let weight : (Fin n → F) → ℕ := fun c =>
    (directionSupportSet u₁).card /
      (a - (directionZeroAgreementSet c u₀ u₁).card)
  have hhighCard : (appC.filter high).card ≤
      n ^ 2 / (hHigh ^ 2 - n * (k - 1)) := by
    simpa [appC, high] using
      highZeroAgreementLineAppearing_card_le_johnson
        dom hk u₀ u₁ hgapHigh
  have hallCard : appC.card ≤ n ^ 2 / (hAll ^ 2 - n * (k - 1)) := by
    simpa [appC] using lineAppearingCodewords_card_le_johnson_of_support
      dom hk u₀ u₁ ((Nat.add_le_add_left hsupport hAll).trans hallFit) hgapAll
  have hhighSum : (∑ c ∈ appC.filter high, weight c) ≤
      (n ^ 2 / (hHigh ^ 2 - n * (k - 1))) * s := by
    calc
      (∑ c ∈ appC.filter high, weight c)
          ≤ ∑ _c ∈ appC.filter high, s := by
            exact Finset.sum_le_sum fun _c _hc =>
              (Nat.div_le_self _ _).trans hsupport
      _ = (appC.filter high).card * s := by
            rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (n ^ 2 / (hHigh ^ 2 - n * (k - 1))) * s :=
            Nat.mul_le_mul_right s hhighCard
  have hlowSum : (∑ c ∈ appC.filter (fun c => ¬ high c), weight c) ≤
      (n ^ 2 / (hAll ^ 2 - n * (k - 1))) * (s / (d + 1)) := by
    calc
      (∑ c ∈ appC.filter (fun c => ¬ high c), weight c)
          ≤ ∑ _c ∈ appC.filter (fun c => ¬ high c), (s / (d + 1)) := by
            refine Finset.sum_le_sum fun c hc => ?_
            have hnotHigh := (Finset.mem_filter.mp hc).2
            have hden : d + 1 ≤
                a - (directionZeroAgreementSet c u₀ u₁).card := by
              simp only [high] at hnotHigh
              omega
            exact (Nat.div_le_div hsupport hden) (by omega)
      _ = (appC.filter (fun c => ¬ high c)).card * (s / (d + 1)) := by
            rw [Finset.sum_const, smul_eq_mul]
      _ ≤ appC.card * (s / (d + 1)) :=
            Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
      _ ≤ (n ^ 2 / (hAll ^ 2 - n * (k - 1))) * (s / (d + 1)) :=
            Nat.mul_le_mul_right _ hallCard
  rw [puncturedZeroStratifiedLineWeight]
  change (∑ c ∈ appC, weight c) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not appC high weight]
  exact Nat.add_le_add hhighSum hlowSum

open Classical in
/-- Generic extreme-zero closure: Johnson bounds the number of appearing codewords, and the
punctured support packing bounds the scalar contribution of each one. -/
theorem lineBadScalars_card_le_johnson_mul_support
    (dom : Fin n ↪ F) {k a h : ℕ} (hk : 1 ≤ k) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hfit : h + (directionSupportSet u₁).card ≤ a)
    (hgap : n * (k - 1) < h ^ 2) :
    (lineBadScalars dom k a u₀ u₁).card ≤
      (n ^ 2 / (h ^ 2 - n * (k - 1))) *
        (directionSupportSet u₁).card := by
  calc
    (lineBadScalars dom k a u₀ u₁).card
      ≤ puncturedZeroStratifiedLineWeight dom k a u₀ u₁ :=
        lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
          dom k a u₀ u₁ hsafe
    _ ≤ (lineAppearingCodewords dom k a u₀ u₁).card *
          (directionSupportSet u₁).card :=
        puncturedZeroStratifiedLineWeight_le_lineList_mul_support
          dom k a u₀ u₁
    _ ≤ (n ^ 2 / (h ^ 2 - n * (k - 1))) *
          (directionSupportSet u₁).card :=
        Nat.mul_le_mul_right _
          (lineAppearingCodewords_card_le_johnson_of_support
            dom hk u₀ u₁ hfit hgap)

end ProximityGap.ExtremeZeroJohnsonBand

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterExtremeZeroJohnsonBand

open _root_.ProximityGap Code
open _root_.ProximityGap.ExtremeZeroJohnsonBand
open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic
open P1RateQuarterPredecessorGenericSplit

local instance localInstance_P1RateQuarterExtremeZeroJohnsonBand_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
local instance localInstance_P1RateQuarterExtremeZeroJohnsonBand_2 : NeZero N := ⟨by norm_num [N]⟩
attribute [local instance] Classical.propDecidable

/-- A round support endpoint inside the exact arithmetic closure. -/
abbrev extremeSupportCap : ℕ := 28000000

/-- Fixed agreement threshold forced on the zero coordinates at the support endpoint. -/
abbrev extremeZeroAgreement : ℕ := predecessorThreshold - extremeSupportCap

theorem extremeZeroAgreement_eq : extremeZeroAgreement = 564794966 := by
  rw [extremeZeroAgreement, predecessorThreshold_eq]
  norm_num [extremeSupportCap]

theorem extremeJohnson_gap :
    N * (k - 1) < extremeZeroAgreement ^ 2 := by
  norm_num [N, k, extremeZeroAgreement_eq]

theorem extremeJohnson_list_cap :
    N ^ 2 / (extremeZeroAgreement ^ 2 - N * (k - 1)) = 37 := by
  norm_num [N, k, extremeZeroAgreement_eq]

theorem extremeJohnson_budget : 37 * extremeSupportCap ≤ N := by
  norm_num [extremeSupportCap, N]

/-! ## A sharper two-tier endpoint -/

/-- Support endpoint closed by the two-tier deficiency split. -/
abbrev twoTierSupportCap : ℕ := 55920000

/-- Codewords within this agreement deficiency use the tighter Johnson list. -/
abbrev twoTierDeficiencyCut : ℕ := 2072000

abbrev twoTierAllAgreement : ℕ := predecessorThreshold - twoTierSupportCap

abbrev twoTierHighAgreement : ℕ := predecessorThreshold - twoTierDeficiencyCut

abbrev twoTierZeroThreshold : ℕ := N - twoTierSupportCap

theorem twoTierAllAgreement_eq : twoTierAllAgreement = 536874966 := by
  rw [twoTierAllAgreement, predecessorThreshold_eq]
  norm_num [twoTierSupportCap]

theorem twoTierHighAgreement_eq : twoTierHighAgreement = 590722966 := by
  rw [twoTierHighAgreement, predecessorThreshold_eq]
  norm_num [twoTierDeficiencyCut]

theorem twoTierZeroThreshold_eq : twoTierZeroThreshold = 1017821824 := by
  norm_num [twoTierZeroThreshold, twoTierSupportCap, N]

theorem twoTierAll_gap : N * (k - 1) < twoTierAllAgreement ^ 2 := by
  norm_num [N, k, twoTierAllAgreement_eq]

theorem twoTierHigh_gap : N * (k - 1) < twoTierHighAgreement ^ 2 := by
  norm_num [N, k, twoTierHighAgreement_eq]

theorem twoTierAll_list_cap :
    N ^ 2 / (twoTierAllAgreement ^ 2 - N * (k - 1)) = 264793 := by
  norm_num [N, k, twoTierAllAgreement_eq]

theorem twoTierHigh_list_cap :
    N ^ 2 / (twoTierHighAgreement ^ 2 - N * (k - 1)) = 18 := by
  norm_num [N, k, twoTierHighAgreement_eq]

theorem twoTier_support_div :
    twoTierSupportCap / (twoTierDeficiencyCut + 1) = 26 := by
  norm_num [twoTierSupportCap, twoTierDeficiencyCut]

theorem twoTier_budget :
    18 * twoTierSupportCap + 264793 * 26 ≤ N := by
  norm_num [twoTierSupportCap, N]

/-- The zero-safe predecessor line is within the prize count whenever its translated direction
has at most `28,000,000` nonzero coordinates. -/
theorem predecessor_lineBadScalars_card_le_N_of_support_le
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hsafe : Ownership.ZeroDirectionSafeLine dom k predecessorThreshold u₀ u₁)
    (hsupport : (Ownership.directionSupportSet u₁).card ≤ extremeSupportCap) :
    (Ownership.lineBadScalars dom k predecessorThreshold u₀ u₁).card ≤ N := by
  have hfit : extremeZeroAgreement +
      (Ownership.directionSupportSet u₁).card ≤ predecessorThreshold := by
    have hcap : extremeSupportCap ≤ predecessorThreshold := by
      rw [predecessorThreshold_eq]
      norm_num [extremeSupportCap]
    rw [extremeZeroAgreement]
    omega
  have hbound := lineBadScalars_card_le_johnson_mul_support
    dom (k := k) (a := predecessorThreshold) (h := extremeZeroAgreement)
    (by norm_num [k]) u₀ u₁ hsafe hfit (by
      simpa only [Fintype.card_fin] using extremeJohnson_gap)
  rw [extremeJohnson_list_cap] at hbound
  exact hbound.trans (le_trans (Nat.mul_le_mul_left 37 hsupport) extremeJohnson_budget)

/-- The two-tier Johnson split closes the zero-safe branch for translated directions supported on
at most `55,920,000` coordinates. -/
theorem predecessor_lineBadScalars_card_le_N_of_support_le_twoTier
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hsafe : Ownership.ZeroDirectionSafeLine dom k predecessorThreshold u₀ u₁)
    (hsupport : (Ownership.directionSupportSet u₁).card ≤ twoTierSupportCap) :
    (Ownership.lineBadScalars dom k predecessorThreshold u₀ u₁).card ≤ N := by
  have hallFit : twoTierAllAgreement + twoTierSupportCap ≤ predecessorThreshold := by
    rw [twoTierAllAgreement_eq, predecessorThreshold_eq]
    norm_num [twoTierSupportCap]
  have hhighEq : twoTierHighAgreement + twoTierDeficiencyCut = predecessorThreshold := by
    rw [twoTierHighAgreement_eq, predecessorThreshold_eq]
    norm_num [twoTierDeficiencyCut]
  have hweight := puncturedZeroStratifiedLineWeight_le_twoTierJohnson
    dom (k := k) (a := predecessorThreshold)
      (hAll := twoTierAllAgreement) (hHigh := twoTierHighAgreement)
      (d := twoTierDeficiencyCut) (s := twoTierSupportCap)
      (by norm_num [k]) u₀ u₁ hsupport hallFit hhighEq
      (by simpa only [Fintype.card_fin] using twoTierAll_gap)
      (by simpa only [Fintype.card_fin] using twoTierHigh_gap)
  rw [twoTierHigh_list_cap, twoTierAll_list_cap, twoTier_support_div] at hweight
  exact (Ownership.lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
    dom k predecessorThreshold u₀ u₁ hsafe).trans (hweight.trans twoTier_budget)

/-- Every predecessor MCA event is a line-list bad scalar at the exact integral agreement floor. -/
theorem predecessor_mcaEvent_filter_subset_lineBadScalars
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F) :
    Finset.univ.filter (fun gamma : F =>
      mcaEvent (predecessorCode dom : Set (Fin N → F)) predecessorDelta u₀ u₁ gamma) ⊆
        Ownership.lineBadScalars dom k predecessorThreshold u₀ u₁ := by
  intro gamma hgamma
  rw [Finset.mem_filter] at hgamma
  obtain ⟨S, hScard, ⟨w, hwCode, hwAgree⟩, _hno⟩ := hgamma.2
  rw [Ownership.lineBadScalars, Finset.mem_filter]
  have hwCode' : w ∈ (SpikeFloor.rsCode dom k : Submodule F (Fin N → F)) :=
    (mem_rsCode_iff_mem_reedSolomonCode dom k w).mpr hwCode
  refine ⟨Finset.mem_univ _, w, hwCode', ?_⟩
  have hthreshold : predecessorThreshold ≤ S.card := by
    rw [Fintype.card_fin] at hScard
    rw [agreement_mass_eq_predecessorThreshold] at hScard
    exact_mod_cast hScard
  exact hthreshold.trans (Finset.card_le_card fun i hi => by
    rw [Ownership.agreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hwAgree i hi⟩)

/-- MCA-facing form of the same closure. -/
theorem predecessor_mcaEvent_filter_card_le_N_of_support_le
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hsafe : Ownership.ZeroDirectionSafeLine dom k predecessorThreshold u₀ u₁)
    (hsupport : (Ownership.directionSupportSet u₁).card ≤ extremeSupportCap) :
    (Finset.univ.filter (fun gamma : F =>
      mcaEvent (predecessorCode dom : Set (Fin N → F)) predecessorDelta
        u₀ u₁ gamma)).card ≤ N := by
  exact (Finset.card_le_card
      (predecessor_mcaEvent_filter_subset_lineBadScalars dom u₀ u₁)).trans
    (predecessor_lineBadScalars_card_le_N_of_support_le dom u₀ u₁ hsafe hsupport)

/-- MCA-facing form of the sharper two-tier closure. -/
theorem predecessor_mcaEvent_filter_card_le_N_of_support_le_twoTier
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hsafe : Ownership.ZeroDirectionSafeLine dom k predecessorThreshold u₀ u₁)
    (hsupport : (Ownership.directionSupportSet u₁).card ≤ twoTierSupportCap) :
    (Finset.univ.filter (fun gamma : F =>
      mcaEvent (predecessorCode dom : Set (Fin N → F)) predecessorDelta
        u₀ u₁ gamma)).card ≤ N :=
  (Finset.card_le_card
      (predecessor_mcaEvent_filter_subset_lineBadScalars dom u₀ u₁)).trans
    (predecessor_lineBadScalars_card_le_N_of_support_le_twoTier
      dom u₀ u₁ hsafe hsupport)

/-- Zero-count form of the two-tier closure. -/
theorem predecessor_mcaEvent_filter_card_le_N_of_zero_card_ge_twoTier
    (dom : Fin N ↪ F) (u₀ u₁ : Fin N → F)
    (hsafe : Ownership.ZeroDirectionSafeLine dom k predecessorThreshold u₀ u₁)
    (hzero : twoTierZeroThreshold ≤ (Ownership.directionZeroSet u₁).card) :
    (Finset.univ.filter (fun gamma : F =>
      mcaEvent (predecessorCode dom : Set (Fin N → F)) predecessorDelta
        u₀ u₁ gamma)).card ≤ N := by
  apply predecessor_mcaEvent_filter_card_le_N_of_support_le_twoTier dom u₀ u₁ hsafe
  rw [ProximityGap.LineListMCAWeld.directionSupportSet_card_eq]
  rw [twoTierZeroThreshold] at hzero
  have hcap : twoTierSupportCap ≤ N := by norm_num [twoTierSupportCap, N]
  omega

end ArkLib.ProximityGap.Frontier.P1RateQuarterExtremeZeroJohnsonBand

/-! ## Axiom audit -/

open ProximityGap.ExtremeZeroJohnsonBand
open ArkLib.ProximityGap.Frontier.P1RateQuarterExtremeZeroJohnsonBand
#print axioms rsCodeFinset_card_le_johnson
#print axioms lineAppearingCodewords_card_le_johnson_of_support
#print axioms puncturedZeroStratifiedLineWeight_le_twoTierJohnson
#print axioms lineBadScalars_card_le_johnson_mul_support
#print axioms predecessor_lineBadScalars_card_le_N_of_support_le
#print axioms predecessor_lineBadScalars_card_le_N_of_support_le_twoTier
#print axioms predecessor_mcaEvent_filter_card_le_N_of_support_le
#print axioms predecessor_mcaEvent_filter_card_le_N_of_support_le_twoTier
#print axioms predecessor_mcaEvent_filter_card_le_N_of_zero_card_ge_twoTier
