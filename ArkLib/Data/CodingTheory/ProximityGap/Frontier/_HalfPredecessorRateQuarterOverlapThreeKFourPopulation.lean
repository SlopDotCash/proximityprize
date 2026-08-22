/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeKFour
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterEqualSlopeHighCores

/-!
# Rate-quarter overlap-three population at `k = 4`

The common-cubic reconciliation makes compatible pairs of saturated
three-root blocks into a matching: for a fixed block in one five-coordinate
petal, at most one block in the other petal is compatible.  The proof uses
the forced intersection of two three-subsets of a five-set and evaluates an
eliminated locator identity at that shared root.

Under the explicit residual hypothesis that every relevant secant core has
size at most eight, the first root block is injective on points off both
reference lines.  This gives the exact population bound `offBoth <= 10`.
The final theorem combines it with the existing three-point per-line cap to
close the equal-slope overlap-three cell at `|G| <= 16`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeCommonFactor
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFour
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeHighCores

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourPopulation

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

theorem eval_domainRootProduct_eq_zero_iff_mem
    (dom : I ↪ F) (S : Finset I) (i : I) :
    (domainRootProduct dom S).eval (dom i) = 0 ↔ i ∈ S := by
  rw [domainRootProduct, eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, hzero⟩
    simp only [eval_sub, eval_X, eval_C] at hzero
    have hij : i = j := dom.injective (sub_eq_zero.mp hzero)
    exact hij ▸ hj
  · intro hi
    exact ⟨i, hi, by simp⟩

def CubicLocatorCompatible (dom : I ↪ F)
    (C0 S T : Finset I) : Prop :=
  ∃ a b c : F, a ≠ 0 ∧ b ≠ 0 ∧
    Polynomial.C a * domainRootProduct dom S -
      Polynomial.C b * domainRootProduct dom T =
        Polynomial.C c * domainRootProduct dom C0

theorem cubicLocatorCompatible_right_unique
    (dom : I ↪ F) (C0 R S T T' : Finset I)
    (hdisj : Disjoint C0 R)
    (hRcard : R.card = 5)
    (hTsub : T ⊆ R) (hTcard : T.card = 3)
    (hT'sub : T' ⊆ R) (hT'card : T'.card = 3)
    (hcompat : CubicLocatorCompatible dom C0 S T)
    (hcompat' : CubicLocatorCompatible dom C0 S T') :
    T = T' := by
  obtain ⟨a, b, c, ha, hb, hrel⟩ := hcompat
  obtain ⟨a', b', c', ha', hb', hrel'⟩ := hcompat'
  have hinterPos : 0 < (T ∩ T').card := by
    have hunionSub : T ∪ T' ⊆ R := Finset.union_subset hTsub hT'sub
    have hunionCard : (T ∪ T').card ≤ R.card := Finset.card_le_card hunionSub
    have hsum := Finset.card_union_add_card_inter T T'
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hinterPos
  have hiT : i ∈ T := (Finset.mem_inter.mp hi).1
  have hiT' : i ∈ T' := (Finset.mem_inter.mp hi).2
  have hiR : i ∈ R := hTsub hiT
  have hiC : i ∉ C0 := by
    intro hiC
    exact Finset.disjoint_left.mp hdisj hiC hiR
  have hPC : (domainRootProduct dom C0).eval (dom i) ≠ 0 := by
    rw [ne_eq, eval_domainRootProduct_eq_zero_iff_mem]
    exact hiC
  have hPT : (domainRootProduct dom T).eval (dom i) = 0 :=
    (eval_domainRootProduct_eq_zero_iff_mem dom T i).mpr hiT
  have hPT' : (domainRootProduct dom T').eval (dom i) = 0 :=
    (eval_domainRootProduct_eq_zero_iff_mem dom T' i).mpr hiT'
  have heval := congrArg (fun p : F[X] => p.eval (dom i)) hrel
  have heval' := congrArg (fun p : F[X] => p.eval (dom i)) hrel'
  simp only [eval_sub, eval_mul, eval_C, hPT, hPT', mul_zero, sub_zero] at heval heval'
  have hcoeff : a' * c = a * c' := by
    apply mul_right_cancel₀ hPC
    calc
      (a' * c) * (domainRootProduct dom C0).eval (dom i) =
          a' * (a * (domainRootProduct dom S).eval (dom i)) := by
        rw [heval]
        ring
      _ = a * (a' * (domainRootProduct dom S).eval (dom i)) := by ring
      _ = (a * c') * (domainRootProduct dom C0).eval (dom i) := by
        rw [heval']
        ring
  have hbexpr : C b * domainRootProduct dom T =
      C a * domainRootProduct dom S - C c * domainRootProduct dom C0 := by
    linear_combination - hrel
  have hb'expr : C b' * domainRootProduct dom T' =
      C a' * domainRootProduct dom S - C c' * domainRootProduct dom C0 := by
    linear_combination - hrel'
  have hcoeffPoly : C a' * C c = C a * C c' := by
    rw [← C_mul, ← C_mul, hcoeff]
  have hlocators :
      C (a' * b) * domainRootProduct dom T =
        C (a * b') * domainRootProduct dom T' := by
    calc
      C (a' * b) * domainRootProduct dom T =
          C a' * (C b * domainRootProduct dom T) := by
        rw [C_mul]
        ring
      _ = C a' *
          (C a * domainRootProduct dom S - C c * domainRootProduct dom C0) := by
        rw [hbexpr]
      _ = C a * C a' * domainRootProduct dom S -
          (C a' * C c) * domainRootProduct dom C0 := by ring
      _ = C a * C a' * domainRootProduct dom S -
          (C a * C c') * domainRootProduct dom C0 := by rw [hcoeffPoly]
      _ = C a *
          (C a' * domainRootProduct dom S - C c' * domainRootProduct dom C0) := by
        ring
      _ = C a * (C b' * domainRootProduct dom T') := by
        rw [hb'expr]
      _ = C (a * b') * domainRootProduct dom T' := by
        rw [C_mul]
        ring
  have hscalars : a' * b = a * b' := by
    have hlead := congrArg Polynomial.leadingCoeff hlocators
    simpa only [leadingCoeff_mul, leadingCoeff_C,
      (domainRootProduct_monic dom T).leadingCoeff,
      (domainRootProduct_monic dom T').leadingCoeff, mul_one] using hlead
  have hleft0 : C (a' * b) ≠ (0 : F[X]) := by
    rw [C_ne_zero]
    exact mul_ne_zero ha' hb
  have hpoly : domainRootProduct dom T = domainRootProduct dom T' := by
    apply mul_left_cancel₀ hleft0
    rw [hlocators, hscalars]
  ext j
  rw [← eval_domainRootProduct_eq_zero_iff_mem dom T j,
    ← eval_domainRootProduct_eq_zero_iff_mem dom T' j, hpoly]

noncomputable def offBothPoints
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line1 line2 : LineParameter F) : Finset F :=
  family.G.filter fun gamma =>
    family.q gamma ≠ line1.1 + C gamma * line1.2 ∧
      family.q gamma ≠ line2.1 + C gamma * line2.2

def firstRootBlockAt
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line1 : LineParameter F) (gamma : F) : Finset I :=
  overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1

def secondRootBlockAt
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line2 : LineParameter F) (gamma : F) : Finset I :=
  overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2

structure KFourOffPointData
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line1 line2 : LineParameter F) (gamma : F) : Prop where
  gamma_mem : gamma ∈ family.G
  agreement_card :
    (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card = 9
  first_card : (firstRootBlockAt family line1 gamma).card = 3
  second_card : (secondRootBlockAt family line2 gamma).card = 3
  first_subset : firstRootBlockAt family line1 gamma ⊆
    jointCore dom (u 0) (u 1) line1.1 line1.2 \
      commonCoreBlock dom (u 0) (u 1) line1 line2
  second_subset : secondRootBlockAt family line2 gamma ⊆
    jointCore dom (u 0) (u 1) line2.1 line2.2 \
      commonCoreBlock dom (u 0) (u 1) line1 line2
  compatible : CubicLocatorCompatible dom
    (commonCoreBlock dom (u 0) (u 1) line1 line2)
    (firstRootBlockAt family line1 gamma)
    (secondRootBlockAt family line2 gamma)
  agreement_partition :
    fullAgreement dom (u 0) (u 1) gamma (family.q gamma) =
      ((firstRootBlockAt family line1 gamma ∪
        secondRootBlockAt family line2 gamma) ∪
          (Finset.univ \
            (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
              jointCore dom (u 0) (u 1) line2.1 line2.2)))

theorem kfourOffPointData
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    {gamma : F} (hgamma : gamma ∈ offBothPoints family line1 line2) :
    KFourOffPointData family line1 line2 gamma := by
  have hgamma' := Finset.mem_filter.mp hgamma
  have hgammaG : gamma ∈ family.G := hgamma'.1
  have hoff1 := hgamma'.2.1
  have hoff2 := hgamma'.2.2
  have hinter' :
      (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 3 := by
    simpa only [commonCoreBlock] using hinter
  have hrigid := fullAgreement_overlap_three_rigidity
    family (by norm_num) (h := 8) (by simpa using hn) rfl
      (by simpa using hthreshold) line1 line2 hline1 hline2
      hcore1 hcore2 hinter' hgammaG hoff1 hoff2
  have hfirstCard : (firstRootBlockAt family line1 gamma).card = 3 := by
    simpa only [firstRootBlockAt, overlapRootBlock] using hrigid.first_root_cap
  have hsecondCard : (secondRootBlockAt family line2 gamma).card = 3 := by
    simpa only [secondRootBlockAt, overlapRootBlock] using hrigid.second_root_cap
  have hfirstSub : firstRootBlockAt family line1 gamma ⊆
      jointCore dom (u 0) (u 1) line1.1 line1.2 \
        commonCoreBlock dom (u 0) (u 1) line1 line2 := by
    intro i hi
    have hi' : i ∈
        fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          jointCore dom (u 0) (u 1) line1.1 line1.2 := by
      simpa only [firstRootBlockAt, overlapRootBlock] using hi
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hi').2, ?_⟩
    intro hiCommon
    have hbad : i ∈
        fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
            jointCore dom (u 0) (u 1) line2.1 line2.2) :=
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi').1,
        (by simpa only [commonCoreBlock] using hiCommon)⟩
    rw [hrigid.no_common_core_agreement] at hbad
    simpa using hbad
  have hsecondSub : secondRootBlockAt family line2 gamma ⊆
      jointCore dom (u 0) (u 1) line2.1 line2.2 \
        commonCoreBlock dom (u 0) (u 1) line1 line2 := by
    intro i hi
    have hi' : i ∈
        fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          jointCore dom (u 0) (u 1) line2.1 line2.2 := by
      simpa only [secondRootBlockAt, overlapRootBlock] using hi
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hi').2, ?_⟩
    intro hiCommon
    have hbad : i ∈
        fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
            jointCore dom (u 0) (u 1) line2.1 line2.2) :=
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi').1,
        (by simpa only [commonCoreBlock] using hiCommon)⟩
    rw [hrigid.no_common_core_agreement] at hbad
    simpa using hbad
  obtain ⟨c1, c2, alpha, rho, hc1, hc2, _hcoeff, _hdegree,
      _hfactorA, _hfactorR, _hproportional, hreconcile, _hunique⟩ :=
    overlap_three_kfour_constant_quotient_reconciliation
      family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
        hinter hgammaG hoff1 hoff2
  have hcompat : CubicLocatorCompatible dom
      (commonCoreBlock dom (u 0) (u 1) line1 line2)
      (firstRootBlockAt family line1 gamma)
      (secondRootBlockAt family line2 gamma) := by
    exact ⟨c1, c2, alpha + gamma * rho, hc1, hc2, by
      simpa only [firstRootBlockAt, secondRootBlockAt] using hreconcile⟩
  refine
    { gamma_mem := hgammaG
      agreement_card := ?_
      first_card := hfirstCard
      second_card := hsecondCard
      first_subset := hfirstSub
      second_subset := hsecondSub
      compatible := hcompat
      agreement_partition := ?_ }
  · simpa using hrigid.agreement_card
  · simpa only [firstRootBlockAt, secondRootBlockAt, overlapRootBlock,
      commonCoreBlock] using hrigid.agreement_partition

theorem second_petal_card_eq_five
    {dom : I ↪ F} (u0 u1 : I → F)
    (line1 line2 : LineParameter F)
    (hcore2 : (jointCore dom u0 u1 line2.1 line2.2).card = 8)
    (hinter : (commonCoreBlock dom u0 u1 line1 line2).card = 3) :
    (jointCore dom u0 u1 line2.1 line2.2 \
      commonCoreBlock dom u0 u1 line1 line2).card = 5 := by
  have hsub : commonCoreBlock dom u0 u1 line1 line2 ⊆
      jointCore dom u0 u1 line2.1 line2.2 := by
    exact Finset.inter_subset_right
  rw [Finset.card_sdiff_of_subset hsub, hcore2, hinter]

theorem first_petal_card_eq_five
    {dom : I ↪ F} (u0 u1 : I → F)
    (line1 line2 : LineParameter F)
    (hcore1 : (jointCore dom u0 u1 line1.1 line1.2).card = 8)
    (hinter : (commonCoreBlock dom u0 u1 line1 line2).card = 3) :
    (jointCore dom u0 u1 line1.1 line1.2 \
      commonCoreBlock dom u0 u1 line1 line2).card = 5 := by
  have hsub : commonCoreBlock dom u0 u1 line1 line2 ⊆
      jointCore dom u0 u1 line1.1 line1.2 := by
    exact Finset.inter_subset_left
  rw [Finset.card_sdiff_of_subset hsub, hcore1, hinter]

theorem offBothPoints_card_le_ten_of_relevant_core_cap
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    (hcoreCap : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8) :
    (offBothPoints family line1 line2).card ≤ 10 := by
  let C0 := commonCoreBlock dom (u 0) (u 1) line1 line2
  let R := jointCore dom (u 0) (u 1) line2.1 line2.2 \ C0
  let L := jointCore dom (u 0) (u 1) line1.1 line1.2 \ C0
  have hRcard : R.card = 5 := by
    simpa only [R, C0] using
      second_petal_card_eq_five (dom := dom) (u 0) (u 1)
        line1 line2 hcore2 hinter
  have hLcard : L.card = 5 := by
    simpa only [L, C0] using
      first_petal_card_eq_five (dom := dom) (u 0) (u 1)
        line1 line2 hcore1 hinter
  have hdisj : Disjoint C0 R := by
    rw [Finset.disjoint_left]
    intro i hiC hiR
    exact (Finset.mem_sdiff.mp hiR).2 hiC
  have hmaps : Set.MapsTo
      (firstRootBlockAt family line1)
      (offBothPoints family line1 line2 : Set F)
      (L.powersetCard 3 : Set (Finset I)) := by
    intro gamma hgamma
    have hdata := kfourOffPointData family hn hthreshold line1 line2
      hline1 hline2 hcore1 hcore2 hinter (by simpa using hgamma)
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨by simpa only [L, C0] using hdata.first_subset, hdata.first_card⟩
  have hinj : Set.InjOn
      (firstRootBlockAt family line1)
      (offBothPoints family line1 line2 : Set F) := by
    intro gamma hgamma beta hbeta hfirstEq
    have hgammaData := kfourOffPointData family hn hthreshold line1 line2
      hline1 hline2 hcore1 hcore2 hinter (by simpa using hgamma)
    have hbetaData := kfourOffPointData family hn hthreshold line1 line2
      hline1 hline2 hcore1 hcore2 hinter (by simpa using hbeta)
    have hsecondEq : secondRootBlockAt family line2 gamma =
        secondRootBlockAt family line2 beta := by
      apply cubicLocatorCompatible_right_unique
        dom C0 R (firstRootBlockAt family line1 gamma)
          (secondRootBlockAt family line2 gamma)
          (secondRootBlockAt family line2 beta)
          hdisj hRcard
      · simpa only [R, C0] using hgammaData.second_subset
      · exact hgammaData.second_card
      · simpa only [R, C0] using hbetaData.second_subset
      · exact hbetaData.second_card
      · exact hgammaData.compatible
      · simpa only [hfirstEq] using hbetaData.compatible
    have hagreementEq :
        fullAgreement dom (u 0) (u 1) gamma (family.q gamma) =
          fullAgreement dom (u 0) (u 1) beta (family.q beta) := by
      calc
        fullAgreement dom (u 0) (u 1) gamma (family.q gamma) =
            ((firstRootBlockAt family line1 gamma ∪
              secondRootBlockAt family line2 gamma) ∪
                (Finset.univ \
                  (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
                    jointCore dom (u 0) (u 1) line2.1 line2.2))) :=
          hgammaData.agreement_partition
        _ = ((firstRootBlockAt family line1 beta ∪
              secondRootBlockAt family line2 beta) ∪
                (Finset.univ \
                  (jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
                    jointCore dom (u 0) (u 1) line2.1 line2.2))) := by
          rw [hfirstEq, hsecondEq]
        _ = fullAgreement dom (u 0) (u 1) beta (family.q beta) :=
          hbetaData.agreement_partition.symm
    by_contra hne
    have hgammaNeBeta : gamma ≠ beta := hne
    let sec := secantParameter family gamma beta
    have hsec : sec ∈ lineParameters family :=
      secantParameter_mem_lineParameters family
        hgammaData.gamma_mem hbetaData.gamma_mem hgammaNeBeta
    have hgammaOn := first_point_mem_pointsOn_secant
      family (beta := beta) hgammaData.gamma_mem
    have hbetaOn := second_point_mem_pointsOn_secant
      family (gamma := gamma) hbetaData.gamma_mem hgammaNeBeta
    have hgammaEq := (mem_pointsOn_iff family sec gamma).mp hgammaOn |>.2
    have hbetaEq := (mem_pointsOn_iff family sec beta).mp hbetaOn |>.2
    have hintersection :
        fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
            fullAgreement dom (u 0) (u 1) beta (family.q beta) =
          jointCore dom (u 0) (u 1) sec.1 sec.2 := by
      simpa only [hgammaEq, hbetaEq] using
        (fullAgreement_inter_eq_jointCore
          dom (u 0) (u 1) sec.1 sec.2 hgammaNeBeta)
    have hcoreNine :
        (jointCore dom (u 0) (u 1) sec.1 sec.2).card = 9 := by
      rw [← hintersection, hagreementEq, Finset.inter_self]
      exact hbetaData.agreement_card
    have hle := hcoreCap sec hsec
    omega
  have hcard := Finset.card_le_card_of_injOn
    (firstRootBlockAt family line1) hmaps hinj
  rw [Finset.card_powersetCard, hLcard] at hcard
  norm_num at hcard ⊢
  exact hcard

/-- **Equal-slope `k = 4` overlap-three closure.**  The two reference lines
contain at most three selected points each, while the cubic-locator matching
bound leaves at most ten points off both lines. -/
theorem card_le_sixteen_of_equal_slope_overlap_three_core_cap
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = 8)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = 8)
    (hinter :
      (commonCoreBlock dom (u 0) (u 1) line1 line2).card = 3)
    (hslope : line2.2 = line1.2)
    (hcoreCap : ∀ line ∈ lineParameters family,
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 8) :
    family.G.card ≤ 16 := by
  have hlineNe : line1 ≠ line2 := by
    intro heq
    subst line2
    simp only [commonCoreBlock, Finset.inter_self] at hinter
    omega
  have hcap1 : (pointsOn family line1).card ≤ 3 := by
    have hcap := pointsOn_card_le_pred_of_relevant_halfCore_in_equalSlope_cluster
      family (k := 4) (h := 8) (by norm_num) (by simpa using hn)
        (by norm_num) line1 line2 line1 hline1 hline2 hline1
        hlineNe hslope (by omega) (by omega) (by omega)
    simpa using hcap
  have hcap2 : (pointsOn family line2).card ≤ 3 := by
    have hcap := pointsOn_card_le_pred_of_relevant_halfCore_in_equalSlope_cluster
      family (k := 4) (h := 8) (by norm_num) (by simpa using hn)
        (by norm_num) line1 line2 line2 hline1 hline2 hline2
        hlineNe hslope (by omega) (by omega) (by omega)
    simpa using hcap
  have hoff : (offBothPoints family line1 line2).card ≤ 10 :=
    offBothPoints_card_le_ten_of_relevant_core_cap
      family hn hthreshold line1 line2 hline1 hline2 hcore1 hcore2
        hinter hcoreCap
  have hcover : family.G ⊆
      (pointsOn family line1 ∪ pointsOn family line2) ∪
        offBothPoints family line1 line2 := by
    intro gamma hgamma
    by_cases hfirst :
        family.q gamma = line1.1 + C gamma * line1.2
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        ((mem_pointsOn_iff family line1 gamma).mpr ⟨hgamma, hfirst⟩))
    by_cases hsecond :
        family.q gamma = line2.1 + C gamma * line2.2
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        ((mem_pointsOn_iff family line2 gamma).mpr ⟨hgamma, hsecond⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hgamma, hfirst, hsecond⟩)
  have hcoverCard := Finset.card_le_card hcover
  have hlines := Finset.card_union_le
    (pointsOn family line1) (pointsOn family line2)
  have hall := Finset.card_union_le
    (pointsOn family line1 ∪ pointsOn family line2)
    (offBothPoints family line1 line2)
  omega

#print axioms cubicLocatorCompatible_right_unique
#print axioms offBothPoints_card_le_ten_of_relevant_core_cap
#print axioms card_le_sixteen_of_equal_slope_overlap_three_core_cap

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFourPopulation
