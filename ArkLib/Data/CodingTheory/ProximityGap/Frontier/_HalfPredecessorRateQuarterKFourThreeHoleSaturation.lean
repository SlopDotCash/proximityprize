/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourCrossTripleThreeHoleConsumer

/-!
# Rate-quarter `k = 4`: saturation of the three-hole cross-secant cell

The five-point endpoint of the three-hole population bound cannot occur.  At
that endpoint every coordinate of the five-element secant petal would be used
by exactly three survivors.  If a survivor misses the pair `{i, j}`, then the
two three-point coordinate fibers at `i` and `j` lie inside the other four
survivors and meet in at least two points.  Both fibers are collinear, so the
no-four theorem forces them to coincide.  Consequently every missed edge has
multiplicity exactly two, contradicting the odd population size five.

Thus a three-hole cell has exactly four regular outsiders off its distinguished
secant.  The source-line lower bound and the secant-line cap then also saturate:
there are exactly eight regular source outsiders and exactly four selected
points on the distinguished secant.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalPruning
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSignatures
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSevenCoreOverlapTwo
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleUniqueCoreConsumer
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCrossTripleThreeHoleConsumer

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourThreeHoleSaturation

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-! ## Equality in the petal double count -/

/-- Inside the secant petal, agreement is exactly the complement of the
regular missed edge. -/
theorem residualSecantPetalAgreement_eq_sdiff_missedEdge
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family) (theta : F) :
    residualSecantPetalAgreement family residual theta =
      secantPetal family residual.source residual.gamma residual.beta \
        regularMissedEdge family residual.source theta := by
  ext i
  simp only [residualSecantPetalAgreement, secantPetal,
    regularMissedEdge, sourceFreshAgreement, Finset.mem_inter,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  tauto

/-- Every regular survivor has a two-element missed edge. -/
theorem regularMissedEdge_card_eq_two_of_regularOff
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {theta : F}
    (htheta : theta ∈ regularOffResidualSecant family residual) :
    (regularMissedEdge family residual.source theta).card = 2 := by
  have hthetaData := htheta
  simp only [regularOffResidualSecant, Finset.mem_sdiff] at hthetaData
  exact (regular_signature_cardinalities family hn
    residual.source_core_card hthetaData.1).2

/-- If the off-secant population had size five, equality would hold in every
coordinate-fiber cap: each of the five petal coordinates would be used by
exactly three survivors. -/
theorem residualPetalCoordinateFiber_card_eq_three_of_population_five
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (hsix : 6 ≤
      (jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1
        (residualSecantLine residual).2).card)
    (hfive : (regularOffResidualSecant family residual).card = 5)
    {i : I}
    (hi : i ∈ secantPetal family residual.source residual.gamma residual.beta) :
    (residualPetalCoordinateFiber family residual i).card = 3 := by
  let O := regularOffResidualSecant family residual
  let P := secantPetal family residual.source residual.gamma residual.beta
  let A : F → Finset I := fun theta =>
    residualSecantPetalAgreement family residual theta
  let Fib : I → Finset F := fun j =>
    residualPetalCoordinateFiber family residual j
  have hPcard : P.card = 5 := by
    simpa only [P] using residualSecantPetal_card residual
  have hOcard : O.card = 5 := by simpa only [O] using hfive
  have hiP : i ∈ P := by simpa only [P] using hi
  have hAdata : ∀ theta ∈ O, A theta ⊆ P ∧ (A theta).card = 3 := by
    intro theta htheta
    have hdata := offResidualSecant_two_triple_data
      family hn residual (by simpa only [O] using htheta)
    exact ⟨by simpa only [A, P] using hdata.2.2.1,
      by simpa only [A] using hdata.2.2.2⟩
  have hFibCap : ∀ j, (Fib j).card ≤ 3 := by
    intro j
    simpa only [Fib] using
      residualPetalCoordinateFiber_card_le_three_of_six_le_secant_core
        family hn hthreshold residual hsix j
  have hswap : (∑ theta ∈ O, (A theta).card) =
      ∑ j ∈ P, (Fib j).card := by
    calc
      (∑ theta ∈ O, (A theta).card) =
          ∑ theta ∈ O, ∑ j ∈ P, if j ∈ A theta then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro theta htheta
        have heq : P.filter (fun j => j ∈ A theta) = A theta := by
          ext j
          constructor
          · intro hj
            exact (Finset.mem_filter.mp hj).2
          · intro hj
            exact Finset.mem_filter.mpr ⟨(hAdata theta htheta).1 hj, hj⟩
        rw [← Finset.card_filter, heq]
      _ = ∑ j ∈ P, ∑ theta ∈ O, if j ∈ A theta then 1 else 0 :=
        Finset.sum_comm
      _ = ∑ j ∈ P, (Fib j).card := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [show Fib j = O.filter (fun theta => j ∈ A theta) by rfl,
          Finset.card_filter]
  have hleft : (∑ theta ∈ O, (A theta).card) = O.card * 3 := by
    calc
      (∑ theta ∈ O, (A theta).card) = ∑ _theta ∈ O, 3 := by
        exact Finset.sum_congr rfl fun theta htheta => (hAdata theta htheta).2
      _ = O.card * 3 := by simp
  have htotal : (∑ j ∈ P, (Fib j).card) = 15 := by
    rw [← hswap, hleft, hOcard]
  have heraseCard : (P.erase i).card = 4 := by
    rw [Finset.card_erase_of_mem hiP, hPcard]
  have hrest : (∑ j ∈ P.erase i, (Fib j).card) ≤ 12 := by
    calc
      (∑ j ∈ P.erase i, (Fib j).card) ≤ ∑ _j ∈ P.erase i, 3 :=
        Finset.sum_le_sum fun j _hj => hFibCap j
      _ = (P.erase i).card * 3 := by simp
      _ = 12 := by rw [heraseCard]
  have hsplit := Finset.add_sum_erase P (fun j => (Fib j).card) hiP
  have htotal' :
      (∑ x ∈ P, (fun j => (Fib j).card) x) = 15 := by
    simpa only using htotal
  have hrest' :
      (∑ x ∈ P.erase i, (fun j => (Fib j).card) x) ≤ 12 := by
    simpa only using hrest
  rw [htotal'] at hsplit
  change (Fib i).card +
      (∑ x ∈ P.erase i, (fun j => (Fib j).card) x) = 15 at hsplit
  have hiCap := hFibCap i
  change (Fib i).card = 3
  omega

/-! ## Saturated fibers force paired missed edges -/

/-- A saturated three-point coordinate fiber lies on the secant through any
two of its distinct points. -/
theorem residualPetalCoordinateFiber_subset_pointsOn_secant
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {i : I} {theta0 theta1 : F}
    (htheta0 : theta0 ∈ residualPetalCoordinateFiber family residual i)
    (htheta1 : theta1 ∈ residualPetalCoordinateFiber family residual i)
    (h01 : theta0 ≠ theta1) :
    residualPetalCoordinateFiber family residual i ⊆
      pointsOn family (secantParameter family theta0 theta1) := by
  have htheta0Data := htheta0
  have htheta1Data := htheta1
  simp only [residualPetalCoordinateFiber, Finset.mem_filter] at htheta0Data htheta1Data
  intro theta htheta
  have hthetaData := htheta
  simp only [residualPetalCoordinateFiber, Finset.mem_filter] at hthetaData
  by_cases htheta0Eq : theta = theta0
  · subst theta
    exact first_point_mem_pointsOn_secant family
      (regularOffResidualSecant_subset_G family residual htheta0Data.1)
  by_cases htheta1Eq : theta = theta1
  · subst theta
    exact second_point_mem_pointsOn_secant family
      (regularOffResidualSecant_subset_G family residual htheta1Data.1) h01
  exact third_mem_pointsOn_secant_of_common_petal_coordinate
    family hn residual htheta0Data.1 htheta1Data.1 hthetaData.1
      h01 (Ne.symm htheta0Eq) htheta0Data.2 htheta1Data.2 hthetaData.2

/-- At population five, the two coordinate fibers indexed by the endpoints
of any missed edge must coincide. -/
theorem residualPetalCoordinateFibers_eq_of_missed_edge_of_population_five
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (hsix : 6 ≤
      (jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1
        (residualSecantLine residual).2).card)
    (hfive : (regularOffResidualSecant family residual).card = 5)
    {theta : F}
    (htheta : theta ∈ regularOffResidualSecant family residual)
    {i j : I}
    (hi : i ∈ regularMissedEdge family residual.source theta)
    (hj : j ∈ regularMissedEdge family residual.source theta) :
    residualPetalCoordinateFiber family residual i =
      residualPetalCoordinateFiber family residual j := by
  by_cases hij : i = j
  · subst j
    rfl
  let O := regularOffResidualSecant family residual
  let Fi := residualPetalCoordinateFiber family residual i
  let Fj := residualPetalCoordinateFiber family residual j
  have hthetaO : theta ∈ O := by simpa only [O] using htheta
  have hOcard : O.card = 5 := by simpa only [O] using hfive
  have hEsub := (offResidualSecant_signature_restrictions
    family hn residual htheta).2.1
  have hiP : i ∈ secantPetal family residual.source residual.gamma residual.beta :=
    hEsub hi
  have hjP : j ∈ secantPetal family residual.source residual.gamma residual.beta :=
    hEsub hj
  have hFiCard : Fi.card = 3 := by
    simpa only [Fi] using
      residualPetalCoordinateFiber_card_eq_three_of_population_five
        family hn hthreshold residual hsix hfive hiP
  have hFjCard : Fj.card = 3 := by
    simpa only [Fj] using
      residualPetalCoordinateFiber_card_eq_three_of_population_five
        family hn hthreshold residual hsix hfive hjP
  have hthetaNotFi : theta ∉ Fi := by
    intro hthetaFi
    have hiAgreement := (Finset.mem_filter.mp (by
      simpa only [Fi, residualPetalCoordinateFiber] using hthetaFi)).2
    rw [residualSecantPetalAgreement_eq_sdiff_missedEdge] at hiAgreement
    exact (Finset.mem_sdiff.mp hiAgreement).2 hi
  have hthetaNotFj : theta ∉ Fj := by
    intro hthetaFj
    have hjAgreement := (Finset.mem_filter.mp (by
      simpa only [Fj, residualPetalCoordinateFiber] using hthetaFj)).2
    rw [residualSecantPetalAgreement_eq_sdiff_missedEdge] at hjAgreement
    exact (Finset.mem_sdiff.mp hjAgreement).2 hj
  have hFiSub : Fi ⊆ O.erase theta := by
    intro phi hphi
    have hphiData := Finset.mem_filter.mp (by
      simpa only [Fi, O, residualPetalCoordinateFiber] using hphi)
    exact Finset.mem_erase.mpr
      ⟨fun hEq => hthetaNotFi (by simpa only [hEq] using hphi), hphiData.1⟩
  have hFjSub : Fj ⊆ O.erase theta := by
    intro phi hphi
    have hphiData := Finset.mem_filter.mp (by
      simpa only [Fj, O, residualPetalCoordinateFiber] using hphi)
    exact Finset.mem_erase.mpr
      ⟨fun hEq => hthetaNotFj (by simpa only [hEq] using hphi), hphiData.1⟩
  have heraseCard : (O.erase theta).card = 4 := by
    rw [Finset.card_erase_of_mem hthetaO, hOcard]
  have hUnionSub : Fi ∪ Fj ⊆ O.erase theta :=
    Finset.union_subset hFiSub hFjSub
  have hUnionCardUpper : (Fi ∪ Fj).card ≤ 4 := by
    rw [← heraseCard]
    exact Finset.card_le_card hUnionSub
  have hInterCard : 2 ≤ (Fi ∩ Fj).card := by
    have hbook := Finset.card_union_add_card_inter Fi Fj
    omega
  obtain ⟨phi, hphi, psi, hpsi, hphiPsi⟩ :=
    Finset.one_lt_card.mp (show 1 < (Fi ∩ Fj).card by omega)
  have hphiData := Finset.mem_inter.mp hphi
  have hpsiData := Finset.mem_inter.mp hpsi
  let line := secantParameter family phi psi
  have hFiLine : Fi ⊆ pointsOn family line := by
    simpa only [Fi, line] using
      residualPetalCoordinateFiber_subset_pointsOn_secant
        family hn residual hphiData.1 hpsiData.1 hphiPsi
  have hFjLine : Fj ⊆ pointsOn family line := by
    simpa only [Fj, line] using
      residualPetalCoordinateFiber_subset_pointsOn_secant
        family hn residual hphiData.2 hpsiData.2 hphiPsi
  have hUnionLine : Fi ∪ Fj ⊆ pointsOn family line :=
    Finset.union_subset hFiLine hFjLine
  have hUnionO : Fi ∪ Fj ⊆ O := by
    intro x hx
    exact (Finset.mem_erase.mp (hUnionSub hx)).2
  have hUnionCard : (Fi ∪ Fj).card ≤ 3 := by
    by_contra hnot
    have hfour : 3 < (Fi ∪ Fj).card := by omega
    obtain ⟨theta0, theta1, theta2, theta3,
        htheta0, htheta1, htheta2, htheta3,
        h01, h02, h03, h12, h13, h23⟩ :=
      Finset.three_lt_card_iff.mp hfour
    have htheta0O : theta0 ∈ O := hUnionO htheta0
    have htheta1O : theta1 ∈ O := hUnionO htheta1
    have htheta2O : theta2 ∈ O := hUnionO htheta2
    have htheta3O : theta3 ∈ O := hUnionO htheta3
    have htheta0Line := hUnionLine htheta0
    have htheta1Line := hUnionLine htheta1
    have hsecant : secantParameter family theta0 theta1 = line :=
      secantParameter_eq_of_mem_pointsOn
        family line htheta0Line htheta1Line h01
    have htheta2On : theta2 ∈
        pointsOn family (secantParameter family theta0 theta1) := by
      rw [hsecant]
      exact hUnionLine htheta2
    have htheta3On : theta3 ∈
        pointsOn family (secantParameter family theta0 theta1) := by
      rw [hsecant]
      exact hUnionLine htheta3
    exact not_four_offResidualSecant_collinear_of_six_le_secant_core
      family hn hthreshold residual hsix
        (by simpa only [O] using htheta0O)
        (by simpa only [O] using htheta1O)
        (by simpa only [O] using htheta2O)
        (by simpa only [O] using htheta3O)
        h01 h02 h03 h12 h13 h23 htheta2On htheta3On
  have hFiUnion : Fi = Fi ∪ Fj := by
    apply Finset.eq_of_subset_of_card_le Finset.subset_union_left
    omega
  have hFjUnion : Fj = Fi ∪ Fj := by
    apply Finset.eq_of_subset_of_card_le Finset.subset_union_right
    omega
  simpa only [Fi, Fj] using hFiUnion.trans hFjUnion.symm

/-- The regular survivors carrying the same missed edge as `theta`. -/
noncomputable def residualMissedEdgeClass
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family) (theta : F) : Finset F :=
  (regularOffResidualSecant family residual).filter fun phi =>
    regularMissedEdge family residual.source phi =
      regularMissedEdge family residual.source theta

/-- At hypothetical population five, every missed edge has multiplicity
exactly two. -/
theorem residualMissedEdgeClass_card_eq_two_of_population_five
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (hsix : 6 ≤
      (jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1
        (residualSecantLine residual).2).card)
    (hfive : (regularOffResidualSecant family residual).card = 5)
    {theta : F}
    (htheta : theta ∈ regularOffResidualSecant family residual) :
    (residualMissedEdgeClass family residual theta).card = 2 := by
  let O := regularOffResidualSecant family residual
  let E : F → Finset I := fun phi =>
    regularMissedEdge family residual.source phi
  have hthetaO : theta ∈ O := by simpa only [O] using htheta
  have hOcard : O.card = 5 := by simpa only [O] using hfive
  have hEthetaCard : (E theta).card = 2 := by
    simpa only [E] using
      regularMissedEdge_card_eq_two_of_regularOff family hn residual htheta
  obtain ⟨i, j, hij, hEtheta⟩ := Finset.card_eq_two.mp hEthetaCard
  have hiE : i ∈ E theta := by rw [hEtheta]; simp
  have hjE : j ∈ E theta := by rw [hEtheta]; simp
  have hEsub := (offResidualSecant_signature_restrictions
    family hn residual htheta).2.1
  have hiP : i ∈ secantPetal family residual.source residual.gamma residual.beta :=
    hEsub (by simpa only [E] using hiE)
  have hjP : j ∈ secantPetal family residual.source residual.gamma residual.beta :=
    hEsub (by simpa only [E] using hjE)
  let Fi := residualPetalCoordinateFiber family residual i
  let Fj := residualPetalCoordinateFiber family residual j
  have hFiCard : Fi.card = 3 := by
    simpa only [Fi] using
      residualPetalCoordinateFiber_card_eq_three_of_population_five
        family hn hthreshold residual hsix hfive hiP
  have hFibEq : Fi = Fj := by
    simpa only [Fi, Fj, E] using
      residualPetalCoordinateFibers_eq_of_missed_edge_of_population_five
        family hn hthreshold residual hsix hfive htheta hiE hjE
  have hFiSubO : Fi ⊆ O := by
    intro phi hphi
    exact (Finset.mem_filter.mp (by
      simpa only [Fi, O, residualPetalCoordinateFiber] using hphi)).1
  have hclass : residualMissedEdgeClass family residual theta = O \ Fi := by
    ext phi
    simp only [residualMissedEdgeClass, Finset.mem_filter,
      Finset.mem_sdiff]
    constructor
    · rintro ⟨hphiO, hphiEdge⟩
      refine ⟨hphiO, ?_⟩
      intro hphiFi
      have hiAgreement := (Finset.mem_filter.mp (by
        simpa only [Fi, O, residualPetalCoordinateFiber] using hphiFi)).2
      rw [residualSecantPetalAgreement_eq_sdiff_missedEdge] at hiAgreement
      have hiNotEdge := (Finset.mem_sdiff.mp hiAgreement).2
      apply hiNotEdge
      rw [hphiEdge]
      simpa only [E] using hiE
    · rintro ⟨hphiO, hphiNotFi⟩
      refine ⟨hphiO, ?_⟩
      have hphiNotFj : phi ∉ Fj := by
        simpa only [← hFibEq] using hphiNotFi
      have hphiO' : phi ∈ regularOffResidualSecant family residual := by
        simpa only [O] using hphiO
      have hEphiCard : (E phi).card = 2 := by
        simpa only [E] using
          regularMissedEdge_card_eq_two_of_regularOff family hn residual hphiO'
      have hiEphi : i ∈ E phi := by
        by_contra hiNot
        apply hphiNotFi
        simp only [Fi, residualPetalCoordinateFiber, Finset.mem_filter]
        refine ⟨hphiO', ?_⟩
        rw [residualSecantPetalAgreement_eq_sdiff_missedEdge]
        exact Finset.mem_sdiff.mpr ⟨hiP, by simpa only [E] using hiNot⟩
      have hjEphi : j ∈ E phi := by
        by_contra hjNot
        apply hphiNotFj
        simp only [Fj, residualPetalCoordinateFiber, Finset.mem_filter]
        refine ⟨hphiO', ?_⟩
        rw [residualSecantPetalAgreement_eq_sdiff_missedEdge]
        exact Finset.mem_sdiff.mpr ⟨hjP, by simpa only [E] using hjNot⟩
      have hpairSub : ({i, j} : Finset I) ⊆ E phi := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hiEphi
        · exact hjEphi
      have hpairCard : ({i, j} : Finset I).card = 2 := by simp [hij]
      have hpairEq : ({i, j} : Finset I) = E phi := by
        apply Finset.eq_of_subset_of_card_le hpairSub
        omega
      have hphiEdgeE : E phi = E theta :=
        hpairEq.symm.trans hEtheta.symm
      simpa only [E] using hphiEdgeE
  rw [hclass, Finset.card_sdiff_of_subset hFiSubO, hOcard, hFiCard]

/-! ## The five-point endpoint is impossible -/

/-- The off-secant population in a three-hole cell cannot be five. -/
theorem regularOffResidualSecant_card_ne_five_of_six_le_secant_core
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (hsix : 6 ≤
      (jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1
        (residualSecantLine residual).2).card) :
    (regularOffResidualSecant family residual).card ≠ 5 := by
  intro hfive
  let O := regularOffResidualSecant family residual
  let E : F → Finset I := fun theta =>
    regularMissedEdge family residual.source theta
  have hOcard : O.card = 5 := by simpa only [O] using hfive
  have hpartition := Finset.card_eq_sum_card_image E O
  have hfibers : ∀ e ∈ O.image E,
      (O.filter fun theta => E theta = e).card = 2 := by
    intro e he
    obtain ⟨theta, hthetaO, rfl⟩ := Finset.mem_image.mp he
    simpa only [O, E, residualMissedEdgeClass] using
      residualMissedEdgeClass_card_eq_two_of_population_five
        family hn hthreshold residual hsix hfive
          (by simpa only [O] using hthetaO)
  have heven : O.card = (O.image E).card * 2 := by
    calc
      O.card = ∑ e ∈ O.image E, (O.filter fun theta => E theta = e).card :=
        hpartition
      _ = ∑ _e ∈ O.image E, 2 := by
        exact Finset.sum_congr rfl hfibers
      _ = (O.image E).card * 2 := by simp
  omega

/-- **Sharp three-hole population.**  Exactly four regular outsiders remain
off the distinguished secant. -/
theorem regularOffResidualSecant_card_eq_four_of_six_le_secant_core
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (hsix : 6 ≤
      (jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1
        (residualSecantLine residual).2).card) :
    (regularOffResidualSecant family residual).card = 4 := by
  have hrange :=
    regularOffResidualSecant_card_four_five_of_six_le_secant_core
      family hn hthreshold residual hsix
  have hne := regularOffResidualSecant_card_ne_five_of_six_le_secant_core
    family hn hthreshold residual hsix
  omega

/-- The source and distinguished-secant counts saturate together: there are
eight regular source outsiders, four of them lie on the distinguished secant,
and that secant has exactly four selected points in total. -/
theorem threeHole_exact_regular_and_secant_counts
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (hsix : 6 ≤
      (jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1
        (residualSecantLine residual).2).card) :
    (regularOutsideLine family residual.source).card = 8 ∧
      (regularOutsideLine family residual.source ∩
        pointsOn family (residualSecantLine residual)).card = 4 ∧
      (pointsOn family (residualSecantLine residual)).card = 4 := by
  let R := regularOutsideLine family residual.source
  let L := pointsOn family (residualSecantLine residual)
  have hOff : (R \ L).card = 4 := by
    simpa only [R, L, regularOffResidualSecant] using
      regularOffResidualSecant_card_eq_four_of_six_le_secant_core
        family hn hthreshold residual hsix
  have hRlower : 8 ≤ R.card := by
    simpa only [R] using residual.eight_regular_outsiders
  have hLupper : L.card ≤ 4 := by
    simpa only [L] using
      residualSecant_pointsOn_card_le_four family hn hthreshold residual
  have hsplit := Finset.card_sdiff_add_card_inter R L
  have hinterUpper : (R ∩ L).card ≤ L.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hRcard : R.card = 8 := by omega
  have hinterCard : (R ∩ L).card = 4 := by omega
  have hLcard : L.card = 4 := by
    have hinterLower : (R ∩ L).card ≤ L.card :=
      Finset.card_le_card Finset.inter_subset_right
    omega
  exact ⟨hRcard, hinterCard, hLcard⟩

/-- Every selected point on the distinguished secant belongs to the regular
source-outsider stratum. -/
theorem residualSecant_points_subset_regularOutsideLine_of_six_le_secant_core
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (hsix : 6 ≤
      (jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1
        (residualSecantLine residual).2).card) :
    pointsOn family (residualSecantLine residual) ⊆
      regularOutsideLine family residual.source := by
  let R := regularOutsideLine family residual.source
  let L := pointsOn family (residualSecantLine residual)
  have hcounts := threeHole_exact_regular_and_secant_counts
    family hn hthreshold residual hsix
  have hinterCard : (R ∩ L).card = 4 := by
    simpa only [R, L] using hcounts.2.1
  have hLcard : L.card = 4 := by
    simpa only [L] using hcounts.2.2
  have hinterEq : R ∩ L = L := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    omega
  intro theta htheta
  have hthetaInter : theta ∈ R ∩ L := by
    rw [hinterEq]
    exact htheta
  exact (Finset.mem_inter.mp hthetaInter).1

/-- The exact surviving package in a favorable three-hole cell.  Its eight
regular source outsiders split into four points on the distinguished secant
and four points off it. -/
structure ThreeHoleExactCountResidual
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u) where
  data : UniqueEightCoreResidual family
  six_le_secant_core : 6 ≤
    (jointCore dom (u 0) (u 1)
      (residualSecantLine data).1 (residualSecantLine data).2).card
  off_regular_card : (regularOffResidualSecant family data).card = 4
  regular_source_outsiders_card :
    (regularOutsideLine family data.source).card = 8
  residual_secant_points_card :
    (pointsOn family (residualSecantLine data)).card = 4
  residual_secant_points_regular :
    pointsOn family (residualSecantLine data) ⊆
      regularOutsideLine family data.source

/-- Package a favorable three-hole residual with all of its now-exact
population counts. -/
noncomputable def threeHoleExactCountResidual
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (hsix : 6 ≤
      (jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1
        (residualSecantLine residual).2).card) :
    ThreeHoleExactCountResidual family := by
  have hcounts := threeHole_exact_regular_and_secant_counts
    family hn hthreshold residual hsix
  exact {
    data := residual
    six_le_secant_core := hsix
    off_regular_card :=
      regularOffResidualSecant_card_eq_four_of_six_le_secant_core
        family hn hthreshold residual hsix
    regular_source_outsiders_card := hcounts.1
    residual_secant_points_card := hcounts.2.2
    residual_secant_points_regular :=
      residualSecant_points_subset_regularOutsideLine_of_six_le_secant_core
        family hn hthreshold residual hsix }

/-! ## Forced-cross composition -/

/-- The favorable forced-cross alternatives have exactly four off-secant
regular outsiders.  The only other alternative remains the core-six,
overlap-two, four-hole support-four cell. -/
theorem crossTriple_threeHole_four_population_or_fourHole
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (residual : UniqueEightCoreResidual family)
    (cross : UniqueCoreCrossTripleResidual family residual) :
    (∃ exact : ThreeHoleExactCountResidual family,
      exact.data.source = residual.source ∧
      exact.data.gamma = cross.gamma1 ∧ exact.data.beta = cross.gamma2) ∨
    ((jointCore dom (u 0) (u 1)
        (secantParameter family cross.gamma1 cross.gamma2).1
        (secantParameter family cross.gamma1 cross.gamma2).2).card = 6 ∧
      (jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∩
        jointCore dom (u 0) (u 1)
          (secantParameter family cross.gamma1 cross.gamma2).1
          (secantParameter family cross.gamma1 cross.gamma2).2).card = 2 ∧
      (Finset.univ \ (
        jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∪
          jointCore dom (u 0) (u 1)
            (secantParameter family cross.gamma1 cross.gamma2).1
            (secantParameter family cross.gamma1 cross.gamma2).2)).card = 4 ∧
      ∀ theta ∈ family.G,
        family.q theta ≠ residual.source.1 + C theta * residual.source.2 →
        family.q theta ≠
          (secantParameter family cross.gamma1 cross.gamma2).1 +
            C theta * (secantParameter family cross.gamma1 cross.gamma2).2 →
        3 ≤ (fullAgreement dom (u 0) (u 1) theta (family.q theta) ∩
          (Finset.univ \ (
            jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∪
              jointCore dom (u 0) (u 1)
                (secantParameter family cross.gamma1 cross.gamma2).1
                (secantParameter family cross.gamma1 cross.gamma2).2))).card) := by
  rcases crossTriple_threeHole_population_or_fourHole
      family hn hthreshold residual cross with hfavorable | hfour
  · apply Or.inl
    obtain ⟨residual2, hsource, hgamma, hbeta, _hlower, _hupper⟩ := hfavorable
    have hsix : 6 ≤
        (jointCore dom (u 0) (u 1)
          (residualSecantLine residual2).1
          (residualSecantLine residual2).2).card := by
      rcases cross.secant_core_card with hcore | hcore
      · simpa only [residualSecantLine, hgamma, hbeta] using hcore.ge
      · have hcoreLower : 6 ≤
            (jointCore dom (u 0) (u 1)
              (secantParameter family cross.gamma1 cross.gamma2).1
              (secantParameter family cross.gamma1 cross.gamma2).2).card := by
          omega
        simpa only [residualSecantLine, hgamma, hbeta] using hcoreLower
    let exact := threeHoleExactCountResidual
      family hn hthreshold residual2 hsix
    refine ⟨exact, ?_, ?_, ?_⟩
    · simpa only [exact, threeHoleExactCountResidual] using hsource
    · simpa only [exact, threeHoleExactCountResidual] using hgamma
    · simpa only [exact, threeHoleExactCountResidual] using hbeta
  · exact Or.inr hfour

#print axioms residualPetalCoordinateFiber_card_eq_three_of_population_five
#print axioms residualPetalCoordinateFibers_eq_of_missed_edge_of_population_five
#print axioms residualMissedEdgeClass_card_eq_two_of_population_five
#print axioms regularOffResidualSecant_card_ne_five_of_six_le_secant_core
#print axioms regularOffResidualSecant_card_eq_four_of_six_le_secant_core
#print axioms threeHole_exact_regular_and_secant_counts
#print axioms residualSecant_points_subset_regularOutsideLine_of_six_le_secant_core
#print axioms threeHoleExactCountResidual
#print axioms crossTriple_threeHole_four_population_or_fourHole

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourThreeHoleSaturation
