/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourCrossTripleCollinearity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourUniqueCoreSignatures

/-!
# Rate-quarter `k = 4`: the three-hole cross-secant cells

This file studies the cells in which the unique source eight-core and a
distinct six- or seven-core secant leave three holes.  These are respectively
the overlap-one and overlap-two cases.  Every regular outsider off both
decoded lines agrees on all three holes.

The common holes have two consequences.  First, all surviving degree-three
polynomials lie in one affine two-plane modulo the monic cubic locator of the
holes.  Second, four survivors cannot be collinear: after removing the common
part of their source-petal and secant-petal triples, one obtains four disjoint
equal-size sets in grounds of sizes at most seven and five, which is arithmetically
impossible.  The five-coordinate secant petal then bounds the surviving
off-secant population by five.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalPruning
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeCommonFactor
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeKFour
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSignatures

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSevenCoreOverlapTwo

attribute [local instance] Classical.propDecidable

/-! ## The finite obstruction behind the no-four-collinear theorem -/

variable {K U : Type} [Fintype K] [DecidableEq K] [DecidableEq U]

/-- Four pairs of triples cannot have fixed pairwise intersections whose
cardinalities sum to four when their ambient grounds have sizes at most seven
and five.

Removing the fixed intersections leaves pairwise-disjoint families.  Their
two packing inequalities are incompatible with the intersection-cardinality
sum. -/
theorem no_four_fixed_intersection_triple_pairs
    (hK : Fintype.card K = 4)
    (Q P KT KP : Finset U) (T A : K → Finset U)
    (hQcard : Q.card ≤ 7) (hPcard : P.card = 5)
    (hT : ∀ x, T x ⊆ Q ∧ (T x).card = 3)
    (hA : ∀ x, A x ⊆ P ∧ (A x).card = 3)
    (hTinter : ∀ x y, x ≠ y → T x ∩ T y = KT)
    (hAinter : ∀ x y, x ≠ y → A x ∩ A y = KP)
    (hfixed : KT.card + KP.card = 4) : False := by
  classical
  haveI : Nontrivial K :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hKTsub : ∀ x, KT ⊆ T x := by
    intro x
    obtain ⟨y, hyx⟩ := exists_ne x
    rw [← hTinter x y hyx.symm]
    exact Finset.inter_subset_left
  have hKPsub : ∀ x, KP ⊆ A x := by
    intro x
    obtain ⟨y, hyx⟩ := exists_ne x
    rw [← hAinter x y hyx.symm]
    exact Finset.inter_subset_left
  have hKTQ : KT ⊆ Q := (hKTsub (Classical.choice inferInstance)).trans
    (hT (Classical.choice inferInstance)).1
  have hKPP : KP ⊆ P := (hKPsub (Classical.choice inferInstance)).trans
    (hA (Classical.choice inferInstance)).1
  let TR : K → Finset U := fun x => T x \ KT
  let AR : K → Finset U := fun x => A x \ KP
  have hTRcard : ∀ x, (TR x).card = 3 - KT.card := by
    intro x
    rw [show TR x = T x \ KT by rfl,
      Finset.card_sdiff_of_subset (hKTsub x), (hT x).2]
  have hARcard : ∀ x, (AR x).card = 3 - KP.card := by
    intro x
    rw [show AR x = A x \ KP by rfl,
      Finset.card_sdiff_of_subset (hKPsub x), (hA x).2]
  have hTRdisj : ∀ x ∈ (Finset.univ : Finset K),
      ∀ y ∈ (Finset.univ : Finset K), x ≠ y → Disjoint (TR x) (TR y) := by
    intro x _hx y _hy hxy
    rw [Finset.disjoint_left]
    intro i hix hiy
    have hiInter : i ∈ T x ∩ T y :=
      Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hix).1,
        (Finset.mem_sdiff.mp hiy).1⟩
    have hiKT : i ∈ KT := by simpa only [hTinter x y hxy] using hiInter
    exact (Finset.mem_sdiff.mp hix).2 hiKT
  have hARdisj : ∀ x ∈ (Finset.univ : Finset K),
      ∀ y ∈ (Finset.univ : Finset K), x ≠ y → Disjoint (AR x) (AR y) := by
    intro x _hx y _hy hxy
    rw [Finset.disjoint_left]
    intro i hix hiy
    have hiInter : i ∈ A x ∩ A y :=
      Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hix).1,
        (Finset.mem_sdiff.mp hiy).1⟩
    have hiKP : i ∈ KP := by simpa only [hAinter x y hxy] using hiInter
    exact (Finset.mem_sdiff.mp hix).2 hiKP
  have hTRsub : (Finset.univ : Finset K).biUnion TR ⊆ Q \ KT := by
    rw [Finset.biUnion_subset_iff_forall_subset]
    intro x _hx i hi
    exact Finset.mem_sdiff.mpr
      ⟨(hT x).1 (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩
  have hARsub : (Finset.univ : Finset K).biUnion AR ⊆ P \ KP := by
    rw [Finset.biUnion_subset_iff_forall_subset]
    intro x _hx i hi
    exact Finset.mem_sdiff.mpr
      ⟨(hA x).1 (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩
  have hTRsum : ((Finset.univ : Finset K).biUnion TR).card =
      4 * (3 - KT.card) := by
    rw [Finset.card_biUnion hTRdisj]
    simp only [hTRcard, Finset.sum_const, Finset.card_univ, hK,
      nsmul_eq_mul]
    norm_num
  have hARsum : ((Finset.univ : Finset K).biUnion AR).card =
      4 * (3 - KP.card) := by
    rw [Finset.card_biUnion hARdisj]
    simp only [hARcard, Finset.sum_const, Finset.card_univ, hK,
      nsmul_eq_mul]
    norm_num
  have hTbudget : 4 * (3 - KT.card) ≤ 7 - KT.card := by
    calc
      4 * (3 - KT.card) =
          ((Finset.univ : Finset K).biUnion TR).card := hTRsum.symm
      _ ≤ (Q \ KT).card := Finset.card_le_card hTRsub
      _ = Q.card - KT.card := Finset.card_sdiff_of_subset hKTQ
      _ ≤ 7 - KT.card := Nat.sub_le_sub_right hQcard KT.card
  have hAbudget : 4 * (3 - KP.card) ≤ 5 - KP.card := by
    rw [← hARsum, ← hPcard,
      ← Finset.card_sdiff_of_subset hKPP]
    exact Finset.card_le_card hARsub
  omega

/-! ## The common-hole affine plane -/

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The three coordinates missed by both distinguished decoded cores. -/
noncomputable def residualHoles
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom 4 delta u}
    (residual : UniqueEightCoreResidual family) : Finset I :=
  Finset.univ \ (
    jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 ∪
      jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1 (residualSecantLine residual).2)

/-- The source-core part outside the distinguished secant core. -/
noncomputable def residualSourcePetal
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom 4 delta u}
    (residual : UniqueEightCoreResidual family) : Finset I :=
  jointCore dom (u 0) (u 1) residual.source.1 residual.source.2 \
    jointCore dom (u 0) (u 1)
      (residualSecantLine residual).1 (residualSecantLine residual).2

/-- The three agreements of a survivor inside the five-coordinate secant
petal. -/
noncomputable def residualSecantPetalAgreement
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family) (theta : F) : Finset I :=
  sourceFreshAgreement family residual.source theta ∩
    secantPetal family residual.source residual.gamma residual.beta

theorem residualHoles_card
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom 4 delta u}
    (residual : UniqueEightCoreResidual family) :
    (residualHoles residual).card = 3 := by
  simpa only [residualHoles, residualSecantLine] using residual.uncovered_card

theorem regularOffResidualSecant_subset_G
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family) :
    regularOffResidualSecant family residual ⊆ family.G := by
  intro theta htheta
  have hthetaData := htheta
  simp only [regularOffResidualSecant, Finset.mem_sdiff,
    regularOutsideLine, Finset.mem_filter] at hthetaData
  exact (mem_outsideLine_iff family residual.source theta).mp
    hthetaData.1.1 |>.1

/-- **Common-cubic affine-plane normal form.**  Fix two distinct surviving
points.  Every other survivor differs from their polynomial secant by a
scalar multiple of the monic cubic locator of the three residual holes. -/
theorem offResidualSecant_affine_plane_normal_form
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {alpha beta theta : F}
    (halpha : alpha ∈ regularOffResidualSecant family residual)
    (hbeta : beta ∈ regularOffResidualSecant family residual)
    (htheta : theta ∈ regularOffResidualSecant family residual)
    (hab : alpha ≠ beta) :
    ∃ c : F,
      family.q theta = family.q alpha +
          C (theta - alpha) * slopePolynomial alpha beta
            (family.q alpha) (family.q beta) +
        C c * domainRootProduct dom (residualHoles residual) := by
  let H := residualHoles residual
  let r := slopePolynomial alpha beta (family.q alpha) (family.q beta)
  let base := family.q alpha + C (theta - alpha) * r
  let p := family.q theta - base
  have halphaG := regularOffResidualSecant_subset_G family residual halpha
  have hbetaG := regularOffResidualSecant_subset_G family residual hbeta
  have hthetaG := regularOffResidualSecant_subset_G family residual htheta
  have hHcard : H.card = 3 := by
    simpa only [H] using residualHoles_card residual
  have halphaH := (offResidualSecant_signature_restrictions
    family hn residual halpha).2.2
  have hbetaH := (offResidualSecant_signature_restrictions
    family hn residual hbeta).2.2
  have hthetaH := (offResidualSecant_signature_restrictions
    family hn residual htheta).2.2
  have hrdeg : r.natDegree < 4 := by
    exact slopePolynomial_natDegree_lt
      (family.degree_lt alpha halphaG) (family.degree_lt beta hbetaG)
  have hbasedeg : base.natDegree < 4 := by
    exact lt_of_le_of_lt (natDegree_add_le _ _)
      (max_lt (family.degree_lt alpha halphaG)
        (lt_of_le_of_lt (natDegree_C_mul_le _ _) hrdeg))
  have hpdeg : p.natDegree < 4 := by
    exact lt_of_le_of_lt (natDegree_sub_le _ _)
      (max_lt (family.degree_lt theta hthetaG) hbasedeg)
  have hroot : ∀ i ∈ H, p.eval (dom i) = 0 := by
    intro i hiH
    have hiAlphaFresh : i ∈ sourceFreshAgreement family residual.source alpha :=
      halphaH (by simpa only [H] using hiH)
    have hiBetaFresh : i ∈ sourceFreshAgreement family residual.source beta :=
      hbetaH (by simpa only [H] using hiH)
    have hiThetaFresh : i ∈ sourceFreshAgreement family residual.source theta :=
      hthetaH (by simpa only [H] using hiH)
    have hiAlpha := (Finset.mem_sdiff.mp hiAlphaFresh).1
    have hiBeta := (Finset.mem_sdiff.mp hiBetaFresh).1
    have hiTheta := (Finset.mem_sdiff.mp hiThetaFresh).1
    have hrEval : r.eval (dom i) = u 1 i := by
      exact slopePolynomial_eval_eq_direction dom (u 0) (u 1) hab
        hiAlpha hiBeta
    simp only [fullAgreement, Finset.mem_filter, Finset.mem_univ,
      true_and] at hiAlpha hiTheta
    simp only [p, base, eval_sub, eval_add, eval_mul, eval_C]
    rw [hrEval, hiAlpha, hiTheta]
    ring
  obtain ⟨q, hfactor, hqdeg⟩ :=
    exists_quotient_natDegree_lt_sub_three_of_three_roots
      dom (k := 4) (by norm_num) p hpdeg H hHcard hroot
  obtain ⟨_hq0, hqC⟩ :=
    eq_C_coeff_zero_of_natDegree_lt_one q (by simpa using hqdeg)
  have hmul : domainRootProduct dom H * q =
      C (q.coeff 0) * domainRootProduct dom H := by
    calc
      domainRootProduct dom H * q =
          domainRootProduct dom H * C (q.coeff 0) :=
        congrArg (fun s : F[X] => domainRootProduct dom H * s) hqC
      _ = C (q.coeff 0) * domainRootProduct dom H := by ring
  refine ⟨q.coeff 0, ?_⟩
  change family.q theta = base + C (q.coeff 0) * domainRootProduct dom H
  calc
    family.q theta = base + p := by simp only [p]; ring
    _ = base + domainRootProduct dom H * q := by rw [hfactor]
    _ = base + C (q.coeff 0) * domainRootProduct dom H := by rw [hmul]

/-! ## Exact source/secant petal signatures -/

theorem residualSourcePetal_card_eq_six_of_secant_core_seven
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom 4 delta u}
    (residual : UniqueEightCoreResidual family)
    (hseven :
      (jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1
        (residualSecantLine residual).2).card = 7) :
    (residualSourcePetal residual).card = 6 := by
  let D := jointCore dom (u 0) (u 1)
    residual.source.1 residual.source.2
  let D2 := jointCore dom (u 0) (u 1)
    (residualSecantLine residual).1 (residualSecantLine residual).2
  have hD : D.card = 8 := by
    simpa only [D] using residual.source_core_card
  have hD2 : D2.card = 7 := by simpa only [D2] using hseven
  have hD2form : D2.card = 5 + (D ∩ D2).card := by
    simpa only [D, D2, residualSecantLine] using residual.secant_core_card
  have hinter : (D ∩ D2).card = 2 := by omega
  have hsplit := Finset.card_sdiff_add_card_inter D D2
  change (D \ D2).card = 6
  omega

theorem residualSourcePetal_card_le_seven_of_six_le_secant_core
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom 4 delta u}
    (residual : UniqueEightCoreResidual family)
    (hsix : 6 ≤
      (jointCore dom (u 0) (u 1)
        (residualSecantLine residual).1
        (residualSecantLine residual).2).card) :
    (residualSourcePetal residual).card ≤ 7 := by
  let D := jointCore dom (u 0) (u 1)
    residual.source.1 residual.source.2
  let D2 := jointCore dom (u 0) (u 1)
    (residualSecantLine residual).1 (residualSecantLine residual).2
  have hD : D.card = 8 := by
    simpa only [D] using residual.source_core_card
  have hD2form : D2.card = 5 + (D ∩ D2).card := by
    simpa only [D, D2, residualSecantLine] using residual.secant_core_card
  have hinter : 1 ≤ (D ∩ D2).card := by
    have hsix' : 6 ≤ D2.card := by simpa only [D2] using hsix
    omega
  have hsplit := Finset.card_sdiff_add_card_inter D D2
  change (D \ D2).card ≤ 7
  omega

theorem residualSecantPetal_card
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom 4 delta u}
    (residual : UniqueEightCoreResidual family) :
    (secantPetal family residual.source residual.gamma residual.beta).card = 5 :=
  residual.secant_petal_card

/-- A survivor carries exactly a three-subset in each of the source and
secant petals. -/
theorem offResidualSecant_two_triple_data
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {theta : F}
    (htheta : theta ∈ regularOffResidualSecant family residual) :
    regularRootTriple family residual.source theta ⊆
        residualSourcePetal residual ∧
      (regularRootTriple family residual.source theta).card = 3 ∧
      residualSecantPetalAgreement family residual theta ⊆
        secantPetal family residual.source residual.gamma residual.beta ∧
      (residualSecantPetalAgreement family residual theta).card = 3 := by
  let D := jointCore dom (u 0) (u 1)
    residual.source.1 residual.source.2
  let D2 := jointCore dom (u 0) (u 1)
    (residualSecantLine residual).1 (residualSecantLine residual).2
  let T := regularRootTriple family residual.source theta
  let S := sourceFreshAgreement family residual.source theta
  let E := regularMissedEdge family residual.source theta
  let P := secantPetal family residual.source residual.gamma residual.beta
  let A := residualSecantPetalAgreement family residual theta
  have hthetaData := htheta
  simp only [regularOffResidualSecant, Finset.mem_sdiff] at hthetaData
  have hregular := hthetaData.1
  have hTcard : T.card = 3 := by
    simpa only [T] using
      (regular_signature_cardinalities
        family hn residual.source_core_card hregular).1
  have hEcard : E.card = 2 := by
    simpa only [E] using
      (regular_signature_cardinalities
        family hn residual.source_core_card hregular).2
  have hrestrict := offResidualSecant_signature_restrictions
    family hn residual htheta
  have hTsub : T ⊆ D \ D2 := by
    intro i hiT
    have hiD : i ∈ D := by
      exact (Finset.mem_inter.mp (by
        simpa only [T, regularRootTriple, D] using hiT)).2
    apply Finset.mem_sdiff.mpr
    refine ⟨hiD, ?_⟩
    intro hiD2
    have hiC : i ∈ D ∩ D2 := Finset.mem_inter.mpr ⟨hiD, hiD2⟩
    exact Finset.disjoint_left.mp hrestrict.1 hiT (by
      simpa only [D, D2] using hiC)
  have hEsub : E ⊆ P := by
    simpa only [E, P, D, D2, residualSecantLine, secantPetal] using hrestrict.2.1
  have hAeq : A = P \ E := by
    ext i
    simp only [A, P, E, residualSecantPetalAgreement,
      regularMissedEdge, secantPetal, sourceFreshAgreement,
      Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  have hAcard : A.card = 3 := by
    rw [hAeq, Finset.card_sdiff_of_subset hEsub,
      residualSecantPetal_card residual, hEcard]
  exact ⟨by simpa only [T, residualSourcePetal, D, D2] using hTsub,
    hTcard, by simpa only [A, P] using Finset.inter_subset_right, hAcard⟩

/-- The full agreement set of every survivor is the disjoint geographical
union of its source-petal triple, its secant-petal triple, and the three
common holes. -/
theorem offResidualSecant_fullAgreement_partition
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {theta : F}
    (htheta : theta ∈ regularOffResidualSecant family residual) :
    fullAgreement dom (u 0) (u 1) theta (family.q theta) =
      (regularRootTriple family residual.source theta ∪
        residualSecantPetalAgreement family residual theta) ∪
        residualHoles residual := by
  let D := jointCore dom (u 0) (u 1)
    residual.source.1 residual.source.2
  let D2 := jointCore dom (u 0) (u 1)
    (residualSecantLine residual).1 (residualSecantLine residual).2
  let Full := fullAgreement dom (u 0) (u 1) theta (family.q theta)
  let T := regularRootTriple family residual.source theta
  let S := sourceFreshAgreement family residual.source theta
  let A := residualSecantPetalAgreement family residual theta
  let H := residualHoles residual
  have hHsub : H ⊆ S := by
    simpa only [H, S, residualHoles] using
      (offResidualSecant_signature_restrictions
        family hn residual htheta).2.2
  ext i
  constructor
  · intro hiFull
    by_cases hiD : i ∈ D
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by
        exact Finset.mem_inter.mpr ⟨hiFull, hiD⟩))
    by_cases hiD2 : i ∈ D2
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hiFull, hiD⟩,
          Finset.mem_sdiff.mpr ⟨hiD2, hiD⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, fun hiUnion =>
          (Finset.mem_union.mp hiUnion).elim hiD hiD2⟩
  · intro hi
    rcases Finset.mem_union.mp hi with hiTA | hiH
    · rcases Finset.mem_union.mp hiTA with hiT | hiA
      · exact (Finset.mem_inter.mp (by
          simpa only [T, regularRootTriple, D] using hiT)).1
      · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp (by
          simpa only [A, residualSecantPetalAgreement] using hiA)).1).1
    · exact (Finset.mem_sdiff.mp (hHsub (by simpa only [H] using hiH))).1

/-! ## No four collinear survivors -/

/-- **No-four theorem in a three-hole, core-at-least-six cell.**  Four distinct regular
outsiders off the two distinguished lines cannot lie on one secant. -/
theorem not_four_offResidualSecant_collinear_of_six_le_secant_core
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
    {theta0 theta1 theta2 theta3 : F}
    (htheta0 : theta0 ∈ regularOffResidualSecant family residual)
    (htheta1 : theta1 ∈ regularOffResidualSecant family residual)
    (htheta2 : theta2 ∈ regularOffResidualSecant family residual)
    (htheta3 : theta3 ∈ regularOffResidualSecant family residual)
    (h01 : theta0 ≠ theta1) (h02 : theta0 ≠ theta2)
    (h03 : theta0 ≠ theta3) (h12 : theta1 ≠ theta2)
    (h13 : theta1 ≠ theta3) (h23 : theta2 ≠ theta3)
    (htheta2On : theta2 ∈ pointsOn family
      (secantParameter family theta0 theta1))
    (htheta3On : theta3 ∈ pointsOn family
      (secantParameter family theta0 theta1)) : False := by
  let line3 := secantParameter family theta0 theta1
  let D := jointCore dom (u 0) (u 1)
    residual.source.1 residual.source.2
  let D2 := jointCore dom (u 0) (u 1)
    (residualSecantLine residual).1 (residualSecantLine residual).2
  let D3 := jointCore dom (u 0) (u 1) line3.1 line3.2
  let Q := residualSourcePetal residual
  let P := secantPetal family residual.source residual.gamma residual.beta
  let H := residualHoles residual
  let theta : Fin 4 → F := ![theta0, theta1, theta2, theta3]
  let T : Fin 4 → Finset I := fun x =>
    regularRootTriple family residual.source (theta x)
  let A : Fin 4 → Finset I := fun x =>
    residualSecantPetalAgreement family residual (theta x)
  have hthetaInj : Function.Injective theta := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [theta]
  have hthetaMem : ∀ x, theta x ∈ regularOffResidualSecant family residual := by
    intro x
    fin_cases x
    · simpa only [theta] using htheta0
    · simpa only [theta] using htheta1
    · simpa only [theta] using htheta2
    · simpa only [theta] using htheta3
  have hthetaG : ∀ x, theta x ∈ family.G := fun x =>
    regularOffResidualSecant_subset_G family residual (hthetaMem x)
  have hline3 : line3 ∈ lineParameters family := by
    exact secantParameter_mem_lineParameters family
      (hthetaG 0) (hthetaG 1) (by simpa only [theta] using h01)
  have htheta0On : theta0 ∈ pointsOn family line3 := by
    exact first_point_mem_pointsOn_secant family (hthetaG 0)
  have htheta1On : theta1 ∈ pointsOn family line3 := by
    exact second_point_mem_pointsOn_secant family (hthetaG 1) h01
  have hthetaOn : ∀ x, theta x ∈ pointsOn family line3 := by
    intro x
    fin_cases x
    · simpa only [theta] using htheta0On
    · simpa only [theta] using htheta1On
    · simpa only [theta, line3] using htheta2On
    · simpa only [theta, line3] using htheta3On
  have hline3Ne : line3 ≠ residual.source := by
    intro heq
    have hsourceOn : theta0 ∈ pointsOn family residual.source := by
      rw [← heq]
      exact htheta0On
    have htheta0Data := htheta0
    simp only [regularOffResidualSecant, Finset.mem_sdiff,
      regularOutsideLine, Finset.mem_filter] at htheta0Data
    exact ((mem_outsideLine_iff family residual.source theta0).mp
      htheta0Data.1.1).2
        ((mem_pointsOn_iff family residual.source theta0).mp hsourceOn).2
  have hD3upper : D3.card ≤ 7 := by
    by_contra hnot
    have hlarge : 8 ≤ (jointCore dom (u 0) (u 1) line3.1 line3.2).card := by
      simpa only [D3] using (show 8 ≤ D3.card by omega)
    exact hline3Ne (residual.source_unique line3 hline3 hlarge)
  have hfour : 3 < (pointsOn family line3).card := by
    apply Finset.three_lt_card_iff.mpr
    exact ⟨theta0, theta1, theta2, theta3,
      htheta0On, htheta1On,
      by simpa only [line3] using htheta2On,
      by simpa only [line3] using htheta3On,
      h01, h02, h03, h12, h13, h23⟩
  have hpack := pointsOn_card_mul_max_add_core_le family hline3
  change (pointsOn family line3).card * max 1
      (⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ - D3.card) + D3.card ≤
    Fintype.card I at hpack
  rw [hthreshold, hn] at hpack
  have hfactor : 9 - D3.card ≤ max 1 (9 - D3.card) := le_max_right _ _
  have hmul : 4 * (9 - D3.card) ≤
      (pointsOn family line3).card * max 1 (9 - D3.card) :=
    Nat.mul_le_mul (by omega) hfactor
  have hbase : 4 * (9 - D3.card) + D3.card ≤ 16 :=
    (Nat.add_le_add_right hmul D3.card).trans hpack
  have hD3card : D3.card = 7 := by omega
  have hfullCore : ∀ x y : Fin 4, x ≠ y →
      fullAgreement dom (u 0) (u 1) (theta x) (family.q (theta x)) ∩
          fullAgreement dom (u 0) (u 1) (theta y) (family.q (theta y)) = D3 := by
    intro x y hxy
    have hxEq := (mem_pointsOn_iff family line3 (theta x)).mp
      (hthetaOn x) |>.2
    have hyEq := (mem_pointsOn_iff family line3 (theta y)).mp
      (hthetaOn y) |>.2
    rw [hxEq, hyEq]
    exact fullAgreement_inter_eq_jointCore
      dom (u 0) (u 1) line3.1 line3.2 (hthetaInj.ne hxy)
  have hHcard : H.card = 3 := by
    simpa only [H] using residualHoles_card residual
  have hQcard : Q.card ≤ 7 := by
    simpa only [Q] using
      residualSourcePetal_card_le_seven_of_six_le_secant_core residual hsix
  have hPcard : P.card = 5 := by
    simpa only [P] using residualSecantPetal_card residual
  have hTdata : ∀ x, T x ⊆ Q ∧ (T x).card = 3 := by
    intro x
    have hdata := offResidualSecant_two_triple_data
      family hn residual (hthetaMem x)
    exact ⟨by simpa only [T, Q] using hdata.1,
      by simpa only [T] using hdata.2.1⟩
  have hAdata : ∀ x, A x ⊆ P ∧ (A x).card = 3 := by
    intro x
    have hdata := offResidualSecant_two_triple_data
      family hn residual (hthetaMem x)
    exact ⟨by simpa only [A, P] using hdata.2.2.1,
      by simpa only [A] using hdata.2.2.2⟩
  have hHsubD3 : H ⊆ D3 := by
    simpa only [H, D3, line3] using
      residual_holes_subset_pair_secant_core
        family hn residual htheta0 htheta1 h01
  have hD3subFull0 : D3 ⊆
      fullAgreement dom (u 0) (u 1) theta0 (family.q theta0) := by
    rw [← hfullCore 0 1 (by decide)]
    exact Finset.inter_subset_left
  have hD3subBlocks : D3 ⊆ H ∪ Q ∪ P := by
    intro i hiD3
    have hiFull : i ∈ fullAgreement dom (u 0) (u 1) theta0 (family.q theta0) :=
      hD3subFull0 hiD3
    have hpartition := offResidualSecant_fullAgreement_partition
      family hn residual htheta0
    rw [hpartition] at hiFull
    rcases Finset.mem_union.mp hiFull with hiTA | hiH
    · rcases Finset.mem_union.mp hiTA with hiT | hiA
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ ((hTdata 0).1 (by simpa only [T] using hiT)))
      · exact Finset.mem_union_right _ ((hAdata 0).1 (by simpa only [A] using hiA))
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (by simpa only [H] using hiH))
  let KT := D3 ∩ Q
  let KP := D3 ∩ P
  have hD3partition : D3 = (H ∪ KT) ∪ KP := by
    ext i
    constructor
    · intro hiD3
      rcases Finset.mem_union.mp (hD3subBlocks hiD3) with hiHQ | hiP
      · rcases Finset.mem_union.mp hiHQ with hiH | hiQ
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hiH)
        · exact Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hiD3, hiQ⟩))
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hiD3, hiP⟩)
    · intro hi
      rcases Finset.mem_union.mp hi with hiHKT | hiKP
      · rcases Finset.mem_union.mp hiHKT with hiH | hiKT
        · exact hHsubD3 hiH
        · exact (Finset.mem_inter.mp hiKT).1
      · exact (Finset.mem_inter.mp hiKP).1
  have hHQ : Disjoint H Q := by
    rw [Finset.disjoint_left]
    intro i hiH hiQ
    have hiHData := Finset.mem_sdiff.mp (by simpa only [H, residualHoles] using hiH)
    have hiQData := Finset.mem_sdiff.mp (by
      simpa only [Q, residualSourcePetal] using hiQ)
    exact hiHData.2 (Finset.mem_union_left _ hiQData.1)
  have hHP : Disjoint H P := by
    rw [Finset.disjoint_left]
    intro i hiH hiP
    have hiHData := Finset.mem_sdiff.mp (by simpa only [H, residualHoles] using hiH)
    have hiPData := Finset.mem_sdiff.mp (by
      simpa only [P, secantPetal, residualSecantLine] using hiP)
    exact hiHData.2 (Finset.mem_union_right _ hiPData.1)
  have hQP : Disjoint Q P := by
    rw [Finset.disjoint_left]
    intro i hiQ hiP
    have hiQData := Finset.mem_sdiff.mp (by
      simpa only [Q, residualSourcePetal] using hiQ)
    have hiPData := Finset.mem_sdiff.mp (by
      simpa only [P, secantPetal, residualSecantLine] using hiP)
    exact hiQData.2 hiPData.1
  have hHKT : Disjoint H KT := hHQ.mono_right Finset.inter_subset_right
  have hHKTP : Disjoint (H ∪ KT) KP := by
    apply Finset.disjoint_union_left.mpr
    exact ⟨hHP.mono_right Finset.inter_subset_right,
      hQP.mono Finset.inter_subset_right Finset.inter_subset_right⟩
  have hfixed : KT.card + KP.card = 4 := by
    have hcardEq := congrArg Finset.card hD3partition
    rw [Finset.card_union_of_disjoint hHKTP,
      Finset.card_union_of_disjoint hHKT, hD3card, hHcard] at hcardEq
    omega
  have hTinter : ∀ x y : Fin 4, x ≠ y → T x ∩ T y = KT := by
    intro x y hxy
    ext i
    constructor
    · intro hi
      have hiPair : i ∈
          fullAgreement dom (u 0) (u 1) (theta x) (family.q (theta x)) ∩
            fullAgreement dom (u 0) (u 1) (theta y) (family.q (theta y)) := by
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp (by
              simpa only [T, regularRootTriple] using
                (Finset.mem_inter.mp hi).1)).1,
            (Finset.mem_inter.mp (by
              simpa only [T, regularRootTriple] using
                (Finset.mem_inter.mp hi).2)).1⟩
      have hiD3 : i ∈ D3 := by simpa only [hfullCore x y hxy] using hiPair
      have hiQ : i ∈ Q := (hTdata x).1 (Finset.mem_inter.mp hi).1
      exact Finset.mem_inter.mpr ⟨hiD3, hiQ⟩
    · intro hi
      have hiD3 := (Finset.mem_inter.mp hi).1
      have hiQ := (Finset.mem_inter.mp hi).2
      have hiPair : i ∈
          fullAgreement dom (u 0) (u 1) (theta x) (family.q (theta x)) ∩
            fullAgreement dom (u 0) (u 1) (theta y) (family.q (theta y)) := by
        rw [hfullCore x y hxy]
        exact hiD3
      have hiD : i ∈ D := (Finset.mem_sdiff.mp (by
        simpa only [Q, residualSourcePetal] using hiQ)).1
      apply Finset.mem_inter.mpr
      constructor <;> simp only [T, regularRootTriple]
      · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hiPair).1, hiD⟩
      · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hiPair).2, hiD⟩
  have hAinter : ∀ x y : Fin 4, x ≠ y → A x ∩ A y = KP := by
    intro x y hxy
    ext i
    constructor
    · intro hi
      have hiA1 := (Finset.mem_inter.mp hi).1
      have hiA2 := (Finset.mem_inter.mp hi).2
      have hiFull1 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (by
        simpa only [A, residualSecantPetalAgreement] using hiA1)).1).1
      have hiFull2 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (by
        simpa only [A, residualSecantPetalAgreement] using hiA2)).1).1
      have hiD3 : i ∈ D3 := by
        rw [← hfullCore x y hxy]
        exact Finset.mem_inter.mpr ⟨hiFull1, hiFull2⟩
      exact Finset.mem_inter.mpr ⟨hiD3, (hAdata x).1 hiA1⟩
    · intro hi
      have hiD3 := (Finset.mem_inter.mp hi).1
      have hiP := (Finset.mem_inter.mp hi).2
      have hiPair : i ∈
          fullAgreement dom (u 0) (u 1) (theta x) (family.q (theta x)) ∩
            fullAgreement dom (u 0) (u 1) (theta y) (family.q (theta y)) := by
        rw [hfullCore x y hxy]
        exact hiD3
      have hiNotD : i ∉ D := (Finset.mem_sdiff.mp (by
        simpa only [P, secantPetal, residualSecantLine] using hiP)).2
      apply Finset.mem_inter.mpr
      constructor <;> simp only [A, residualSecantPetalAgreement]
      · exact Finset.mem_inter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hiPair).1, hiNotD⟩, hiP⟩
      · exact Finset.mem_inter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hiPair).2, hiNotD⟩, hiP⟩
  exact no_four_fixed_intersection_triple_pairs
    (K := Fin 4) (U := I) (by simp) Q P KT KP T A
      hQcard hPcard hTdata hAdata hTinter hAinter hfixed

/-! ## The five-coordinate petal population bound -/

/-- Three survivors sharing a secant-petal agreement coordinate are
collinear.  Together with the three common holes, that coordinate gives four
common roots, exceeding the degree-three noncollinear cap. -/
theorem third_mem_pointsOn_secant_of_common_petal_coordinate
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {theta0 theta1 theta2 : F}
    (htheta0 : theta0 ∈ regularOffResidualSecant family residual)
    (htheta1 : theta1 ∈ regularOffResidualSecant family residual)
    (htheta2 : theta2 ∈ regularOffResidualSecant family residual)
    (h01 : theta0 ≠ theta1) (h02 : theta0 ≠ theta2)
    {i : I}
    (hi0 : i ∈ residualSecantPetalAgreement family residual theta0)
    (hi1 : i ∈ residualSecantPetalAgreement family residual theta1)
    (hi2 : i ∈ residualSecantPetalAgreement family residual theta2) :
    theta2 ∈ pointsOn family (secantParameter family theta0 theta1) := by
  let H := residualHoles residual
  let R : Finset I := insert i H
  let Full : F → Finset I := fun theta =>
    fullAgreement dom (u 0) (u 1) theta (family.q theta)
  have hHcard : H.card = 3 := by
    simpa only [H] using residualHoles_card residual
  have hiP := (offResidualSecant_two_triple_data
    family hn residual htheta0).2.2.1 hi0
  have hiNotH : i ∉ H := by
    intro hiH
    have hdis : Disjoint H
        (secantPetal family residual.source residual.gamma residual.beta) := by
      rw [Finset.disjoint_left]
      intro j hjH hjP
      have hjHData := Finset.mem_sdiff.mp (by
        simpa only [H, residualHoles] using hjH)
      have hjPData := Finset.mem_sdiff.mp (by
        simpa only [secantPetal, residualSecantLine] using hjP)
      exact hjHData.2 (Finset.mem_union_right _ hjPData.1)
    exact Finset.disjoint_left.mp hdis hiH hiP
  have hRcard : R.card = 4 := by
    rw [show R = insert i H by rfl, Finset.card_insert_of_notMem hiNotH, hHcard]
  have hH0 := (offResidualSecant_signature_restrictions
    family hn residual htheta0).2.2
  have hH1 := (offResidualSecant_signature_restrictions
    family hn residual htheta1).2.2
  have hH2 := (offResidualSecant_signature_restrictions
    family hn residual htheta2).2.2
  have hi0Full : i ∈ Full theta0 := by
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp (by
      simpa only [residualSecantPetalAgreement] using hi0)).1).1
  have hi1Full : i ∈ Full theta1 := by
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp (by
      simpa only [residualSecantPetalAgreement] using hi1)).1).1
  have hi2Full : i ∈ Full theta2 := by
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp (by
      simpa only [residualSecantPetalAgreement] using hi2)).1).1
  have hRsub : R ⊆ (Full theta0 ∩ Full theta1) ∩ Full theta2 := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjH
    · exact Finset.mem_inter.mpr
        ⟨Finset.mem_inter.mpr ⟨hi0Full, hi1Full⟩, hi2Full⟩
    · have hj0 := (Finset.mem_sdiff.mp (hH0 (by simpa only [H] using hjH))).1
      have hj1 := (Finset.mem_sdiff.mp (hH1 (by simpa only [H] using hjH))).1
      have hj2 := (Finset.mem_sdiff.mp (hH2 (by simpa only [H] using hjH))).1
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hj0, hj1⟩, hj2⟩
  have htriple : 3 < ((Full theta0 ∩ Full theta1) ∩ Full theta2).card := by
    have hRlarge : 3 < R.card := by omega
    exact hRlarge.trans_le (Finset.card_le_card hRsub)
  have htheta0G := regularOffResidualSecant_subset_G family residual htheta0
  have htheta1G := regularOffResidualSecant_subset_G family residual htheta1
  have htheta2G := regularOffResidualSecant_subset_G family residual htheta2
  have hslope :
      slopePolynomial theta0 theta1 (family.q theta0) (family.q theta1) =
        slopePolynomial theta0 theta2 (family.q theta0) (family.q theta2) := by
    by_contra hslopeNe
    have hupper := triple_fullAgreement_card_le_pred_of_slope_ne
      dom (u 0) (u 1) (k := 4) (by norm_num) h01 h02
        (family.degree_lt theta0 htheta0G)
        (family.degree_lt theta1 htheta1G)
        (family.degree_lt theta2 htheta2G) hslopeNe
    change ((Full theta0 ∩ Full theta1) ∩ Full theta2).card ≤ 4 - 1 at hupper
    norm_num only at hupper
    exact (Nat.not_lt_of_ge hupper htriple).elim
  have hthird := third_point_on_secant_line_of_slope_eq h02 hslope.symm
  exact (mem_pointsOn_iff family
      (secantParameter family theta0 theta1) theta2).mpr
    ⟨htheta2G, by simpa only [secantParameter] using hthird⟩

/-- Survivors agreeing at a fixed coordinate of the distinguished secant
petal. -/
noncomputable def residualPetalCoordinateFiber
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (residual : UniqueEightCoreResidual family) (i : I) : Finset F :=
  (regularOffResidualSecant family residual).filter fun theta =>
    i ∈ residualSecantPetalAgreement family residual theta

/-- Every distinguished-petal coordinate is used by at most three surviving
regular outsiders. -/
theorem residualPetalCoordinateFiber_card_le_three_of_six_le_secant_core
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
    (i : I) :
    (residualPetalCoordinateFiber family residual i).card ≤ 3 := by
  by_contra hnot
  have hfour : 3 < (residualPetalCoordinateFiber family residual i).card := by omega
  obtain ⟨theta0, theta1, theta2, theta3,
      htheta0, htheta1, htheta2, htheta3,
      h01, h02, h03, h12, h13, h23⟩ :=
    Finset.three_lt_card_iff.mp hfour
  simp only [residualPetalCoordinateFiber, Finset.mem_filter] at htheta0
  simp only [residualPetalCoordinateFiber, Finset.mem_filter] at htheta1
  simp only [residualPetalCoordinateFiber, Finset.mem_filter] at htheta2
  simp only [residualPetalCoordinateFiber, Finset.mem_filter] at htheta3
  have htheta2On := third_mem_pointsOn_secant_of_common_petal_coordinate
    family hn residual htheta0.1 htheta1.1 htheta2.1 h01 h02
      htheta0.2 htheta1.2 htheta2.2
  have htheta3On := third_mem_pointsOn_secant_of_common_petal_coordinate
    family hn residual htheta0.1 htheta1.1 htheta3.1 h01 h03
      htheta0.2 htheta1.2 htheta3.2
  exact not_four_offResidualSecant_collinear_of_six_le_secant_core
    family hn hthreshold residual hsix
      htheta0.1 htheta1.1 htheta2.1 htheta3.1
      h01 h02 h03 h12 h13 h23 htheta2On htheta3On

/-- **Population bound for the three-hole cells.**  Every survivor uses
three of the five distinguished-petal coordinates, while each coordinate is
used by at most three survivors. -/
theorem regularOffResidualSecant_card_le_five_of_six_le_secant_core
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
    (regularOffResidualSecant family residual).card ≤ 5 := by
  let O := regularOffResidualSecant family residual
  let P := secantPetal family residual.source residual.gamma residual.beta
  let A : F → Finset I := fun theta =>
    residualSecantPetalAgreement family residual theta
  let Fib : I → Finset F := fun i => residualPetalCoordinateFiber family residual i
  have hPcard : P.card = 5 := by
    simpa only [P] using residualSecantPetal_card residual
  have hAdata : ∀ theta ∈ O, A theta ⊆ P ∧ (A theta).card = 3 := by
    intro theta htheta
    have hdata := offResidualSecant_two_triple_data
      family hn residual (by simpa only [O] using htheta)
    exact ⟨by simpa only [A, P] using hdata.2.2.1,
      by simpa only [A] using hdata.2.2.2⟩
  have hFib : ∀ i, (Fib i).card ≤ 3 := by
    intro i
    simpa only [Fib] using
      residualPetalCoordinateFiber_card_le_three_of_six_le_secant_core
        family hn hthreshold residual hsix i
  have hswap : (∑ theta ∈ O, (A theta).card) =
      ∑ i ∈ P, (Fib i).card := by
    calc
      (∑ theta ∈ O, (A theta).card) =
          ∑ theta ∈ O, ∑ i ∈ P, if i ∈ A theta then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro theta htheta
        have heq : P.filter (fun i => i ∈ A theta) = A theta := by
          ext i
          constructor
          · intro hi
            exact (Finset.mem_filter.mp hi).2
          · intro hi
            exact Finset.mem_filter.mpr ⟨(hAdata theta htheta).1 hi, hi⟩
        rw [← Finset.card_filter]
        rw [heq]
      _ = ∑ i ∈ P, ∑ theta ∈ O, if i ∈ A theta then 1 else 0 :=
        Finset.sum_comm
      _ = ∑ i ∈ P, (Fib i).card := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [show Fib i = O.filter (fun theta => i ∈ A theta) by rfl,
          Finset.card_filter]
  have hleft : (∑ theta ∈ O, (A theta).card) = O.card * 3 := by
    calc
      (∑ theta ∈ O, (A theta).card) = ∑ _theta ∈ O, 3 := by
        exact Finset.sum_congr rfl fun theta htheta => (hAdata theta htheta).2
      _ = O.card * 3 := by simp
  have hright : (∑ i ∈ P, (Fib i).card) ≤ P.card * 3 := by
    calc
      (∑ i ∈ P, (Fib i).card) ≤ ∑ _i ∈ P, 3 :=
        Finset.sum_le_sum fun i _hi => hFib i
      _ = P.card * 3 := by simp
  rw [← hswap, hleft, hPcard] at hright
  change O.card ≤ 5
  omega

/-- Each three-hole cross-secant cell leaves four or five regular outsiders off the
distinguished secant. -/
theorem regularOffResidualSecant_card_four_five_of_six_le_secant_core
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
    4 ≤ (regularOffResidualSecant family residual).card ∧
      (regularOffResidualSecant family residual).card ≤ 5 := by
  exact ⟨four_le_regularOffResidualSecant_card family hn hthreshold residual,
    regularOffResidualSecant_card_le_five_of_six_le_secant_core
      family hn hthreshold residual hsix⟩

#print axioms no_four_fixed_intersection_triple_pairs
#print axioms offResidualSecant_affine_plane_normal_form
#print axioms offResidualSecant_two_triple_data
#print axioms not_four_offResidualSecant_collinear_of_six_le_secant_core
#print axioms residualPetalCoordinateFiber_card_le_three_of_six_le_secant_core
#print axioms regularOffResidualSecant_card_le_five_of_six_le_secant_core
#print axioms regularOffResidualSecant_card_four_five_of_six_le_secant_core

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSevenCoreOverlapTwo
