/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourUniqueCoreSyndrome
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourCompactEdgeCollinearity

/-!
# Rate-quarter `n = 16`, `k = 4`: dependent-syndrome collapse

This file treats the dependent-row branch of the punctured syndrome
reduction.  A specialized syndrome witness retains the fact that its two
endpoints are exactly the regular outsider's missed edge.  If the quotient
row span avoids every coordinate column, its dimension is at most one, and
the MDS chord-uniqueness theorem forces all regular outsiders to have the
same missed edge.  If it contains a coordinate column, every missed edge is
incident to that column instead.

In either case any three missed edges cover at most four coordinates, leaving
at least four common fresh coordinates.  Compact-edge collinearity puts every
regular decoded point on the secant through two fixed regular points.
Fresh-fibre packing forces that second line to have an eight-core,
contradicting uniqueness of the source core.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial Module Submodule
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfRadiusEvenThirdBlockObstruction
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSyndromeChordBound
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourWeightTwoSyndrome
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSyndrome
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourCompactEdgeCollinearity

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourDependentSyndromeCollapse

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-! ## A missed-edge-aware syndrome witness -/

/-- A regular syndrome witness retaining its concrete missed edge and the
nonvanishing of the represented affine quotient point. -/
structure RegularMissedEdgeRepresentation
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (gamma : F) where
  left : ↑(sourceComplement family line)
  right : ↑(sourceComplement family line)
  left_ne_right : left ≠ right
  leftCoeff : F
  rightCoeff : F
  leftCoeff_ne_zero : leftCoeff ≠ 0
  rightCoeff_ne_zero : rightCoeff ≠ 0
  syndrome :
    quotientAffinePoint
        (sourceComplementCode family line)
        (sourceComplementRow0 family line)
        (sourceComplementRow1 family line) gamma =
      leftCoeff • quotientColumn (sourceComplementCode family line) left +
        rightCoeff • quotientColumn (sourceComplementCode family line) right
  endpoint_pair :
    ({left.1, right.1} : Finset I) = regularMissedEdge family line gamma
  syndrome_ne_zero :
    quotientAffinePoint
        (sourceComplementCode family line)
        (sourceComplementRow0 family line)
        (sourceComplementRow1 family line) gamma ≠ 0

/-- The concrete regular residual gives a nonzero quotient chord whose
endpoint pair is exactly its missed edge. -/
theorem regular_missedEdgeSyndromeRepresentation
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    {gamma : F} (hgamma : gamma ∈ regularOutsideLine family line) :
    Nonempty (RegularMissedEdgeRepresentation family line gamma) := by
  classical
  let V := sourceComplement family line
  let domV := sourceComplementDomain family line
  let C0 := sourceComplementCode family line
  let v0 := sourceComplementRow0 family line
  let v1 := sourceComplementRow1 family line
  let T := regularRootTriple family line gamma
  let E := regularMissedEdge family line gamma
  obtain ⟨c, _hc, hfactor⟩ :=
    regular_residual_factorization family hline hgamma
  let p : F[X] := C c * domainRootProduct dom T
  let w : ↑V → F := fun i ↦ p.eval (dom i.1)
  let e : ↑V → F := v0 + gamma • v1 - w
  have hgammaData := hgamma
  simp only [regularOutsideLine, Finset.mem_filter] at hgammaData
  have hgammaOut :=
    (mem_outsideLine_iff family line gamma).mp hgammaData.1
  have hlineDeg := lineParameter_degree_lt family hline
  have hpdeg : p.natDegree < 4 := by
    dsimp only [p, T]
    rw [← hfactor]
    exact lineResidual_natDegree_lt
      (family.degree_lt gamma hgammaOut.1) hlineDeg.1 hlineDeg.2
  have hwC : w ∈ C0 := by
    apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval p hpdeg
    intro i
    rfl
  have hEcard : E.card = 2 := by
    simpa only [E] using
      (regular_signature_cardinalities family hn hcore hgamma).2
  obtain ⟨left0, right0, hlr, hEeq⟩ := Finset.card_eq_two.mp hEcard
  have hEsubV : E ⊆ V := by
    simpa only [E, V, regularMissedEdge, sourceComplement] using
      (Finset.sdiff_subset :
        (sourceComplement family line \
          sourceFreshAgreement family line gamma) ⊆
            sourceComplement family line)
  let left : ↑V := ⟨left0, hEsubV (by simp [hEeq])⟩
  let right : ↑V := ⟨right0, hEsubV (by simp [hEeq])⟩
  have hleftRight : left ≠ right := by
    intro heq
    apply hlr
    exact congrArg Subtype.val heq
  have heZero : ∀ i : ↑V, i ≠ left → i ≠ right → e i = 0 := by
    intro i hiLeft hiRight
    have hiLeft0 : i.1 ≠ left0 := by
      intro heq
      apply hiLeft
      exact Subtype.ext heq
    have hiRight0 : i.1 ≠ right0 := by
      intro heq
      apply hiRight
      exact Subtype.ext heq
    have hiNotE : i.1 ∉ E := by
      rw [hEeq]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hiFresh : i.1 ∈ sourceFreshAgreement family line gamma := by
      by_contra hiNotFresh
      apply hiNotE
      exact Finset.mem_sdiff.mpr ⟨i.2, hiNotFresh⟩
    have hrow := regular_affine_row_on_fresh
      family line gamma c hfactor hiFresh
    change
      (u 0 i.1 - line.1.eval (dom i.1)) +
          gamma * (u 1 i.1 - line.2.eval (dom i.1)) -
        (C c * domainRootProduct dom T).eval (dom i.1) = 0
    simpa only [T, eval_mul, eval_C, sub_eq_zero] using hrow
  have heSupport :
      e = e left • (Pi.single left (1 : F) : ↑V → F) +
        e right • (Pi.single right (1 : F) : ↑V → F) := by
    ext i
    by_cases hiLeft : i = left
    · subst i
      simp [hleftRight]
    · by_cases hiRight : i = right
      · subst i
        simp [hiLeft]
      · have hzero := heZero i hiLeft hiRight
        simp [hiLeft, hiRight, hzero]
  have hsyndrome :
      quotientAffinePoint C0 v0 v1 gamma =
        e left • quotientColumn C0 left +
          e right • quotientColumn C0 right := by
    have hwZero : C0.mkQ w = 0 :=
      (Submodule.Quotient.mk_eq_zero C0).mpr hwC
    calc
      quotientAffinePoint C0 v0 v1 gamma = C0.mkQ e := by
        simp only [quotientAffinePoint, e, map_sub, map_add, map_smul,
          hwZero, sub_zero]
      _ = C0.mkQ
          (e left • (Pi.single left (1 : F) : ↑V → F) +
            e right • (Pi.single right (1 : F) : ↑V → F)) := by
        exact congrArg C0.mkQ heSupport
      _ = e left • quotientColumn C0 left +
            e right • quotientColumn C0 right := by
        simp only [map_add, map_smul, quotientColumn]
  have heNe_of_mem (i : ↑V) (hiE : i.1 ∈ E) : e i ≠ 0 := by
    intro hei
    have hiNotFresh : i.1 ∉ sourceFreshAgreement family line gamma :=
      (Finset.mem_sdiff.mp hiE).2
    apply hiNotFresh
    apply mem_sourceFreshAgreement_of_affine_row
      family line gamma c hfactor i.2
    change
      (u 0 i.1 - line.1.eval (dom i.1)) +
          gamma * (u 1 i.1 - line.2.eval (dom i.1)) -
        (C c * domainRootProduct dom T).eval (dom i.1) = 0 at hei
    simpa only [eval_mul, eval_C, T, sub_eq_zero] using hei
  have heLeftNe : e left ≠ 0 :=
    heNe_of_mem left (by simp [hEeq, left])
  have heRightNe : e right ≠ 0 :=
    heNe_of_mem right (by simp [hEeq, right])
  have hVcard : Fintype.card ↑V = 8 := by
    rw [Fintype.card_coe]
    simp only [V, sourceComplement, Finset.card_sdiff,
      Finset.inter_univ, Finset.card_univ, hn, hcore]
  have hsyndromeNe : quotientAffinePoint C0 v0 v1 gamma ≠ 0 := by
    intro hzero
    have haffineC : v0 + gamma • v1 ∈ C0 := by
      apply (Submodule.Quotient.mk_eq_zero C0).mp
      simpa only [map_add, map_smul, quotientAffinePoint] using hzero
    have heC : e ∈ C0 := by
      exact C0.sub_mem haffineC hwC
    have heWeight : Code.wt e ≤ 4 := by
      have hsupport :
          Finset.univ.filter (fun i : ↑V ↦ e i ≠ 0) ⊆
            ({left, right} : Finset ↑V) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_contra hipair
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hipair
        exact hi (heZero i hipair.1 hipair.2)
      have hcard := Finset.card_le_card hsupport
      unfold Code.wt
      exact hcard.trans (by
        rcases Finset.card_pair_eq_one_or_two (a := left) (b := right) with h | h
        · omega
        · omega)
    have heEqZero := reedSolomon_eight_four_noSparseCodeword
      domV hVcard e heC heWeight
    have heLeftZero : e left = 0 := congrFun heEqZero left
    have hleftE : left0 ∈ E := by simp [hEeq]
    have hleftNotFresh : left0 ∉
        sourceFreshAgreement family line gamma :=
      (Finset.mem_sdiff.mp hleftE).2
    apply hleftNotFresh
    apply mem_sourceFreshAgreement_of_affine_row
      family line gamma c hfactor left.2
    change
      (u 0 left0 - line.1.eval (dom left0)) +
          gamma * (u 1 left0 - line.2.eval (dom left0)) =
        c * (domainRootProduct dom T).eval (dom left0)
    change
      (u 0 left0 - line.1.eval (dom left0)) +
          gamma * (u 1 left0 - line.2.eval (dom left0)) -
        (C c * domainRootProduct dom T).eval (dom left0) = 0 at heLeftZero
    simpa only [eval_mul, eval_C, T, sub_eq_zero] using heLeftZero
  refine ⟨{
    left := left
    right := right
    left_ne_right := hleftRight
    leftCoeff := e left
    rightCoeff := e right
    leftCoeff_ne_zero := heLeftNe
    rightCoeff_ne_zero := heRightNe
    syndrome := ?_
    endpoint_pair := ?_
    syndrome_ne_zero := ?_ }⟩
  · simpa only [C0, v0, v1] using hsyndrome
  · simpa only [left, right, E] using hEeq.symm
  · simpa only [C0, v0, v1] using hsyndromeNe

/-! ## One-dimensional row spans have one missed edge -/

/-- Failure of quotient-row independence makes the span of the two row
classes at most one-dimensional. -/
theorem rowPlane_finrank_le_one_of_not_independent
    {J : Type} [Fintype J] [DecidableEq J]
    (C : Submodule F (J → F)) (v0 v1 : J → F)
    (hdep : ¬ QuotientRowsIndependent C v0 v1) :
    finrank F (span F ({C.mkQ v0, C.mkQ v1} :
      Set ((J → F) ⧸ C))) ≤ 1 := by
  classical
  rw [QuotientRowsIndependent] at hdep
  push Not at hdep
  obtain ⟨a, b, hrel, hnontrivial⟩ := hdep
  let x := C.mkQ v0
  let y := C.mkQ v1
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      exact hnontrivial ha hb
    subst a
    simp only [zero_smul, zero_add] at hrel
    have hy : y = 0 := by
      exact (smul_eq_zero.mp hrel).resolve_left hb
    have hsub : span F ({x, y} : Set ((J → F) ⧸ C)) ≤
        span F ({x} : Set ((J → F) ⧸ C)) := by
      apply span_le.mpr
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact subset_span (by simp)
      · rw [hy]
        exact Submodule.zero_mem _
    have hmono := Submodule.finrank_mono hsub
    have hone : finrank F (span F ({x} : Set ((J → F) ⧸ C))) ≤ 1 := by
      by_cases hx0 : x = 0
      · rw [hx0]
        rw [Submodule.span_zero_singleton]
        simp
      · rw [finrank_span_singleton hx0]
    simpa only [x, y] using hmono.trans hone
  · have hx : x = -(a⁻¹ * b) • y := by
      have hax : a • x = -(b • y) :=
        eq_neg_of_add_eq_zero_left hrel
      calc
        x = a⁻¹ • (a • x) := by rw [inv_smul_smul₀ ha]
        _ = a⁻¹ • (-(b • y)) := by rw [hax]
        _ = -(a⁻¹ * b) • y := by
          simp only [smul_neg, smul_smul, neg_smul]
    have hsub : span F ({x, y} : Set ((J → F) ⧸ C)) ≤
        span F ({y} : Set ((J → F) ⧸ C)) := by
      apply span_le.mpr
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · rw [hx]
        exact smul_mem _ _ (subset_span (by simp))
      · exact subset_span (by simp)
    have hmono := Submodule.finrank_mono hsub
    have hone : finrank F (span F ({y} : Set ((J → F) ⧸ C))) ≤ 1 := by
      by_cases hy0 : y = 0
      · rw [hy0]
        rw [Submodule.span_zero_singleton]
        simp
      · rw [finrank_span_singleton hy0]
    simpa only [x, y] using hmono.trans hone

/-- A nonzero vector in a submodule of dimension at most one spans that
submodule. -/
theorem le_span_singleton_of_mem_of_finrank_le_one
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (P : Submodule F V) (x : V)
    (hP : finrank F P ≤ 1) (hxP : x ∈ P) (hxNe : x ≠ 0) :
    P ≤ span F ({x} : Set V) := by
  let xP : P := ⟨x, hxP⟩
  have hxPNe : xP ≠ 0 := by
    intro hzero
    apply hxNe
    have hcoe := congrArg Subtype.val hzero
    simpa only [xP, Submodule.coe_zero] using hcoe
  have hPpos : 0 < finrank F P :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨xP, hxPNe⟩
  have hPone : finrank F P = 1 := by omega
  intro y hy
  let yP : P := ⟨y, hy⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hPone hxPNe yP
  have hcVal : c • x = y := congrArg Subtype.val hc
  rw [← hcVal]
  exact smul_mem _ c (subset_span (by simp))

/-- If a one-dimensional syndrome subspace contains a frame column, every
MDS chord meeting the subspace is incident to that column. -/
theorem endpoint_mem_of_column_mem_of_finrank_le_one_of_chordMeets
    {V J : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Fintype J] [DecidableEq J]
    (P : Submodule F V) (v : J → V)
    (hP : finrank F P ≤ 1)
    (hMDS4 : IndependentUpTo (F := F) v 4)
    (key : J) (hkey : v key ∈ P)
    {left right : J} (hchord : ChordMeets P v left right) :
    key = left ∨ key = right := by
  classical
  have hkeyNe : v key ≠ 0 := by
    have hsingle := hMDS4 ({key} : Finset J) (by simp)
    simpa using hsingle.ne_zero ⟨key, by simp⟩
  let S : Finset J := {key}
  let C : Finset J := {left, right}
  have hPS : P ≤ columnSpan (F := F) v S := by
    have hraw := le_span_singleton_of_mem_of_finrank_le_one
      P (v key) hP hkey hkeyNe
    simpa only [S, columnSpan, Finset.coe_singleton,
      Set.image_singleton] using hraw
  have hPC : P ≤ columnSpan (F := F) v C := by
    have hraw := le_pairSpan_of_finrank_le_one_of_chordMeets
      P v hP hchord
    simpa only [C, columnSpan, Finset.coe_insert, Finset.coe_singleton,
      Set.image_pair] using hraw
  by_contra hnot
  have hkeyLeft : key ≠ left := fun h ↦ hnot (Or.inl h)
  have hkeyRight : key ≠ right := fun h ↦ hnot (Or.inr h)
  have hunionCard : (S ∪ C).card ≤ 4 := by
    exact (Finset.card_union_le S C).trans (by
      simp only [S, C, Finset.card_singleton]
      rcases Finset.card_pair_eq_one_or_two (a := left) (b := right) with h | h <;>
        omega)
  have hLI' := hMDS4 (S ∪ C) hunionCard
  have hLI : LinearIndepOn F v (((S ∪ C : Finset J) : Set J)) := by
    simpa only [LinearIndepOn] using hLI'
  have hcommon : P ≤ columnSpan (F := F) v (S ∩ C) :=
    sharedSubmodule_le_commonSpan v S C P hLI hPS hPC
  have hinter : S ∩ C = ∅ := by
    ext j
    simp only [S, C, Finset.mem_inter, Finset.mem_singleton,
      Finset.mem_insert, Finset.notMem_empty]
    constructor
    · rintro ⟨rfl, h | h⟩
      · exact (hkeyLeft h).elim
      · exact (hkeyRight h).elim
    · intro h
      exact h.elim
  have hkeyCommon := hcommon hkey
  rw [hinter] at hkeyCommon
  have hkeyZero : v key = 0 := by
    simpa only [columnSpan, Finset.coe_empty, Set.image_empty,
      Submodule.span_empty, Submodule.mem_bot] using hkeyCommon
  exact hkeyNe hkeyZero

/-- The missed-edge-aware regular witness is a genuine chord meeting the
quotient row span. -/
theorem RegularMissedEdgeRepresentation.chordMeets
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    {family : BadScalarRichPointFamily dom 4 delta u}
    {line : LineParameter F} {gamma : F}
    (rep : RegularMissedEdgeRepresentation family line gamma) :
    ChordMeets
      (span F ({
        (sourceComplementCode family line).mkQ
          (sourceComplementRow0 family line),
        (sourceComplementCode family line).mkQ
          (sourceComplementRow1 family line)} :
          Set ((↑(sourceComplement family line) → F) ⧸
            sourceComplementCode family line)))
      (quotientColumn (sourceComplementCode family line))
      rep.left rep.right := by
  refine ⟨rep.left_ne_right, rep.leftCoeff, rep.rightCoeff, ?_, ?_⟩
  · rw [← rep.syndrome]
    exact rep.syndrome_ne_zero
  · rw [← rep.syndrome]
    exact quotientAffinePoint_mem_rowPlane
      (sourceComplementCode family line)
      (sourceComplementRow0 family line)
      (sourceComplementRow1 family line) gamma

/-! ## Dependent regular signatures are compact -/

/-- If the two quotient rows are dependent, any three regular outsiders have
missed-edge union of size at most four.  With a contained quotient column the
three edges form a star; without one, chord uniqueness makes all three edges
equal. -/
theorem three_regular_missedUnion_card_le_four_of_rows_dependent
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    (hdep : ¬ QuotientRowsIndependent
      (sourceComplementCode family line)
      (sourceComplementRow0 family line)
      (sourceComplementRow1 family line))
    {gamma1 gamma2 gamma3 : F}
    (hgamma1 : gamma1 ∈ regularOutsideLine family line)
    (hgamma2 : gamma2 ∈ regularOutsideLine family line)
    (hgamma3 : gamma3 ∈ regularOutsideLine family line) :
    (regularMissedEdge family line gamma1 ∪
      regularMissedEdge family line gamma2 ∪
      regularMissedEdge family line gamma3).card ≤ 4 := by
  classical
  let V := sourceComplement family line
  let domV := sourceComplementDomain family line
  let C0 := sourceComplementCode family line
  let v0 := sourceComplementRow0 family line
  let v1 := sourceComplementRow1 family line
  let P := span F ({C0.mkQ v0, C0.mkQ v1} :
    Set ((↑V → F) ⧸ C0))
  let col : ↑V → ((↑V → F) ⧸ C0) := quotientColumn C0
  let E1 := regularMissedEdge family line gamma1
  let E2 := regularMissedEdge family line gamma2
  let E3 := regularMissedEdge family line gamma3
  let rep1 := Classical.choice
    (regular_missedEdgeSyndromeRepresentation
      family hn hline hcore hgamma1)
  let rep2 := Classical.choice
    (regular_missedEdgeSyndromeRepresentation
      family hn hline hcore hgamma2)
  let rep3 := Classical.choice
    (regular_missedEdgeSyndromeRepresentation
      family hn hline hcore hgamma3)
  have hVcard : Fintype.card ↑V = 8 := by
    rw [Fintype.card_coe]
    simp only [V, sourceComplement, Finset.card_sdiff,
      Finset.inter_univ, Finset.card_univ, hn, hcore]
  have hMDS4 : IndependentUpTo (F := F) col 4 := by
    simpa only [col, C0, sourceComplementCode, domV] using
      reedSolomon_eight_four_quotientColumns_independentUpTo_four
        domV hVcard
  have hPdim : finrank F P ≤ 1 := by
    simpa only [P, C0, v0, v1] using
      rowPlane_finrank_le_one_of_not_independent
        (sourceComplementCode family line)
        (sourceComplementRow0 family line)
        (sourceComplementRow1 family line) hdep
  have hchord1 : ChordMeets P col rep1.left rep1.right := by
    simpa only [P, col, C0, v0, v1, V] using rep1.chordMeets
  have hchord2 : ChordMeets P col rep2.left rep2.right := by
    simpa only [P, col, C0, v0, v1, V] using rep2.chordMeets
  have hchord3 : ChordMeets P col rep3.left rep3.right := by
    simpa only [P, col, C0, v0, v1, V] using rep3.chordMeets
  have hE1card : E1.card = 2 := by
    simpa only [E1] using
      (regular_signature_cardinalities family hn hcore hgamma1).2
  have hE2card : E2.card = 2 := by
    simpa only [E2] using
      (regular_signature_cardinalities family hn hcore hgamma2).2
  have hE3card : E3.card = 2 := by
    simpa only [E3] using
      (regular_signature_cardinalities family hn hcore hgamma3).2
  by_cases hcolumn : ∃ key : ↑V, col key ∈ P
  · obtain ⟨key, hkey⟩ := hcolumn
    have hkey1 := endpoint_mem_of_column_mem_of_finrank_le_one_of_chordMeets
      P col hPdim hMDS4 key hkey hchord1
    have hkey2 := endpoint_mem_of_column_mem_of_finrank_le_one_of_chordMeets
      P col hPdim hMDS4 key hkey hchord2
    have hkey3 := endpoint_mem_of_column_mem_of_finrank_le_one_of_chordMeets
      P col hPdim hMDS4 key hkey hchord3
    have hkeyE1 : key.1 ∈ E1 := by
      change key.1 ∈ regularMissedEdge family line gamma1
      rw [← rep1.endpoint_pair]
      rcases hkey1 with h | h
      · simp [h]
      · simp [h]
    have hkeyE2 : key.1 ∈ E2 := by
      change key.1 ∈ regularMissedEdge family line gamma2
      rw [← rep2.endpoint_pair]
      rcases hkey2 with h | h
      · simp [h]
      · simp [h]
    have hkeyE3 : key.1 ∈ E3 := by
      change key.1 ∈ regularMissedEdge family line gamma3
      rw [← rep3.endpoint_pair]
      rcases hkey3 with h | h
      · simp [h]
      · simp [h]
    simpa only [E1, E2, E3] using
      three_pairs_union_card_le_four_of_common_mem
        E1 E2 E3 key.1 hE1card hE2card hE3card
          hkeyE1 hkeyE2 hkeyE3
  · have hnoColumn : ∀ i : ↑V, col i ∉ P := by
      simpa only [not_exists] using hcolumn
    have hp12 := pair_eq_of_chordMeets_of_finrank_le_one
      P col hPdim hMDS4 hnoColumn hchord1 hchord2
    have hp13 := pair_eq_of_chordMeets_of_finrank_le_one
      P col hPdim hMDS4 hnoColumn hchord1 hchord3
    have hp12Val := congrArg
      (fun S : Finset ↑V ↦ S.image Subtype.val) hp12
    have hp13Val := congrArg
      (fun S : Finset ↑V ↦ S.image Subtype.val) hp13
    have hE12 : E1 = E2 := by
      calc
        E1 = {rep1.left.1, rep1.right.1} := rep1.endpoint_pair.symm
        _ = {rep2.left.1, rep2.right.1} := by
          simpa only [Finset.image_insert, Finset.image_singleton] using hp12Val
        _ = E2 := rep2.endpoint_pair
    have hE13 : E1 = E3 := by
      calc
        E1 = {rep1.left.1, rep1.right.1} := rep1.endpoint_pair.symm
        _ = {rep3.left.1, rep3.right.1} := by
          simpa only [Finset.image_insert, Finset.image_singleton] using hp13Val
        _ = E3 := rep3.endpoint_pair
    change (E1 ∪ E2 ∪ E3).card ≤ 4
    rw [← hE12, ← hE13, Finset.union_self, Finset.union_self,
      hE1card]
    omega

/-- **Dependent-row branch closed.**  The punctured quotient rows of a
unique-eight-core residual are independent.  Dependence would make every
triple of regular missed edges compact; compact-edge collinearity and line
packing then contradict uniqueness of the source eight-core. -/
theorem uniqueEightCoreResidual_quotientRowsIndependent
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (residual : UniqueEightCoreResidual family) :
    QuotientRowsIndependent
      (sourceComplementCode family residual.source)
      (sourceComplementRow0 family residual.source)
      (sourceComplementRow1 family residual.source) := by
  classical
  by_contra hdep
  have htwo : 1 <
      (regularOutsideLine family residual.source).card := by
    have height := residual.eight_regular_outsiders
    omega
  obtain ⟨gamma, hgamma, beta, hbeta, hne⟩ :=
    Finset.one_lt_card.mp htwo
  apply uniqueEightCoreResidual_false_of_compact_missed_edges
    family hn hthreshold residual hgamma hbeta hne
  intro theta htheta
  exact three_regular_missedUnion_card_le_four_of_rows_dependent
    family hn residual.source_mem residual.source_core_card hdep
      hgamma hbeta htheta

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourDependentSyndromeCollapse

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourDependentSyndromeCollapse
#print axioms regular_missedEdgeSyndromeRepresentation
#print axioms rowPlane_finrank_le_one_of_not_independent
#print axioms endpoint_mem_of_column_mem_of_finrank_le_one_of_chordMeets
#print axioms three_regular_missedUnion_card_le_four_of_rows_dependent
#print axioms uniqueEightCoreResidual_quotientRowsIndependent
