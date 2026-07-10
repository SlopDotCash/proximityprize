/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourUniqueCoreSignatures
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourWeightTwoSyndrome

/-!
# Rate-quarter `n = 16`, `k = 4`: unique-core syndrome reduction

Restrict the received rows to the eight coordinates outside a unique source
eight-core, after subtracting the source decoded line.  For a regular outsider
`gamma`, residual factorization supplies a cubic Reed--Solomon codeword.  The
received affine row agrees with that cubic on the six fresh coordinates, so
their difference is supported on the outsider's exact two-coordinate missed
edge.  Passing to the punctured `RS[8,4]` quotient therefore represents the
affine quotient point on the chord of the two missed-edge columns.

The strict seven-edge syndrome bound contradicts the eight regular outsiders
unless one of two genuine quotient degeneracies occurs: the two punctured
quotient rows are dependent, or their quotient plane contains a coordinate
column.  Thus the abstract eight-signature countermodel is not realizable in a
column-avoiding MDS syndrome plane.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

open Finset Polynomial Module Submodule
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfRadiusEvenThirdBlockObstruction
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSignatures
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSyndromeChordBound
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourWeightTwoSyndrome

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSyndrome

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The eight coordinates outside the source core. -/
noncomputable def sourceComplement
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) : Finset I :=
  Finset.univ \ jointCore dom (u 0) (u 1) line.1 line.2

/-- The original evaluation embedding restricted to the source complement. -/
noncomputable def sourceComplementDomain
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) : ↑(sourceComplement family line) ↪ F where
  toFun i := dom i.1
  inj' _ _ h := Subtype.ext (dom.injective h)

/-- First received row after subtracting the source-line intercept. -/
noncomputable def sourceComplementRow0
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) : ↑(sourceComplement family line) → F :=
  fun i ↦ u 0 i.1 - line.1.eval (dom i.1)

/-- Second received row after subtracting the source-line direction. -/
noncomputable def sourceComplementRow1
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) : ↑(sourceComplement family line) → F :=
  fun i ↦ u 1 i.1 - line.2.eval (dom i.1)

/-- The punctured `[8,4]` Reed--Solomon code on the source complement. -/
noncomputable def sourceComplementCode
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) :
    Submodule F (↑(sourceComplement family line) → F) :=
  ReedSolomon.code (sourceComplementDomain family line) 4

/-- A chosen nonzero two-column representation of one affine quotient point. -/
structure WeightTwoRepresentation
    {J : Type} [Fintype J] [DecidableEq J]
    (C : Submodule F (J → F)) (v0 v1 : J → F) (gamma : F) where
  left : J
  right : J
  left_ne_right : left ≠ right
  leftCoeff : F
  rightCoeff : F
  syndrome :
    quotientAffinePoint C v0 v1 gamma =
      leftCoeff • quotientColumn C left +
        rightCoeff • quotientColumn C right

/-- A version of the weight-two syndrome theorem accepting an existential
representation for each selected scalar. -/
theorem weightTwoSyndromeLine_card_le_of_representations
    {J : Type} [Fintype J] [Nonempty J] [DecidableEq J]
    (C : Submodule F (J → F)) (v0 v1 : J → F)
    (hrows : QuotientRowsIndependent C v0 v1)
    (hMDS4 : IndependentUpTo (F := F) (quotientColumn C) 4)
    (hnoColumn : ∀ i, quotientColumn C i ∉
      span F ({C.mkQ v0, C.mkQ v1} : Set ((J → F) ⧸ C)))
    (G : Finset F)
    (hrepr : ∀ gamma ∈ G,
      Nonempty (WeightTwoRepresentation C v0 v1 gamma)) :
    G.card ≤ Fintype.card J := by
  classical
  let rep (gamma : F) (hgamma : gamma ∈ G) :
      WeightTwoRepresentation C v0 v1 gamma :=
    Classical.choice (hrepr gamma hgamma)
  let fallback : J := Classical.choice (inferInstance : Nonempty J)
  let left : F → J := fun gamma ↦
    if hgamma : gamma ∈ G then (rep gamma hgamma).left else fallback
  let right : F → J := fun gamma ↦
    if hgamma : gamma ∈ G then (rep gamma hgamma).right else fallback
  let a : F → F := fun gamma ↦
    if hgamma : gamma ∈ G then (rep gamma hgamma).leftCoeff else 0
  let b : F → F := fun gamma ↦
    if hgamma : gamma ∈ G then (rep gamma hgamma).rightCoeff else 0
  apply weightTwoSyndromeLine_card_le
    C v0 v1 hrows hMDS4 hnoColumn G left right a b
  · intro gamma hgamma
    simp only [left, right, dif_pos hgamma]
    exact (rep gamma hgamma).left_ne_right
  · intro gamma hgamma
    simp only [left, right, a, b, dif_pos hgamma]
    exact (rep gamma hgamma).syndrome

/-- The strict seven-edge version for an eight-coordinate quotient frame. -/
theorem weightTwoSyndromeLine_card_le_seven_of_representations
    {J : Type} [Fintype J] [Nonempty J] [DecidableEq J]
    (C : Submodule F (J → F)) (v0 v1 : J → F)
    (hJ : Fintype.card J = 8)
    (hrows : QuotientRowsIndependent C v0 v1)
    (hMDS4 : IndependentUpTo (F := F) (quotientColumn C) 4)
    (hnoColumn : ∀ i, quotientColumn C i ∉
      span F ({C.mkQ v0, C.mkQ v1} : Set ((J → F) ⧸ C)))
    (G : Finset F)
    (hrepr : ∀ gamma ∈ G,
      Nonempty (WeightTwoRepresentation C v0 v1 gamma)) :
    G.card ≤ 7 := by
  classical
  let rep (gamma : F) (hgamma : gamma ∈ G) :
      WeightTwoRepresentation C v0 v1 gamma :=
    Classical.choice (hrepr gamma hgamma)
  let fallback : J := Classical.choice (inferInstance : Nonempty J)
  let left : F → J := fun gamma ↦
    if hgamma : gamma ∈ G then (rep gamma hgamma).left else fallback
  let right : F → J := fun gamma ↦
    if hgamma : gamma ∈ G then (rep gamma hgamma).right else fallback
  let a : F → F := fun gamma ↦
    if hgamma : gamma ∈ G then (rep gamma hgamma).leftCoeff else 0
  let b : F → F := fun gamma ↦
    if hgamma : gamma ∈ G then (rep gamma hgamma).rightCoeff else 0
  apply weightTwoSyndromeLine_card_le_seven
    C v0 v1 hJ hrows hMDS4 hnoColumn G left right a b
  · intro gamma hgamma
    simp only [left, right, dif_pos hgamma]
    exact (rep gamma hgamma).left_ne_right
  · intro gamma hgamma
    simp only [left, right, a, b, dif_pos hgamma]
    exact (rep gamma hgamma).syndrome

/-- A regular outsider gives an actual two-column syndrome on the punctured
source complement.  The subtracted word is the cubic residual from
`regular_residual_factorization`; no division by its locator is used. -/
theorem regular_weightTwoSyndromeRepresentation
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hcore :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 8)
    {gamma : F} (hgamma : gamma ∈ regularOutsideLine family line) :
    Nonempty (WeightTwoRepresentation
      (sourceComplementCode family line)
      (sourceComplementRow0 family line)
      (sourceComplementRow1 family line) gamma) := by
  classical
  let V := sourceComplement family line
  let domV := sourceComplementDomain family line
  let C0 := sourceComplementCode family line
  let v0 := sourceComplementRow0 family line
  let v1 := sourceComplementRow1 family line
  let T := regularRootTriple family line gamma
  let E := regularMissedEdge family line gamma
  obtain ⟨c, hc, hfactor⟩ :=
    regular_residual_factorization family hline hgamma
  let p : F[X] := C c * domainRootProduct dom T
  let w : ↑V → F := fun i ↦ p.eval (dom i.1)
  let e : ↑V → F := v0 + gamma • v1 - w
  have hgammaData := hgamma
  simp only [regularOutsideLine, Finset.mem_filter] at hgammaData
  have hgammaOut := (mem_outsideLine_iff family line gamma).mp hgammaData.1
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
      apply Subtype.ext
      exact heq
    have hiRight0 : i.1 ≠ right0 := by
      intro heq
      apply hiRight
      apply Subtype.ext
      exact heq
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
  refine ⟨{
    left := left
    right := right
    left_ne_right := hleftRight
    leftCoeff := e left
    rightCoeff := e right
    syndrome := ?_ }⟩
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

/-- The older non-strict chord bound would force the regular population to be
exactly eight.  The strict theorem below shows that these two quotient
hypotheses cannot in fact hold simultaneously for a unique-core residual. -/
theorem regularOutsideLine_card_eq_eight_of_quotient_generic
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    (hrows : QuotientRowsIndependent
      (sourceComplementCode family residual.source)
      (sourceComplementRow0 family residual.source)
      (sourceComplementRow1 family residual.source))
    (hnoColumn : ∀ i : ↑(sourceComplement family residual.source),
      quotientColumn (sourceComplementCode family residual.source) i ∉
        span F ({
          (sourceComplementCode family residual.source).mkQ
            (sourceComplementRow0 family residual.source),
          (sourceComplementCode family residual.source).mkQ
            (sourceComplementRow1 family residual.source)} :
              Set ((↑(sourceComplement family residual.source) → F) ⧸
                sourceComplementCode family residual.source))) :
    (regularOutsideLine family residual.source).card = 8 := by
  classical
  let V := sourceComplement family residual.source
  let domV := sourceComplementDomain family residual.source
  let C0 := sourceComplementCode family residual.source
  let v0 := sourceComplementRow0 family residual.source
  let v1 := sourceComplementRow1 family residual.source
  let G := regularOutsideLine family residual.source
  have hVcard : Fintype.card ↑V = 8 := by
    rw [Fintype.card_coe]
    simp only [V, sourceComplement, Finset.card_sdiff,
      Finset.inter_univ, Finset.card_univ, hn,
      residual.source_core_card]
  haveI : Nonempty ↑V := by
    apply Finset.Nonempty.to_subtype
    apply Finset.card_pos.mp
    rw [← Fintype.card_coe]
    omega
  have hrows' : QuotientRowsIndependent C0 v0 v1 := by
    simpa only [C0, v0, v1] using hrows
  have hnoColumn' : ∀ i : ↑V, quotientColumn C0 i ∉
      span F ({C0.mkQ v0, C0.mkQ v1} : Set ((↑V → F) ⧸ C0)) := by
    simpa only [V, C0, v0, v1] using hnoColumn
  have hMDS4 : IndependentUpTo (F := F) (quotientColumn C0) 4 := by
    simpa only [C0, sourceComplementCode, domV] using
      reedSolomon_eight_four_quotientColumns_independentUpTo_four
        domV hVcard
  have hrepr : ∀ gamma ∈ G,
      Nonempty (WeightTwoRepresentation C0 v0 v1 gamma) := by
    intro gamma hgamma
    simpa only [G, C0, v0, v1] using
      regular_weightTwoSyndromeRepresentation
        family hn residual.source_mem residual.source_core_card hgamma
  have hupper : G.card ≤ 8 := by
    have hbound := weightTwoSyndromeLine_card_le_of_representations
      C0 v0 v1 hrows' hMDS4 hnoColumn' G hrepr
    change G.card ≤ Fintype.card ↑V at hbound
    rw [hVcard] at hbound
    exact hbound
  have hlower : 8 ≤ G.card := by
    simpa only [G] using residual.eight_regular_outsiders
  simpa only [G] using Nat.le_antisymm hupper hlower

/-- The intermediate non-strict quotient trichotomy.  It is strictly sharpened
to the two degeneracy branches below. -/
theorem regularOutsideLine_card_eq_eight_or_quotient_degenerate
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family) :
    (regularOutsideLine family residual.source).card = 8 ∨
      ¬ QuotientRowsIndependent
        (sourceComplementCode family residual.source)
        (sourceComplementRow0 family residual.source)
        (sourceComplementRow1 family residual.source) ∨
      ∃ i : ↑(sourceComplement family residual.source),
        quotientColumn (sourceComplementCode family residual.source) i ∈
          span F ({
            (sourceComplementCode family residual.source).mkQ
              (sourceComplementRow0 family residual.source),
            (sourceComplementCode family residual.source).mkQ
              (sourceComplementRow1 family residual.source)} :
              Set ((↑(sourceComplement family residual.source) → F) ⧸
                sourceComplementCode family residual.source)) := by
  classical
  let V := sourceComplement family residual.source
  let domV := sourceComplementDomain family residual.source
  let C0 := sourceComplementCode family residual.source
  let v0 := sourceComplementRow0 family residual.source
  let v1 := sourceComplementRow1 family residual.source
  let G := regularOutsideLine family residual.source
  have hVcard : Fintype.card ↑V = 8 := by
    rw [Fintype.card_coe]
    simp only [V, sourceComplement, Finset.card_sdiff,
      Finset.inter_univ, Finset.card_univ, hn,
      residual.source_core_card]
  haveI : Nonempty ↑V := by
    apply Finset.Nonempty.to_subtype
    apply Finset.card_pos.mp
    rw [← Fintype.card_coe]
    omega
  by_cases hrows : QuotientRowsIndependent C0 v0 v1
  · by_cases hcolumn : ∃ i : ↑V, quotientColumn C0 i ∈
        span F ({C0.mkQ v0, C0.mkQ v1} : Set ((↑V → F) ⧸ C0))
    · exact Or.inr (Or.inr (by
        simpa only [V, C0, v0, v1] using hcolumn))
    · have hnoColumn : ∀ i : ↑V, quotientColumn C0 i ∉
          span F ({C0.mkQ v0, C0.mkQ v1} : Set ((↑V → F) ⧸ C0)) := by
        simpa only [not_exists] using hcolumn
      have hMDS4 : IndependentUpTo (F := F) (quotientColumn C0) 4 := by
        simpa only [C0, sourceComplementCode, domV] using
          reedSolomon_eight_four_quotientColumns_independentUpTo_four
            domV hVcard
      have hrepr : ∀ gamma ∈ G,
          Nonempty (WeightTwoRepresentation C0 v0 v1 gamma) := by
        intro gamma hgamma
        simpa only [G, C0, v0, v1] using
          regular_weightTwoSyndromeRepresentation
            family hn residual.source_mem residual.source_core_card hgamma
      have hupper : G.card ≤ 8 := by
        have hbound := weightTwoSyndromeLine_card_le_of_representations
          C0 v0 v1 hrows hMDS4 hnoColumn G hrepr
        change G.card ≤ Fintype.card ↑V at hbound
        rw [hVcard] at hbound
        exact hbound
      have hlower : 8 ≤ G.card := by
        simpa only [G] using residual.eight_regular_outsiders
      exact Or.inl (by simpa only [G] using Nat.le_antisymm hupper hlower)
  · exact Or.inr (Or.inl (by simpa only [C0, v0, v1] using hrows))

/-- **The nondegenerate unique-core syndrome branch is impossible.**

The punctured quotient rows must be dependent, or their plane contains a
coordinate column.  Otherwise the strict syndrome-chord theorem gives at most
seven regular outsiders, contradicting the eight outsiders carried by the
unique-core residual. -/
theorem uniqueEightCoreResidual_quotient_degenerate
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family) :
    ¬ QuotientRowsIndependent
        (sourceComplementCode family residual.source)
        (sourceComplementRow0 family residual.source)
        (sourceComplementRow1 family residual.source) ∨
      ∃ i : ↑(sourceComplement family residual.source),
        quotientColumn (sourceComplementCode family residual.source) i ∈
          span F ({
            (sourceComplementCode family residual.source).mkQ
              (sourceComplementRow0 family residual.source),
            (sourceComplementCode family residual.source).mkQ
              (sourceComplementRow1 family residual.source)} :
              Set ((↑(sourceComplement family residual.source) → F) ⧸
                sourceComplementCode family residual.source)) := by
  classical
  let V := sourceComplement family residual.source
  let domV := sourceComplementDomain family residual.source
  let C0 := sourceComplementCode family residual.source
  let v0 := sourceComplementRow0 family residual.source
  let v1 := sourceComplementRow1 family residual.source
  let G := regularOutsideLine family residual.source
  have hVcard : Fintype.card ↑V = 8 := by
    rw [Fintype.card_coe]
    simp only [V, sourceComplement, Finset.card_sdiff,
      Finset.inter_univ, Finset.card_univ, hn,
      residual.source_core_card]
  haveI : Nonempty ↑V := by
    apply Finset.Nonempty.to_subtype
    apply Finset.card_pos.mp
    rw [← Fintype.card_coe]
    omega
  by_cases hrows : QuotientRowsIndependent C0 v0 v1
  · apply Or.inr
    by_contra hcolumn
    have hnoColumn : ∀ i : ↑V, quotientColumn C0 i ∉
        span F ({C0.mkQ v0, C0.mkQ v1} : Set ((↑V → F) ⧸ C0)) := by
      simpa only [not_exists] using hcolumn
    have hMDS4 : IndependentUpTo (F := F) (quotientColumn C0) 4 := by
      simpa only [C0, sourceComplementCode, domV] using
        reedSolomon_eight_four_quotientColumns_independentUpTo_four
          domV hVcard
    have hrepr : ∀ gamma ∈ G,
        Nonempty (WeightTwoRepresentation C0 v0 v1 gamma) := by
      intro gamma hgamma
      simpa only [G, C0, v0, v1] using
        regular_weightTwoSyndromeRepresentation
          family hn residual.source_mem residual.source_core_card hgamma
    have hupper : G.card ≤ 7 :=
      weightTwoSyndromeLine_card_le_seven_of_representations
        C0 v0 v1 hVcard hrows hMDS4 hnoColumn G hrepr
    have hlower : 8 ≤ G.card := by
      simpa only [G] using residual.eight_regular_outsiders
    omega
  · exact Or.inl (by simpa only [C0, v0, v1] using hrows)

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSyndrome

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSyndrome
#print axioms weightTwoSyndromeLine_card_le_of_representations
#print axioms weightTwoSyndromeLine_card_le_seven_of_representations
#print axioms regular_weightTwoSyndromeRepresentation
#print axioms regularOutsideLine_card_eq_eight_of_quotient_generic
#print axioms regularOutsideLine_card_eq_eight_or_quotient_degenerate
#print axioms uniqueEightCoreResidual_quotient_degenerate
