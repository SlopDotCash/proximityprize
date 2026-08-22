/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourUniqueCoreSyndrome

/-!
# Rate-quarter `n = 16`, `k = 4`: sparse syndrome reduction for no-eight cores

The no-eight residual has a direct punctured-syndrome form which does not
require an exact regular-signature stratum.  Puncture at its six- or
seven-coordinate source core and subtract the source decoded line.  Every
source outsider has at least six fresh agreements.  Its residual polynomial
has degree below four, so it is a word of the punctured Reed--Solomon code;
the remaining quotient representative is supported only where those fresh
agreements fail.

Consequently every counterexample in the no-eight branch has one of two
forms:

* a size-seven source gives at least thirteen selected parameters on the
  affine quotient pencil for `RS[9,4]`, each of coset weight at most three;
* a size-six source gives at least fourteen selected parameters on the
  affine quotient pencil for `RS[10,4]`, each of coset weight at most four.

This is a reduction, not a closure.  A bare cardinal bound for weight-three
points on an MDS syndrome line is not available; a closing argument must use
the coupling between these sparse representatives and their source-core
root polynomials (or an equally strong Reed--Solomon-specific constraint).
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourLongOutsiderCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourWeightTwoSyndrome
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSyndrome

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSyndromeReduction

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- A quotient class has a representative supported on at most `t`
coordinates. -/
def QuotientCosetWeightAtMost
    {J : Type} [Fintype J] [DecidableEq J]
    (C : Submodule F (J → F)) (x : (J → F) ⧸ C) (t : Nat) : Prop :=
  ∃ e : J → F, x = C.mkQ e ∧
    ((Finset.univ.filter fun i ↦ e i ≠ 0).card ≤ t)

/-- Every outsider from an arbitrary relevant source has a quotient
representative supported on at most `|source complement| - 6` coordinates.
The bound uses only threshold nine and the degree-three off-line root cap. -/
theorem outside_quotientCosetWeightAtMost_complement_sub_six
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line) :
    QuotientCosetWeightAtMost
      (sourceComplementCode family line)
      (quotientAffinePoint
        (sourceComplementCode family line)
        (sourceComplementRow0 family line)
        (sourceComplementRow1 family line) gamma)
      ((sourceComplement family line).card - 6) := by
  classical
  let V := sourceComplement family line
  let domV := sourceComplementDomain family line
  let C0 := sourceComplementCode family line
  let v0 := sourceComplementRow0 family line
  let v1 := sourceComplementRow1 family line
  let p := lineResidual (family.q gamma) gamma line
  let w : ↑V → F := fun i ↦ p.eval (dom i.1)
  let e : ↑V → F := v0 + gamma • v1 - w
  let S : Finset ↑V := Finset.univ.filter fun i ↦ e i ≠ 0
  let Fresh := sourceFreshAgreement family line gamma
  have hgammaData := (mem_outsideLine_iff family line gamma).mp hgamma
  have hlineDeg := lineParameter_degree_lt family hline
  have hpdeg : p.natDegree < 4 := by
    exact lineResidual_natDegree_lt
      (family.degree_lt gamma hgammaData.1) hlineDeg.1 hlineDeg.2
  have hwC : w ∈ C0 := by
    apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval p hpdeg
    intro i
    rfl
  have hFreshLower : 6 ≤ Fresh.card := by
    simpa only [Fresh] using
      (six_le_fresh_and_core_inter_le_three_of_outside
        family hthreshold hline hgamma).1
  have hFreshSub : Fresh ⊆ V := by
    simpa only [Fresh, V, sourceComplement] using
      sourceFreshAgreement_subset_coreComplement family line gamma
  have heZero (i : ↑V) (hi : i.1 ∈ Fresh) : e i = 0 := by
    have hiFresh : i.1 ∈ sourceFreshAgreement family line gamma := by
      simpa only [Fresh] using hi
    have hiAgree := (Finset.mem_sdiff.mp hiFresh).1
    simp only [fullAgreement, Finset.mem_filter, Finset.mem_univ,
      true_and] at hiAgree
    change
      (u 0 i.1 - line.1.eval (dom i.1)) +
          gamma * (u 1 i.1 - line.2.eval (dom i.1)) -
        (lineResidual (family.q gamma) gamma line).eval (dom i.1) = 0
    simp only [lineResidual, eval_sub, eval_add, eval_mul, eval_C]
    rw [hiAgree]
    ring
  let valEmbedding : ↑V ↪ I :=
    ⟨fun i ↦ i.1, fun _ _ h ↦ Subtype.ext h⟩
  have hmapSub : S.map valEmbedding ⊆ V \ Fresh := by
    intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have hjNe : e j ≠ 0 := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    exact Finset.mem_sdiff.mpr ⟨j.2, fun hjFresh ↦ hjNe (heZero j hjFresh)⟩
  have hScard : S.card ≤ (V \ Fresh).card := by
    calc
      S.card = (S.map valEmbedding).card := by rw [Finset.card_map]
      _ ≤ (V \ Fresh).card := Finset.card_le_card hmapSub
  have hmissedCard : (V \ Fresh).card = V.card - Fresh.card :=
    Finset.card_sdiff_of_subset hFreshSub
  have hsupport : S.card ≤ V.card - 6 := by
    rw [hmissedCard] at hScard
    omega
  refine ⟨e, ?_, by simpa only [S] using hsupport⟩
  have hwZero : C0.mkQ w = 0 :=
    (Submodule.Quotient.mk_eq_zero C0).mpr hwC
  calc
    quotientAffinePoint C0 v0 v1 gamma = C0.mkQ e := by
      simp only [quotientAffinePoint, e, map_sub, map_add, map_smul,
        hwZero, sub_zero]
    _ = (sourceComplementCode family line).mkQ e := by rfl

/-- A size-seven source has a nine-coordinate complement. -/
theorem sourceComplement_card_eq_nine_of_source_seven
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16) (line : LineParameter F)
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 7) :
    (sourceComplement family line).card = 9 := by
  simp only [sourceComplement, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_univ, hn, hsource]

/-- A size-six source has a ten-coordinate complement. -/
theorem sourceComplement_card_eq_ten_of_source_six
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16) (line : LineParameter F)
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 6) :
    (sourceComplement family line).card = 10 := by
  simp only [sourceComplement, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_univ, hn, hsource]

/-- In a counterexample, a size-seven relevant source has at least thirteen
selected outsiders. -/
theorem thirteen_le_outsideLine_card_of_source_seven
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (hcard : 16 < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 7) :
    13 ≤ (outsideLine family line).card := by
  have hpack := pointsOn_card_mul_max_add_core_le family hline
  rw [hthreshold, hsource, hn] at hpack
  norm_num at hpack
  have hpartition := pointsOn_card_add_outsideLine_card family line
  omega

/-- In a counterexample, a size-six relevant source has at least fourteen
selected outsiders. -/
theorem fourteen_le_outsideLine_card_of_source_six
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (hcard : 16 < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 6) :
    14 ≤ (outsideLine family line).card := by
  have hpack := pointsOn_card_mul_max_add_core_le family hline
  rw [hthreshold, hsource, hn] at hpack
  norm_num at hpack
  have hpartition := pointsOn_card_add_outsideLine_card family line
  omega

/-- **Sparse-syndrome form of the complete no-eight residual.**  The source
size determines a large affine family of weight-at-most-three or
weight-at-most-four quotient classes. -/
theorem noEight_sparse_syndrome_dichotomy
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9)
    (hcard : 16 < family.G.card)
    (residual : NoEightCoreIntermediateResidual family) :
    ((jointCore dom (u 0) (u 1)
          residual.source.1 residual.source.2).card = 7 ∧
      13 ≤ (outsideLine family residual.source).card ∧
      ∀ gamma ∈ outsideLine family residual.source,
        QuotientCosetWeightAtMost
          (sourceComplementCode family residual.source)
          (quotientAffinePoint
            (sourceComplementCode family residual.source)
            (sourceComplementRow0 family residual.source)
            (sourceComplementRow1 family residual.source) gamma) 3) ∨
    ((jointCore dom (u 0) (u 1)
          residual.source.1 residual.source.2).card = 6 ∧
      14 ≤ (outsideLine family residual.source).card ∧
      ∀ gamma ∈ outsideLine family residual.source,
        QuotientCosetWeightAtMost
          (sourceComplementCode family residual.source)
          (quotientAffinePoint
            (sourceComplementCode family residual.source)
            (sourceComplementRow0 family residual.source)
            (sourceComplementRow1 family residual.source) gamma) 4) := by
  rcases residual.source_core_card with hsourceSix | hsourceSeven
  · apply Or.inr
    refine ⟨hsourceSix,
      fourteen_le_outsideLine_card_of_source_six
        family hn hthreshold hcard residual.source_mem hsourceSix, ?_⟩
    intro gamma hgamma
    have hweight :=
      outside_quotientCosetWeightAtMost_complement_sub_six
        family hthreshold.ge residual.source_mem hgamma
    rw [sourceComplement_card_eq_ten_of_source_six
      family hn residual.source hsourceSix] at hweight
    norm_num at hweight ⊢
    exact hweight
  · apply Or.inl
    refine ⟨hsourceSeven,
      thirteen_le_outsideLine_card_of_source_seven
        family hn hthreshold hcard residual.source_mem hsourceSeven, ?_⟩
    intro gamma hgamma
    have hweight :=
      outside_quotientCosetWeightAtMost_complement_sub_six
        family hthreshold.ge residual.source_mem hgamma
    rw [sourceComplement_card_eq_nine_of_source_seven
      family hn residual.source hsourceSeven] at hweight
    norm_num at hweight ⊢
    exact hweight

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSyndromeReduction

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSyndromeReduction
#print axioms outside_quotientCosetWeightAtMost_complement_sub_six
#print axioms thirteen_le_outsideLine_card_of_source_seven
#print axioms fourteen_le_outsideLine_card_of_source_six
#print axioms noEight_sparse_syndrome_dichotomy
