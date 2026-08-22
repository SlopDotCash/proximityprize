/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourNoEightSyndromeReduction

/-!
# Rate-quarter `n = 16`, `k = 4`: source-six root/support coupling

The size-six branch of the no-eight reduction punctures at a ten-coordinate
source complement.  A source outsider has a degree-below-four residual
polynomial.  Its roots inside the source core and its missed coordinates
outside the source core are not independent:

```text
  missed outside coordinates <= source-core roots + 1.
```

The off-line root cap is three, so this recovers the weight-at-most-four
bound while retaining the information discarded by a bare quotient-weight
statement.  In the saturated weight-four case there are exactly three
source-core roots, exactly six fresh agreements, and exactly nine total
agreements.  The residual polynomial is consequently a nonzero scalar
multiple of the cubic locator of that root triple.

This is the source-polynomial coupling needed by any closing argument for
the `RS[10,4]` quotient branch.  It does not assert the still-open global
bound of thirteen selected quotient points.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourRegularSignatureRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSyndrome
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSyndromeReduction

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSixRootSupport

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Coordinates in the source complement at which an outsider does not
have a fresh agreement.  This is the support of the canonical residual
representative used in the punctured-syndrome reduction. -/
noncomputable def sourceMissedSet
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (gamma : F) : Finset I :=
  sourceComplement family line \ sourceFreshAgreement family line gamma

/-- Once the residual has been factored through its source-core root
locator, missed support is exactly failure of the corresponding affine-row
equation.  This records equality of supports, rather than only an upper
bound on their cardinalities. -/
theorem mem_sourceMissedSet_iff_affine_row_ne_of_factorization
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (gamma c : F)
    (hfactor :
      lineResidual (family.q gamma) gamma line =
        C c * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma
            (family.q gamma) line))
    {i : I} (hiV : i ∈ sourceComplement family line) :
    i ∈ sourceMissedSet family line gamma ↔
      (u 0 i - line.1.eval (dom i)) +
          gamma * (u 1 i - line.2.eval (dom i)) ≠
        c * (domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma
            (family.q gamma) line)).eval (dom i) := by
  have hfactor' :
      lineResidual (family.q gamma) gamma line =
        C c * domainRootProduct dom
          (regularRootTriple family line gamma) := by
    simpa only [regularRootTriple, overlapRootBlock] using hfactor
  constructor
  · intro hi hrow
    have hiData := Finset.mem_sdiff.mp hi
    have hiFresh := mem_sourceFreshAgreement_of_affine_row
      family line gamma c hfactor'
        (by simpa only [sourceComplement] using hiV)
        (by simpa only [regularRootTriple, overlapRootBlock] using hrow)
    exact hiData.2 hiFresh
  · intro hrow
    apply Finset.mem_sdiff.mpr
    refine ⟨hiV, ?_⟩
    intro hiFresh
    have hrow' := regular_affine_row_on_fresh
      family line gamma c hfactor' hiFresh
    exact hrow
      (by simpa only [regularRootTriple, overlapRootBlock] using hrow')

/-- For a size-six source, the missed support is at most one larger than
the residual's root block inside the source core. -/
theorem sourceSix_missed_card_le_root_card_add_one
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F}
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 6)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line) :
    (sourceMissedSet family line gamma).card ≤
      (overlapRootBlock dom (u 0) (u 1) gamma
        (family.q gamma) line).card + 1 := by
  let A := fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V := sourceComplement family line
  let Fresh := sourceFreshAgreement family line gamma
  let T := overlapRootBlock dom (u 0) (u 1) gamma
    (family.q gamma) line
  have hgammaData := (mem_outsideLine_iff family line gamma).mp hgamma
  have hAcard : 9 ≤ A.card := by
    simpa only [A] using
      hthreshold.trans (family.threshold_le gamma hgammaData.1)
  have hsplit : Fresh.card + T.card = A.card := by
    simpa only [Fresh, T, A, D, sourceFreshAgreement,
      overlapRootBlock] using
      Finset.card_sdiff_add_card_inter A D
  have hFreshSub : Fresh ⊆ V := by
    simpa only [Fresh, V, sourceComplement] using
      sourceFreshAgreement_subset_coreComplement family line gamma
  have hVcard : V.card = 10 := by
    simpa only [V] using
      sourceComplement_card_eq_ten_of_source_six family hn line hsource
  have hmissedCard : (sourceMissedSet family line gamma).card =
      V.card - Fresh.card := by
    rw [sourceMissedSet, Finset.card_sdiff_of_subset hFreshSub]
  have hbound : (sourceMissedSet family line gamma).card ≤
      T.card + 1 := by
    rw [hmissedCard, hVcard]
    omega
  simpa only [T] using hbound

/-- An off-line degree-below-four residual has at most three roots in the
source core. -/
theorem sourceSix_root_card_le_three
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line) :
    (overlapRootBlock dom (u 0) (u 1) gamma
      (family.q gamma) line).card ≤ 3 := by
  simpa only [overlapRootBlock] using
    (six_le_fresh_and_core_inter_le_three_of_outside
      family hthreshold hline hgamma).2

/-- The source/root tradeoff implies the canonical missed support has size
at most four. -/
theorem sourceSix_missed_card_le_four
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 6)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line) :
    (sourceMissedSet family line gamma).card ≤ 4 := by
  have htrade := sourceSix_missed_card_le_root_card_add_one
    family hn hthreshold hsource hgamma
  have hroot := sourceSix_root_card_le_three
    family hthreshold hline hgamma
  omega

/-- Saturating the weight-four bound forces equality everywhere in the
threshold/root/support count. -/
theorem sourceSix_weight_four_saturation
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 6)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line)
    (hmiss : (sourceMissedSet family line gamma).card = 4) :
    (sourceFreshAgreement family line gamma).card = 6 ∧
      (overlapRootBlock dom (u 0) (u 1) gamma
        (family.q gamma) line).card = 3 ∧
      (fullAgreement dom (u 0) (u 1) gamma
        (family.q gamma)).card = 9 := by
  let A := fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let D := jointCore dom (u 0) (u 1) line.1 line.2
  let V := sourceComplement family line
  let Fresh := sourceFreshAgreement family line gamma
  let T := overlapRootBlock dom (u 0) (u 1) gamma
    (family.q gamma) line
  have htrade := sourceSix_missed_card_le_root_card_add_one
    family hn hthreshold hsource hgamma
  have hroot := sourceSix_root_card_le_three
    family hthreshold hline hgamma
  have hTcard : T.card = 3 := by
    have htrade' : (sourceMissedSet family line gamma).card ≤
        T.card + 1 := by
      simpa only [T] using htrade
    have hroot' : T.card ≤ 3 := by
      simpa only [T] using hroot
    omega
  have hFreshSub : Fresh ⊆ V := by
    simpa only [Fresh, V, sourceComplement] using
      sourceFreshAgreement_subset_coreComplement family line gamma
  have hVcard : V.card = 10 := by
    simpa only [V] using
      sourceComplement_card_eq_ten_of_source_six family hn line hsource
  have hmissedCard : (sourceMissedSet family line gamma).card =
      V.card - Fresh.card := by
    rw [sourceMissedSet, Finset.card_sdiff_of_subset hFreshSub]
  have hFreshCard : Fresh.card = 6 := by omega
  have hsplit : Fresh.card + T.card = A.card := by
    simpa only [Fresh, T, A, D, sourceFreshAgreement,
      overlapRootBlock] using
      Finset.card_sdiff_add_card_inter A D
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fresh] using hFreshCard
  · simpa only [T] using hTcard
  · simpa only [A] using (show A.card = 9 by omega)

/-- A weight-four source-six outsider has a cubic residual equal to a
nonzero scalar multiple of the locator of its three source-core roots. -/
theorem sourceSix_weight_four_residual_factorization
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 6)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line)
    (hmiss : (sourceMissedSet family line gamma).card = 4) :
    ∃ c : F, c ≠ 0 ∧
      (lineResidual (family.q gamma) gamma line).natDegree = 3 ∧
      lineResidual (family.q gamma) gamma line =
        C c * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma
            (family.q gamma) line) := by
  have hgammaData := (mem_outsideLine_iff family line gamma).mp hgamma
  have hp0 : lineResidual (family.q gamma) gamma line ≠ 0 := by
    simpa only [lineResidual, sub_ne_zero] using hgammaData.2
  have hlineDeg := lineParameter_degree_lt family hline
  have hpdeg :
      (lineResidual (family.q gamma) gamma line).natDegree < 4 :=
    lineResidual_natDegree_lt
      (family.degree_lt gamma hgammaData.1) hlineDeg.1 hlineDeg.2
  have hTcard :
      (overlapRootBlock dom (u 0) (u 1) gamma
        (family.q gamma) line).card = 4 - 1 := by
    simpa using
      (sourceSix_weight_four_saturation family hn hthreshold hline
        hsource hgamma hmiss).2.1
  have hroot : ∀ i ∈ overlapRootBlock dom (u 0) (u 1) gamma
      (family.q gamma) line,
      (lineResidual (family.q gamma) gamma line).eval (dom i) = 0 := by
    intro i hi
    exact lineResidual_eval_eq_zero_of_mem_overlapRootBlock
      dom (u 0) (u 1) gamma (family.q gamma) line hi
  have hfactor := factorization_of_domain_root_subset_card_eq_pred
    dom (k := 4) (by norm_num)
      (lineResidual (family.q gamma) gamma line) hp0 hpdeg
      (overlapRootBlock dom (u 0) (u 1) gamma
        (family.q gamma) line) hTcard hroot
  refine ⟨(lineResidual (family.q gamma) gamma line).leadingCoeff,
    hfactor.2.1, ?_, hfactor.2.2⟩
  simpa using hfactor.1

/-- The saturated source-six statement in support form: one cubic locator
and one nonzero scalar simultaneously determine the residual polynomial and
the exact four-coordinate failure support on the ten-coordinate puncture. -/
theorem sourceSix_weight_four_support_coupling
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 6)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line)
    (hmiss : (sourceMissedSet family line gamma).card = 4) :
    ∃ c : F, c ≠ 0 ∧
      (lineResidual (family.q gamma) gamma line).natDegree = 3 ∧
      lineResidual (family.q gamma) gamma line =
        C c * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma
            (family.q gamma) line) ∧
      ∀ i ∈ sourceComplement family line,
        (i ∈ sourceMissedSet family line gamma ↔
          (u 0 i - line.1.eval (dom i)) +
              gamma * (u 1 i - line.2.eval (dom i)) ≠
            c * (domainRootProduct dom
              (overlapRootBlock dom (u 0) (u 1) gamma
                (family.q gamma) line)).eval (dom i)) := by
  obtain ⟨c, hc, hdeg, hfactor⟩ :=
    sourceSix_weight_four_residual_factorization
      family hn hthreshold hline hsource hgamma hmiss
  refine ⟨c, hc, hdeg, hfactor, ?_⟩
  intro i hiV
  exact mem_sourceMissedSet_iff_affine_row_ne_of_factorization
    family line gamma c hfactor hiV

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSixRootSupport

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSixRootSupport
#print axioms sourceSix_missed_card_le_root_card_add_one
#print axioms sourceSix_weight_four_saturation
#print axioms sourceSix_weight_four_residual_factorization
#print axioms sourceSix_weight_four_support_coupling
