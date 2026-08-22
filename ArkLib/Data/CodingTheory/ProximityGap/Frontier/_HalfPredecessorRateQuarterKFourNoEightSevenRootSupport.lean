/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourNoEightSyndromeReduction

/-!
# Rate-quarter no-eight seven-core: root/support coupling for every outsider

The bare punctured `RS[9,4]` quotient statement remembers only that every
source outsider has a representative of weight at most three.  The actual
no-eight residual retains more information.  For a size-seven source, the
canonical missed support in the nine-coordinate complement satisfies

```text
  missed coordinates <= roots inside the source core <= 3.
```

Thus the top weight-three stratum is exactly regular: six fresh agreements,
three source roots, and nine total agreements.  Its residual is a nonzero
scalar multiple of the cubic locator of those roots.  Every nonregular
outsider belongs to the long stratum and misses at most two complement
coordinates.  This dichotomy is the source-coupled replacement for the false
bare twelve-point syndrome-line bound; it does not itself count either
stratum.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSyndrome
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSyndromeReduction

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenRootSupport

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Coordinates in the source complement missed by the canonical residual
representative of an arbitrary outsider. -/
noncomputable def sourceSevenMissedSet
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (line : LineParameter F) (gamma : F) : Finset I :=
  sourceComplement family line \ sourceFreshAgreement family line gamma

/-- For a size-seven source, the missed support is no larger than the
residual root block inside the source core. -/
theorem sourceSeven_missed_card_le_root_card
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F}
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 7)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line) :
    (sourceSevenMissedSet family line gamma).card ≤
      (overlapRootBlock dom (u 0) (u 1) gamma
        (family.q gamma) line).card := by
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
  have hVcard : V.card = 9 := by
    simpa only [V] using
      sourceComplement_card_eq_nine_of_source_seven family hn line hsource
  have hmissedCard : (sourceSevenMissedSet family line gamma).card =
      V.card - Fresh.card := by
    rw [sourceSevenMissedSet, Finset.card_sdiff_of_subset hFreshSub]
  rw [hmissedCard, hVcard]
  change 9 - Fresh.card ≤ T.card
  apply Nat.sub_le_iff_le_add.mpr
  calc
    9 ≤ A.card := hAcard
    _ = Fresh.card + T.card := hsplit.symm
    _ = T.card + Fresh.card := Nat.add_comm _ _

/-- An off-source degree-below-four residual has at most three roots inside
the source core. -/
theorem sourceSeven_root_card_le_three
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

/-- The source/root tradeoff recovers the canonical weight-three bound. -/
theorem sourceSeven_missed_card_le_three
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 7)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line) :
    (sourceSevenMissedSet family line gamma).card ≤ 3 := by
  exact (sourceSeven_missed_card_le_root_card
    family hn hthreshold hsource hgamma).trans
      (sourceSeven_root_card_le_three family hthreshold hline hgamma)

/-- Saturating missed support three forces the exact regular
`(fresh, roots, full) = (6,3,9)` stratum. -/
theorem sourceSeven_missed_three_saturation
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 7)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line)
    (hmiss : (sourceSevenMissedSet family line gamma).card = 3) :
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
  have htrade := sourceSeven_missed_card_le_root_card
    family hn hthreshold hsource hgamma
  have hroot := sourceSeven_root_card_le_three
    family hthreshold hline hgamma
  have hTcard : T.card = 3 := by
    have htrade' : (sourceSevenMissedSet family line gamma).card ≤ T.card := by
      simpa only [T] using htrade
    have hroot' : T.card ≤ 3 := by simpa only [T] using hroot
    omega
  have hFreshSub : Fresh ⊆ V := by
    simpa only [Fresh, V, sourceComplement] using
      sourceFreshAgreement_subset_coreComplement family line gamma
  have hVcard : V.card = 9 := by
    simpa only [V] using
      sourceComplement_card_eq_nine_of_source_seven family hn line hsource
  have hFreshCardLe : Fresh.card ≤ 9 := by
    have hle := Finset.card_le_card hFreshSub
    omega
  have hmissedCard : (sourceSevenMissedSet family line gamma).card =
      V.card - Fresh.card := by
    rw [sourceSevenMissedSet, Finset.card_sdiff_of_subset hFreshSub]
  have hFreshCard : Fresh.card = 6 := by omega
  have hsplit : Fresh.card + T.card = A.card := by
    simpa only [Fresh, T, A, D, sourceFreshAgreement,
      overlapRootBlock] using
      Finset.card_sdiff_add_card_inter A D
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fresh] using hFreshCard
  · simpa only [T] using hTcard
  · simpa only [A] using (show A.card = 9 by omega)

/-- Missed support three is a regular outsider. -/
theorem mem_regularOutsideLine_of_sourceSeven_missed_three
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 7)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line)
    (hmiss : (sourceSevenMissedSet family line gamma).card = 3) :
    gamma ∈ regularOutsideLine family line := by
  have hsaturation := sourceSeven_missed_three_saturation
    family hn hthreshold hline hsource hgamma hmiss
  simp only [regularOutsideLine, Finset.mem_filter]
  exact ⟨hgamma, hsaturation.1, hsaturation.2.2,
    by simpa only [overlapRootBlock] using hsaturation.2.1⟩

/-- A saturated source-seven outsider carries its source-root cubic locator,
not an arbitrary weight-three quotient representative. -/
theorem sourceSeven_missed_three_residual_factorization
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 7)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line)
    (hmiss : (sourceSevenMissedSet family line gamma).card = 3) :
    ∃ c : F, c ≠ 0 ∧
      lineResidual (family.q gamma) gamma line =
        C c * domainRootProduct dom
          (overlapRootBlock dom (u 0) (u 1) gamma
            (family.q gamma) line) := by
  have hregular := mem_regularOutsideLine_of_sourceSeven_missed_three
    family hn hthreshold hline hsource hgamma hmiss
  obtain ⟨c, hc, hfactor⟩ :=
    regular_residual_factorization family hline hregular
  refine ⟨c, hc, ?_⟩
  simpa only [regularRootTriple, overlapRootBlock] using hfactor

/-- Every source-seven outsider is either in the regular cubic stratum or
misses at most two complement coordinates.  The latter alternative contains
all long types. -/
theorem sourceSeven_regular_or_missed_card_le_two
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    {line : LineParameter F} (hline : line ∈ lineParameters family)
    (hsource :
      (jointCore dom (u 0) (u 1) line.1 line.2).card = 7)
    {gamma : F} (hgamma : gamma ∈ outsideLine family line) :
    gamma ∈ regularOutsideLine family line ∨
      (sourceSevenMissedSet family line gamma).card ≤ 2 := by
  have hle := sourceSeven_missed_card_le_three
    family hn hthreshold hline hsource hgamma
  by_cases hthree : (sourceSevenMissedSet family line gamma).card = 3
  · exact Or.inl (mem_regularOutsideLine_of_sourceSeven_missed_three
      family hn hthreshold hline hsource hgamma hthree)
  · exact Or.inr (by omega)

/-- **All-outsider residual pair law.**  For two distinct outsiders from a
size-seven no-eight source, the global core-seven cap forces
`2 + |root intersection| <= |missed union|`.  Unlike the regular-signature
specialization, this statement also covers every long type. -/
theorem two_add_root_inter_le_missed_union_of_noEight_source_seven
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : NoEightCoreIntermediateResidual family)
    (hsource :
      (jointCore dom (u 0) (u 1)
        residual.source.1 residual.source.2).card = 7)
    {gamma beta : F}
    (hgamma : gamma ∈ outsideLine family residual.source)
    (hbeta : beta ∈ outsideLine family residual.source)
    (hne : gamma ≠ beta) :
    2 +
        ((overlapRootBlock dom (u 0) (u 1) gamma
            (family.q gamma) residual.source) ∩
          (overlapRootBlock dom (u 0) (u 1) beta
            (family.q beta) residual.source)).card ≤
      ((sourceSevenMissedSet family residual.source gamma) ∪
        (sourceSevenMissedSet family residual.source beta)).card := by
  let D := jointCore dom (u 0) (u 1)
    residual.source.1 residual.source.2
  let V := sourceComplement family residual.source
  let line2 := secantParameter family gamma beta
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let Tg := overlapRootBlock dom (u 0) (u 1) gamma
    (family.q gamma) residual.source
  let Tb := overlapRootBlock dom (u 0) (u 1) beta
    (family.q beta) residual.source
  let Sg := sourceFreshAgreement family residual.source gamma
  let Sb := sourceFreshAgreement family residual.source beta
  let Eg := sourceSevenMissedSet family residual.source gamma
  let Eb := sourceSevenMissedSet family residual.source beta
  have hgammaData :=
    (mem_outsideLine_iff family residual.source gamma).mp hgamma
  have hbetaData :=
    (mem_outsideLine_iff family residual.source beta).mp hbeta
  have hline2 : line2 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family
      hgammaData.1 hbetaData.1 hne
  have hgammaOn : gamma ∈ pointsOn family line2 :=
    first_point_mem_pointsOn_secant family hgammaData.1
  have hbetaOn : beta ∈ pointsOn family line2 :=
    second_point_mem_pointsOn_secant family hbetaData.1 hne
  have hgammaEq := (mem_pointsOn_iff family line2 gamma).mp hgammaOn |>.2
  have hbetaEq := (mem_pointsOn_iff family line2 beta).mp hbetaOn |>.2
  have hcoreEq :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          fullAgreement dom (u 0) (u 1) beta (family.q beta) = D2 := by
    dsimp only [D2]
    rw [hgammaEq, hbetaEq]
    exact fullAgreement_inter_eq_jointCore
      dom (u 0) (u 1) line2.1 line2.2 hne
  have hD2cap : D2.card ≤ 7 := by
    simpa only [D2] using residual.global_core_cap line2 hline2
  have hrootEq : Tg ∩ Tb = D2 ∩ D := by
    rw [← hcoreEq]
    ext i
    simp only [Tg, Tb, overlapRootBlock, D, Finset.mem_inter]
    tauto
  have hfreshEq : Sg ∩ Sb = D2 \ D := by
    rw [← hcoreEq]
    ext i
    simp only [Sg, Sb, sourceFreshAgreement, D,
      Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hVcard : V.card = 9 := by
    simpa only [V] using
      sourceComplement_card_eq_nine_of_source_seven
        family hn residual.source hsource
  have hSgSub : Sg ⊆ V := by
    simpa only [Sg, V, sourceComplement] using
      sourceFreshAgreement_subset_coreComplement
        family residual.source gamma
  have hSbSub : Sb ⊆ V := by
    simpa only [Sb, V, sourceComplement] using
      sourceFreshAgreement_subset_coreComplement
        family residual.source beta
  have hEg : Eg = V \ Sg := rfl
  have hEb : Eb = V \ Sb := rfl
  have hSg : Sg = V \ Eg := by
    rw [hEg]
    ext i
    simp only [Finset.mem_sdiff]
    constructor
    · intro hi
      exact ⟨hSgSub hi, fun hnot ↦ hnot.2 hi⟩
    · rintro ⟨hiV, hi⟩
      by_contra hiSg
      exact hi ⟨hiV, hiSg⟩
  have hSb : Sb = V \ Eb := by
    rw [hEb]
    ext i
    simp only [Finset.mem_sdiff]
    constructor
    · intro hi
      exact ⟨hSbSub hi, fun hnot ↦ hnot.2 hi⟩
    · rintro ⟨hiV, hi⟩
      by_contra hiSb
      exact hi ⟨hiV, hiSb⟩
  have hEunionSub : Eg ∪ Eb ⊆ V := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (Finset.mem_sdiff.mp (hEg ▸ hi)).1
    · exact (Finset.mem_sdiff.mp (hEb ▸ hi)).1
  have hfreshComplement : Sg ∩ Sb = V \ (Eg ∪ Eb) := by
    rw [hSg, hSb]
    ext i
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hfreshCard : (Sg ∩ Sb).card = 9 - (Eg ∪ Eb).card := by
    rw [hfreshComplement,
      Finset.card_sdiff_of_subset hEunionSub, hVcard]
  have hsplit := Finset.card_sdiff_add_card_inter D2 D
  have hsplit' : (D2 \ D).card + (D2 ∩ D).card = D2.card := by
    simpa only [Finset.inter_comm D D2] using hsplit
  change 2 + (Tg ∩ Tb).card ≤ (Eg ∪ Eb).card
  rw [hrootEq]
  rw [hfreshEq] at hfreshCard
  omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenRootSupport

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourNoEightSevenRootSupport
#print axioms sourceSeven_missed_card_le_root_card
#print axioms sourceSeven_missed_three_saturation
#print axioms sourceSeven_missed_three_residual_factorization
#print axioms sourceSeven_regular_or_missed_card_le_two
#print axioms two_add_root_inter_le_missed_union_of_noEight_source_seven
