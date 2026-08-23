/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDirectionCoreThirteenClosure
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSupportFourSafeLine

/-!
# Rate-quarter closure of the unsafe direction-core-twelve branch

Subtracting a degree-below-four direction polynomial with twelve fixed
coordinates leaves a direction supported on four coordinates.  If the
translated line is not zero-safe, an unsafe codeword has a fixed trace of
size at least nine.  Every distinct appearing codeword then has fixed trace
at most six.

The selected family consequently splits into one unsafe translated-word
fiber, the five-trace stratum, and the six-trace stratum.  These have sizes
at most four, four, and three.  The last bound is the new point: every
six-trace contains the three-coordinate complement of the unsafe trace, and
their remaining three-coordinate petals are disjoint inside nine points.

Thus direction core twelve can remain exceptional only in the zero-safe
support-four branch.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open _root_.ProximityGap.Ownership _root_.ProximityGap.SpikeFloor
open _root_.ProximityGap.LargeZeroWitnessSplit _root_.ProximityGap.LineListMCAWeld
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCapDichotomy
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterExceptionalDirectionPuncture
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSparseSafeLine
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportThreeSafeLine
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourSafeLine
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCoreThirteenClosure

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCoreTwelveUnsafe

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem directionSupportSet_translatedDirectionWord_card_eq_four
    (dom : Fin 16 ↪ F) (u1 : Fin 16 → F) (r : F[X])
    (hcore : (directionAgreement dom u1 r).card = 12) :
    (directionSupportSet (translatedDirectionWord dom u1 r)).card = 4 := by
  rw [directionSupportSet_translatedDirectionWord,
    Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, hcore]

theorem three_le_directionFreshTraceSubtype_of_trace_le_six
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) {gamma : F} (hgamma : gamma ∈ family.G)
    (htrace : (directionCoreTrace family r gamma).card ≤ 6) :
    3 ≤ (directionFreshTraceSubtype family r gamma).card := by
  let A := fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let D := directionAgreement dom (u 1) r
  have hA : 9 ≤ A.card := by
    have hlarge := family.threshold_le gamma hgamma
    simpa only [hthreshold, A] using hlarge
  have hsplit := Finset.card_sdiff_add_card_inter A D
  have hfresh := directionFreshTraceSubtype_card family r gamma
  change (directionFreshTraceSubtype family r gamma).card = (A \ D).card at hfresh
  change (A ∩ D).card ≤ 6 at htrace
  rw [hfresh]
  omega

theorem translatedInterceptWord_injective_of_trace_le_six
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hcore : (directionAgreement dom (u 1) r).card = 12)
    {gamma beta : F} (hgamma : gamma ∈ family.G)
    (hbeta : beta ∈ family.G)
    (hgammaTrace : (directionCoreTrace family r gamma).card ≤ 6)
    (hbetaTrace : (directionCoreTrace family r beta).card ≤ 6)
    (hword : translatedInterceptWord family r gamma =
      translatedInterceptWord family r beta) :
    gamma = beta := by
  by_contra hne
  let A := directionFreshTraceSubtype family r gamma
  let B := directionFreshTraceSubtype family r beta
  have hdisj : Disjoint A B := by
    simpa only [A, B] using
      directionFreshTraceSubtype_disjoint_of_word_eq_of_ne
        family r hne hword
  have hA : 3 ≤ A.card := by
    simpa only [A] using
      three_le_directionFreshTraceSubtype_of_trace_le_six
        family hthreshold r hgamma hgammaTrace
  have hB : 3 ≤ B.card := by
    simpa only [B] using
      three_le_directionFreshTraceSubtype_of_trace_le_six
        family hthreshold r hbeta hbetaTrace
  have hU : Fintype.card
      {i : Fin 16 // i ∉ directionAgreement dom (u 1) r} = 4 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_coe, Fintype.card_fin, hcore]
  have hunion : (A ∪ B).card ≤ 4 := by
    have hle := Finset.card_le_univ (A ∪ B)
    simpa only [Finset.card_univ, hU] using hle
  rw [Finset.card_union_of_disjoint hdisj] at hunion
  omega

theorem translatedWordFiber_card_le_four
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 12)
    (c : Fin 16 → F) :
    (translatedWordFiber family r c).card ≤ 4 := by
  let Gc := translatedWordFiber family r c
  let H := {i : Fin 16 // i ∉ directionAgreement dom (u 1) r}
  let pick : {gamma : F // gamma ∈ Gc} → H := fun gamma ↦
    Classical.choose (directionFreshTraceSubtype_nonempty family r hr
      (Finset.mem_filter.mp gamma.2).1)
  have hpickMem : ∀ gamma : {gamma : F // gamma ∈ Gc},
      pick gamma ∈ directionFreshTraceSubtype family r gamma.1 := by
    intro gamma
    exact Classical.choose_spec
      (directionFreshTraceSubtype_nonempty family r hr
        (Finset.mem_filter.mp gamma.2).1)
  have hinj : Function.Injective pick := by
    intro gamma beta hpick
    apply Subtype.ext
    have hgammaWord := (Finset.mem_filter.mp gamma.2).2
    have hbetaWord := (Finset.mem_filter.mp beta.2).2
    have hgammaFresh := hpickMem gamma
    have hbetaFresh : pick gamma ∈
        directionFreshTraceSubtype family r beta.1 := by
      simpa only [hpick] using hpickMem beta
    have hgammaFull : (pick gamma).1 ∈
        fullAgreement dom (u 0) (u 1) gamma.1 (family.q gamma.1) := by
      simpa only [directionFreshTraceSubtype, Finset.mem_filter,
        Finset.mem_univ, true_and] using hgammaFresh
    have hbetaFull : (pick gamma).1 ∈
        fullAgreement dom (u 0) (u 1) beta.1 (family.q beta.1) := by
      simpa only [directionFreshTraceSubtype, Finset.mem_filter,
        Finset.mem_univ, true_and] using hbetaFresh
    exact gamma_eq_of_translatedInterceptWord_eq_of_common_fresh
      family r (hgammaWord.trans hbetaWord.symm)
        hgammaFull hbetaFull (pick gamma).2
  have hcard := Fintype.card_le_of_injective pick hinj
  have hH : Fintype.card H = 4 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_coe, Fintype.card_fin, hcore]
  simpa only [Gc, H, Fintype.card_coe, hH] using hcard

theorem five_le_directionCoreTrace_of_core_twelve
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hcore : (directionAgreement dom (u 1) r).card = 12)
    {gamma : F} (hgamma : gamma ∈ family.G) :
    5 ≤ (directionCoreTrace family r gamma).card := by
  have hbudget := nine_add_direction_core_card_le_sixteen_add_trace_card
    family (by norm_num) (by rw [hthreshold]) r hgamma
  rw [hcore] at hbudget
  omega

theorem directionCoreTrace_card_le_six_of_unsafeCodeword_ne
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 12)
    (c0 : Fin 16 → F)
    (hc0 : c0 ∈ (rsCode dom 4 : Submodule F (Fin 16 → F)))
    (hzero : 9 ≤ (directionZeroAgreementSet c0 (u 0)
      (translatedDirectionWord dom (u 1) r)).card)
    {gamma : F} (hgamma : gamma ∈ family.G)
    (hne : translatedInterceptWord family r gamma ≠ c0) :
    (directionCoreTrace family r gamma).card ≤ 6 := by
  let v1 := translatedDirectionWord dom (u 1) r
  let c := translatedInterceptWord family r gamma
  let U := {i : Fin 16 // i ∈ directionZeroSet v1}
  let T : Finset U := zeroAgreementTrace c (u 0) v1
  let K : Finset U := zeroAgreementTrace c0 (u 0) v1
  have hU : Fintype.card U = 12 := by
    have hsupport : (directionSupportSet v1).card = 4 := by
      simpa only [v1] using
        directionSupportSet_translatedDirectionWord_card_eq_four
          dom (u 1) r hcore
    have hpartition := directionSupportSet_card_eq (n := 16) v1
    have hz : (directionZeroSet v1).card = 12 := by omega
    simpa only [U, Fintype.card_coe] using hz
  have hK : 9 ≤ K.card := by
    rw [show K.card = (directionZeroAgreementSet c0 (u 0) v1).card by
      simpa only [K] using zeroAgreementTrace_card c0 (u 0) v1]
    exact hzero
  have hcApp : c ∈ lineAppearingCodewords dom 4 9 (u 0) v1 := by
    simpa only [c, v1] using translatedInterceptWord_mem_lineAppearingCodewords
      family hthreshold r hr hgamma
  have hc0App : c0 ∈ lineAppearingCodewords dom 4 9 (u 0) v1 :=
    unsafeCodeword_mem_lineAppearingCodewords dom (u 0) v1 c0 hc0 hzero
  have hinter : (T ∩ K).card ≤ 3 := by
    simpa only [T, K, c] using
      zeroAgreementTrace_pair_card_le_three_of_appearing
        dom (u 0) v1 hcApp hc0App hne
  have hW : (Finset.univ \ K).card ≤ 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hU]
    omega
  have hdiffSub : T \ K ⊆ Finset.univ \ K := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hdiff : (T \ K).card ≤ 3 :=
    (Finset.card_le_card hdiffSub).trans hW
  have hsplit := Finset.card_sdiff_add_card_inter T K
  have hTtrace : T.card = (directionCoreTrace family r gamma).card := by
    calc
      T.card = (directionZeroAgreementSet c (u 0) v1).card := by
        simpa only [T, c] using zeroAgreementTrace_card c (u 0) v1
      _ = (directionCoreTrace family r gamma).card := by
        simpa only [c, v1] using congrArg Finset.card
          (directionZeroAgreementSet_translatedInterceptWord family r gamma)
  rw [hTtrace] at hsplit
  omega

open Classical in
theorem zeroAgreementStratum_six_card_le_three_of_support_four_of_not_safe
    (dom : Fin 16 ↪ F) (u0 v1 : Fin 16 → F)
    (hsupport : (directionSupportSet v1).card = 4)
    (hunsafe : ¬ ZeroDirectionSafeLine dom 4 9 u0 v1) :
    (zeroAgreementStratum dom 4 9 u0 v1 6).card ≤ 3 := by
  obtain ⟨c0, hc0, hzero⟩ :=
    (not_zeroDirectionSafeLine_iff_exists_codeword_zeroAgreement_ge
      dom 4 9 u0 v1).mp hunsafe
  let I := {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 v1 6}
  let U := {i : Fin 16 // i ∈ directionZeroSet v1}
  let K : Finset U := zeroAgreementTrace c0 u0 v1
  let W : Finset U := Finset.univ \ K
  let B : I → Finset U := fun c ↦ zeroAgreementTrace c.1 u0 v1
  have hU : Fintype.card U = 12 := by
    have hpartition := directionSupportSet_card_eq (n := 16) v1
    have hz : (directionZeroSet v1).card = 12 := by omega
    simpa only [U, Fintype.card_coe] using hz
  have hK : 9 ≤ K.card := by
    rw [show K.card = (directionZeroAgreementSet c0 u0 v1).card by
      simpa only [K] using zeroAgreementTrace_card c0 u0 v1]
    exact hzero
  have hc0App : c0 ∈ lineAppearingCodewords dom 4 9 u0 v1 :=
    unsafeCodeword_mem_lineAppearingCodewords dom u0 v1 c0 hc0 hzero
  by_cases hempty : zeroAgreementStratum dom 4 9 u0 v1 6 = ∅
  · simp only [hempty, Finset.card_empty, Nat.zero_le]
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let cI : I := ⟨c, hc⟩
  have hsize : ∀ d : I, (B d).card = 6 := by
    intro d
    rw [show B d = zeroAgreementTrace d.1 u0 v1 by rfl,
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp d.2).2
  have hnotc0 : ∀ d : I, d.1 ≠ c0 := by
    intro d heq
    have hdsize := hsize d
    change (zeroAgreementTrace d.1 u0 v1).card = 6 at hdsize
    rw [heq, zeroAgreementTrace_card] at hdsize
    omega
  have hinter : ∀ d : I, (B d ∩ K).card ≤ 3 := by
    intro d
    have hdApp : d.1 ∈ lineAppearingCodewords dom 4 9 u0 v1 :=
      (Finset.mem_filter.mp d.2).1
    simpa only [B, K] using
      zeroAgreementTrace_pair_card_le_three_of_appearing
        dom u0 v1 hdApp hc0App (hnotc0 d)
  have hWupper : W.card ≤ 3 := by
    rw [show W = Finset.univ \ K by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hU]
    omega
  have hdiffSub : ∀ d : I, B d \ K ⊆ W := by
    intro d i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hdiffLower : ∀ d : I, 3 ≤ (B d \ K).card := by
    intro d
    have hsplit := Finset.card_sdiff_add_card_inter (B d) K
    have hdsize := hsize d
    have hdinter := hinter d
    omega
  have hWcard : W.card = 3 := by
    have hlower := hdiffLower cI
    have hsub := Finset.card_le_card (hdiffSub cI)
    omega
  have hWsub : ∀ d : I, W ⊆ B d := by
    intro d
    have heq : B d \ K = W := by
      apply Finset.eq_of_subset_of_card_le (hdiffSub d)
      have hlower := hdiffLower d
      omega
    intro i hi
    have : i ∈ B d \ K := by rw [heq]; exact hi
    exact (Finset.mem_sdiff.mp this).1
  have hpair : ∀ d e : I, d ≠ e → B d ∩ B e = W := by
    intro d e hde
    have hsub : W ⊆ B d ∩ B e := fun i hi ↦
      Finset.mem_inter.mpr ⟨hWsub d hi, hWsub e hi⟩
    have hupper : (B d ∩ B e).card ≤ 3 := by
      simpa only [B] using zeroAgreementTrace_pair_card_le_three
        dom u0 v1 6 d.2 e.2 (fun h ↦ hde (Subtype.ext h))
    apply Finset.Subset.antisymm
    · exact Finset.eq_of_subset_of_card_le hsub (by omega) |>.symm.subset
    · exact hsub
  have hpacking := commonKernel_packing_bound
    (Finset.univ : Finset U) 6 B W
    (fun _ ↦ Finset.subset_univ _)
    hsize (Finset.subset_univ _)
    hWsub hpair
  have hambient : (Finset.univ : Finset U).card = 12 := by
    rw [Finset.card_univ, hU]
  rw [hWcard, hambient] at hpacking
  simpa only [I, Fintype.card_coe] using (show Fintype.card I ≤ 3 by omega)

noncomputable def traceFiveScalars
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u) (r : F[X]) : Finset F :=
  family.G.filter fun gamma ↦ (directionCoreTrace family r gamma).card = 5

noncomputable def traceSixScalars
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u) (r : F[X]) : Finset F :=
  family.G.filter fun gamma ↦ (directionCoreTrace family r gamma).card = 6

theorem traceFiveScalars_card_le_four
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 12) :
    (traceFiveScalars family r).card ≤ 4 := by
  let G5 := traceFiveScalars family r
  let v1 := translatedDirectionWord dom (u 1) r
  let f : F → (Fin 16 → F) := translatedInterceptWord family r
  have hinj : Set.InjOn f G5 := by
    intro gamma hgamma beta hbeta hword
    have hgammaData := Finset.mem_filter.mp hgamma
    have hbetaData := Finset.mem_filter.mp hbeta
    apply translatedInterceptWord_injective_of_trace_le_six
      family hthreshold r hcore hgammaData.1 hbetaData.1
        (by omega) (by omega) hword
  have hsub : G5.image f ⊆ zeroAgreementStratum dom 4 9 (u 0) v1 5 := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨gamma, hgamma, rfl⟩ := hc
    have hgammaData := Finset.mem_filter.mp hgamma
    exact translatedInterceptWord_mem_zeroAgreementStratum
      family hthreshold r hr hgammaData.1 5 hgammaData.2
  calc
    G5.card = (G5.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (zeroAgreementStratum dom 4 9 (u 0) v1 5).card :=
      Finset.card_le_card hsub
    _ ≤ 4 := zeroAgreementStratum_five_card_le_four_of_support_four
      dom (u 0) v1 (by
        simpa only [v1] using
          directionSupportSet_translatedDirectionWord_card_eq_four
            dom (u 1) r hcore)

theorem traceSixScalars_card_le_three_of_not_safe
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 12)
    (hunsafe : ¬ ZeroDirectionSafeLine dom 4 9 (u 0)
      (translatedDirectionWord dom (u 1) r)) :
    (traceSixScalars family r).card ≤ 3 := by
  let G6 := traceSixScalars family r
  let v1 := translatedDirectionWord dom (u 1) r
  let f : F → (Fin 16 → F) := translatedInterceptWord family r
  have hinj : Set.InjOn f G6 := by
    intro gamma hgamma beta hbeta hword
    have hgammaData := Finset.mem_filter.mp hgamma
    have hbetaData := Finset.mem_filter.mp hbeta
    apply translatedInterceptWord_injective_of_trace_le_six
      family hthreshold r hcore hgammaData.1 hbetaData.1
        (by omega) (by omega) hword
  have hsub : G6.image f ⊆ zeroAgreementStratum dom 4 9 (u 0) v1 6 := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨gamma, hgamma, rfl⟩ := hc
    have hgammaData := Finset.mem_filter.mp hgamma
    exact translatedInterceptWord_mem_zeroAgreementStratum
      family hthreshold r hr hgammaData.1 6 hgammaData.2
  calc
    G6.card = (G6.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (zeroAgreementStratum dom 4 9 (u 0) v1 6).card :=
      Finset.card_le_card hsub
    _ ≤ 3 := zeroAgreementStratum_six_card_le_three_of_support_four_of_not_safe
      dom (u 0) v1 (by
        simpa only [v1] using
          directionSupportSet_translatedDirectionWord_card_eq_four
            dom (u 1) r hcore) (by simpa only [v1] using hunsafe)

theorem family_card_le_eleven_of_direction_core_twelve_of_not_safe
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 12)
    (hunsafe : ¬ ZeroDirectionSafeLine dom 4 9 (u 0)
      (translatedDirectionWord dom (u 1) r)) :
    family.G.card ≤ 11 := by
  let v1 := translatedDirectionWord dom (u 1) r
  obtain ⟨c0, hc0, hzero⟩ :=
    (not_zeroDirectionSafeLine_iff_exists_codeword_zeroAgreement_ge
      dom 4 9 (u 0) v1).mp (by simpa only [v1] using hunsafe)
  let G0 := translatedWordFiber family r c0
  let G5 := traceFiveScalars family r
  let G6 := traceSixScalars family r
  have hcover : family.G ⊆ (G0 ∪ G5) ∪ G6 := by
    intro gamma hgamma
    by_cases hsame : translatedInterceptWord family r gamma = c0
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hgamma, hsame⟩
    · have hlower := five_le_directionCoreTrace_of_core_twelve
        family hthreshold r hcore hgamma
      have hupper := directionCoreTrace_card_le_six_of_unsafeCodeword_ne
        family hthreshold r hr hcore c0 hc0 hzero hgamma hsame
      by_cases hfive : (directionCoreTrace family r gamma).card = 5
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨hgamma, hfive⟩
      · apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨hgamma, by omega⟩
  have h0 : G0.card ≤ 4 := by
    simpa only [G0] using translatedWordFiber_card_le_four
      family r hr hcore c0
  have h5 : G5.card ≤ 4 := by
    simpa only [G5] using traceFiveScalars_card_le_four
      family hthreshold r hr hcore
  have h6 : G6.card ≤ 3 := by
    simpa only [G6, v1] using traceSixScalars_card_le_three_of_not_safe
      family hthreshold r hr hcore hunsafe
  have hcard := Finset.card_le_card hcover
  have hleft := Finset.card_union_le G0 G5
  have htotal := Finset.card_union_le (G0 ∪ G5) G6
  omega

/-- The direction-core residual now consists of cores six through eleven,
or a zero-safe support-four line at core twelve. -/
theorem card_le_sixteen_or_exceptional_direction_core_band_eleven_or_safe_twelve
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9) :
    family.G.card ≤ 16 ∨
      (∃ r : F[X], r.natDegree < 4 ∧
        6 ≤ (directionAgreement dom (u 1) r).card ∧
        (directionAgreement dom (u 1) r).card ≤ 11 ∧
        ∀ gamma ∈ family.G, ∃ i : Fin 16,
          i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
          i ∉ directionAgreement dom (u 1) r) ∨
      (∃ r : F[X], r.natDegree < 4 ∧
        (directionAgreement dom (u 1) r).card = 12 ∧
        ZeroDirectionSafeLine dom 4 9 (u 0)
          (translatedDirectionWord dom (u 1) r) ∧
        ∀ gamma ∈ family.G, ∃ i : Fin 16,
          i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
          i ∉ directionAgreement dom (u 1) r) := by
  rcases card_le_sixteen_or_exceptional_direction_core_band_twelve
      family hthreshold with hcard | ⟨r, hr, hlower, hupper, hfresh⟩
  · exact Or.inl hcard
  · by_cases htwelve : (directionAgreement dom (u 1) r).card = 12
    · by_cases hsafe : ZeroDirectionSafeLine dom 4 9 (u 0)
          (translatedDirectionWord dom (u 1) r)
      · exact Or.inr (Or.inr ⟨r, hr, htwelve, hsafe, hfresh⟩)
      · exact Or.inl
          ((family_card_le_eleven_of_direction_core_twelve_of_not_safe
            family hthreshold r hr htwelve hsafe).trans (by norm_num))
    · exact Or.inr (Or.inl ⟨r, hr, hlower, by omega, hfresh⟩)

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCoreTwelveUnsafe

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCoreTwelveUnsafe
#print axioms zeroAgreementStratum_six_card_le_three_of_support_four_of_not_safe
#print axioms family_card_le_eleven_of_direction_core_twelve_of_not_safe
#print axioms card_le_sixteen_or_exceptional_direction_core_band_eleven_or_safe_twelve
