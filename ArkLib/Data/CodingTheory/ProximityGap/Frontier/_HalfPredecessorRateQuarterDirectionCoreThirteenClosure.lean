/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterExceptionalDirectionPuncture
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSupportThreeSafeLine

/-!
# Rate-quarter closure of an exceptional direction core of size thirteen

Subtract a degree-below-four direction polynomial whose agreement core has
size thirteen.  The translated direction is supported on exactly three
coordinates.  The existing support-three theorem closes zero-safe lines.

The unsafe case is smaller, not larger, for the MCA-selected family.  An
unsafe codeword agrees with the translated base row on at least nine of the
thirteen fixed coordinates.  Every other selected translated intercept then
has fixed-coordinate trace size at most seven.  The size-six trace stratum has
at most eight codewords, the size-seven stratum has at most one, and the
saturated unsafe fiber uses at most the three moving coordinates.
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

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCoreThirteenClosure

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The received direction after subtracting the exceptional polynomial. -/
noncomputable def translatedDirectionWord
    (dom : Fin 16 ↪ F) (u1 : Fin 16 → F) (r : F[X]) : Fin 16 → F :=
  fun i ↦ u1 i - r.eval (dom i)

/-- Evaluation word of the translated selected intercept. -/
noncomputable def translatedInterceptWord
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (r : F[X]) (gamma : F) : Fin 16 → F :=
  fun i ↦ (translatedIntercept family r gamma).eval (dom i)

theorem directionSupportSet_translatedDirectionWord
    (dom : Fin 16 ↪ F) (u1 : Fin 16 → F) (r : F[X]) :
    directionSupportSet (translatedDirectionWord dom u1 r) =
      Finset.univ \ directionAgreement dom u1 r := by
  ext i
  simp only [directionSupportSet, translatedDirectionWord, directionAgreement,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  constructor
  · intro h hEq
    apply h
    rw [hEq, sub_self]
  · intro h hzero
    apply h
    exact (sub_eq_zero.mp hzero).symm

theorem directionSupportSet_translatedDirectionWord_card_eq_three
    (dom : Fin 16 ↪ F) (u1 : Fin 16 → F) (r : F[X])
    (hcore : (directionAgreement dom u1 r).card = 13) :
    (directionSupportSet (translatedDirectionWord dom u1 r)).card = 3 := by
  rw [directionSupportSet_translatedDirectionWord,
    Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, hcore]

/-- Translation turns the exceptional-core trace into the ordinary zero
agreement trace of the translated affine line. -/
theorem directionZeroAgreementSet_translatedInterceptWord
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (r : F[X]) (gamma : F) :
    directionZeroAgreementSet
        (translatedInterceptWord family r gamma) (u 0)
        (translatedDirectionWord dom (u 1) r) =
      directionCoreTrace family r gamma := by
  ext i
  simp only [directionZeroAgreementSet, directionZeroSet,
    translatedDirectionWord, translatedInterceptWord, directionCoreTrace,
    directionAgreement, fullAgreement, translatedIntercept,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
    eval_sub, eval_mul, eval_C]
  constructor
  · rintro ⟨hzero, hbase⟩
    have hdir : r.eval (dom i) = u 1 i := (sub_eq_zero.mp hzero).symm
    refine ⟨?_, hdir⟩
    linear_combination hbase + gamma * hdir
  · rintro ⟨hfull, hdir⟩
    refine ⟨?_, ?_⟩
    · rw [hdir, sub_self]
    · linear_combination hfull - gamma * hdir

/-- The same translation preserves the full agreement set, now viewed on the
ordinary affine line with sparse direction. -/
theorem agreeSet_translatedInterceptWord_eq_fullAgreement
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (r : F[X]) (gamma : F) :
    agreeSet (translatedInterceptWord family r gamma)
        (fun i ↦ u 0 i + gamma • translatedDirectionWord dom (u 1) r i) =
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) := by
  ext i
  simp only [agreeSet, translatedInterceptWord, translatedDirectionWord,
    translatedIntercept, fullAgreement, Finset.mem_filter, Finset.mem_univ,
    true_and, eval_sub, eval_mul, eval_C, smul_eq_mul]
  constructor <;> intro h
  · linear_combination h
  · linear_combination h

theorem translatedInterceptWord_mem_rsCode
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (r : F[X]) (hr : r.natDegree < 4)
    {gamma : F} (hgamma : gamma ∈ family.G) :
    translatedInterceptWord family r gamma ∈
      (rsCode dom 4 : Submodule F (Fin 16 → F)) := by
  refine ⟨translatedIntercept family r gamma, ?_, rfl⟩
  have hnat := translatedIntercept_natDegree_lt family r hr hgamma
  by_cases hzero : translatedIntercept family r gamma = 0
  · simp only [hzero, degree_zero]
    exact WithBot.bot_lt_coe 4
  · exact (natDegree_lt_iff_degree_lt hzero).mp hnat

theorem translatedInterceptWord_mem_lineAppearingCodewords
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hr : r.natDegree < 4)
    {gamma : F} (hgamma : gamma ∈ family.G) :
    translatedInterceptWord family r gamma ∈
      lineAppearingCodewords dom 4 9 (u 0)
        (translatedDirectionWord dom (u 1) r) := by
  rw [lineAppearingCodewords, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, translatedInterceptWord_mem_rsCode
    family r hr hgamma, gamma, ?_⟩
  rw [agreeSet_translatedInterceptWord_eq_fullAgreement]
  have hlarge := family.threshold_le gamma hgamma
  simpa only [hthreshold] using hlarge

theorem translatedInterceptWord_mem_zeroAgreementStratum
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hr : r.natDegree < 4)
    {gamma : F} (hgamma : gamma ∈ family.G) (t : Nat)
    (htrace : (directionCoreTrace family r gamma).card = t) :
    translatedInterceptWord family r gamma ∈
      zeroAgreementStratum dom 4 9 (u 0)
        (translatedDirectionWord dom (u 1) r) t := by
  rw [zeroAgreementStratum, Finset.mem_filter]
  refine ⟨translatedInterceptWord_mem_lineAppearingCodewords
    family hthreshold r hr hgamma, ?_⟩
  rw [directionZeroAgreementSet_translatedInterceptWord]
  exact htrace

/-- A common fresh coordinate determines the scalar even when translated
intercepts are compared only as evaluation words. -/
theorem gamma_eq_of_translatedInterceptWord_eq_of_common_fresh
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (r : F[X]) {gamma beta : F}
    (hword : translatedInterceptWord family r gamma =
      translatedInterceptWord family r beta)
    {i : Fin 16}
    (hgamma : i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma))
    (hbeta : i ∈ fullAgreement dom (u 0) (u 1) beta (family.q beta))
    (hout : i ∉ directionAgreement dom (u 1) r) :
    gamma = beta := by
  have hqgamma : (family.q gamma).eval (dom i) =
      u 0 i + gamma * u 1 i := by
    simpa only [fullAgreement, Finset.mem_filter, Finset.mem_univ,
      true_and] using hgamma
  have hqbeta : (family.q beta).eval (dom i) =
      u 0 i + beta * u 1 i := by
    simpa only [fullAgreement, Finset.mem_filter, Finset.mem_univ,
      true_and] using hbeta
  have heval := congrFun hword i
  simp only [translatedInterceptWord, translatedIntercept, eval_sub,
    eval_mul, eval_C] at heval
  rw [hqgamma, hqbeta] at heval
  have hmul : (gamma - beta) * (u 1 i - r.eval (dom i)) = 0 := by
    linear_combination heval
  have hdir : u 1 i - r.eval (dom i) ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    apply hout
    simp only [directionAgreement, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact heq.symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hdir)

theorem directionFreshTraceSubtype_disjoint_of_word_eq_of_ne
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (r : F[X]) {gamma beta : F} (hne : gamma ≠ beta)
    (hword : translatedInterceptWord family r gamma =
      translatedInterceptWord family r beta) :
    Disjoint (directionFreshTraceSubtype family r gamma)
      (directionFreshTraceSubtype family r beta) := by
  rw [Finset.disjoint_left]
  intro i hgamma hbeta
  have hgamma' : i.1 ∈
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) := by
    simpa only [directionFreshTraceSubtype, Finset.mem_filter,
      Finset.mem_univ, true_and] using hgamma
  have hbeta' : i.1 ∈
      fullAgreement dom (u 0) (u 1) beta (family.q beta) := by
    simpa only [directionFreshTraceSubtype, Finset.mem_filter,
      Finset.mem_univ, true_and] using hbeta
  exact hne (gamma_eq_of_translatedInterceptWord_eq_of_common_fresh
    family r hword hgamma' hbeta' i.2)

theorem two_le_directionFreshTraceSubtype_of_trace_le_seven
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) {gamma : F} (hgamma : gamma ∈ family.G)
    (htrace : (directionCoreTrace family r gamma).card ≤ 7) :
    2 ≤ (directionFreshTraceSubtype family r gamma).card := by
  let A := fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let D := directionAgreement dom (u 1) r
  have hA : 9 ≤ A.card := by
    have hlarge := family.threshold_le gamma hgamma
    simpa only [hthreshold, A] using hlarge
  have hsplit := Finset.card_sdiff_add_card_inter A D
  have hfresh := directionFreshTraceSubtype_card family r gamma
  change (directionFreshTraceSubtype family r gamma).card = (A \ D).card at hfresh
  change (A ∩ D).card ≤ 7 at htrace
  rw [hfresh]
  omega

theorem translatedInterceptWord_injective_of_trace_le_seven
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hcore : (directionAgreement dom (u 1) r).card = 13)
    {gamma beta : F} (hgamma : gamma ∈ family.G)
    (hbeta : beta ∈ family.G)
    (hgammaTrace : (directionCoreTrace family r gamma).card ≤ 7)
    (hbetaTrace : (directionCoreTrace family r beta).card ≤ 7)
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
  have hA : 2 ≤ A.card := by
    simpa only [A] using two_le_directionFreshTraceSubtype_of_trace_le_seven
      family hthreshold r hgamma hgammaTrace
  have hB : 2 ≤ B.card := by
    simpa only [B] using two_le_directionFreshTraceSubtype_of_trace_le_seven
      family hthreshold r hbeta hbetaTrace
  have hU : Fintype.card
      {i : Fin 16 // i ∉ directionAgreement dom (u 1) r} = 3 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_coe, Fintype.card_fin, hcore]
  have hunion : (A ∪ B).card ≤ 3 := by
    have hle := Finset.card_le_univ (A ∪ B)
    simpa only [Finset.card_univ, hU] using hle
  rw [Finset.card_union_of_disjoint hdisj] at hunion
  omega

/-- At core size thirteen, every selected translated intercept has a trace of
size at least six. -/
theorem six_le_directionCoreTrace_of_core_thirteen
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hcore : (directionAgreement dom (u 1) r).card = 13)
    {gamma : F} (hgamma : gamma ∈ family.G) :
    6 ≤ (directionCoreTrace family r gamma).card := by
  have hbudget := nine_add_direction_core_card_le_sixteen_add_trace_card
    family (by norm_num) (by rw [hthreshold]) r hgamma
  rw [hcore] at hbudget
  omega

/-- Scalars whose translated intercept has a six-coordinate fixed trace. -/
noncomputable def traceSixScalars
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u) (r : F[X]) : Finset F :=
  family.G.filter fun gamma ↦ (directionCoreTrace family r gamma).card = 6

/-- Scalars whose translated intercept has a seven-coordinate fixed trace. -/
noncomputable def traceSevenScalars
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u) (r : F[X]) : Finset F :=
  family.G.filter fun gamma ↦ (directionCoreTrace family r gamma).card = 7

/-- Scalars sharing one fixed translated evaluation word. -/
noncomputable def translatedWordFiber
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u) (r : F[X])
    (c : Fin 16 → F) : Finset F :=
  family.G.filter fun gamma ↦ translatedInterceptWord family r gamma = c

/-- The six-trace selected scalars inject into the existing support-three
six-stratum, hence there are at most eight. -/
theorem traceSixScalars_card_le_eight
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 13) :
    (traceSixScalars family r).card ≤ 8 := by
  let G6 := traceSixScalars family r
  let v1 := translatedDirectionWord dom (u 1) r
  let f : F → (Fin 16 → F) := translatedInterceptWord family r
  have hinj : Set.InjOn f G6 := by
    intro gamma hgamma beta hbeta hword
    have hgammaData := Finset.mem_filter.mp hgamma
    have hbetaData := Finset.mem_filter.mp hbeta
    apply translatedInterceptWord_injective_of_trace_le_seven
      family hthreshold r hcore hgammaData.1 hbetaData.1
        (by omega) (by omega) hword
  have hsub : G6.image f ⊆
      zeroAgreementStratum dom 4 9 (u 0) v1 6 := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨gamma, hgamma, rfl⟩ := hc
    have hgammaData := Finset.mem_filter.mp hgamma
    exact translatedInterceptWord_mem_zeroAgreementStratum
      family hthreshold r hr hgammaData.1 6 hgammaData.2
  calc
    G6.card = (G6.image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (zeroAgreementStratum dom 4 9 (u 0) v1 6).card :=
      Finset.card_le_card hsub
    _ ≤ 8 := zeroAgreementStratum_six_card_le_eight_of_support_three
      dom (u 0) v1
        (directionSupportSet_translatedDirectionWord_card_eq_three
          dom (u 1) r hcore)

/-- A fixed translated word can carry at most three selected scalars, one per
moving coordinate. -/
theorem translatedWordFiber_card_le_three
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 13)
    (c : Fin 16 → F) :
    (translatedWordFiber family r c).card ≤ 3 := by
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
  have hH : Fintype.card H = 3 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_coe, Fintype.card_fin, hcore]
  simpa only [Gc, H, Fintype.card_coe, hH] using hcard

/-- In a thirteen-point universe, a seven-set meeting a set of size at least
nine in at most three points contains the whole complement of the large set. -/
theorem complement_subset_seven_set
    {U : Type} [Fintype U] [DecidableEq U]
    (hU : Fintype.card U = 13) (K T : Finset U)
    (hK : 9 ≤ K.card) (hT : T.card = 7)
    (hinter : (T ∩ K).card ≤ 3) :
    Finset.univ \ K ⊆ T := by
  let W := Finset.univ \ K
  have hW : W.card ≤ 4 := by
    dsimp only [W]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hU]
    omega
  have hdiffSub : T \ K ⊆ W := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hdiff : 4 ≤ (T \ K).card := by
    have hinter' : (K ∩ T).card ≤ 3 := by
      rw [Finset.inter_comm]
      exact hinter
    rw [Finset.card_sdiff, hT]
    omega
  have hWsub : W ⊆ T \ K := by
    have heq : T \ K = W :=
      Finset.eq_of_subset_of_card_le hdiffSub (by omega)
    exact heq.symm.subset
  intro i hi
  exact (Finset.mem_sdiff.mp (hWsub hi)).1

theorem unsafeCodeword_mem_lineAppearingCodewords
    (dom : Fin 16 ↪ F) (u0 v1 c : Fin 16 → F)
    (hc : c ∈ (rsCode dom 4 : Submodule F (Fin 16 → F)))
    (hzero : 9 ≤ (directionZeroAgreementSet c u0 v1).card) :
    c ∈ lineAppearingCodewords dom 4 9 u0 v1 := by
  rw [lineAppearingCodewords, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, hc, 0, ?_⟩
  exact hzero.trans (directionZeroAgreementSet_card_le_agreeSet_line c u0 v1 0)

/-- Once an unsafe codeword occupies at least nine fixed coordinates, every
distinct selected translated intercept has trace size at most seven. -/
theorem directionCoreTrace_card_le_seven_of_unsafeCodeword_ne
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 13)
    (c0 : Fin 16 → F)
    (hc0 : c0 ∈
      (rsCode dom 4 : Submodule F (Fin 16 → F)))
    (hzero : 9 ≤ (directionZeroAgreementSet c0 (u 0)
      (translatedDirectionWord dom (u 1) r)).card)
    {gamma : F} (hgamma : gamma ∈ family.G)
    (hne : translatedInterceptWord family r gamma ≠ c0) :
    (directionCoreTrace family r gamma).card ≤ 7 := by
  let v1 := translatedDirectionWord dom (u 1) r
  let c := translatedInterceptWord family r gamma
  let U := {i : Fin 16 // i ∈ directionZeroSet v1}
  let T : Finset U := zeroAgreementTrace c (u 0) v1
  let K : Finset U := zeroAgreementTrace c0 (u 0) v1
  have hU : Fintype.card U = 13 := by
    have hsupport : (directionSupportSet v1).card = 3 := by
      simpa only [v1] using
        directionSupportSet_translatedDirectionWord_card_eq_three
          dom (u 1) r hcore
    have hpartition := directionSupportSet_card_eq (n := 16) v1
    have hz : (directionZeroSet v1).card = 13 := by omega
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
  have hW : (Finset.univ \ K).card ≤ 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hU]
    omega
  have hdiffSub : T \ K ⊆ Finset.univ \ K := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hdiff : (T \ K).card ≤ 4 :=
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

/-- In the unsafe support-three branch there is at most one codeword in the
seven-trace stratum. -/
theorem zeroAgreementStratum_seven_card_le_one_of_not_safe
    (dom : Fin 16 ↪ F) (u0 v1 : Fin 16 → F)
    (hsupport : (directionSupportSet v1).card = 3)
    (hunsafe : ¬ ZeroDirectionSafeLine dom 4 9 u0 v1) :
    (zeroAgreementStratum dom 4 9 u0 v1 7).card ≤ 1 := by
  obtain ⟨c0, hc0, hzero⟩ :=
    (not_zeroDirectionSafeLine_iff_exists_codeword_zeroAgreement_ge
      dom 4 9 u0 v1).mp hunsafe
  let U := {i : Fin 16 // i ∈ directionZeroSet v1}
  let K : Finset U := zeroAgreementTrace c0 u0 v1
  have hU : Fintype.card U = 13 := by
    have hpartition := directionSupportSet_card_eq (n := 16) v1
    have hz : (directionZeroSet v1).card = 13 := by omega
    simpa only [U, Fintype.card_coe] using hz
  have hK : 9 ≤ K.card := by
    rw [show K.card = (directionZeroAgreementSet c0 u0 v1).card by
      simpa only [K] using zeroAgreementTrace_card c0 u0 v1]
    exact hzero
  have hc0App : c0 ∈ lineAppearingCodewords dom 4 9 u0 v1 :=
    unsafeCodeword_mem_lineAppearingCodewords dom u0 v1 c0 hc0 hzero
  rw [Finset.card_le_one]
  intro c hc d hd
  by_contra hcd
  let T : Finset U := zeroAgreementTrace c u0 v1
  let S : Finset U := zeroAgreementTrace d u0 v1
  have hcApp : c ∈ lineAppearingCodewords dom 4 9 u0 v1 :=
    (Finset.mem_filter.mp hc).1
  have hdApp : d ∈ lineAppearingCodewords dom 4 9 u0 v1 :=
    (Finset.mem_filter.mp hd).1
  have hT : T.card = 7 := by
    calc
      T.card = (directionZeroAgreementSet c u0 v1).card := by
        simpa only [T] using zeroAgreementTrace_card c u0 v1
      _ = 7 := (Finset.mem_filter.mp hc).2
  have hS : S.card = 7 := by
    calc
      S.card = (directionZeroAgreementSet d u0 v1).card := by
        simpa only [S] using zeroAgreementTrace_card d u0 v1
      _ = 7 := (Finset.mem_filter.mp hd).2
  have hcne : c ≠ c0 := by
    intro heq
    subst c
    rw [zeroAgreementTrace_card] at hT
    omega
  have hdne : d ≠ c0 := by
    intro heq
    subst d
    rw [zeroAgreementTrace_card] at hS
    omega
  have hTK : (T ∩ K).card ≤ 3 := by
    simpa only [T, K] using
      zeroAgreementTrace_pair_card_le_three_of_appearing
        dom u0 v1 hcApp hc0App hcne
  have hSK : (S ∩ K).card ≤ 3 := by
    simpa only [S, K] using
      zeroAgreementTrace_pair_card_le_three_of_appearing
        dom u0 v1 hdApp hc0App hdne
  have hWT := complement_subset_seven_set hU K T hK hT hTK
  have hWS := complement_subset_seven_set hU K S hK hS hSK
  have hWcard : 4 ≤ (Finset.univ \ K).card := by
    have hdiffSub : T \ K ⊆ Finset.univ \ K := by
      intro i hi
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
    have hdiff : 4 ≤ (T \ K).card := by
      have hinter' : (K ∩ T).card ≤ 3 := by
        rw [Finset.inter_comm]
        exact hTK
      rw [Finset.card_sdiff, hT]
      omega
    exact hdiff.trans (Finset.card_le_card hdiffSub)
  have hWsub : Finset.univ \ K ⊆ T ∩ S := by
    intro i hi
    exact Finset.mem_inter.mpr ⟨hWT hi, hWS hi⟩
  have hfour : 4 ≤ (T ∩ S).card :=
    hWcard.trans (Finset.card_le_card hWsub)
  have hthree : (T ∩ S).card ≤ 3 := by
    simpa only [T, S] using
      zeroAgreementTrace_pair_card_le_three_of_appearing
        dom u0 v1 hcApp hdApp hcd
  omega

theorem traceSevenScalars_card_le_one_of_not_safe
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 13)
    (hunsafe : ¬ ZeroDirectionSafeLine dom 4 9 (u 0)
      (translatedDirectionWord dom (u 1) r)) :
    (traceSevenScalars family r).card ≤ 1 := by
  let G7 := traceSevenScalars family r
  let v1 := translatedDirectionWord dom (u 1) r
  let f : F → (Fin 16 → F) := translatedInterceptWord family r
  have hinj : Set.InjOn f G7 := by
    intro gamma hgamma beta hbeta hword
    have hgammaData := Finset.mem_filter.mp hgamma
    have hbetaData := Finset.mem_filter.mp hbeta
    exact translatedInterceptWord_injective_of_trace_le_seven
      family hthreshold r hcore hgammaData.1 hbetaData.1
        (by omega) (by omega) hword
  have hsub : G7.image f ⊆
      zeroAgreementStratum dom 4 9 (u 0) v1 7 := by
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨gamma, hgamma, rfl⟩ := hc
    have hgammaData := Finset.mem_filter.mp hgamma
    exact translatedInterceptWord_mem_zeroAgreementStratum
      family hthreshold r hr hgammaData.1 7 hgammaData.2
  calc
    G7.card = (G7.image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (zeroAgreementStratum dom 4 9 (u 0) v1 7).card :=
      Finset.card_le_card hsub
    _ ≤ 1 := zeroAgreementStratum_seven_card_le_one_of_not_safe
      dom (u 0) v1
        (directionSupportSet_translatedDirectionWord_card_eq_three
          dom (u 1) r hcore) hunsafe

/-- The unsafe branch is actually bounded by twelve: eight six-trace scalars,
one seven-trace scalar, and at most three scalars on the saturated word. -/
theorem family_card_le_twelve_of_direction_core_thirteen_of_not_safe
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 13)
    (hunsafe : ¬ ZeroDirectionSafeLine dom 4 9 (u 0)
      (translatedDirectionWord dom (u 1) r)) :
    family.G.card ≤ 12 := by
  let v1 := translatedDirectionWord dom (u 1) r
  obtain ⟨c0, hc0, hzero⟩ :=
    (not_zeroDirectionSafeLine_iff_exists_codeword_zeroAgreement_ge
      dom 4 9 (u 0) v1).mp hunsafe
  let G0 := translatedWordFiber family r c0
  let G6 := traceSixScalars family r
  let G7 := traceSevenScalars family r
  have hcover : family.G ⊆ (G0 ∪ G6) ∪ G7 := by
    intro gamma hgamma
    by_cases hsame : translatedInterceptWord family r gamma = c0
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hgamma, hsame⟩
    · have hlower := six_le_directionCoreTrace_of_core_thirteen
        family hthreshold r hcore hgamma
      have hupper := directionCoreTrace_card_le_seven_of_unsafeCodeword_ne
        family hthreshold r hr hcore c0 hc0 hzero hgamma hsame
      by_cases hsix : (directionCoreTrace family r gamma).card = 6
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨hgamma, hsix⟩
      · apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨hgamma, by omega⟩
  have h0 : G0.card ≤ 3 := by
    simpa only [G0] using translatedWordFiber_card_le_three
      family r hr hcore c0
  have h6 : G6.card ≤ 8 := by
    simpa only [G6] using traceSixScalars_card_le_eight
      family hthreshold r hr hcore
  have h7 : G7.card ≤ 1 := by
    simpa only [G7, v1] using traceSevenScalars_card_le_one_of_not_safe
      family hthreshold r hr hcore hunsafe
  have hcard := Finset.card_le_card hcover
  have hleft := Finset.card_union_le G0 G6
  have htotal := Finset.card_union_le (G0 ∪ G6) G7
  omega

/-- **Direction-core thirteen closes unconditionally.**  The zero-safe branch
uses the support-three line theorem; the unsafe branch is bounded by twelve. -/
theorem card_le_sixteen_of_direction_core_card_eq_thirteen
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9)
    (r : F[X]) (hr : r.natDegree < 4)
    (hcore : (directionAgreement dom (u 1) r).card = 13) :
    family.G.card ≤ 16 := by
  let v1 := translatedDirectionWord dom (u 1) r
  by_cases hsafe : ZeroDirectionSafeLine dom 4 9 (u 0) v1
  · have hsub : family.G ⊆ lineBadScalars dom 4 9 (u 0) v1 := by
      intro gamma hgamma
      rw [lineBadScalars, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, translatedInterceptWord family r gamma,
        translatedInterceptWord_mem_rsCode family r hr hgamma, ?_⟩
      rw [agreeSet_translatedInterceptWord_eq_fullAgreement]
      have hlarge := family.threshold_le gamma hgamma
      simpa only [hthreshold] using hlarge
    have hfamily := Finset.card_le_card hsub
    have hline := lineBadScalars_card_le_sixteen_of_support_three
      dom (u 0) v1 hsafe
        (by
          simpa only [v1] using
            (directionSupportSet_translatedDirectionWord_card_eq_three
              dom (u 1) r hcore))
    exact hfamily.trans hline
  · have hunsafe : ¬ ZeroDirectionSafeLine dom 4 9 (u 0)
        (translatedDirectionWord dom (u 1) r) := by
      simpa only [v1] using hsafe
    exact (family_card_le_twelve_of_direction_core_thirteen_of_not_safe
      family hthreshold r hr hcore hunsafe).trans (by norm_num)

/-- The exceptional-direction residual for a literal length-sixteen stack can
therefore be sharpened from the band `6..13` to `6..12`. -/
theorem card_le_sixteen_or_exceptional_direction_core_band_twelve
    {dom : Fin 16 ↪ F} {delta : NNReal}
    {u : WordStack F (Fin 2) (Fin 16)}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card (Fin 16) : NNReal)⌉₊ = 9) :
    family.G.card ≤ 16 ∨
      ∃ r : F[X], r.natDegree < 4 ∧
        6 ≤ (directionAgreement dom (u 1) r).card ∧
        (directionAgreement dom (u 1) r).card ≤ 12 ∧
        ∀ gamma ∈ family.G, ∃ i : Fin 16,
          i ∈ fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∧
          i ∉ directionAgreement dom (u 1) r := by
  rcases card_le_sixteen_or_exceptional_direction_core_band
      family (by norm_num) hthreshold with hcard | ⟨r, hr, hlower, hupper, hfresh⟩
  · exact Or.inl hcard
  · by_cases hthirteen :
        (directionAgreement dom (u 1) r).card = 13
    · exact Or.inl
        (card_le_sixteen_of_direction_core_card_eq_thirteen
          family hthreshold r hr hthirteen)
    · exact Or.inr ⟨r, hr, hlower, by omega, hfresh⟩

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCoreThirteenClosure

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCoreThirteenClosure
#print axioms card_le_sixteen_of_direction_core_card_eq_thirteen
#print axioms card_le_sixteen_or_exceptional_direction_core_band_twelve
