/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Whir.Protocol
import ArkLib.ProofSystem.Whir.ProtocolCompleteness
import ArkLib.ProofSystem.Whir.ThresholdKSF
import ArkLib.ProofSystem.Whir.CheckedVerifier
import ArkLib.ProofSystem.Whir.WhirVectorIOPProof
import ArkLib.ProofSystem.Whir.MCAJohnsonBound
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RemainingCore
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# WHIR Vector IOP Soundness and the Johnson MCA Bound (Issue #302)

This file records the issue-facing wiring for Issue #302.  It relates the
`mca_johnson_bound_CONJECTURE` / WHIR keystone surfaces to the BCIKS20 core producers, re-exports
the proved indicator-budget RBR package for the current WHIR skeleton, exposes the graded K4
Johnson capstone from `MCAJohnsonBound.lean`, and records the checked verifier's genuine RBR
obligation without fabricating it.

The concrete Vector IOP in `Protocol.lean` currently uses a dummy verifier (`pure true`).
The real checking verifier lives in `CheckedVerifier.lean`; its perfect-completeness leg is proven,
while its RBR knowledge-soundness leg remains an explicit hypothesis.
-/

namespace ProximityGap

open scoped NNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Issue #302/#304 corrected-core keystone export.**  The unified BCIKS20 remaining core
(`StrictCoeffPolysLargeResidual` at the target and floor-matched working radii) yields the
numeric per-round curve-CA quantity consumed by WHIR/STIR accounting:
`epsCA_curves C k δ δ ≤ k * max(errorBound δ, errorBound δ')`.

The theorem remains conditional on `BCIKS20RemainingCore`; this lemma is only the
predicate-to-numeric bridge, using `correlatedAgreement_of_remainingCore` plus the in-tree
`δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le`. -/
theorem keystone_curves_bound_of_remainingCore {k deg : ℕ} [NeZero deg]
    {domain : ι ↪ F} {δ δ' : ℝ≥0}
    (hδ' : δ' < 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι))
    (hCore : BCIKS20RemainingCore k deg domain δ δ') :
    epsCA_curves (F := F) (ReedSolomon.code domain deg : Set (ι → F)) k δ δ ≤
      ((k * max (errorBound δ deg domain) (errorBound δ' deg domain) : ℝ≥0) : ENNReal) :=
  (δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le (F := F) (k := k)
    (C := (ReedSolomon.code domain deg : Set (ι → F))) δ
    (max (errorBound δ deg domain) (errorBound δ' deg domain))).mp
    (correlatedAgreement_of_remainingCore hδ' hfloor hCore)

/-- **Raw-GS producer export for the WHIR/STIR numeric keystone.**  Two large-sector raw cargo
producers assemble `BCIKS20RemainingCore`, and hence yield the per-round curve-CA error bound
used by WHIR/STIR accounting. -/
theorem keystone_curves_bound_of_rawGSCargoLarge {k deg : ℕ} [NeZero deg]
    {domain : ι ↪ F} {δ δ' : ℝ≥0}
    (hδ' : δ' < 1 - ReedSolomon.sqrtRate deg domain)
    (hfloor : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι))
    (hRawδ : ArkLib.RawGS304.RawGSCargoLargeProducer
      (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hRawδ' : ArkLib.RawGS304.RawGSCargoLargeProducer
      (k := k) (deg := deg) (domain := domain) (δ := δ')) :
    epsCA_curves (F := F) (ReedSolomon.code domain deg : Set (ι → F)) k δ δ ≤
      ((k * max (errorBound δ deg domain) (errorBound δ' deg domain) : ℝ≥0) : ENNReal) :=
  keystone_curves_bound_of_remainingCore hδ' hfloor
    (ArkLib.RawGS304.remainingCore_of_rawGSCargoLarge hRawδ hRawδ')

#print axioms ProximityGap.keystone_curves_bound_of_remainingCore
#print axioms ProximityGap.keystone_curves_bound_of_rawGSCargoLarge

end ProximityGap

namespace WhirIOP

open MutualCorrAgreement
open scoped NNReal

/-- **Coarse all-one RBR surface — NOT the nontrivial WHIR theorem.**  This is the compatibility
shape for the current `Protocol.lean` skeleton at the all-one budget.  The proved content is the
strictly sharper indicator-budget theorem below; the real checked verifier still needs its own RBR
bound. -/
def whirVectorIOP_rbrKnowledgeSoundness_dummy
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : _root_.WhirIOP.Params ιs F) (d : ℕ) {m0 : ℕ}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)] (δ : ℝ≥0) :
    Prop :=
  whirVectorIOP_rbrKnowledgeSoundness P d δ
    (fun _ : (_root_.WhirIOP.Construction.whirPaperTranscriptVectorSpec P d).ChallengeIdx =>
      (1 : ℝ≥0))
    (m0 := m0)

/-- **Proved indicator-budget RBR package for the current WHIR skeleton.**  The state-function
argument in `ThresholdKSF.lean` concentrates the whole RBR budget at the final randomness
challenge. -/
theorem whirVectorIOP_rbrKnowledgeSoundness_indicator
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : _root_.WhirIOP.Params ιs F) (d : ℕ) {m0 : ℕ}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)] (δ : ℝ≥0) :
    whirVectorIOP_rbrKnowledgeSoundness P d δ
      (fun i => if i = _root_.WhirIOP.Construction.finalRandomnessChallengeIdx P d then
        (1 : ℝ≥0) else 0)
      (m0 := m0) :=
  Whir302RBR.whirVectorIOP_rbrKnowledgeSoundness_indicator P d δ

/-- The indicator-budget theorem implies the coarse all-one budget by monotonicity of the final
probability bound. -/
theorem whirVectorIOP_rbrKnowledgeSoundness_dummy_holds
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : _root_.WhirIOP.Params ιs F) (d : ℕ) {m0 : ℕ}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)] (δ : ℝ≥0) :
    whirVectorIOP_rbrKnowledgeSoundness_dummy P d δ (m0 := m0) := by
  have hIndicator :
      whirVectorIOP_rbrKnowledgeSoundness P d δ
        (fun i => if i = _root_.WhirIOP.Construction.finalRandomnessChallengeIdx P d then
          (1 : ℝ≥0) else 0)
        (m0 := m0) :=
    whirVectorIOP_rbrKnowledgeSoundness_indicator P d δ
  unfold whirVectorIOP_rbrKnowledgeSoundness_dummy
  unfold whirVectorIOP_rbrKnowledgeSoundness OracleProof.rbrKnowledgeSoundness
    OracleVerifier.rbrKnowledgeSoundness at hIndicator ⊢
  rcases hIndicator with ⟨WitMid, extractor, kSF, hbound⟩
  refine ⟨WitMid, extractor, kSF, ?_⟩
  intro stmtIn witIn prover i
  exact le_trans (hbound stmtIn witIn prover i) (by
    change (((if i = _root_.WhirIOP.Construction.finalRandomnessChallengeIdx P d then
      (1 : ℝ≥0) else 0) : ℝ≥0) : ENNReal) ≤ ((1 : ℝ≥0) : ENNReal)
    by_cases hi : i = _root_.WhirIOP.Construction.finalRandomnessChallengeIdx P d
    · rw [if_pos hi]
    · rw [if_neg hi]
      exact zero_le _)

/-- The placeholder WHIR `VectorIOP` is secure with gap for the trivial all-one RBR budget.

This is the complete packaging step once the explicit dummy RBR residual is supplied. The
nontrivial WHIR theorem still requires replacing `whirVerify` with the real verifier and proving
its genuine RBR bound. -/
theorem whirVectorIOP_isSecureWithGap_dummy_of_rbr
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : _root_.WhirIOP.Params ιs F) (d : ℕ) {m0 : ℕ}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)] (δ : ℝ≥0)
    (hSound : whirVectorIOP_rbrKnowledgeSoundness_dummy P d δ (m0 := m0)) :
    whirVectorIOP_isSecureWithGap P d δ
      (fun _ : (_root_.WhirIOP.Construction.whirPaperTranscriptVectorSpec P d).ChallengeIdx =>
        (1 : ℝ≥0))
      (m0 := m0) :=
  Whir302.whirVectorIOP_isSecureWithGap_of_rbr P d δ
    (fun _ : (_root_.WhirIOP.Construction.whirPaperTranscriptVectorSpec P d).ChallengeIdx =>
      (1 : ℝ≥0))
    hSound

/-- Secure-with-gap package for the current WHIR skeleton at the proved indicator budget. -/
theorem whirVectorIOP_isSecureWithGap_indicator
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : _root_.WhirIOP.Params ιs F) (d : ℕ) {m0 : ℕ}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)] (δ : ℝ≥0) :
    whirVectorIOP_isSecureWithGap P d δ
      (fun i => if i = _root_.WhirIOP.Construction.finalRandomnessChallengeIdx P d then
        (1 : ℝ≥0) else 0)
      (m0 := m0) :=
  Whir302RBR.whirVectorIOP_isSecureWithGap_indicator P d δ

/-- Coarse all-one secure-with-gap package, derived from the proved indicator RBR theorem. -/
theorem whirVectorIOP_isSecureWithGap_dummy
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : _root_.WhirIOP.Params ιs F) (d : ℕ) {m0 : ℕ}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)] (δ : ℝ≥0) :
    whirVectorIOP_isSecureWithGap P d δ
      (fun _ : (_root_.WhirIOP.Construction.whirPaperTranscriptVectorSpec P d).ChallengeIdx =>
        (1 : ℝ≥0))
      (m0 := m0) :=
  whirVectorIOP_isSecureWithGap_dummy_of_rbr P d δ
    (whirVectorIOP_rbrKnowledgeSoundness_dummy_holds P d δ)

/-- RBR knowledge-soundness residual for the real checking verifier. -/
def whirCheckedVectorIOP_rbrKnowledgeSoundness
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : _root_.WhirIOP.Params ιs F) (d : ℕ) {m0 : ℕ}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)] (δ : ℝ≥0)
    (εRbr : (_root_.WhirIOP.Construction.whirPaperTranscriptVectorSpec P d).ChallengeIdx →
      ℝ≥0) :
    Prop :=
  OracleProof.rbrKnowledgeSoundness (pure ()) isEmptyElim
    (whirRelation m0 (P.φ 0) δ)
    (_root_.WhirIOP.Construction.paperTranscriptOracleVerifier P d
      (Whir302Checked.whirVerifyChecked P d))
    εRbr

/-- The checked WHIR `VectorIOP` has the secure-with-gap package once its genuine RBR
knowledge-soundness residual is supplied. -/
theorem whirCheckedVectorIOP_isSecureWithGap_of_rbr
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : _root_.WhirIOP.Params ιs F) (d : ℕ) {m0 : ℕ}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)] (δ : ℝ≥0)
    (εRbr : (_root_.WhirIOP.Construction.whirPaperTranscriptVectorSpec P d).ChallengeIdx →
      ℝ≥0)
    (hSound : whirCheckedVectorIOP_rbrKnowledgeSoundness P d δ εRbr (m0 := m0)) :
    VectorIOP.IsSecureWithGap (whirRelation m0 (P.φ 0) 0)
      (whirRelation m0 (P.φ 0) δ) εRbr
      (Whir302Checked.whirCheckedVectorIOP P d) :=
  Whir302Checked.whirCheckedVectorIOP_isSecureWithGap_of_rbr P d δ εRbr hSound

#print axioms WhirIOP.whirVectorIOP_rbrKnowledgeSoundness_dummy
#print axioms WhirIOP.whirVectorIOP_rbrKnowledgeSoundness_indicator
#print axioms WhirIOP.whirVectorIOP_rbrKnowledgeSoundness_dummy_holds
#print axioms WhirIOP.whirVectorIOP_isSecureWithGap_dummy_of_rbr
#print axioms WhirIOP.whirVectorIOP_isSecureWithGap_indicator
#print axioms WhirIOP.whirVectorIOP_isSecureWithGap_dummy
#print axioms WhirIOP.whirCheckedVectorIOP_rbrKnowledgeSoundness
#print axioms WhirIOP.whirCheckedVectorIOP_isSecureWithGap_of_rbr

end WhirIOP
