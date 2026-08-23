/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.Data.Hash.DuplexSponge
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Preliminaries
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.Rewinding

/-!
# Substrate for Duplex-Sponge Fiat-Shamir

This module provides the unified API and paper-facing aliases for the cryptographic primitives,
security definitions, and transformations established in Section 3 and Section 4 of Chiesa-Orrù
[CO25] for Duplex-Sponge Fiat-Shamir (DSFS) interactive oracle reductions.

## Overview

- **Section 3.2**: Core uniform preimage sampling lemmas (`DuplexSpongeFS.lemma_3_2`).
- **Section 3.3**: Sponge and permutation API abstractions (`SpongeState`, `Sponge`).
- **Section 3.4**: High-level aliases for Non-Interactive Argument (NARG) security properties,
  including completeness, soundness, failure probabilities, and straightline/rewinding knowledge
  soundness.
- **Section 4**: The core DSFS transformation definitions, including unsalted, salted, and
  generalized
  explicit salt source variants for both the prover and verifier.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace DuplexSpongeFS

/-! ## Section 3.3 -/

/-- Paper-facing alias for the canonical duplex-sponge state used in CO25 Section 3.3. -/
abbrev SpongeState (U : Type) [SpongeUnit U] [SpongeSize] := CanonicalSpongeState U

/-- Paper-facing alias for the canonical duplex sponge used in CO25 Section 3.3. -/
abbrev Sponge (U : Type) [SpongeUnit U] [SpongeSize] := CanonicalDuplexSponge U

/-! ## Section 3.4 -/

namespace NARG

variable {ι : Type} {oSpec : OracleSpec ι}
  {Statement Witness : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Paper-facing alias for CO25 Section 3.4 completeness. -/
abbrev completeness
    (relation : Set (Statement × Witness))
    (completenessError : ℝ≥0)
    (proof : Proof oSpec Statement Witness pSpec) : Prop :=
  Proof.completeness init impl relation completenessError proof

/-- Paper-facing alias for CO25 Section 3.4 perfect completeness. -/
abbrev perfectCompleteness
    (relation : Set (Statement × Witness))
    (proof : Proof oSpec Statement Witness pSpec) : Prop :=
  Proof.perfectCompleteness init impl relation proof

/-- Paper-facing alias for CO25 Section 3.4 soundness. -/
abbrev soundness
    (langIn : Set Statement)
    (verifier : Verifier oSpec Statement Bool pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  Proof.soundness init impl langIn verifier soundnessError

/-- Paper-facing alias for CO25 Section 3.4 straightline knowledge soundness. -/
abbrev straightlineKnowledgeSoundness
    (relation : Set (Statement × Bool))
    (verifier : Verifier oSpec Statement Bool pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  Proof.knowledgeSoundness init impl relation verifier knowledgeError

/-- Paper-facing alias for the straightline extractor interface used in Section 3.4. -/
abbrev StraightlineExtractor := Extractor.Straightline oSpec Statement Witness Bool pSpec

/-- Paper-facing alias for a malicious non-interactive prover used in CO25 Definition 3.7. -/
abbrev FailureProver (Message : Type) := _root_.Prover.NARG oSpec Statement Message

/-- Paper-facing alias for a `λ`-indexed family of malicious non-interactive provers. -/
abbrev FailureProverFamily
    (oSpec : (secParam : ℕ) → OracleSpec ι)
    (Statement : (secParam : ℕ) → Type)
    (Message : (secParam : ℕ) → Type) :=
  _root_.Prover.NARG.Family oSpec Statement Message

/-- Paper-facing alias for the total `t`-query malicious prover condition from CO25 Definition 3.8.
-/
abbrev queryBounded
    {Message : Type}
    (prover : FailureProver (oSpec := oSpec) (Statement := Statement) Message)
    (queryBound : ℕ) : Prop :=
  _root_.Prover.NARG.queryBounded prover queryBound

/-- Paper-facing alias for explicit `t(λ)`-query bounds on a `λ`-indexed prover family. -/
abbrev queryBoundedFamily
    {oSpec : ℕ → OracleSpec ι}
    {Statement Message : ℕ → Type}
    (prover : FailureProverFamily (ι := ι) oSpec Statement Message)
    (queryBound : (secParam : ℕ) → ℕ) : Prop :=
  _root_.Prover.NARG.Family.queryBounded prover queryBound

/-- Stronger per-oracle-index query bound for malicious provers. -/
abbrev perIndexQueryBounded
    [DecidableEq ι]
    {Message : Type}
    (prover : FailureProver (oSpec := oSpec) (Statement := Statement) Message)
    (queryBound : (oracleIdx : ι) → ℕ) : Prop :=
  _root_.Prover.NARG.perIndexQueryBounded prover queryBound

/-- Paper-facing alias for explicit per-index query bounds on a `λ`-indexed prover family. -/
abbrev perIndexQueryBoundedFamily
    [DecidableEq ι]
    {oSpec : ℕ → OracleSpec ι}
    {Statement Message : ℕ → Type}
    (prover : FailureProverFamily (ι := ι) oSpec Statement Message)
    (queryBound : (secParam : ℕ) → (oracleIdx : ι) → ℕ) : Prop :=
  _root_.Prover.NARG.Family.perIndexQueryBounded prover queryBound

/-- Paper-facing alias for CO25 Definition 3.7 failure probability. -/
abbrev failureProbability
    {Message : Type}
    [oSpec.Fintype] [oSpec.Inhabited]
    (admissible : Set Statement)
    (verifier : NonInteractiveVerifier Message oSpec Statement Bool)
    (prover : OracleComp oSpec (Statement × Message))
    (failureError : ℝ≥0) : Prop :=
  _root_.Verifier.failureProbability admissible verifier prover failureError

/-- Paper-facing alias for CO25 Definition 3.7 with explicit security parameter `λ`. -/
abbrev failureProbabilityFamily
    {oSpec : ℕ → OracleSpec ι}
    [∀ secParam, (oSpec secParam).Fintype] [∀ secParam, (oSpec secParam).Inhabited]
    {Statement Message : ℕ → Type}
    (admissible : (secParam : ℕ) → Set (Statement secParam))
    (verifier :
      (secParam : ℕ) → NonInteractiveVerifier (Message secParam) (oSpec secParam)
        (Statement secParam) Bool)
    (prover : FailureProverFamily (ι := ι) oSpec Statement Message)
    (failureError : (secParam : ℕ) → ℝ≥0) : Prop :=
  _root_.Verifier.failureProbabilityFamily admissible verifier prover failureError

/-- Paper-facing alias for the rewinding extractor interface from CO25 Definition 3.8. -/
abbrev RewindingExtractor (Message : Type) :=
  Extractor.RewindingNARG oSpec Statement Witness Message

/-- Paper-facing alias for CO25 Definition 3.8 rewinding knowledge soundness. -/
abbrev rewindingKnowledgeSoundness
    {Message : Type}
    [oSpec.Fintype] [oSpec.Inhabited]
    (admissible : Set Statement)
    (relation : Set (Statement × Witness))
    (verifier : NonInteractiveVerifier Message oSpec Statement Bool)
    (knowledgeError : (queryBound : ℕ) → (failureError : ℝ≥0) → ℝ≥0)
    {ω : Type} [AddCommMonoid ω]
    (costModel : CostModel oSpec ω)
    (val : ω → ℝ≥0∞)
    (timeBound :
      (prover : FailureProver (oSpec := oSpec) (Statement := Statement) Message) →
        (queryBound : ℕ) → (failureError : ℝ≥0) → ℝ≥0∞) : Prop :=
  _root_.Verifier.rewindingKnowledgeSoundness admissible relation verifier knowledgeError
    costModel val timeBound

/-- Paper-facing alias for CO25 Definition 3.8 with explicit security parameter `λ`. -/
abbrev rewindingKnowledgeSoundnessFamily
    {oSpec : ℕ → OracleSpec ι}
    [∀ secParam, (oSpec secParam).Fintype] [∀ secParam, (oSpec secParam).Inhabited]
    {Statement Witness Message : ℕ → Type}
    (admissible : (secParam : ℕ) → Set (Statement secParam))
    (relation : (secParam : ℕ) → Set (Statement secParam × Witness secParam))
    (verifier :
      (secParam : ℕ) → NonInteractiveVerifier (Message secParam) (oSpec secParam)
        (Statement secParam) Bool)
    (knowledgeError :
      (secParam : ℕ) → (queryBound : ℕ) → (failureError : ℝ≥0) → ℝ≥0)
    {ω : Type} [AddCommMonoid ω]
    (costModel : (secParam : ℕ) → CostModel (oSpec secParam) ω)
    (val : ω → ℝ≥0∞)
    (timeBound :
      (secParam : ℕ) →
        (prover :
          FailureProver (oSpec := oSpec secParam) (Statement := Statement secParam)
            (Message secParam)) →
        (queryBound : ℕ) → (failureError : ℝ≥0) → ℝ≥0∞) : Prop :=
  _root_.Verifier.rewindingKnowledgeSoundnessFamily admissible relation verifier knowledgeError
    costModel val timeBound

end NARG

/-! ## Section 4 -/

/-- Paper-facing alias for CO25 Definition 4.1 codecs. -/
abbrev Codec {n : ℕ} (pSpec : ProtocolSpec n) (U : Type) := ProtocolSpec.Codec pSpec U

/-- Paper-facing alias for the semantic codec obligations from CO25 Definition 4.1.

`IsLawful` is a `Prop`-valued class taking the `Codec` as an instance argument, so the codec
is passed via `(c := codec)`. -/
abbrev LawfulCodec {n : ℕ} {pSpec : ProtocolSpec n} {U : Type}
    (codec : ProtocolSpec.Codec pSpec U) : Prop :=
  ProtocolSpec.Codec.IsLawful (c := codec)

section Section4

variable (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- Paper-facing alias for the hybrid oracle from CO25 Equation 16. -/
abbrev HybridOracle : OracleSpec
    ((i : pSpec.ChallengeIdx) × StmtIn ×
      ((j : pSpec.MessageIdx) → (hj : j.1 < i.1) → Vector U (pSpec.Lₚᵢ j))) :=
  ProtocolSpec.duplexSpongeHybridOracle (StmtIn := StmtIn) (pSpec := pSpec) (U := U)

/-- Paper-facing alias for the random-oracle / ideal-permutation oracle from CO25 Definition 4.2.
-/
abbrev ChallengeOracle : OracleSpec (StmtIn ⊕ CanonicalSpongeState U ⊕ CanonicalSpongeState U) :=
  OracleSpec.duplexSpongeChallengeOracle StmtIn U

end Section4

section Transforms

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- Paper-facing alias for the unsalted DSFS transform from Section 4. -/
abbrev duplexSpongeFiatShamir
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :=
  Reduction.duplexSpongeFiatShamir (U := U) R

/-- Paper-facing alias for the salted DSFS transform from CO25 Construction 4.3. -/
abbrev duplexSpongeFiatShamirSalted {δ : Nat}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    [SampleableType U]
    [unifSpec ⊂ₒ oSpec] [OracleSpec.LawfulSubSpec unifSpec oSpec] :=
  Reduction.duplexSpongeFiatShamirSaltedRandom (U := U) (δ := δ) R

/-- Generalized salted DSFS alias exposing an explicit salt source. This strictly generalizes the
paper-native random-salt wrapper above. -/
abbrev duplexSpongeFiatShamirSaltedWithSaltSource {δ : Nat}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U δ)) :=
  Reduction.duplexSpongeFiatShamirSalted (U := U) sampleSalt R

end Transforms

end DuplexSpongeFS
