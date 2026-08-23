/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import VCVio
import ArkLib.OracleReduction.Security.Basic

/-!
  # Ordinary Commitment Schemes

  This file defines ordinary commitment schemes, where committing to a message also returns the
  opening value that the verifier checks directly.

  This differs from `ArkLib.CommitmentScheme.Basic`, which formalizes *functional* commitment
  schemes with interactive oracle openings for claims of the form "this committed data answers query
  `q` with response `r`".  The structures here are intended for schemes such as Pedersen and Ajtai
  commitments:

  - `keygen : OracleComp oSpec (CommitterKey × VerifierKey)`
  - `commit : CommitterKey → Message → OracleComp oSpec (Commitment × Opening)`
  - `verify : VerifierKey → Commitment → Message → Opening → OracleComp oSpec Bool`
-/

namespace CommitmentScheme

open OracleSpec OracleComp

variable {ι : Type} (oSpec : OracleSpec ι)
  (CommitterKey VerifierKey Message Commitment Opening : Type)

/-- The key-generation algorithm, returning separate keys for the committer and verifier. -/
structure KeyGen where
  keygen : OracleComp oSpec (CommitterKey × VerifierKey)

/-- The commitment algorithm, returning both the commitment and its opening value. -/
structure Commit where
  commit : CommitterKey → Message → OracleComp oSpec (Commitment × Opening)

/-- The verifier for a claimed opening. -/
structure Verify where
  verify : VerifierKey → Commitment → Message → Opening → OracleComp oSpec Bool

/-- An ordinary commitment scheme. -/
structure Scheme extends
    KeyGen oSpec CommitterKey VerifierKey,
    Commit oSpec CommitterKey Message Commitment Opening,
    Verify oSpec VerifierKey Message Commitment Opening

section Security

noncomputable section

open scoped NNReal

variable [DecidableEq ι]
  {oSpec : OracleSpec ι} {CommitterKey VerifierKey Message Commitment Opening : Type}
  [oSpec.Fintype] [oSpec.Inhabited]

/-- A commitment scheme satisfies **correctness** with error `correctnessError` if, for every
  message, the honestly generated commitment and opening verify with probability at least
  `1 - correctnessError`. -/
def correctness (scheme : Scheme oSpec CommitterKey VerifierKey Message Commitment Opening)
    (correctnessError : ℝ≥0) : Prop :=
  ∀ message : Message,
    Pr[ fun accepted => accepted | do
        let ⟨committerKey, verifierKey⟩ ← scheme.keygen
        let ⟨cm, op⟩ ← scheme.commit committerKey message
        scheme.verify verifierKey cm message op] ≥ 1 - correctnessError

/-- A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no
  error. -/
def perfectCorrectness
    (scheme : Scheme oSpec CommitterKey VerifierKey Message Commitment Opening) : Prop :=
  correctness scheme 0

/-- The output of an adversary in the binding game: a commitment and two purported openings to
  possibly different messages. -/
structure BindingAdversaryOutput (Message Commitment Opening : Type) where
  commitment : Commitment
  message₁ : Message
  opening₁ : Opening
  message₂ : Message
  opening₂ : Opening

/-- An adversary in the binding game returns a commitment and two purported openings to possibly
  different messages. -/
structure BindingAdversary (oSpec : OracleSpec ι)
    (CommitterKey VerifierKey Message Commitment Opening : Type) where
  run : CommitterKey → VerifierKey →
    OracleComp oSpec (BindingAdversaryOutput Message Commitment Opening)

/-- The outcome tracked in the binding experiment. -/
structure BindingExperimentOutput (Message : Type) where
  message₁ : Message
  message₂ : Message
  accept₁ : Bool
  accept₂ : Bool

/-- A commitment scheme satisfies **binding** with error `bindingError` if every adversary's
  probability of producing two accepting openings of the same commitment to distinct messages is at
  most `bindingError`. -/
def binding (scheme : Scheme oSpec CommitterKey VerifierKey Message Commitment Opening)
    (bindingError : ℝ≥0) : Prop :=
  ∀ adversary : BindingAdversary oSpec CommitterKey VerifierKey Message Commitment Opening,
    Pr[ fun result : BindingExperimentOutput Message =>
        result.message₁ ≠ result.message₂ ∧ result.accept₁ ∧ result.accept₂ | do
      let ⟨committerKey, verifierKey⟩ ← scheme.keygen
      let result ← adversary.run committerKey verifierKey
      let accept₁ ← scheme.verify verifierKey result.commitment result.message₁ result.opening₁
      let accept₂ ← scheme.verify verifierKey result.commitment result.message₂ result.opening₂
      return (BindingExperimentOutput.mk result.message₁ result.message₂ accept₁ accept₂)] ≤
        bindingError

/-- A commitment scheme satisfies **perfect binding** if it satisfies binding with no error. -/
def perfectBinding
    (scheme : Scheme oSpec CommitterKey VerifierKey Message Commitment Opening) : Prop :=
  binding scheme 0

/-- A **straightline extractor** for a standard commitment scheme takes the commitment and the log
  of queries made while producing it, and returns a message. -/
def StraightlineExtractor (oSpec : OracleSpec ι)
    (CommitterKey VerifierKey Message Commitment : Type) :=
  CommitterKey → VerifierKey → Commitment → QueryLog oSpec → Message

/-- An adversary in the extractability game returns a commitment, a claimed message/opening pair,
  and auxiliary state that can be used by later security games. -/
structure ExtractabilityAdversaryOutput (Message Commitment Opening AuxState : Type) where
  commitment : Commitment
  message : Message
  opening : Opening
  auxState : AuxState

/-- An adversary in the extractability game returns a commitment, a claimed message/opening pair,
  and auxiliary state that can be used by later security games. -/
structure ExtractabilityAdversary (oSpec : OracleSpec ι)
    (CommitterKey VerifierKey Message Commitment Opening AuxState : Type) where
  run : CommitterKey → VerifierKey →
    OracleComp oSpec (ExtractabilityAdversaryOutput Message Commitment Opening AuxState)

/-- The outcome tracked in the extractability experiment. -/
structure ExtractabilityExperimentOutput (Message : Type) where
  claimedMessage : Message
  extractedMessage : Message
  accept : Bool

/-- A commitment scheme satisfies **extractability** with error `extractabilityError` if there
  exists a straightline extractor `extractor` such that for every adversary outputting a commitment
  and a claimed opening, the probability that:

  1. the claimed opening verifies, and
  2. the extractor returns a different message from the claimed one

  is at most `extractabilityError`.

  The extractor is straightline: it receives only the commitment and the log of the adversary's
  oracle queries made while producing that commitment. -/
def extractability (scheme : Scheme oSpec CommitterKey VerifierKey Message Commitment Opening)
    (extractabilityError : ℝ≥0) : Prop :=
  ∃ extractor : StraightlineExtractor oSpec CommitterKey VerifierKey Message Commitment,
  ∀ AuxState : Type,
  ∀ adversary :
    ExtractabilityAdversary oSpec CommitterKey VerifierKey Message Commitment Opening AuxState,
    Pr[ fun result : ExtractabilityExperimentOutput Message =>
        result.accept ∧ result.extractedMessage ≠ result.claimedMessage | do
      let ⟨committerKey, verifierKey⟩ ← scheme.keygen
      let ⟨result, queryLog⟩ ←
        WriterT.run (simulateQ loggingOracle (adversary.run committerKey verifierKey))
      let extractedMessage := extractor committerKey verifierKey result.commitment queryLog
      let accept ← scheme.verify verifierKey result.commitment result.message result.opening
      return (ExtractabilityExperimentOutput.mk result.message extractedMessage accept)] ≤
        extractabilityError

/-- The first-phase output of a hiding adversary: two challenge messages and state passed to the
  distinguishing phase. -/
structure HidingChallenge (Message State : Type) where
  message₁ : Message
  message₂ : Message
  state : State

/-- A two-phase adversary for the hiding game. The adversary first chooses two messages and private
  state, then receives a commitment to one of the two messages and tries to distinguish which
  experiment it is in. -/
structure HidingAdversary (oSpec : OracleSpec ι)
    (CommitterKey VerifierKey Message Commitment : Type) where
  State : Type
  choose : CommitterKey → VerifierKey → OracleComp oSpec (HidingChallenge Message State)
  distinguish : CommitterKey → VerifierKey → State → Commitment → OracleComp oSpec Bool

/-- The left/right hiding experiment. If `useRight = false`, the challenger commits to the first
  message chosen by the adversary; if `useRight = true`, it commits to the second. In both cases,
  only the commitment, not the opening value, is given to the distinguisher. -/
def hidingExperiment (scheme : Scheme oSpec CommitterKey VerifierKey Message Commitment Opening)
    (adversary : HidingAdversary oSpec CommitterKey VerifierKey Message Commitment)
    (useRight : Bool) :
    OracleComp oSpec Bool := do
  let ⟨committerKey, verifierKey⟩ ← scheme.keygen
  let challenge ← adversary.choose committerKey verifierKey
  let message := if useRight then challenge.message₂ else challenge.message₁
  let ⟨cm, _⟩ ← scheme.commit committerKey message
  adversary.distinguish committerKey verifierKey challenge.state cm

/-- A commitment scheme satisfies **hiding** with error `hidingError` if no two-phase adversary can
  distinguish commitments to two adaptively chosen messages except with statistical distance at most
  `hidingError`.

  We state this as the standard pair of one-sided inequalities between the adversary's acceptance
  probabilities in the left and right experiments. This avoids baking a particular random-bit
  sampler into the oracle specification while remaining equivalent to bounding the usual
  left-vs-right distinguishing advantage. -/
def hiding' (scheme : Scheme oSpec CommitterKey VerifierKey Message Commitment Opening)
    (hidingError : ℝ≥0) : Prop :=
  ∀ adversary : HidingAdversary oSpec CommitterKey VerifierKey Message Commitment,
    Pr[= true | hidingExperiment scheme adversary false] ≤
        Pr[= true | hidingExperiment scheme adversary true] + hidingError ∧
    Pr[= true | hidingExperiment scheme adversary true] ≤
        Pr[= true | hidingExperiment scheme adversary false] + hidingError

end

end Security

end CommitmentScheme
