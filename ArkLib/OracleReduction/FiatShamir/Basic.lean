/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.Security.ZeroKnowledge
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec

/-!
  # The Basic Fiat-Shamir Transformation

  This file defines the basic Fiat-Shamir transformation. This transformation takes in a
  (public-coin) interactive reduction (IR) `R` and transforms it into a non-interactive reduction in
  the following way:
  - Each verifier's challenge, instead of being sent from the verifier, will be obtained from a
    Fiat-Shamir oracle, which for the `i`-th challenge requires the input statement and all messages
    up to round `i`

  This is the _basic_ (or slow) version to be distinguished from the more efficient version based on
  duplex sponge (see `DuplexSponge` folder).

  We will show that the transformation satisfies security properties as follows:

  - Completeness is preserved
  - State-restoration (knowledge) soundness implies (knowledge) soundness
  - Honest-verifier zero-knowledge implies zero-knowledge

  ## Notes

  Our formalization mostly follows the treatment in the Chiesa-Yogev textbook.
-/

universe u v

section find_home

variable {n : ℕ} {σ τ : Type u} {m : Type u → Type v} [Monad m]

/-- Traverse a dependent function indexed by `Fin n` in any monad. -/
def Fin.traverseM {β : Fin n → Type u}
    (f : (i : Fin n) → m (β i)) : m ((i : Fin n) → β i) :=
  let rec aux (k : ℕ) (h : k ≤ n) : m ((i : Fin k) → β (Fin.castLE h i)) :=
    match k with
    | 0 => pure (fun i => i.elim0)
    | k' + 1 => do
      let tail ← aux k' (Nat.le_of_succ_le h)
      let head ← f (Fin.castLE h (Fin.last k'))
      return (Fin.snoc tail head)
  aux n (le_refl n)

instance : MonadLift (StateT σ m) (StateT (σ × τ) m) where
  monadLift := fun x st => do let y ← x st.1; return (y.1, y.2, st.2)

instance : MonadLift (StateT τ m) (StateT (σ × τ) m) where
  monadLift := fun x st => do let y ← x st.2; return (y.1, st.1, y.2)

end find_home

open ProtocolSpec OracleComp OracleSpec

open scoped BigOperators

variable {n : ℕ}

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

-- In order to define the Fiat-Shamir transformation for the prover, we need to define
-- a slightly altered execution for the prover

/--
Prover's function for processing the next round, given the current result of the previous round.

  This is modified for Fiat-Shamir, where we only accumulate the messages and not the challenges.
-/
@[inline, specialize]
def Prover.processRoundFS [∀ i, VCVCompatible (pSpec.Challenge i)] (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
      (pSpec.MessagesUpTo j.castSucc × StmtIn × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
        (pSpec.MessagesUpTo j.succ × StmtIn × prover.PrvState j.succ) := do
  let ⟨messages, stmtIn, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let f ← prover.receiveChallenge ⟨j, hDir⟩ state
    let challenge ← query (spec := fsChallengeOracle StmtIn pSpec) ⟨⟨j, hDir⟩, ⟨stmtIn, messages⟩⟩
    return ⟨messages.extend hDir, stmtIn, f challenge⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨messages.concat hDir msg, stmtIn, newState⟩

/--
Run the prover in an interactive reduction up to round index `i`, via first inputting the
  statement and witness, and then processing each round up to round `i`. Returns the transcript up
  to round `i`, and the prover's state after round `i`.
-/
@[inline, specialize]
def Prover.runToRoundFS [∀ i, VCVCompatible (pSpec.Challenge i)] (i : Fin (n + 1))
    (stmt : StmtIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
          (pSpec.MessagesUpTo i × StmtIn × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, stmt, state⟩)
    prover.processRoundFS
    i

/-- The (slow) Fiat-Shamir transformation for the prover. -/
def Prover.fiatShamir (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveProver (∀ i, pSpec.Message i) (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => StmtIn × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨ctx.1, P.input ctx⟩
  -- Compute the messages to send via the modified `runToRoundFS`
  sendMessage | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ => do
    let ⟨messages, _, state⟩ ← P.runToRoundFS (Fin.last n) stmtIn state
    return ⟨messages, state⟩
  -- This function is never invoked so we apply the elimination principle
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => (P.output st).liftComp _

/-- The (slow) Fiat-Shamir transformation for the verifier. -/
def Verifier.fiatShamir (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (∀ i, pSpec.Message i) (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    let messages : pSpec.Messages := proof 0
    let transcript ← (messages.deriveTranscriptFS (oSpec := oSpec) stmtIn)
    Option.getM (← (V.verify stmtIn transcript).run)

/-- The Fiat-Shamir transformation for an (interactive) reduction, which consists of applying the
  Fiat-Shamir transformation to both the prover and the verifier. -/
def Reduction.fiatShamir (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    NonInteractiveReduction (∀ i, pSpec.Message i) (oSpec + fsChallengeOracle StmtIn pSpec)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.fiatShamir
  verifier := R.verifier.fiatShamir

section Execution

-- Show that the Fiat-Shamir prover's run gives the same output as the original prover's run

namespace Verifier

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Expanding the basic Fiat-Shamir verifier shows that it re-derives the transcript from the proof
messages via the Fiat-Shamir oracle and then runs the original verifier. -/
@[simp]
theorem fiatShamir_verify_eq
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : FullTranscript ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩) :
    (V.fiatShamir).verify stmtIn proof =
      (do
        let messages : pSpec.Messages := proof 0
        let transcript ← messages.deriveTranscriptFS (oSpec := oSpec) stmtIn
        let v ← (V.verify stmtIn transcript).run
        v.getM) := by
  rfl

end Verifier

#print axioms Prover.processRoundFS
#print axioms Prover.runToRoundFS
#print axioms Prover.fiatShamir
#print axioms Verifier.fiatShamir
#print axioms Verifier.fiatShamir_verify_eq
#print axioms Reduction.fiatShamir


end Execution

section Security

noncomputable section

open scoped NNReal

variable [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

namespace Reduction

section Completeness

local instance fiatShamirProverOnly : ProtocolSpec.ProverOnly
    ⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩ where
  prover_first' := by simp

abbrev FiatShamirProtocolSpec : ProtocolSpec 1 :=
  ⟨!v[Direction.P_to_V], !v[(i : pSpec.MessageIdx) → pSpec.Message i]⟩

local instance fiatShamirChallengeOracleInterface :
    ∀ i : (FiatShamirProtocolSpec (pSpec := pSpec)).ChallengeIdx,
      OracleInterface ((FiatShamirProtocolSpec (pSpec := pSpec)).Challenge i) :=
  challengeOracleInterface (pSpec := FiatShamirProtocolSpec (pSpec := pSpec))

/-- The one-message proof transcript produced by the basic Fiat-Shamir transform. -/
abbrev FiatShamirProofTranscript :=
  FullTranscript (FiatShamirProtocolSpec (pSpec := pSpec))

/-- The explicit honest execution underlying the basic Fiat-Shamir transform. -/
def fiatShamirHonestExecution
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
      ((FiatShamirProofTranscript (pSpec := pSpec) × StmtOut × WitOut) × StmtOut) := do
  let state := R.prover.input (stmtIn, witIn)
  let ⟨messages, _, state⟩ ← liftM <|
    R.prover.runToRoundFS (Fin.last n) stmtIn state
  let ctxOut ← liftM <|
    (R.prover.output state).liftComp (oSpec + fsChallengeOracle StmtIn pSpec)
  let proof : FiatShamirProofTranscript (pSpec := pSpec) := fun
    | ⟨0, _⟩ => messages
  let stmtOut ← (R.verifier.fiatShamir).run stmtIn proof
  return ⟨⟨proof, ctxOut⟩, stmtOut⟩

omit [VCVCompatible StmtIn] [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Raw proof-message send step of the transformed basic Fiat-Shamir prover. -/
theorem fiatShamir_sendMessage_eq_raw
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    (R.prover.fiatShamir).sendMessage =
      fun | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ => do
        let ⟨messages, _, state⟩ ←
          R.prover.runToRoundFS (Fin.last n) stmtIn state
        return ⟨messages, state⟩ := by
  rfl

omit [VCVCompatible StmtIn] [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Specializing the generic single-prover-message run theorem to the basic Fiat-Shamir transform
exposes the outer run shell: transformed prover input, one transformed proof-message send,
transcript assembly, transformed verifier run, and final `OptionT` verdict extraction. -/
theorem fiatShamir_run_eq_oneMessage
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    R.fiatShamir.run stmtIn witIn =
      (have state := R.fiatShamir.prover.input (stmtIn, witIn)
      do
        let ⟨msg, state⟩ ←
          (liftM
            (m := OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
            (n := OptionT (OracleComp
              ((oSpec + fsChallengeOracle StmtIn pSpec) +
                [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)))
            (self := instMonadLiftTOfMonadLift
              (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
              (OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)))
              (OptionT (OracleComp
                ((oSpec + fsChallengeOracle StmtIn pSpec) +
                  [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))))
            (R.fiatShamir.prover.sendMessage ⟨0, by simp⟩ state))
        let ctxOut ←
          (liftM
            (m := OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
            (n := OptionT (OracleComp
              ((oSpec + fsChallengeOracle StmtIn pSpec) +
                [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)))
            (self := instMonadLiftTOfMonadLift
              (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
              (OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)))
              (OptionT (OracleComp
                ((oSpec + fsChallengeOracle StmtIn pSpec) +
                  [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))))
            (R.fiatShamir.prover.output state))
        have transcript : (FiatShamirProtocolSpec (pSpec := pSpec)).FullTranscript :=
          fun i => match i with | ⟨0, _⟩ => msg
        let stmtOut ←
          (liftM
            (m := OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
            (n := OptionT (OracleComp
              ((oSpec + fsChallengeOracle StmtIn pSpec) +
                [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ)))
            (self := instMonadLiftTOfMonadLift
              (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
              (OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)))
              (OptionT (OracleComp
                ((oSpec + fsChallengeOracle StmtIn pSpec) +
                  [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ))))
            (R.fiatShamir.verifier.verify stmtIn transcript).run)
        return (⟨transcript, ctxOut⟩, ← stmtOut.getM)) := by
  simpa only using
    (Reduction.run_of_prover_first
      (pSpec := FiatShamirProtocolSpec (pSpec := pSpec))
      stmtIn witIn R.fiatShamir)

/-- The transformed basic Fiat-Shamir run is the lifted explicit honest execution. -/
def fiatShamir_run_eq_honestExecution
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prop :=
    R.fiatShamir.run stmtIn witIn =
      liftM (R.fiatShamirHonestExecution stmtIn witIn)

/-- Residual for collapsing the outer basic-Fiat-Shamir challenge implementation after unrolling
the transformed run. The right-hand honest execution already queries the Fiat-Shamir challenge
oracle directly; the remaining content is the same `OptionT` lift-coherence wall as the DSFS
completeness bridge, specialized to the unsalted basic transform. -/
def fiatShamir_runCollapseResidual
    {σ : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prop :=
    simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (R.fiatShamir.run stmtIn witIn).run =
      simulateQ impl
        (R.fiatShamirHonestExecution stmtIn witIn).run

/-- The named run-equality residual discharges the outer basic-Fiat-Shamir challenge-collapse
residual.  After rewriting the transformed run to the lifted explicit honest execution, the only
normalization step is the `OptionT.run` lift through the right-associated oracle sum; this is
collapsed by `simulateQ_add_liftComp_add_assoc_left`. -/
theorem fiatShamir_runCollapseResidual_of_run_eq_honestExecution
    {σ : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn)
    (hRun : fiatShamir_run_eq_honestExecution R stmtIn witIn) :
    fiatShamir_runCollapseResidual impl R stmtIn witIn := by
  unfold fiatShamir_runCollapseResidual fiatShamir_run_eq_honestExecution at *
  rw [hRun]
  let chSpec := [(FiatShamirProtocolSpec (pSpec := pSpec)).Challenge]ₒ
  change simulateQ (QueryImpl.addLift impl challengeQueryImpl)
      (OracleComp.liftComp
        (OracleComp.liftComp (R.fiatShamirHonestExecution stmtIn witIn).run
          (oSpec + (fsChallengeOracle StmtIn pSpec + chSpec)))
        ((oSpec + fsChallengeOracle StmtIn pSpec) + chSpec)) =
    simulateQ impl (R.fiatShamirHonestExecution stmtIn witIn).run
  simpa [chSpec, QueryImpl.addLift_def, QueryImpl.liftTarget_self] using
    simulateQ_add_liftComp_add_assoc_left
      (spec₁ := oSpec) (spec₂ := fsChallengeOracle StmtIn pSpec) (spec₃ := chSpec)
      impl
      (QueryImpl.liftTarget (StateT σ ProbComp)
        (challengeQueryImpl (pSpec := FiatShamirProtocolSpec (pSpec := pSpec))))
      (R.fiatShamirHonestExecution stmtIn witIn).run

/-- Completeness of the transformed one-message reduction is equivalent to the explicit honest
Fiat-Shamir execution packaged via `Reduction.fiatShamirHonestExecution`. -/
def fiatShamir_completeness_unroll
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Prop :=
    R.fiatShamir.completeness init impl relIn relOut completenessError ↔
      Reduction.completenessFromRun init impl relIn relOut
        (R.fiatShamirHonestExecution) completenessError

/-- **Reduction of `fiatShamir_completeness_unroll` to the run-collapse residual.**

Given the per-input `fiatShamir_runCollapseResidual`, completeness of the transformed one-message
basic Fiat-Shamir reduction is definitionally the generic `completenessFromRun` predicate over
`fiatShamirHonestExecution`. -/
theorem fiatShamir_completeness_unroll_of_runCollapse
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      fiatShamir_runCollapseResidual impl R stmtIn witIn) :
    fiatShamir_completeness_unroll init impl relIn relOut completenessError R := by
  unfold fiatShamir_completeness_unroll
  rw [Reduction.completeness_iff_completenessFromRun]
  unfold Reduction.completenessFromRun
  refine forall_congr' fun stmtIn => forall_congr' fun witIn => ?_
  refine imp_congr_right fun _ => ?_
  have hcollapse :
      simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          (R.fiatShamir.run stmtIn witIn).run =
        simulateQ impl
          (R.fiatShamirHonestExecution stmtIn witIn).run :=
    hCollapse stmtIn witIn
  rw [hcollapse]

/-- The named run-equality residual is enough to unroll basic-Fiat-Shamir completeness to the
explicit honest-execution experiment. This packages
`fiatShamir_runCollapseResidual_of_run_eq_honestExecution` into the existing unroll bridge. -/
theorem fiatShamir_completeness_unroll_of_runEq
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      fiatShamir_run_eq_honestExecution R stmtIn witIn) :
    fiatShamir_completeness_unroll init impl relIn relOut completenessError R :=
  fiatShamir_completeness_unroll_of_runCollapse init impl relIn relOut
    completenessError R fun stmtIn witIn =>
      fiatShamir_runCollapseResidual_of_run_eq_honestExecution impl R stmtIn witIn
        (hRun stmtIn witIn)

/-- Basic Fiat-Shamir completeness follows from the run-collapse residual and completeness of the
explicit honest-execution experiment. This is the forward direction of
`fiatShamir_completeness_unroll_of_runCollapse`, packaged for downstream users that do not need the
full equivalence. -/
theorem fiatShamir_completeness_of_honestExecution
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      fiatShamir_runCollapseResidual impl R stmtIn witIn)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      (R.fiatShamirHonestExecution) completenessError) :
    R.fiatShamir.completeness init impl relIn relOut completenessError :=
  (fiatShamir_completeness_unroll_of_runCollapse init impl relIn relOut completenessError
    R hCollapse).2 hHonest

/-- Basic Fiat-Shamir completeness follows from the named run-equality residual and completeness of
the explicit honest-execution experiment. This leaves the genuine run-equality theorem as the only
completeness-side residual. -/
theorem fiatShamir_completeness_of_runEq
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      fiatShamir_run_eq_honestExecution R stmtIn witIn)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      (R.fiatShamirHonestExecution) completenessError) :
    R.fiatShamir.completeness init impl relIn relOut completenessError :=
  (fiatShamir_completeness_unroll_of_runEq init impl relIn relOut completenessError
    R hRun).2 hHonest

/-- Transformed basic Fiat-Shamir completeness can be projected back to completeness of the explicit
honest-execution experiment once the run-collapse residual is available. This is the reverse
direction of `fiatShamir_completeness_unroll_of_runCollapse`, exposed as a theorem-level helper. -/
theorem fiatShamir_honestExecution_completeness_of_completeness
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      fiatShamir_runCollapseResidual impl R stmtIn witIn)
    (hFS : R.fiatShamir.completeness init impl relIn relOut completenessError) :
    Reduction.completenessFromRun init impl relIn relOut
      (R.fiatShamirHonestExecution) completenessError :=
  (fiatShamir_completeness_unroll_of_runCollapse init impl relIn relOut completenessError
    R hCollapse).1 hFS

/-- Transformed basic Fiat-Shamir completeness can be projected back to completeness of the explicit
honest-execution experiment once the named run-equality residual is available. -/
theorem fiatShamir_honestExecution_completeness_of_runEq
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      fiatShamir_run_eq_honestExecution R stmtIn witIn)
    (hFS : R.fiatShamir.completeness init impl relIn relOut completenessError) :
    Reduction.completenessFromRun init impl relIn relOut
      (R.fiatShamirHonestExecution) completenessError :=
  (fiatShamir_completeness_unroll_of_runEq init impl relIn relOut completenessError
    R hRun).1 hFS

/-- Perfect completeness of the transformed one-message reduction is equivalent to perfect
completeness of the explicit honest Fiat-Shamir execution. This is the zero-error specialization
of `fiatShamir_completeness_unroll`, stated in the `perfectCompleteness` API. -/
def fiatShamir_perfectCompleteness_unroll
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Prop :=
    R.fiatShamir.perfectCompleteness init impl relIn relOut ↔
      Reduction.perfectCompletenessFromRun init impl relIn relOut
        R.fiatShamirHonestExecution

/-- The run-collapse residual unrolls basic-Fiat-Shamir perfect completeness to the explicit
honest-execution perfect-completeness predicate. -/
theorem fiatShamir_perfectCompleteness_unroll_of_runCollapse
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      fiatShamir_runCollapseResidual impl R stmtIn witIn) :
    fiatShamir_perfectCompleteness_unroll init impl relIn relOut R := by
  unfold fiatShamir_perfectCompleteness_unroll Reduction.perfectCompleteness
    Reduction.perfectCompletenessFromRun
  exact fiatShamir_completeness_unroll_of_runCollapse init impl relIn relOut 0 R hCollapse

/-- The named run-equality residual unrolls basic-Fiat-Shamir perfect completeness to the explicit
honest-execution perfect-completeness predicate. -/
theorem fiatShamir_perfectCompleteness_unroll_of_runEq
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      fiatShamir_run_eq_honestExecution R stmtIn witIn) :
    fiatShamir_perfectCompleteness_unroll init impl relIn relOut R :=
  fiatShamir_perfectCompleteness_unroll_of_runCollapse init impl relIn relOut R
    fun stmtIn witIn =>
      fiatShamir_runCollapseResidual_of_run_eq_honestExecution impl R stmtIn witIn
        (hRun stmtIn witIn)

/-- Basic Fiat-Shamir perfect completeness follows from perfect completeness of the explicit
honest-execution experiment and the run-collapse residual. -/
theorem fiatShamir_perfectCompleteness_of_honestExecution
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      fiatShamir_runCollapseResidual impl R stmtIn witIn)
    (hHonest : Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution) :
    R.fiatShamir.perfectCompleteness init impl relIn relOut :=
  (fiatShamir_perfectCompleteness_unroll_of_runCollapse init impl relIn relOut R
    hCollapse).2 hHonest

/-- Basic Fiat-Shamir perfect completeness follows from perfect completeness of the explicit
honest-execution experiment and the named run-equality residual. -/
theorem fiatShamir_perfectCompleteness_of_runEq
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      fiatShamir_run_eq_honestExecution R stmtIn witIn)
    (hHonest : Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution) :
    R.fiatShamir.perfectCompleteness init impl relIn relOut :=
  (fiatShamir_perfectCompleteness_unroll_of_runEq init impl relIn relOut R hRun).2 hHonest

/-- Basic Fiat-Shamir perfect completeness can be projected back to perfect completeness of the
explicit honest-execution experiment once the run-collapse residual is available. -/
theorem fiatShamir_honestExecution_perfectCompleteness_of_perfectCompleteness
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      fiatShamir_runCollapseResidual impl R stmtIn witIn)
    (hFS : R.fiatShamir.perfectCompleteness init impl relIn relOut) :
    Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution :=
  (fiatShamir_perfectCompleteness_unroll_of_runCollapse init impl relIn relOut R
    hCollapse).1 hFS

/-- Basic Fiat-Shamir perfect completeness can be projected back to perfect completeness of the
explicit honest-execution experiment once the named run-equality residual is available. -/
theorem fiatShamir_honestExecution_perfectCompleteness_of_runEq
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      fiatShamir_run_eq_honestExecution R stmtIn witIn)
    (hFS : R.fiatShamir.perfectCompleteness init impl relIn relOut) :
    Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution :=
  (fiatShamir_perfectCompleteness_unroll_of_runEq init impl relIn relOut R hRun).1 hFS

/-- Basic Fiat-Shamir completeness at a larger target error follows from honest-execution
completeness at a smaller error after applying the run-collapse residual. -/
theorem fiatShamir_completeness_of_honestExecution_mono_error
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    {completenessError₁ completenessError₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      fiatShamir_runCollapseResidual impl R stmtIn witIn)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      (R.fiatShamirHonestExecution) completenessError₁)
    (hle : completenessError₁ ≤ completenessError₂) :
    R.fiatShamir.completeness init impl relIn relOut completenessError₂ :=
  Reduction.completeness_error_mono init impl hle
    (fiatShamir_completeness_of_honestExecution init impl relIn relOut
      completenessError₁ R hCollapse hHonest)

/-- Basic Fiat-Shamir completeness can be transported to a smaller input relation and a larger
output relation after applying the run-collapse residual. -/
theorem fiatShamir_completeness_of_honestExecution_mono_relations
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)}
    {relOut relOut' : Set (StmtOut × WitOut)}
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      fiatShamir_runCollapseResidual impl R stmtIn witIn)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      (R.fiatShamirHonestExecution) completenessError)
    (hIn : relIn' ⊆ relIn) (hOut : relOut ⊆ relOut') :
    R.fiatShamir.completeness init impl relIn' relOut' completenessError :=
  Reduction.completeness_relOut_mono init impl hOut <|
    Reduction.completeness_relIn_mono init impl hIn <|
      fiatShamir_completeness_of_honestExecution init impl relIn relOut
        completenessError R hCollapse hHonest

/-- Basic Fiat-Shamir completeness can simultaneously transport relations and increase the target
completeness error after applying the run-collapse residual. -/
theorem fiatShamir_completeness_of_honestExecution_mono_relations_error
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)}
    {relOut relOut' : Set (StmtOut × WitOut)}
    {completenessError₁ completenessError₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      fiatShamir_runCollapseResidual impl R stmtIn witIn)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      (R.fiatShamirHonestExecution) completenessError₁)
    (hIn : relIn' ⊆ relIn) (hOut : relOut ⊆ relOut')
    (hle : completenessError₁ ≤ completenessError₂) :
    R.fiatShamir.completeness init impl relIn' relOut' completenessError₂ := by
  have hComplete :
      R.fiatShamir.completeness init impl relIn' relOut' completenessError₁ :=
    fiatShamir_completeness_of_honestExecution_mono_relations init impl
      completenessError₁ R hCollapse hHonest hIn hOut
  exact Reduction.completeness_error_mono init impl hle hComplete

/-- Basic Fiat-Shamir completeness at a larger target error follows directly from the named
run-equality residual and honest-execution completeness at a smaller error. -/
theorem fiatShamir_completeness_of_runEq_mono_error
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    {completenessError₁ completenessError₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      fiatShamir_run_eq_honestExecution R stmtIn witIn)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      (R.fiatShamirHonestExecution) completenessError₁)
    (hle : completenessError₁ ≤ completenessError₂) :
    R.fiatShamir.completeness init impl relIn relOut completenessError₂ :=
  fiatShamir_completeness_of_honestExecution_mono_error init impl relIn relOut R
    (fun stmtIn witIn =>
      fiatShamir_runCollapseResidual_of_run_eq_honestExecution impl R stmtIn witIn
        (hRun stmtIn witIn))
    hHonest hle

/-- Basic Fiat-Shamir completeness can be transported to a smaller input relation and a larger
output relation after applying the named run-equality residual. -/
theorem fiatShamir_completeness_of_runEq_mono_relations
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)}
    {relOut relOut' : Set (StmtOut × WitOut)}
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      fiatShamir_run_eq_honestExecution R stmtIn witIn)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      (R.fiatShamirHonestExecution) completenessError)
    (hIn : relIn' ⊆ relIn) (hOut : relOut ⊆ relOut') :
    R.fiatShamir.completeness init impl relIn' relOut' completenessError :=
  fiatShamir_completeness_of_honestExecution_mono_relations init impl
    completenessError R
    (fun stmtIn witIn =>
      fiatShamir_runCollapseResidual_of_run_eq_honestExecution impl R stmtIn witIn
        (hRun stmtIn witIn))
    hHonest hIn hOut

/-- Basic Fiat-Shamir completeness can simultaneously transport relations and increase the target
completeness error after applying the named run-equality residual. -/
theorem fiatShamir_completeness_of_runEq_mono_relations_error
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)}
    {relOut relOut' : Set (StmtOut × WitOut)}
    {completenessError₁ completenessError₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      fiatShamir_run_eq_honestExecution R stmtIn witIn)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      (R.fiatShamirHonestExecution) completenessError₁)
    (hIn : relIn' ⊆ relIn) (hOut : relOut ⊆ relOut')
    (hle : completenessError₁ ≤ completenessError₂) :
    R.fiatShamir.completeness init impl relIn' relOut' completenessError₂ :=
  fiatShamir_completeness_of_honestExecution_mono_relations_error init impl R
    (fun stmtIn witIn =>
      fiatShamir_runCollapseResidual_of_run_eq_honestExecution impl R stmtIn witIn
        (hRun stmtIn witIn))
    hHonest hIn hOut hle

/-- Basic Fiat-Shamir perfect completeness can be transported to a smaller input relation and a
larger output relation after applying the run-collapse residual. This is the zero-error counterpart
of `fiatShamir_completeness_of_honestExecution_mono_relations`. -/
theorem fiatShamir_perfectCompleteness_of_honestExecution_mono_relations
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)}
    {relOut relOut' : Set (StmtOut × WitOut)}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      fiatShamir_runCollapseResidual impl R stmtIn witIn)
    (hHonest : Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution)
    (hIn : relIn' ⊆ relIn) (hOut : relOut ⊆ relOut') :
    R.fiatShamir.perfectCompleteness init impl relIn' relOut' := by
  unfold Reduction.perfectCompleteness Reduction.perfectCompletenessFromRun at *
  exact fiatShamir_completeness_of_honestExecution_mono_relations init impl
    (relIn := relIn) (relIn' := relIn') (relOut := relOut) (relOut' := relOut')
    0 R hCollapse hHonest hIn hOut

/-- Basic Fiat-Shamir perfect completeness can be transported to a smaller input relation and a
larger output relation after applying the named run-equality residual. -/
theorem fiatShamir_perfectCompleteness_of_runEq_mono_relations
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)}
    {relOut relOut' : Set (StmtOut × WitOut)}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      fiatShamir_run_eq_honestExecution R stmtIn witIn)
    (hHonest : Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution)
    (hIn : relIn' ⊆ relIn) (hOut : relOut ⊆ relOut') :
    R.fiatShamir.perfectCompleteness init impl relIn' relOut' :=
  fiatShamir_perfectCompleteness_of_honestExecution_mono_relations init impl
    (relIn := relIn) (relIn' := relIn') (relOut := relOut) (relOut' := relOut')
    R
    (fun stmtIn witIn =>
      fiatShamir_runCollapseResidual_of_run_eq_honestExecution impl R stmtIn witIn
        (hRun stmtIn witIn))
    hHonest hIn hOut

/-- Basic Fiat-Shamir completeness at any target error follows from perfect completeness of the
explicit honest-execution experiment and the run-collapse residual. -/
theorem fiatShamir_completeness_of_perfect_honestExecution_mono_error
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      fiatShamir_runCollapseResidual impl R stmtIn witIn)
    (hHonest : Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution) :
    R.fiatShamir.completeness init impl relIn relOut completenessError := by
  unfold Reduction.perfectCompletenessFromRun at hHonest
  exact fiatShamir_completeness_of_honestExecution_mono_error init impl relIn relOut
    (completenessError₁ := 0) (completenessError₂ := completenessError)
    R hCollapse hHonest (zero_le completenessError)

/-- Basic Fiat-Shamir completeness at any target error follows from perfect completeness of the
explicit honest-execution experiment and the named run-equality residual. -/
theorem fiatShamir_completeness_of_perfect_runEq_mono_error
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      fiatShamir_run_eq_honestExecution R stmtIn witIn)
    (hHonest : Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution) :
    R.fiatShamir.completeness init impl relIn relOut completenessError := by
  unfold Reduction.perfectCompletenessFromRun at hHonest
  exact fiatShamir_completeness_of_runEq_mono_error init impl relIn relOut
    (completenessError₁ := 0) (completenessError₂ := completenessError)
    R hRun hHonest (zero_le completenessError)

/-- Basic Fiat-Shamir completeness can be transported to a smaller input relation, larger output
relation, and arbitrary target error from perfect completeness of the explicit honest-execution
experiment after applying the run-collapse residual. -/
theorem fiatShamir_completeness_of_perfect_honestExecution_mono_relations_error
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)}
    {relOut relOut' : Set (StmtOut × WitOut)}
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      fiatShamir_runCollapseResidual impl R stmtIn witIn)
    (hHonest : Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution)
    (hIn : relIn' ⊆ relIn) (hOut : relOut ⊆ relOut') :
    R.fiatShamir.completeness init impl relIn' relOut' completenessError := by
  unfold Reduction.perfectCompletenessFromRun at hHonest
  exact fiatShamir_completeness_of_honestExecution_mono_relations_error init impl
    (relIn := relIn) (relIn' := relIn') (relOut := relOut) (relOut' := relOut')
    (completenessError₁ := 0) (completenessError₂ := completenessError)
    R hCollapse hHonest hIn hOut (zero_le completenessError)

/-- Basic Fiat-Shamir completeness can be transported to a smaller input relation, larger output
relation, and arbitrary target error from perfect completeness of the explicit honest-execution
experiment after applying the named run-equality residual. -/
theorem fiatShamir_completeness_of_perfect_runEq_mono_relations_error
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)}
    {relOut relOut' : Set (StmtOut × WitOut)}
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRun : ∀ stmtIn witIn,
      fiatShamir_run_eq_honestExecution R stmtIn witIn)
    (hHonest : Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution)
    (hIn : relIn' ⊆ relIn) (hOut : relOut ⊆ relOut') :
    R.fiatShamir.completeness init impl relIn' relOut' completenessError := by
  unfold Reduction.perfectCompletenessFromRun at hHonest
  exact fiatShamir_completeness_of_runEq_mono_relations_error init impl
    (relIn := relIn) (relIn' := relIn') (relOut := relOut) (relOut' := relOut')
    (completenessError₁ := 0) (completenessError₂ := completenessError)
    R hRun hHonest hIn hOut (zero_le completenessError)

-- Future work: discharge `fiatShamir_run_eq_honestExecution` itself.  The outer challenge-collapse
-- residual is now a theorem once that run equality is supplied; the remaining content is the
-- structural equality between `R.fiatShamir.run` and the explicit honest Fiat-Shamir execution.

#print axioms Reduction.fiatShamir_runCollapseResidual
#print axioms Reduction.fiatShamir_runCollapseResidual_of_run_eq_honestExecution
#print axioms Reduction.FiatShamirProtocolSpec
#print axioms Reduction.FiatShamirProofTranscript
#print axioms Reduction.fiatShamirHonestExecution
#print axioms Reduction.fiatShamir_sendMessage_eq_raw
#print axioms Reduction.fiatShamir_run_eq_oneMessage
#print axioms Reduction.fiatShamir_run_eq_honestExecution
#print axioms Reduction.fiatShamir_completeness_unroll
#print axioms Reduction.fiatShamir_completeness_unroll_of_runCollapse
#print axioms Reduction.fiatShamir_completeness_unroll_of_runEq
#print axioms Reduction.fiatShamir_completeness_of_honestExecution
#print axioms Reduction.fiatShamir_completeness_of_runEq
#print axioms Reduction.fiatShamir_honestExecution_completeness_of_completeness
#print axioms Reduction.fiatShamir_honestExecution_completeness_of_runEq
#print axioms Reduction.fiatShamir_perfectCompleteness_unroll
#print axioms Reduction.fiatShamir_perfectCompleteness_unroll_of_runCollapse
#print axioms Reduction.fiatShamir_perfectCompleteness_unroll_of_runEq
#print axioms Reduction.fiatShamir_perfectCompleteness_of_honestExecution
#print axioms Reduction.fiatShamir_perfectCompleteness_of_runEq
#print axioms Reduction.fiatShamir_honestExecution_perfectCompleteness_of_perfectCompleteness
#print axioms Reduction.fiatShamir_honestExecution_perfectCompleteness_of_runEq
#print axioms Reduction.fiatShamir_completeness_of_honestExecution_mono_error
#print axioms Reduction.fiatShamir_completeness_of_honestExecution_mono_relations
#print axioms Reduction.fiatShamir_completeness_of_honestExecution_mono_relations_error
#print axioms Reduction.fiatShamir_completeness_of_runEq_mono_error
#print axioms Reduction.fiatShamir_completeness_of_runEq_mono_relations
#print axioms Reduction.fiatShamir_completeness_of_runEq_mono_relations_error
#print axioms Reduction.fiatShamir_perfectCompleteness_of_honestExecution_mono_relations
#print axioms Reduction.fiatShamir_perfectCompleteness_of_runEq_mono_relations
#print axioms Reduction.fiatShamir_completeness_of_perfect_honestExecution_mono_error
#print axioms Reduction.fiatShamir_completeness_of_perfect_runEq_mono_error
#print axioms Reduction.fiatShamir_completeness_of_perfect_honestExecution_mono_relations_error
#print axioms Reduction.fiatShamir_completeness_of_perfect_runEq_mono_relations_error

end Completeness

section StateRestorationSoundness

variable [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]

local instance fiatShamirNoChallengeSampleable :
    ∀ i : (FiatShamirProtocolSpec (pSpec := pSpec)).ChallengeIdx,
      SampleableType ((FiatShamirProtocolSpec (pSpec := pSpec)).Challenge i) := by
  intro i
  rcases i with ⟨i, hi⟩
  exact False.elim (by
    rcases i with ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst k
    simp at hi)

/-- Residual statement for the basic Fiat-Shamir state-restoration soundness transfer.

The state-restoration game samples an `fsChallengeOracle` table as its ambient state; the
Fiat-Shamir target exposes that same challenge table as part of the transformed reduction's oracle
spec. Discharging this residual is the remaining semantic coupling between those two views. -/
def fiatShamir_soundnessTransferResidual
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  Verifier.StateRestoration.soundness srInit srImpl langIn langOut V soundnessError →
    Verifier.soundness fsInit fsImpl langIn langOut V.fiatShamir soundnessError

/-- Basic Fiat-Shamir soundness follows immediately from a discharged state-restoration transfer
residual. This theorem isolates the remaining proof obligation without claiming to solve it. -/
theorem fiatShamir_soundness_of_stateRestoration
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn langOut soundnessError V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError) :
    Verifier.soundness fsInit fsImpl langIn langOut V.fiatShamir soundnessError :=
  hTransfer hSR

/-- Basic Fiat-Shamir soundness at a larger target error follows from a state-restoration transfer
residual proved at a smaller error budget. -/
theorem fiatShamir_soundness_of_stateRestoration_mono_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn langOut soundnessError₁ V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError₁)
    (hle : soundnessError₁ ≤ soundnessError₂) :
    Verifier.soundness fsInit fsImpl langIn langOut V.fiatShamir soundnessError₂ := by
  have hSound :
      Verifier.soundness fsInit fsImpl langIn langOut V.fiatShamir soundnessError₁ :=
    fiatShamir_soundness_of_stateRestoration srInit srImpl fsInit fsImpl langIn langOut
      soundnessError₁ V hTransfer hSR
  exact Verifier.soundness.mono_error fsInit fsImpl hSound hle

/-- Basic Fiat-Shamir soundness can be transported to a larger honest input language and a
smaller accepting output language after applying the state-restoration transfer residual. -/
theorem fiatShamir_soundness_of_stateRestoration_mono_languages
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {langIn langIn' : Set StmtIn} {langOut langOut' : Set StmtOut}
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn langOut soundnessError V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError)
    (hIn : langIn ⊆ langIn') (hOut : langOut' ⊆ langOut) :
    Verifier.soundness fsInit fsImpl langIn' langOut' V.fiatShamir soundnessError := by
  have hSound :
      Verifier.soundness fsInit fsImpl langIn langOut V.fiatShamir soundnessError :=
    fiatShamir_soundness_of_stateRestoration srInit srImpl fsInit fsImpl langIn langOut
      soundnessError V hTransfer hSR
  exact Verifier.soundness.mono_languages fsInit fsImpl hSound hIn hOut

/-- Basic Fiat-Shamir soundness can simultaneously transport languages and increase the target
soundness error after applying a state-restoration transfer residual. -/
theorem fiatShamir_soundness_of_stateRestoration_mono_languages_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {langIn langIn' : Set StmtIn} {langOut langOut' : Set StmtOut}
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_soundnessTransferResidual srInit srImpl fsInit fsImpl
        langIn langOut soundnessError₁ V)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl
      langIn langOut V soundnessError₁)
    (hIn : langIn ⊆ langIn') (hOut : langOut' ⊆ langOut)
    (hle : soundnessError₁ ≤ soundnessError₂) :
    Verifier.soundness fsInit fsImpl langIn' langOut' V.fiatShamir soundnessError₂ := by
  have hSound :
      Verifier.soundness fsInit fsImpl langIn' langOut' V.fiatShamir soundnessError₁ :=
    fiatShamir_soundness_of_stateRestoration_mono_languages srInit srImpl fsInit fsImpl
      soundnessError₁ V hTransfer hSR hIn hOut
  exact Verifier.soundness.mono_error fsInit fsImpl hSound hle

/-- Residual statement for the basic Fiat-Shamir state-restoration knowledge-soundness transfer.

As in `fiatShamir_soundnessTransferResidual`, this names only the semantic bridge from an
interactive state-restoration adversary/extractor game to the one-message Fiat-Shamir verifier
game. The extractor construction and query-log correspondence remain the open content. -/
def fiatShamir_knowledgeSoundnessTransferResidual
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (knowledgeError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec) : Prop :=
  Verifier.StateRestoration.knowledgeSoundness srInit srImpl relIn relOut V knowledgeError →
    Verifier.knowledgeSoundness fsInit fsImpl relIn relOut V.fiatShamir knowledgeError

/-- Basic Fiat-Shamir knowledge soundness follows immediately from a discharged
state-restoration knowledge-soundness transfer residual. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (knowledgeError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn relOut knowledgeError V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn relOut V.fiatShamir knowledgeError :=
  hTransfer hSR

/-- Basic Fiat-Shamir knowledge soundness at a larger target error follows from a
state-restoration transfer residual proved at a smaller error budget. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_mono_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn relOut knowledgeError₁ V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError₁)
    (hle : knowledgeError₁ ≤ knowledgeError₂) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn relOut V.fiatShamir knowledgeError₂ := by
  have hSound :
      Verifier.knowledgeSoundness fsInit fsImpl relIn relOut V.fiatShamir knowledgeError₁ :=
    fiatShamir_knowledgeSoundness_of_stateRestoration srInit srImpl fsInit fsImpl relIn relOut
      knowledgeError₁ V hTransfer hSR
  exact Verifier.knowledgeSoundness.mono_error fsInit fsImpl hSound hle

/-- Basic Fiat-Shamir knowledge soundness can be transported to a larger valid input relation and
a smaller valid output relation after applying the state-restoration transfer residual. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_mono_relations
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    (knowledgeError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn relOut knowledgeError V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError)
    (hIn : relIn ⊆ relIn') (hOut : relOut' ⊆ relOut) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn' relOut' V.fiatShamir knowledgeError := by
  have hSound :
      Verifier.knowledgeSoundness fsInit fsImpl relIn relOut V.fiatShamir knowledgeError :=
    fiatShamir_knowledgeSoundness_of_stateRestoration srInit srImpl fsInit fsImpl relIn relOut
      knowledgeError V hTransfer hSR
  exact Verifier.knowledgeSoundness.mono_relations fsInit fsImpl hSound hIn hOut

/-- Basic Fiat-Shamir knowledge soundness can simultaneously transport relations and increase the
target knowledge error after applying a state-restoration transfer residual. -/
theorem fiatShamir_knowledgeSoundness_of_stateRestoration_mono_relations_error
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (fsInit : ProbComp σ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hTransfer :
      fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl fsInit fsImpl
        relIn relOut knowledgeError₁ V)
    (hSR : Verifier.StateRestoration.knowledgeSoundness srInit srImpl
      relIn relOut V knowledgeError₁)
    (hIn : relIn ⊆ relIn') (hOut : relOut' ⊆ relOut)
    (hle : knowledgeError₁ ≤ knowledgeError₂) :
    Verifier.knowledgeSoundness fsInit fsImpl relIn' relOut' V.fiatShamir
      knowledgeError₂ := by
  have hSound :
      Verifier.knowledgeSoundness fsInit fsImpl relIn' relOut' V.fiatShamir
        knowledgeError₁ :=
    fiatShamir_knowledgeSoundness_of_stateRestoration_mono_relations srInit srImpl fsInit fsImpl
      knowledgeError₁ V hTransfer hSR hIn hOut
  exact Verifier.knowledgeSoundness.mono_error fsInit fsImpl hSound hle

#print axioms Reduction.fiatShamir_soundnessTransferResidual
#print axioms Reduction.fiatShamir_soundness_of_stateRestoration
#print axioms Reduction.fiatShamir_soundness_of_stateRestoration_mono_error
#print axioms Reduction.fiatShamir_soundness_of_stateRestoration_mono_languages
#print axioms Reduction.fiatShamir_soundness_of_stateRestoration_mono_languages_error
#print axioms Reduction.fiatShamir_knowledgeSoundnessTransferResidual
#print axioms Reduction.fiatShamir_knowledgeSoundness_of_stateRestoration
#print axioms Reduction.fiatShamir_knowledgeSoundness_of_stateRestoration_mono_error
#print axioms Reduction.fiatShamir_knowledgeSoundness_of_stateRestoration_mono_relations
#print axioms Reduction.fiatShamir_knowledgeSoundness_of_stateRestoration_mono_relations_error

end StateRestorationSoundness

section ZeroKnowledgeTransfer

/-!
### Basic Fiat-Shamir zero-knowledge transfer

The transformed reduction `R.fiatShamir` is *non-interactive*: its protocol spec
`FiatShamirProtocolSpec` carries a single prover message and no verifier challenges. For a
one-message reduction there is no challenge transcript for a zero-knowledge simulator to
re-randomize beyond the honest transcript distribution, so the relevant zero-knowledge notion here
is exactly honest-verifier zero-knowledge of the transformed reduction.

A full simulator-based zero-knowledge predicate for arbitrary reductions is not yet defined in the
core security layer: `Reduction.Simulator` is declared in `Security/Basic.lean`, but no
`zeroKnowledge` predicate is built on it (see the zero-knowledge-definition issue). Pending that, we
record the transfer at the HVZK level in both its statistical form (`Reduction.isStatHVZK`, with a
free error `ε`) and its perfect form (`Reduction.isHVZK`, exact distributions), naming each
obligation as a residual with its bridge theorem, mirroring the completeness and state-restoration
soundness scaffolding above.
-/

local instance fiatShamirZKNoChallengeSampleable :
    ∀ i : (FiatShamirProtocolSpec (pSpec := pSpec)).ChallengeIdx,
      SampleableType ((FiatShamirProtocolSpec (pSpec := pSpec)).Challenge i) := by
  intro i
  rcases i with ⟨i, hi⟩
  exact False.elim (by
    rcases i with ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst k
    simp at hi)

/-- Residual statement for the basic Fiat-Shamir HVZK-to-statistical-HVZK transfer.

The underlying interactive reduction is measured by the transcript-level `Reduction.isHVZK`
predicate. The transformed one-message Fiat-Shamir reduction is measured by `Reduction.isStatHVZK`
over the enlarged oracle specification containing the Fiat-Shamir challenge oracle. Supplying this
residual is exactly the semantic simulator-transfer theorem promised by the basic Fiat-Shamir
interface; this wrapper keeps that construction explicit. -/
def fiatShamir_statisticalHVZKTransferResidual
    {τ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn)) (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  Reduction.isHVZK init impl rel R →
    Reduction.isStatHVZK fsInit fsImpl rel R.fiatShamir ε

omit [VCVCompatible StmtIn] in
/-- The basic-Fiat-Shamir statistical HVZK transfer residual is monotone in the target
statistical error.  A simulator-transfer theorem proved at a smaller error budget can be reused
at any larger error budget. -/
theorem fiatShamir_statisticalHVZKTransferResidual.mono_error
    {τ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn)) {ε₁ ε₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel ε₁ R)
    (hle : ε₁ ≤ ε₂) :
    fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel ε₂ R := by
  intro hHVZK
  exact (hTransfer hHVZK).mono_error hle

omit [VCVCompatible StmtIn] in
/-- A zero-error basic-Fiat-Shamir statistical HVZK transfer residual can be reused at any target
statistical error budget. -/
theorem fiatShamir_statisticalHVZKTransferResidual.of_zero
    {τ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn)) (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel 0 R) :
    fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel ε R :=
  fiatShamir_statisticalHVZKTransferResidual.mono_error init impl fsInit fsImpl
    rel R hTransfer (zero_le ε)

/-- Basic Fiat-Shamir statistical HVZK follows immediately from a discharged simulator-transfer
residual. This theorem names the target surface for the future malicious-verifier/Fiat-Shamir
simulator argument without claiming to construct that simulator here. -/
theorem fiatShamir_isStatHVZK_of_HVZK
    {τ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn)) (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel ε R)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isStatHVZK fsInit fsImpl rel R.fiatShamir ε :=
  hTransfer hHVZK

/-- Basic Fiat-Shamir statistical HVZK at a larger error budget follows from a transfer residual
proved at a smaller budget. This is the theorem-level companion to
`fiatShamir_statisticalHVZKTransferResidual.mono_error`. -/
theorem fiatShamir_isStatHVZK_of_HVZK_mono_error
    {τ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn)) {ε₁ ε₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel ε₁ R)
    (hle : ε₁ ≤ ε₂)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isStatHVZK fsInit fsImpl rel R.fiatShamir ε₂ :=
  (fiatShamir_isStatHVZK_of_HVZK init impl fsInit fsImpl rel ε₁ R hTransfer hHVZK).mono_error
    hle

/-- Basic Fiat-Shamir statistical HVZK can be restricted to a sub-relation after applying a
simulator-transfer residual on the larger relation. -/
theorem fiatShamir_isStatHVZK_of_HVZK_mono_relation
    {τ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {rel relSub : Set (StmtIn × WitIn)} (hsub : relSub ⊆ rel) (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel ε R)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isStatHVZK fsInit fsImpl relSub R.fiatShamir ε :=
  (fiatShamir_isStatHVZK_of_HVZK init impl fsInit fsImpl rel ε R hTransfer hHVZK).mono_relation
    hsub

/-- Basic Fiat-Shamir statistical HVZK can be restricted to a sub-relation and relaxed to a larger
error budget after applying a simulator-transfer residual on the larger relation. -/
theorem fiatShamir_isStatHVZK_of_HVZK_mono_relation_error
    {τ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {rel relSub : Set (StmtIn × WitIn)} (hsub : relSub ⊆ rel) {ε₁ ε₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel ε₁ R)
    (hle : ε₁ ≤ ε₂)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isStatHVZK fsInit fsImpl relSub R.fiatShamir ε₂ :=
  (fiatShamir_isStatHVZK_of_HVZK_mono_relation init impl fsInit fsImpl hsub ε₁ R
    hTransfer hHVZK).mono_error hle

/-- Residual statement for the basic Fiat-Shamir *perfect* honest-verifier zero-knowledge transfer.

The exact-distribution counterpart of `fiatShamir_statisticalHVZKTransferResidual` (the `ε = 0`
case): `R.fiatShamir` is the one-message non-interactive reduction, whose only randomness is the
prover message recomputed through the Fiat-Shamir challenge oracle. The open content of this
residual is the construction of a transcript simulator for the transformed reduction out of a
transcript simulator for the interactive source, together with the distribution-equality argument
coupling the Fiat-Shamir honest transcript distribution to the source honest transcript
distribution. -/
def fiatShamir_hvzkTransferResidual
    {τ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  Reduction.isHVZK init impl rel R →
    Reduction.isHVZK fsInit fsImpl rel R.fiatShamir

omit [VCVCompatible StmtIn] in
/-- A perfect Fiat-Shamir HVZK transfer residual supplies the statistical transfer residual at
any target error budget. -/
theorem fiatShamir_statisticalHVZKTransferResidual.of_perfectTransfer
    {τ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn)) (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R) :
    fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel ε R := by
  intro hHVZK
  exact (hTransfer hHVZK).isStatHVZK ε

omit [VCVCompatible StmtIn] in
/-- A zero-error statistical Fiat-Shamir simulator-transfer residual is exactly strong enough to
recover the perfect HVZK transfer residual. This is the residual-level counterpart of
`fiatShamir_isHVZK_of_HVZK_zero`. -/
theorem fiatShamir_hvzkTransferResidual.of_statistical_zero
    {τ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel 0 R) :
    fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R := by
  intro hHVZK
  exact _root_.Reduction.isStatHVZK_zero.isHVZK (hTransfer hHVZK)

omit [VCVCompatible StmtIn] in
/-- Perfect basic-Fiat-Shamir HVZK transfer is equivalent to statistical HVZK transfer at
zero error. This is only an API equivalence between residual statements; the simulator
construction remains the content of either residual. -/
theorem fiatShamir_hvzkTransferResidual_iff_statistical_zero
    {τ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R ↔
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel 0 R := by
  constructor
  · intro hTransfer
    exact fiatShamir_statisticalHVZKTransferResidual.of_perfectTransfer init impl fsInit fsImpl
      rel 0 R hTransfer
  · intro hTransfer
    exact fiatShamir_hvzkTransferResidual.of_statistical_zero init impl fsInit fsImpl
      rel R hTransfer

/-- Basic Fiat-Shamir perfect honest-verifier zero-knowledge follows immediately from a discharged
transfer residual. This isolates the remaining proof obligation (simulator construction plus
transcript distribution coupling) without claiming to solve it. -/
theorem fiatShamir_isHVZK_of_transfer
    {τ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isHVZK fsInit fsImpl rel R.fiatShamir :=
  hTransfer hHVZK

omit [VCVCompatible StmtIn] in
/-- Basic Fiat-Shamir statistical HVZK follows from the stronger perfect transfer residual. -/
theorem fiatShamir_isStatHVZK_of_transfer
    {τ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn)) (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isStatHVZK fsInit fsImpl rel R.fiatShamir ε :=
  (hTransfer hHVZK).isStatHVZK ε

/-- Basic Fiat-Shamir perfect HVZK can be restricted to a sub-relation after applying a perfect
simulator-transfer residual on the larger relation. -/
theorem fiatShamir_isHVZK_of_transfer_mono_relation
    {τ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {rel relSub : Set (StmtIn × WitIn)} (hsub : relSub ⊆ rel)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isHVZK fsInit fsImpl relSub R.fiatShamir :=
  (fiatShamir_isHVZK_of_transfer init impl fsInit fsImpl rel R hTransfer hHVZK).mono_relation
    hsub

omit [VCVCompatible StmtIn] in
/-- Basic Fiat-Shamir statistical HVZK can be restricted to a sub-relation after applying the
stronger perfect transfer residual on the larger relation. -/
theorem fiatShamir_isStatHVZK_of_transfer_mono_relation
    {τ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {rel relSub : Set (StmtIn × WitIn)} (hsub : relSub ⊆ rel) (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isStatHVZK fsInit fsImpl relSub R.fiatShamir ε :=
  _root_.Reduction.isHVZK.isStatHVZK
    ((hTransfer hHVZK).mono_relation hsub)
    ε

omit [VCVCompatible StmtIn] in
/-- Basic Fiat-Shamir statistical HVZK can be restricted to a sub-relation and relaxed to a larger
error budget after applying the stronger perfect transfer residual on the larger relation. -/
theorem fiatShamir_isStatHVZK_of_transfer_mono_relation_error
    {τ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {rel relSub : Set (StmtIn × WitIn)} (hsub : relSub ⊆ rel) {ε₁ ε₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R)
    (hle : ε₁ ≤ ε₂)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isStatHVZK fsInit fsImpl relSub R.fiatShamir ε₂ :=
  (fiatShamir_isStatHVZK_of_transfer_mono_relation init impl fsInit fsImpl hsub ε₁ R
    hTransfer hHVZK).mono_error hle

/-- If the Fiat-Shamir simulator-transfer residual is discharged at zero statistical error, then
basic Fiat-Shamir preserves perfect HVZK. This is only the zero-error API wrapper: the simulator
construction remains the content of `fiatShamir_statisticalHVZKTransferResidual`. -/
theorem fiatShamir_isHVZK_of_HVZK_zero
    {τ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel 0 R)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isHVZK fsInit fsImpl rel R.fiatShamir :=
  _root_.Reduction.isStatHVZK_zero.isHVZK
    (fiatShamir_isStatHVZK_of_HVZK init impl fsInit fsImpl rel 0 R hTransfer hHVZK)

/-- A zero-error statistical Fiat-Shamir simulator transfer gives statistical HVZK at any target
error on the same relation. -/
theorem fiatShamir_isStatHVZK_of_HVZK_zero
    {τ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn)) (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel 0 R)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isStatHVZK fsInit fsImpl rel R.fiatShamir ε :=
  _root_.Reduction.isHVZK.isStatHVZK
    (fiatShamir_isHVZK_of_HVZK_zero init impl fsInit fsImpl rel R hTransfer hHVZK)
    ε

/-- A zero-error statistical Fiat-Shamir simulator transfer also preserves perfect HVZK after
restricting to a sub-relation. -/
theorem fiatShamir_isHVZK_of_HVZK_zero_mono_relation
    {τ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {rel relSub : Set (StmtIn × WitIn)} (hsub : relSub ⊆ rel)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel 0 R)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isHVZK fsInit fsImpl relSub R.fiatShamir :=
  (fiatShamir_isHVZK_of_HVZK_zero init impl fsInit fsImpl rel R hTransfer hHVZK).mono_relation
    hsub

/-- A zero-error statistical Fiat-Shamir simulator transfer gives statistical HVZK at any target
error after restricting to a sub-relation. -/
theorem fiatShamir_isStatHVZK_of_HVZK_zero_mono_relation
    {τ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {rel relSub : Set (StmtIn × WitIn)} (hsub : relSub ⊆ rel) (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel 0 R)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isStatHVZK fsInit fsImpl relSub R.fiatShamir ε :=
  _root_.Reduction.isHVZK.isStatHVZK
    (fiatShamir_isHVZK_of_HVZK_zero_mono_relation init impl fsInit fsImpl hsub R
      hTransfer hHVZK)
    ε

#print axioms Reduction.fiatShamir_statisticalHVZKTransferResidual
#print axioms Reduction.fiatShamir_statisticalHVZKTransferResidual.mono_error
#print axioms Reduction.fiatShamir_statisticalHVZKTransferResidual.of_zero
#print axioms Reduction.fiatShamir_isStatHVZK_of_HVZK
#print axioms Reduction.fiatShamir_isStatHVZK_of_HVZK_mono_error
#print axioms Reduction.fiatShamir_isStatHVZK_of_HVZK_mono_relation
#print axioms Reduction.fiatShamir_isStatHVZK_of_HVZK_mono_relation_error
#print axioms Reduction.fiatShamir_hvzkTransferResidual
#print axioms Reduction.fiatShamir_statisticalHVZKTransferResidual.of_perfectTransfer
#print axioms Reduction.fiatShamir_hvzkTransferResidual.of_statistical_zero
#print axioms Reduction.fiatShamir_hvzkTransferResidual_iff_statistical_zero
#print axioms Reduction.fiatShamir_isHVZK_of_transfer
#print axioms Reduction.fiatShamir_isStatHVZK_of_transfer
#print axioms Reduction.fiatShamir_isHVZK_of_transfer_mono_relation
#print axioms Reduction.fiatShamir_isStatHVZK_of_transfer_mono_relation
#print axioms Reduction.fiatShamir_isStatHVZK_of_transfer_mono_relation_error
#print axioms Reduction.fiatShamir_isHVZK_of_HVZK_zero
#print axioms Reduction.fiatShamir_isStatHVZK_of_HVZK_zero
#print axioms Reduction.fiatShamir_isHVZK_of_HVZK_zero_mono_relation
#print axioms Reduction.fiatShamir_isStatHVZK_of_HVZK_zero_mono_relation

end ZeroKnowledgeTransfer

end Reduction

-- Future work: discharge the run-collapse, state-restoration transfer, and HVZK simulator-transfer
-- residuals named above for the basic Fiat-Shamir transform (statistical and perfect forms); the
-- HVZK legs are additionally gated on a core simulator-based zero-knowledge definition.

end

end Security
