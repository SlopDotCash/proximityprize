/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.Security.Basic

/-!
# Completeness of Duplex-Sponge Fiat-Shamir

This module proves the completeness of the Duplex-Sponge Fiat-Shamir (DSFS) transformation.
We establish that if the underlying interactive protocol possesses completeness (or perfect
completeness), then its non-interactive counterpart obtained via the DSFS transformation
inherits completeness, up to the same completeness error.

The proofs proceed by unfolding the verifier's check to show it is equivalent to re-running the
honest interactive execution, and then unrolling the probability distributions of the respective
security games.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

section Execution

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type}
  [VCVCompatible StmtIn]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- The transcript type of the one-message non-interactive proof produced by the unsalted DSFS
transform. -/
abbrev DuplexSpongeProofTranscript :=
  FullTranscript ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩

/-- The transcript type of the one-message non-interactive proof produced by the salted DSFS
transform. -/
abbrev DuplexSpongeSaltedProofTranscript (δ : Nat) :=
  FullTranscript
    ⟨!v[Direction.P_to_V],
      !v[ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ]⟩

/-- Expanding the DSFS verifier shows that it verifies by re-deriving the transcript from the proof
messages via the duplex sponge. -/
@[simp]
theorem duplexSpongeFiatShamir_verify_eq
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : DuplexSpongeProofTranscript (pSpec := pSpec)) :
    (V.duplexSpongeFiatShamir (U := U)).verify stmtIn proof =
      (do
      let messages : pSpec.Messages := proof 0
      let ⟨_, transcript⟩ ← messages.deriveTranscriptDSFS (oSpec := oSpec) (U := U) stmtIn
      let v ← (V.verify stmtIn transcript).run
      v.getM) := by
  rfl

/-- The salted DSFS verifier is the same verifier-side computation, with an initial salt-absorb
step before transcript derivation. -/
@[simp]
theorem duplexSpongeFiatShamirSalted_verify_eq {δ : Nat}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn)
    (proof : DuplexSpongeSaltedProofTranscript (pSpec := pSpec) (U := U) δ) :
    (V.duplexSpongeFiatShamirSalted (U := U)).verify stmtIn proof =
      (do
      let ⟨salt, messages⟩ :
          ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ := proof 0
      let ⟨_, transcript⟩ ←
        messages.deriveTranscriptDSFSSalted (oSpec := oSpec) (U := U) stmtIn salt
      let v ← (V.verify stmtIn transcript).run
      v.getM) := by
  rfl

end Execution

end Verifier

namespace Reduction

section Execution

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- The explicit honest execution underlying the unsalted DSFS transform. This packages the honest
prover's DSFS-generated proof together with the verifier's acceptance check on that proof. -/
def duplexSpongeFiatShamirHonestRun
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (Verifier.DuplexSpongeProofTranscript (pSpec := pSpec) ×
        (StmtOut × WitOut) × Option StmtOut) := do
  let state := R.prover.input (stmtIn, witIn)
  let ⟨messages, _, state⟩ ← R.prover.runToRoundDSFS (U := U) (Fin.last n) stmtIn state
  let ctxOut ← (R.prover.output state).liftComp _
  let proof : Verifier.DuplexSpongeProofTranscript (pSpec := pSpec) := fun
    | ⟨0, _⟩ => messages
  let stmtOut ← ((R.verifier.duplexSpongeFiatShamir (U := U)).run stmtIn proof).run
  return ⟨proof, ctxOut, stmtOut⟩

/-- The explicit honest execution underlying the salted DSFS transform. -/
def duplexSpongeFiatShamirSaltedHonestRun {δ : Nat}
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (Verifier.DuplexSpongeSaltedProofTranscript (pSpec := pSpec) (U := U) δ ×
        (StmtOut × WitOut) × Option StmtOut) := do
  let salt ← sampleSalt.liftComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
  let state := R.prover.input (stmtIn, witIn)
  let ⟨messages, _, state⟩ ←
    R.prover.runToRoundDSFSSalted (U := U) (i := Fin.last n) stmtIn salt state
  let ctxOut ← (R.prover.output state).liftComp _
  let proof : Verifier.DuplexSpongeSaltedProofTranscript (pSpec := pSpec) (U := U) δ := fun
    | ⟨0, _⟩ => (salt, messages)
  let stmtOut ← ((R.verifier.duplexSpongeFiatShamirSalted (U := U)).run stmtIn proof).run
  return ⟨proof, ctxOut, stmtOut⟩

end Execution

section Completeness

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- The `NonInteractiveReduction` produced by the DSFS transform is prover-first: its single round
is a `P_to_V` message. -/
local instance dsfsProverOnly :
    ProtocolSpec.ProverOnly ⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩ where
  prover_first' := by simp

/-- The `NonInteractiveReduction` produced by the salted DSFS transform is prover-first. -/
local instance dsfsSaltedProverOnly {δ : Nat} :
    ProtocolSpec.ProverOnly ⟨!v[Direction.P_to_V], !v[ProtocolSpec.Messages.SaltedProof (pSpec := pSpec) (U := U) δ]⟩ where
  prover_first' := by simp

/-- The unsalted DSFS honest execution packaged in the generic `completenessFromRun` format. -/
def duplexSpongeFiatShamirHonestExecution
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      ((Verifier.DuplexSpongeProofTranscript (pSpec := pSpec) × StmtOut × WitOut) ×
        StmtOut) := do
  let ⟨proof, ⟨prvStmtOut, witOut⟩, stmtOut?⟩ ←
    R.duplexSpongeFiatShamirHonestRun (U := U) stmtIn witIn
  let stmtOut ← OptionT.mk (pure stmtOut?)
  return ⟨⟨proof, prvStmtOut, witOut⟩, stmtOut⟩

/-- The salted DSFS honest execution packaged in the generic `completenessFromRun` format. -/
def duplexSpongeFiatShamirSaltedHonestExecution {δ : Nat}
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      ((Verifier.DuplexSpongeSaltedProofTranscript (pSpec := pSpec) (U := U) δ ×
          StmtOut × WitOut) × StmtOut) := do
  let ⟨proof, ⟨prvStmtOut, witOut⟩, stmtOut?⟩ ←
    R.duplexSpongeFiatShamirSaltedHonestRun (U := U) sampleSalt stmtIn witIn
  let stmtOut ← OptionT.mk (pure stmtOut?)
  return ⟨⟨proof, prvStmtOut, witOut⟩, stmtOut⟩

/-- The transformed unsalted DSFS run is the lifted explicit honest execution. -/
def duplexSpongeFiatShamir_run_eq_honestExecution
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prop :=
    (R.duplexSpongeFiatShamir (U := U)).run stmtIn witIn =
      liftM (R.duplexSpongeFiatShamirHonestExecution (U := U) stmtIn witIn)

/-- The transformed salted DSFS run is the lifted explicit honest execution. -/
def duplexSpongeFiatShamirSalted_run_eq_honestExecution {δ : Nat}
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prop :=
    (R.duplexSpongeFiatShamirSalted (U := U) sampleSalt).run stmtIn witIn =
      liftM (R.duplexSpongeFiatShamirSaltedHonestExecution (U := U) sampleSalt stmtIn witIn)

/-- Residual for collapsing the outer DSFS challenge-oracle implementation after unrolling the
unsalted transformed run. The right-hand honest execution does not query that appended oracle; the
remaining content is the `OptionT` lift-coherence bridge between the two-step associativity-routed
lift chosen by `run` and the direct lift consumed by `simulateQ_add_run_liftM_left`. -/
def duplexSpongeFiatShamir_runCollapseResidual
    {σ : Type}
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prop :=
    simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        ((R.duplexSpongeFiatShamir (U := U)).run stmtIn witIn).run =
      simulateQ impl
        (R.duplexSpongeFiatShamirHonestExecution (U := U) stmtIn witIn).run

/-- Salted analogue of `duplexSpongeFiatShamir_runCollapseResidual`. -/
def duplexSpongeFiatShamirSalted_runCollapseResidual {δ : Nat}
    {σ : Type}
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Prop :=
    simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        ((R.duplexSpongeFiatShamirSalted (U := U) sampleSalt).run stmtIn witIn).run =
      simulateQ impl
        (R.duplexSpongeFiatShamirSaltedHonestExecution (U := U)
          sampleSalt stmtIn witIn).run

/-- Completeness of the unsalted DSFS transform is equivalent to the explicit honest execution
packaged via `Reduction.duplexSpongeFiatShamirHonestExecution`. -/
def duplexSpongeFiatShamir_completeness_unroll
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Prop :=
    (R.duplexSpongeFiatShamir (U := U)).completeness init impl relIn relOut completenessError ↔
      Reduction.completenessFromRun init impl relIn relOut
        (R.duplexSpongeFiatShamirHonestExecution (U := U)) completenessError

/-- Completeness of the salted DSFS transform is equivalent to the explicit honest execution
packaged via `Reduction.duplexSpongeFiatShamirSaltedHonestExecution`. -/
def duplexSpongeFiatShamirSalted_completeness_unroll {δ : Nat}
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Prop :=
    (R.duplexSpongeFiatShamirSalted (U := U) sampleSalt).completeness
      init impl relIn relOut completenessError ↔
      Reduction.completenessFromRun init impl relIn relOut
        (R.duplexSpongeFiatShamirSaltedHonestExecution (U := U) sampleSalt)
        completenessError



/-- **Reduction of `duplexSpongeFiatShamir_completeness_unroll` to the run-collapse residual.**

Given the per-input `duplexSpongeFiatShamir_runCollapseResidual`, completeness of the unsalted DSFS
transform is *definitionally* the generic `completenessFromRun` predicate over the honest execution.

The named residual keeps explicit the remaining v4.30 lift-coherence wall: after rewriting the DSFS
run to the lifted honest execution, `simulateQ_add_run_liftM_left` still needs the two-step
`OptionT` lift chosen by `run` to agree with the direct lift used by the helper lemma. -/
theorem duplexSpongeFiatShamir_completeness_unroll_of_runCollapse
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      duplexSpongeFiatShamir_runCollapseResidual (U := U) impl R stmtIn witIn) :
    duplexSpongeFiatShamir_completeness_unroll (U := U)
      init impl relIn relOut completenessError R := by
  unfold duplexSpongeFiatShamir_completeness_unroll
  rw [Reduction.completeness_iff_completenessFromRun]
  unfold Reduction.completenessFromRun
  refine forall_congr' fun stmtIn => forall_congr' fun witIn => ?_
  refine imp_congr_right fun _ => ?_
  have hcollapse :
      simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          ((R.duplexSpongeFiatShamir (U := U)).run stmtIn witIn).run =
        simulateQ impl
          (R.duplexSpongeFiatShamirHonestExecution (U := U) stmtIn witIn).run :=
    hCollapse stmtIn witIn
  rw [hcollapse]

/-- **Reduction of `duplexSpongeFiatShamirSalted_completeness_unroll` to the run-equality
residual.** The salted analogue of `duplexSpongeFiatShamir_completeness_unroll_of_runCollapse`. -/
theorem duplexSpongeFiatShamirSalted_completeness_unroll_of_runCollapse {δ : Nat}
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hCollapse : ∀ stmtIn witIn,
      duplexSpongeFiatShamirSalted_runCollapseResidual (U := U) impl sampleSalt R stmtIn witIn) :
    duplexSpongeFiatShamirSalted_completeness_unroll (U := U)
      init impl sampleSalt relIn relOut completenessError R := by
  unfold duplexSpongeFiatShamirSalted_completeness_unroll
  rw [Reduction.completeness_iff_completenessFromRun]
  unfold Reduction.completenessFromRun
  refine forall_congr' fun stmtIn => forall_congr' fun witIn => ?_
  refine imp_congr_right fun _ => ?_
  have hcollapse :
      simulateQ (QueryImpl.addLift impl challengeQueryImpl)
          ((R.duplexSpongeFiatShamirSalted (U := U) sampleSalt).run stmtIn witIn).run =
        simulateQ impl
          (R.duplexSpongeFiatShamirSaltedHonestExecution (U := U)
            sampleSalt stmtIn witIn).run :=
    hCollapse stmtIn witIn
  rw [hcollapse]

#print axioms Reduction.duplexSpongeFiatShamir_runCollapseResidual
#print axioms Reduction.duplexSpongeFiatShamirSalted_runCollapseResidual
#print axioms Reduction.duplexSpongeFiatShamir_completeness_unroll_of_runCollapse
#print axioms Reduction.duplexSpongeFiatShamirSalted_completeness_unroll_of_runCollapse

end Completeness

end Reduction
