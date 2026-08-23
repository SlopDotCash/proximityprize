/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# Whole-zkVM boundary template for ArkLib

This file is intentionally import-light. It records the final theorem shape ArkLib
is meant to support when composed with external VM semantics, arithmetization,
implementation, transcript, recursion, and deployment proofs.

ArkLib proves proof-system and oracle-reduction components. A whole-zkVM theorem
must additionally connect an accepted concrete verifier execution to a valid VM
execution trace and public output. The structures below name those interfaces as
assumptions rather than hiding them in prose.

For the current whole-zkVM roadmap, `Verified-zkEVM/evm-asm` is the named
guest-program semantics provider: it should supply RV64/EVM execution,
public-input/output, halting, and guest-program correctness theorems. ArkLib
consumes that work only through the abstract relation and boundary assumptions
below.
-/

namespace ArkLib
namespace ZkVMBoundary

/-- Boundary data supplied by a concrete zkVM project outside ArkLib.

The type parameters intentionally stay abstract: a RISC-V zkVM, EVM-on-RISC-V
zkVM, recursive prover, or on-chain verifier can instantiate them with its own
trace, statement, proof, transcript, and verifier implementation types. -/
structure WholeZkVMInterfaces where
  /-- Public statement or public input/output object. -/
  PublicInput : Type
  /-- Concrete proof artifact consumed by the implementation verifier. -/
  ConcreteProof : Type
  /-- Concrete verifier implementation state or executable verifier object. -/
  ConcreteVerifier : Type
  /-- ArkLib-level protocol statement used by the proof-system theorem. -/
  ArkStatement : Type
  /-- ArkLib-level proof/witness object, transcript, or accepted protocol artifact. -/
  ArkProof : Type
  /-- VM execution trace type: registers, memory, nondeterminism, and halting state. -/
  VmTrace : Type
  /-- Arithmetized trace / constraint-system witness type. -/
  ArithmetizationWitness : Type
  /-- Optional recursion or aggregation artifact. Use `Unit` when absent. -/
  RecursionArtifact : Type
  /-- Optional deployment serialization / on-chain verifier artifact. Use `Unit` when absent. -/
  DeploymentArtifact : Type

/-- Named assumptions needed to turn ArkLib proof-system verification into a
whole-zkVM correctness theorem. -/
structure WholeZkVMAssumptions (I : WholeZkVMInterfaces) where
  /-- The concrete verifier accepts the concrete proof for the public input. -/
  concreteVerifierAccepts :
    I.ConcreteVerifier -> I.PublicInput -> I.ConcreteProof -> Prop
  /-- The concrete verifier/proof pair decodes to the ArkLib statement/proof surface. -/
  implementationMatchesArkSpec :
    I.ConcreteVerifier -> I.PublicInput -> I.ConcreteProof ->
      I.ArkStatement -> I.ArkProof -> Prop
  /-- ArkLib's proved proof-system theorem accepts or extracts the arithmetization witness. -/
  arkProofSystemSoundness :
    I.ArkStatement -> I.ArkProof -> I.ArithmetizationWitness -> Prop
  /-- The arithmetization witness exactly encodes a valid VM trace for the public input. -/
  arithmetizationSoundness :
    I.PublicInput -> I.ArithmetizationWitness -> I.VmTrace -> Prop
  /-- The VM trace satisfies the intended instruction semantics and public-output convention. -/
  vmExecutionValid :
    I.PublicInput -> I.VmTrace -> Prop
  /-- Fiat-Shamir, BCS, commitments, random-oracle queries, and transcript derivation match ArkLib. -/
  transcriptAndCommitmentBinding :
    I.ConcreteProof -> I.ArkProof -> Prop
  /-- Recursion/aggregation preserves the same ArkLib statement when the zkVM uses it. -/
  recursionSoundness :
    I.RecursionArtifact -> I.ArkStatement -> Prop
  /-- Serialization, deployment, or on-chain verifier encoding preserves the concrete verifier call. -/
  deploymentSoundness :
    I.DeploymentArtifact -> I.ConcreteVerifier -> I.ConcreteProof -> Prop

/-- Final theorem template: an accepted concrete zkVM proof is meaningful only
after all external boundary assumptions are supplied. -/
def WholeZkVMEndToEndClaim (I : WholeZkVMInterfaces) (A : WholeZkVMAssumptions I) : Prop :=
  forall
    (verifier : I.ConcreteVerifier)
    (publicInput : I.PublicInput)
    (proof : I.ConcreteProof)
    (arkStatement : I.ArkStatement)
    (arkProof : I.ArkProof)
    (arithWitness : I.ArithmetizationWitness)
    (trace : I.VmTrace)
    (recursionArtifact : I.RecursionArtifact)
    (deploymentArtifact : I.DeploymentArtifact),
    A.concreteVerifierAccepts verifier publicInput proof ->
    A.implementationMatchesArkSpec verifier publicInput proof arkStatement arkProof ->
    A.transcriptAndCommitmentBinding proof arkProof ->
    A.arkProofSystemSoundness arkStatement arkProof arithWitness ->
    A.arithmetizationSoundness publicInput arithWitness trace ->
    A.vmExecutionValid publicInput trace ->
    A.recursionSoundness recursionArtifact arkStatement ->
    A.deploymentSoundness deploymentArtifact verifier proof ->
    exists validTrace : I.VmTrace,
      A.vmExecutionValid publicInput validTrace

-- `WholeZkVMResidual` (∃ A, WholeZkVMEndToEndClaim I A) was deleted in the proof-debt grind:
-- zero in-tree consumers, and VACUOUS as a Prop — the claim's conclusion
-- (∃ validTrace, vmExecutionValid publicInput validTrace) is directly witnessed by its own
-- hypotheses (trace, A.vmExecutionValid publicInput trace), so any degenerate `A` satisfies it.
-- The interface structures above remain as the documentation template.

end ZkVMBoundary
end ArkLib
