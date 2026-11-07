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
execution trace and public output. This file names that connection in three layers,
so that none of it is hidden in prose:

* `WholeZkVMInterfaces`: the abstract types that cross the boundary.
* `WholeZkVMRelations`: the boundary predicates (acceptance, decoding, the arithmetized
  relation, VM validity, and the binding/encoding conditions). They are data; choosing
  them asserts nothing.
* `WholeZkVMSoundness`: the soundness implications, each an explicit external
  obligation. Implementation acceptance produces an ArkLib statement and proof that the
  ArkLib verifier accepts; ArkLib acceptance of a bound proof produces an arithmetization
  witness; a witness for a statement that encodes the public input produces a valid VM
  trace.

`WholeZkVMEndToEndClaim` assumes concrete acceptance and the binding/encoding
conditions of one verifier call and concludes that a valid VM trace exists; VM validity
is its conclusion, not a premise. `wholeZkVMEndToEndClaim_of_soundness` derives it from
`WholeZkVMSoundness` by composing the three implications.
`not_wholeZkVMSoundness_of_acceptAll` shows that the implications have content: a
concrete verifier that accepts every proof cannot satisfy them at a public input with no
valid VM trace, once the binding/encoding conditions hold for one call there. The `Toy`
namespace checks a two-input instance in both directions.

## Scope

The implications are deterministic and model no soundness error. An instantiation whose
proof system is only computationally or statistically sound must put the corresponding
good event (no commitment collision, no Fiat-Shamir/BCS bad challenge) into
`transcriptAndCommitmentBinding` and bound the probability of its complement separately.
ArkLib's protocol theorems bound soundness error probabilistically, so they yield the
deterministic `arkProofSystemSoundness` only on such a good event. That probability bound,
the binding/encoding conditions, and every field of `WholeZkVMSoundness` remain external
obligations: nothing in this file proves them for a concrete zkVM.

For the current whole-zkVM roadmap, `Verified-zkEVM/evm-asm` is the named
guest-program semantics provider: it should supply RV64/EVM execution,
public-input/output, halting, and guest-program correctness theorems. ArkLib
consumes that work only through the abstract relations and soundness obligations
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

/-- Boundary predicates of a whole-zkVM stack.

The fields are data, not assumptions: instantiating them asserts nothing. The soundness
implications relating them are the fields of `WholeZkVMSoundness`. -/
structure WholeZkVMRelations (I : WholeZkVMInterfaces) where
  /-- The concrete verifier accepts the concrete proof for the public input. This is the
  observed acceptance, on-chain when the verifier is deployed. -/
  concreteVerifierAccepts : I.ConcreteVerifier → I.PublicInput → I.ConcreteProof → Prop
  /-- The concrete verifier call decodes to this ArkLib statement and ArkLib proof under the
  executable or mathematical ArkLib spec. -/
  implementationMatchesArkSpec :
    I.ConcreteVerifier → I.PublicInput → I.ConcreteProof → I.ArkStatement → I.ArkProof → Prop
  /-- The ArkLib protocol verifier accepts the ArkLib proof for the ArkLib statement. -/
  arkVerifierAccepts : I.ArkStatement → I.ArkProof → Prop
  /-- The relation the ArkLib proof-system theorem is sound for: the arithmetized trace
  (constraint-system) relation between ArkLib statements and arithmetization witnesses. -/
  arithmetizedRelation : I.ArkStatement → I.ArithmetizationWitness → Prop
  /-- Protocol binding: the ArkLib statement encodes this public input. -/
  publicInputEncoding : I.PublicInput → I.ArkStatement → Prop
  /-- The VM trace satisfies the intended instruction semantics and public-output convention. -/
  vmExecutionValid : I.PublicInput → I.VmTrace → Prop
  /-- Binding condition: the Fiat-Shamir/BCS challenges, commitments, random-oracle queries,
  and openings of the ArkLib proof are the ones bound by the concrete proof. For a
  computationally or statistically sound proof system this is also the good event outside
  which the deterministic `WholeZkVMSoundness.arkProofSystemSoundness` is claimed. -/
  transcriptAndCommitmentBinding : I.ConcreteProof → I.ArkProof → Prop
  /-- Binding condition: recursion/aggregation preserves this ArkLib statement. Without
  recursion, take `RecursionArtifact := Unit` and this condition to be `True`. -/
  recursionPreservesStatement : I.RecursionArtifact → I.ArkStatement → Prop
  /-- Encoding condition: serialization, deployment, or the on-chain verifier encoding performs
  exactly this concrete verifier call on this proof. Without deployment, take
  `DeploymentArtifact := Unit` and this condition to be `True`. -/
  deploymentPreservesCall : I.DeploymentArtifact → I.ConcreteVerifier → I.ConcreteProof → Prop

namespace WholeZkVMRelations

variable {I : WholeZkVMInterfaces}

/-- The binding/encoding conditions of one concrete verifier call: the deployment preserves the
call, and every ArkLib statement and proof decoded from the call is bound to the concrete proof
and has its statement preserved by the recursion layer. They are premises of
`WholeZkVMEndToEndClaim`, not consequences of acceptance. -/
def BindingConditions (R : WholeZkVMRelations I) (verifier : I.ConcreteVerifier)
    (publicInput : I.PublicInput) (proof : I.ConcreteProof)
    (recursionArtifact : I.RecursionArtifact) (deploymentArtifact : I.DeploymentArtifact) :
    Prop :=
  R.deploymentPreservesCall deploymentArtifact verifier proof ∧
    ∀ (arkStatement : I.ArkStatement) (arkProof : I.ArkProof),
      R.implementationMatchesArkSpec verifier publicInput proof arkStatement arkProof →
        R.transcriptAndCommitmentBinding proof arkProof ∧
          R.recursionPreservesStatement recursionArtifact arkStatement

end WholeZkVMRelations

/-- The soundness implications that turn ArkLib proof-system verification into a whole-zkVM
correctness theorem. Each field is an explicit external obligation; see
`docs/wiki/arklib-zkvm-boundary.md` for the project expected to discharge it. -/
structure WholeZkVMSoundness (I : WholeZkVMInterfaces) (R : WholeZkVMRelations I) : Prop where
  /-- Implementation soundness: if the deployment preserves the call, acceptance by the
  concrete verifier produces a decoded ArkLib statement, which encodes the public input, and a
  decoded ArkLib proof that the ArkLib verifier accepts. -/
  implementationSoundness :
    ∀ (verifier : I.ConcreteVerifier) (publicInput : I.PublicInput) (proof : I.ConcreteProof)
      (deploymentArtifact : I.DeploymentArtifact),
      R.deploymentPreservesCall deploymentArtifact verifier proof →
      R.concreteVerifierAccepts verifier publicInput proof →
      ∃ (arkStatement : I.ArkStatement) (arkProof : I.ArkProof),
        R.implementationMatchesArkSpec verifier publicInput proof arkStatement arkProof ∧
          R.publicInputEncoding publicInput arkStatement ∧
          R.arkVerifierAccepts arkStatement arkProof
  /-- Proof-system soundness: ArkLib acceptance of a proof that is bound to a concrete proof,
  for a statement that the recursion layer preserves, produces a witness of the arithmetized
  relation. -/
  arkProofSystemSoundness :
    ∀ (proof : I.ConcreteProof) (arkStatement : I.ArkStatement) (arkProof : I.ArkProof)
      (recursionArtifact : I.RecursionArtifact),
      R.transcriptAndCommitmentBinding proof arkProof →
      R.recursionPreservesStatement recursionArtifact arkStatement →
      R.arkVerifierAccepts arkStatement arkProof →
      ∃ arithWitness : I.ArithmetizationWitness, R.arithmetizedRelation arkStatement arithWitness
  /-- Arithmetization soundness: a witness of the arithmetized relation for a statement that
  encodes the public input produces a valid VM trace for that public input. -/
  arithmetizationSoundness :
    ∀ (publicInput : I.PublicInput) (arkStatement : I.ArkStatement)
      (arithWitness : I.ArithmetizationWitness),
      R.publicInputEncoding publicInput arkStatement →
      R.arithmetizedRelation arkStatement arithWitness →
      ∃ trace : I.VmTrace, R.vmExecutionValid publicInput trace

/-- Final theorem shape: whenever the concrete verifier accepts and the binding/encoding
conditions of that call hold, a valid VM trace exists for the public input. VM validity is the
conclusion, not a premise; `wholeZkVMEndToEndClaim_of_soundness` derives the claim from
`WholeZkVMSoundness`, and `Toy.acceptAll_not_endToEndClaim` shows that it can fail. -/
def WholeZkVMEndToEndClaim (I : WholeZkVMInterfaces) (R : WholeZkVMRelations I) : Prop :=
  ∀ (verifier : I.ConcreteVerifier) (publicInput : I.PublicInput) (proof : I.ConcreteProof)
    (recursionArtifact : I.RecursionArtifact) (deploymentArtifact : I.DeploymentArtifact),
    R.concreteVerifierAccepts verifier publicInput proof →
    R.BindingConditions verifier publicInput proof recursionArtifact deploymentArtifact →
    ∃ validTrace : I.VmTrace, R.vmExecutionValid publicInput validTrace

/-- Chain composition: the three soundness implications yield the end-to-end claim. -/
theorem wholeZkVMEndToEndClaim_of_soundness {I : WholeZkVMInterfaces}
    {R : WholeZkVMRelations I} (S : WholeZkVMSoundness I R) : WholeZkVMEndToEndClaim I R := by
  intro verifier publicInput proof recursionArtifact deploymentArtifact haccept hconditions
  obtain ⟨hdeploy, hdecoded⟩ := hconditions
  obtain ⟨arkStatement, arkProof, hmatch, hencode, harkAccept⟩ :=
    S.implementationSoundness verifier publicInput proof deploymentArtifact hdeploy haccept
  obtain ⟨hbind, hrecursion⟩ := hdecoded arkStatement arkProof hmatch
  obtain ⟨arithWitness, hrelation⟩ :=
    S.arkProofSystemSoundness proof arkStatement arkProof recursionArtifact hbind hrecursion
      harkAccept
  exact S.arithmetizationSoundness publicInput arkStatement arithWitness hencode hrelation

/-- The soundness implications cannot hold if some accepted call at a public input with no
valid VM trace satisfies the binding/encoding conditions. -/
theorem not_wholeZkVMSoundness_of_accepts {I : WholeZkVMInterfaces} {R : WholeZkVMRelations I}
    {verifier : I.ConcreteVerifier} {publicInput : I.PublicInput} {proof : I.ConcreteProof}
    {recursionArtifact : I.RecursionArtifact} {deploymentArtifact : I.DeploymentArtifact}
    (haccept : R.concreteVerifierAccepts verifier publicInput proof)
    (hconditions :
      R.BindingConditions verifier publicInput proof recursionArtifact deploymentArtifact)
    (hnoTrace : ∀ trace : I.VmTrace, ¬ R.vmExecutionValid publicInput trace) :
    ¬ WholeZkVMSoundness I R := by
  intro S
  obtain ⟨trace, htrace⟩ := wholeZkVMEndToEndClaim_of_soundness S verifier publicInput proof
    recursionArtifact deploymentArtifact haccept hconditions
  exact hnoTrace trace htrace

/-- An accept-all concrete verifier cannot instantiate the soundness implications for a false
VM statement: if it accepts every proof at a public input with no valid VM trace, and the
binding/encoding conditions hold for one call there, `WholeZkVMSoundness` fails. The last
hypothesis is needed: if no call at that public input satisfies the binding/encoding conditions,
the end-to-end claim says nothing about that public input. -/
theorem not_wholeZkVMSoundness_of_acceptAll {I : WholeZkVMInterfaces}
    {R : WholeZkVMRelations I} {publicInput : I.PublicInput}
    (hacceptAll : ∀ (verifier : I.ConcreteVerifier) (proof : I.ConcreteProof),
      R.concreteVerifierAccepts verifier publicInput proof)
    (hnoTrace : ∀ trace : I.VmTrace, ¬ R.vmExecutionValid publicInput trace)
    {verifier : I.ConcreteVerifier} {proof : I.ConcreteProof}
    {recursionArtifact : I.RecursionArtifact} {deploymentArtifact : I.DeploymentArtifact}
    (hconditions :
      R.BindingConditions verifier publicInput proof recursionArtifact deploymentArtifact) :
    ¬ WholeZkVMSoundness I R :=
  not_wholeZkVMSoundness_of_accepts (hacceptAll verifier proof) hconditions hnoTrace

/-! ### Two-input sanity check

Public input `true` has a valid (unit) VM trace and public input `false` has none. The ArkLib
statement is the public input itself, the ArkLib verifier and the arithmetized relation accept
exactly `true`, and the binding/encoding conditions always hold. The verifier that accepts
exactly `true` satisfies `WholeZkVMSoundness`; the accept-all verifier satisfies neither
`WholeZkVMSoundness` nor `WholeZkVMEndToEndClaim`. -/

namespace Toy

/-- Interfaces of the two-input sanity check. -/
abbrev interfaces : WholeZkVMInterfaces where
  PublicInput := Bool
  ConcreteProof := Unit
  ConcreteVerifier := Unit
  ArkStatement := Bool
  ArkProof := Unit
  VmTrace := Unit
  ArithmetizationWitness := Unit
  RecursionArtifact := Unit
  DeploymentArtifact := Unit

/-- Relations of the two-input sanity check; `accepts` says which public inputs the concrete
verifier accepts. -/
abbrev relations (accepts : Bool → Prop) : WholeZkVMRelations interfaces where
  concreteVerifierAccepts _ publicInput _ := accepts publicInput
  implementationMatchesArkSpec _ publicInput _ arkStatement _ := arkStatement = publicInput
  arkVerifierAccepts arkStatement _ := arkStatement = true
  arithmetizedRelation arkStatement _ := arkStatement = true
  publicInputEncoding publicInput arkStatement := arkStatement = publicInput
  vmExecutionValid publicInput _ := publicInput = true
  transcriptAndCommitmentBinding _ _ := True
  recursionPreservesStatement _ _ := True
  deploymentPreservesCall _ _ _ := True

/-- The verifier that accepts exactly the valid public input satisfies the obligations. -/
theorem honest_soundness :
    WholeZkVMSoundness interfaces (relations fun publicInput => publicInput = true) where
  implementationSoundness _ publicInput _ _ _ haccept := ⟨publicInput, (), rfl, rfl, haccept⟩
  arkProofSystemSoundness _ _ _ _ _ _ harkAccept := ⟨(), harkAccept⟩
  arithmetizationSoundness _ _ _ hencode hrelation := ⟨(), hencode ▸ hrelation⟩

/-- The binding/encoding conditions hold for the unique call at public input `false`. -/
theorem bindingConditions_false (accepts : Bool → Prop) :
    (relations accepts).BindingConditions () false () () () :=
  ⟨trivial, fun _ _ _ => ⟨trivial, trivial⟩⟩

/-- The accept-all verifier cannot satisfy the obligations: it accepts public input `false`,
which has no valid VM trace. -/
theorem acceptAll_not_soundness : ¬ WholeZkVMSoundness interfaces (relations fun _ => True) :=
  not_wholeZkVMSoundness_of_acceptAll (publicInput := false) (fun _ _ => trivial)
    (fun _ hvalid => Bool.noConfusion hvalid) (bindingConditions_false _)

/-- The end-to-end claim is not vacuous: it fails for the accept-all verifier. -/
theorem acceptAll_not_endToEndClaim :
    ¬ WholeZkVMEndToEndClaim interfaces (relations fun _ => True) := by
  intro hclaim
  obtain ⟨_, hvalid⟩ := hclaim () false () () () trivial (bindingConditions_false _)
  exact Bool.noConfusion hvalid

end Toy

/-! ### History

Audit L02 (2026-10-28): the previous `WholeZkVMEndToEndClaim` took
`vmExecutionValid publicInput trace` as a premise and concluded
`∃ validTrace, vmExecutionValid publicInput validTrace`, so it held for every choice of boundary
predicates and no verifier, transcript, arithmetization, recursion, or deployment condition
mattered. The existential `WholeZkVMResidual` (`∃ A, WholeZkVMEndToEndClaim I A`) had already
been deleted for the same reason. VM validity is now only the conclusion of the claim, which is
derived from the implications in `WholeZkVMSoundness`. -/

end ZkVMBoundary
end ArkLib
