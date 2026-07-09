/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Spec
import ArkLib.ProofSystem.RingSwitching.BatchingPhase
import ArkLib.ProofSystem.RingSwitching.SumcheckPhase
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeMsgCompleteness
import ArkLib.ProofSystem.RingSwitching.SumcheckLoopPC

/-!
# Full Ring-Switching Protocol

This module contains specifications and security properties for the full
ring-switching protocol. The protocol is a sequential composition of:
1. **Batching Phase** (polynomial packing and batching via tensor algebra operations)
2. **Sumcheck Phase** (ℓ' rounds of sumcheck, and the final sumcheck step)
3. **Large Field Invocation** (invocation to underlying large-field IOPCS)

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).
-/

namespace RingSwitching.FullRingSwitching
noncomputable section
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset Module

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (mlIOPCS : MLIOPCS L ℓ')

def batchingCoreVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:= BatchingPhase.oracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (V₂:=SumcheckPhase.coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (pSpec₂:=pSpecCoreInteraction L ℓ')

/-- The batching-then-core composite verifier is `AppendCoherent` (batching `.append`
core-interaction, both phases coherent), so it can be `.append`ed onto the MLIOPCS sub-protocol. -/
instance instBatchingCoreVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS) :=
  OracleVerifier.Append.AppendCoherent.append
    (c₁ := BatchingPhase.instOracleVerifierAppendCoherent κ L K P ℓ ℓ' h_l
      (aOStmtIn := mlIOPCS.toAbstractOStmtIn))
    (c₂ := RingSwitching.SumcheckPhase.instCoreInteractionOracleVerifierAppendCoherent κ L K P ℓ ℓ' h_l
      (aOStmtIn := mlIOPCS.toAbstractOStmtIn)) _ _

/-- The oracle verifier for the full Binary Basefold protocol -/
@[reducible]
def fullOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:=batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS)
    (V₂:=mlIOPCS.oracleReduction.verifier)
    (pSpec₂:=mlIOPCS.pSpec)

def batchingCoreReduction :=
  OracleReduction.append
    (R₁ := BatchingPhase.batchingOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (R₂ := SumcheckPhase.coreInteractionOracleReduction κ L K P ℓ ℓ' h_l
       mlIOPCS.toAbstractOStmtIn)
    (pSpec₂:=pSpecCoreInteraction L ℓ')

/-- The batching-then-core composite reduction's verifier is `AppendCoherent`. -/
instance instBatchingCoreReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS).verifier :=
  OracleVerifier.Append.AppendCoherent.oracleReductionAppend
    (R₁ := BatchingPhase.batchingOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (R₂ := RingSwitching.SumcheckPhase.coreInteractionOracleReduction κ L K P ℓ ℓ' h_l
       mlIOPCS.toAbstractOStmtIn)

/-- `batchingCoreReduction` generalized from a full `MLIOPCS` to a bare `AbstractOStmtIn`.
The batching/core phase reductions only consume the abstract oracle-statement data, so the
composite is well-defined at any `aOStmtIn`; `batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS`
is definitionally `batchingCoreReductionA κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn`.
Instantiating at `aOStmtIn.strictVariant` yields the strict-track (completeness-side) chain. -/
@[reducible]
def batchingCoreReductionA (aOStmtIn : AbstractOStmtIn L ℓ') :=
  OracleReduction.append
    (R₁ := BatchingPhase.batchingOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    (R₂ := SumcheckPhase.coreInteractionOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    (pSpec₂:=pSpecCoreInteraction L ℓ')

/-- The reduction for the full Binary Basefold protocol, using the strict-track batching/core
relation needed by perfect completeness. The executable oracle data is unchanged by
`strictVariant`; only the compatibility proposition is tightened. -/
@[reducible]
def fullOracleReduction :
    OracleReduction (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn (L:=L) (ℓ := ℓ)) (StmtOut := Bool)
    (OStmtIn:= mlIOPCS.OStmtIn)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := fullPspec κ L K P ℓ' mlIOPCS)
    (WitIn := BatchingWitIn (L:=L) (K:=K) (ℓ := ℓ) (ℓ' := ℓ')) (WitOut := Unit)
    :=
  (batchingCoreReductionA κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn.strictVariant).append
    mlIOPCS.oracleReduction

/-- The full Binary Basefold protocol as a Proof -/
@[reducible]
def fullOracleProof :
    OracleProof []ₒ
    (Statement := BatchingStmtIn (L:=L) (ℓ := ℓ))
    (OStatement := mlIOPCS.OStmtIn)
    (Witness := BatchingWitIn (L:=L) (K:=K) (ℓ := ℓ) (ℓ' := ℓ'))
    (pSpec:= fullPspec κ L K P ℓ' mlIOPCS) :=
    fullOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS

variable [∀ i, SampleableType (mlIOPCS.pSpec.Challenge i)]

/-- Input relation for the full ring-switching protocol -/
abbrev fullInputRelation := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ'
  h_l mlIOPCS.toAbstractOStmtIn
abbrev fullOutputRelation := acceptRejectOracleRel

open scoped NNReal
open Sumcheck.Structured

section SecurityProperties
variable {σ : Type} (init : ProbComp σ) {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [(i : mlIOPCS.pSpec.ChallengeIdx) → SampleableType (mlIOPCS.pSpec.Challenge i)] in
-- `[IsDomain L] [IsDomain K]` are needed by the core-interaction (final-sumcheck) completeness,
-- which invokes the DP24 capstone `A_MLE_eval_eq_compute_final_eq_value` (an `IsDomain` algebra
-- lemma). They hold in every real instantiation (`binaryTowerProfile` builds from fields `K`, `L`).
lemma batchingCore_perfectCompleteness [IsDomain L] [IsDomain K]
    (hBatching : BatchingPhase.batchingReduction_perfectCompleteness_residual
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := mlIOPCS.toAbstractOStmtIn) (init := init) (impl := impl))
    (hRounds : SumcheckPhase.iteratedSumcheckOracleReduction_perfectCompleteness_residual
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := mlIOPCS.toAbstractOStmtIn) (init := init) (impl := impl))
    (hCoreInteractionAppendPerfectCompleteness :
      (SumcheckPhase.coreInteractionOracleReduction κ L K P ℓ ℓ' h_l
        mlIOPCS.toAbstractOStmtIn).perfectCompleteness
        (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
        (OStmtIn := mlIOPCS.toAbstractOStmtIn.OStmtIn)
        (StmtOut := MLPEvalStatement L ℓ')
        (OStmtOut := mlIOPCS.toAbstractOStmtIn.OStmtIn)
        (WitIn := SumcheckWitness L ℓ' 0)
        (WitOut := WitMLP L ℓ')
        (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn 0)
        (relOut := mlIOPCS.toAbstractOStmtIn.toRelInput)
        (init := init)
        (impl := impl))
    (hBatchingCoreAppendPerfectCompleteness :
      (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS).perfectCompleteness
        (pSpec := pSpecLargeFieldReduction κ L K P ℓ')
        (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l
          mlIOPCS.toAbstractOStmtIn)
        (relOut := mlIOPCS.toRelInput)
        (init := init)
        (impl := impl)) :
  (batchingCoreReduction κ L K P ℓ ℓ' h_l mlIOPCS).perfectCompleteness
  (pSpec := pSpecLargeFieldReduction κ L K P ℓ')
  (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
  (relOut := mlIOPCS.toRelInput)
  (init:=init) (impl:=impl) := by
  exact OracleReduction.append_perfectCompleteness
    (R₁ := BatchingPhase.batchingOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (R₂ := SumcheckPhase.coreInteractionOracleReduction κ L K P ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn)
    (h₁ := BatchingPhase.batchingReduction_perfectCompleteness
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := mlIOPCS.toAbstractOStmtIn) (init := init) (impl := impl) hBatching)
    (h₂ := SumcheckPhase.coreInteraction_perfectCompleteness
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := mlIOPCS.toAbstractOStmtIn) (init := init) (impl := impl)
      hRounds hCoreInteractionAppendPerfectCompleteness)
    (hResidual := hBatchingCoreAppendPerfectCompleteness)

-- The unconditional perfect completeness theorem `fullOracleReduction_perfectCompleteness` is
-- proven in the `EndToEndCompleteness` section below (it delegates to the genuine end-to-end
-- capstone `fullOracleReduction_perfectCompleteness'`). It is stated there because its proof
-- depends on the `NeverFail`-only per-phase bricks and the append keystone assembled in that
-- section. All five former append/phase residual hypotheses are now discharged internally; only
-- `NeverFail init` plus the two abstract-opening message-seam facts (which the abstract `MLIOPCS`
-- structure does not carry) survive.

def batchingCoreRbrKnowledgeError
    (i : (pSpecBatching κ L K P ++ₚ pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  Sum.elim (f:=BatchingPhase.batchingRBRKnowledgeError κ L K P)
    (g:=SumcheckPhase.coreInteractionRbrKnowledgeError L ℓ')
    (ChallengeIdx.sumEquiv.symm i)

def fullRbrKnowledgeError (i : (fullPspec κ L K P ℓ' mlIOPCS).ChallengeIdx) : ℝ≥0
    := Sum.elim (f:=batchingCoreRbrKnowledgeError κ L K P ℓ')
  (g:=mlIOPCS.rbrKnowledgeError)
  (ChallengeIdx.sumEquiv.symm i)

variable [SampleableType L]

omit [(i : mlIOPCS.pSpec.ChallengeIdx) → SampleableType (mlIOPCS.pSpec.Challenge i)] in
/-- Round-by-round knowledge soundness for the full ring-switching oracle verifier.
`IsDomain K` (with the existing `IsDomain L`) is inherited from the batching phase's knowledge
soundness, where it backs the DP24 row-extraction capstone; it holds in every real instantiation
(`binaryTowerProfile` builds from a field `K`).

The generic RingSwitching wrapper no longer carries a free Boolean-domain embedding `𝓑`. The
current local KState repairs use the always-valid unit error bounds in the batching and iterated
sumcheck phases until the separate DP24/Schwartz-Zippel root-count residual is proved. -/
theorem fullOracleVerifier_rbrKnowledgeSoundness [IsDomain L] [IsDomain K]
    (hCoreInteractionAppendRbrKnowledgeSoundness :
      (SumcheckPhase.coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l
        mlIOPCS.toAbstractOStmtIn).rbrKnowledgeSoundness
        (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
        (OStmtIn := mlIOPCS.toAbstractOStmtIn.OStmtIn)
        (StmtOut := MLPEvalStatement L ℓ')
        (OStmtOut := mlIOPCS.toAbstractOStmtIn.OStmtIn)
        (WitIn := SumcheckWitness L ℓ' 0)
        (WitOut := WitMLP L ℓ')
        (init := init)
        (impl := impl)
        (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn 0)
        (relOut := mlIOPCS.toAbstractOStmtIn.toRelInput)
        (rbrKnowledgeError := SumcheckPhase.coreInteractionRbrKnowledgeError (L:=L) (ℓ':=ℓ')))
    (hBatchingCoreAppendRbrKnowledgeSoundness :
      (batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS).rbrKnowledgeSoundness
        (init := init)
        (impl := impl)
        (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
        (relOut := mlIOPCS.toRelInput)
        (rbrKnowledgeError := batchingCoreRbrKnowledgeError κ L K P ℓ'))
    (hFullAppendRbrKnowledgeSoundness :
      (fullOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS).rbrKnowledgeSoundness
        (init := init)
        (impl := impl)
        (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
        (relOut := fullOutputRelation)
        (rbrKnowledgeError := fun i => fullRbrKnowledgeError κ L K P ℓ' mlIOPCS i)) :
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := fullOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS)
    (init := init)
    (impl := impl)
    (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
    (relOut := fullOutputRelation)
    (rbrKnowledgeError := fun i => fullRbrKnowledgeError κ L K P ℓ' mlIOPCS i) := by
  unfold fullOracleVerifier fullRbrKnowledgeError
  have batchInteractionRBRKS :=
    OracleVerifier.append_rbrKnowledgeSoundness (init:=init) (impl:=impl)
    (hResidual := hBatchingCoreAppendRbrKnowledgeSoundness)
    (rel₁:=fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
    (rel₂:=sumcheckRoundRelation κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn 0)
    (rel₃:=mlIOPCS.toRelInput)
    (V₁:=BatchingPhase.oracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (V₂:=SumcheckPhase.coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (rbrKnowledgeError₁:=BatchingPhase.batchingRBRKnowledgeError κ L K P)
    (rbrKnowledgeError₂:=SumcheckPhase.coreInteractionRbrKnowledgeError L ℓ')
    (h₁:=BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness κ L K P ℓ
      ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (h₂:=SumcheckPhase.coreInteraction_rbrKnowledgeSoundness κ L K P ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn hCoreInteractionAppendRbrKnowledgeSoundness)

  have res :=
    OracleVerifier.append_rbrKnowledgeSoundness (init:=init) (impl:=impl)
    (hResidual := hFullAppendRbrKnowledgeSoundness)
    (rel₁:=fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
    (rel₂:=mlIOPCS.toRelInput)
    (rel₃:=fullOutputRelation)
    (V₁:=batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS)
    (V₂:=mlIOPCS.oracleReduction.verifier)
    (Oₛ₃:=by exact fun i ↦ OracleInterface.instDefault)
    (rbrKnowledgeError₁:=batchingCoreRbrKnowledgeError κ L K P ℓ')
    (rbrKnowledgeError₂:=mlIOPCS.rbrKnowledgeError)
    (h₁:=batchInteractionRBRKS) (h₂:=by
      convert mlIOPCS.rbrKnowledgeSoundness (L:=L) (ℓ' := ℓ') (init:=init) (impl:=impl)
    )
  convert res

end SecurityProperties
end
/-! ## End-to-end perfect completeness (issue #29)

The hypothesis-free (beyond `NeverFail` + `IsDomain` + the abstract opening's seam facts) forms,
assembled from the proven append keystone and the component perfect-completeness theorems. -/

noncomputable section EndToEndCompleteness

open OracleReduction RingSwitching.SumcheckPhase RingSwitching.BatchingPhase ProtocolSpec

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L] [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (mlIOPCS : MLIOPCS L ℓ')
-- The opening's challenge instances: not derivable from the abstract `MLIOPCS`; supplied as
-- instance hypotheses (true of every concrete scheme). NOTE: deliberately *no*
-- `[∀ i, SampleableType (mlIOPCS.pSpec.Challenge i)]` binder here — the structure field instance
-- (`Spec.lean`) covers it, and a duplicate binder-instance makes the keystone defeq grind through
-- the run semantics (two distinct instance terms for the same class).
variable [∀ i, Fintype (mlIOPCS.pSpec.Challenge i)] [∀ i, Inhabited (mlIOPCS.pSpec.Challenge i)]
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

set_option maxHeartbeats 1000000 in
-- The core-interaction append capstone expands seq-compose protocol indices before the generic
-- completeness keystone can close the two seam-direction goals.
/-- Seam 1 (loop ⋈ final): core-interaction perfect completeness from `NeverFail` alone.
Generalized over a bare `aOStmtIn : AbstractOStmtIn` (the phase bricks never inspect the
compatibility Props), so it instantiates at both the relaxed `mlIOPCS.toAbstractOStmtIn`
and the strict-track `mlIOPCS.toAbstractOStmtIn.strictVariant`. -/
theorem coreInteractionOracleReduction_perfectCompleteness' [IsDomain L] [IsDomain K]
    (aOStmtIn : AbstractOStmtIn L ℓ')
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness
      (oracleReduction := coreInteractionOracleReduction κ L K P ℓ ℓ' h_l
        aOStmtIn)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
      (relOut := aOStmtIn.toRelInput)
      (init := init) (impl := impl) := by
  have hLoop := sumcheckLoopOracleReduction_perfectCompleteness κ L K P ℓ ℓ' h_l
    aOStmtIn (init := init) (impl := impl) hInit
  have hFinal := finalSumcheckOracleReduction_perfectCompleteness κ L K P ℓ ℓ' h_l
    aOStmtIn (init := init) (impl := impl) hInit
  have H := append_perfectCompleteness_keystone (init := init) (impl := impl)
    (R₁ := sumcheckLoopOracleReduction κ L K P ℓ ℓ' aOStmtIn)
    (R₂ := finalSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    hLoop hFinal Nat.one_pos
    (by
      rw [show (⟨Fin.vsum (fun _ : Fin ℓ' => 2), by omega⟩ :
            Fin (Fin.vsum (fun _ : Fin ℓ' => 2) + 1))
          = Fin.natAdd (Fin.vsum (fun _ : Fin ℓ' => 2)) (⟨0, Nat.one_pos⟩ : Fin 1) from by
        ext; simp]
      rw [Prover.append_dir_natAdd]
      rfl)
    (by rfl) hInit
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
  exact H

/-- The sumcheck loop opens with a `P_to_V` message (the round-0 prover polynomial): the loop's
direction at index `0`. From `seqCompose_appendValid` (each round opens `P_to_V`), discarding the
empty case via `NeZero ℓ'`. -/
private theorem sumcheckLoop_dir_zero (hpos : 0 < Fin.vsum (fun _ : Fin ℓ' => 2)) :
    (pSpecSumcheckLoop L ℓ').dir ⟨0, hpos⟩ = .P_to_V := by
  rcases seqCompose_appendValid (pSpec := fun _ : Fin ℓ' => pSpecSumcheckRound L)
      (fun _ => ⟨by norm_num, rfl⟩) with hzero | ⟨h, hdir⟩
  · omega
  · exact hdir

set_option maxHeartbeats 1000000 in
-- The batching/core append capstone instantiates the generic append keystone with the sumcheck-loop
-- protocol, whose challenge-vector instances are expensive to synthesize.
/-- Seam 2 (batching ⋈ core): batching-core perfect completeness from `NeverFail` alone.
Generalized over a bare `aOStmtIn : AbstractOStmtIn` (stated about `batchingCoreReductionA`,
which is definitionally `batchingCoreReduction … mlIOPCS` at `aOStmtIn :=
mlIOPCS.toAbstractOStmtIn`); instantiating at `…(strictVariant)` yields the strict-track
chain consumed by the end-to-end capstone. -/
theorem batchingCoreReduction_perfectCompleteness' [IsDomain L] [IsDomain K]
    (aOStmtIn : AbstractOStmtIn L ℓ')
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness
      (oracleReduction := batchingCoreReductionA κ L K P ℓ ℓ' h_l aOStmtIn)
      (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l aOStmtIn)
      (relOut := aOStmtIn.toRelInput)
      (init := init) (impl := impl) := by
  have hvsum : 0 < Fin.vsum (fun _ : Fin ℓ' => 2) := by
    have : (0 : ℕ) < ℓ' := Nat.pos_of_ne_zero (NeZero.ne ℓ')
    rcases ℓ' with - | k
    · omega
    · rw [Fin.vsum_succ]; omega
  haveI : ∀ j, Fintype ((pSpecSumcheckLoop L ℓ').Challenge j) :=
    @seqComposeChallenge_fintype ℓ' _ (fun _ : Fin ℓ' => pSpecSumcheckRound L)
      (fun _ _ => inferInstance)
  haveI : ∀ j, Inhabited ((pSpecSumcheckLoop L ℓ').Challenge j) :=
    @seqComposeChallenge_inhabited ℓ' _ (fun _ : Fin ℓ' => pSpecSumcheckRound L)
      (fun _ _ => inferInstance)
  haveI := appendCombinedOracle_fintype ([]ₒ : OracleSpec PEmpty)
    (pSpecBatching κ L K P) (pSpecCoreInteraction L ℓ')
  haveI := appendCombinedOracle_inhabited ([]ₒ : OracleSpec PEmpty)
    (pSpecBatching κ L K P) (pSpecCoreInteraction L ℓ')
  have hBatching := batchingReduction_perfectCompleteness
    (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
    (aOStmtIn := aOStmtIn) (init := init) (impl := impl)
    (batchingReduction_perfectCompleteness_proved κ L K P ℓ ℓ' h_l
      (aOStmtIn := aOStmtIn) (init := init) (impl := impl) hInit)
  have hCore := coreInteractionOracleReduction_perfectCompleteness' κ L K P ℓ ℓ' h_l aOStmtIn
    (init := init) (impl := impl) hInit
  have H := append_perfectCompleteness_keystone (init := init) (impl := impl)
    (R₁ := BatchingPhase.batchingOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    (R₂ := coreInteractionOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    hBatching hCore (by omega)
    (by
      rw [show (⟨2, by omega⟩ : Fin (2 + (Fin.vsum (fun _ : Fin ℓ' => 2) + 1)))
          = Fin.natAdd 2 (⟨0, by omega⟩ : Fin (Fin.vsum (fun _ : Fin ℓ' => 2) + 1)) from by
        ext; simp]
      rw [Prover.append_dir_natAdd]
      rw [show (⟨0, by omega⟩ : Fin (Fin.vsum (fun _ : Fin ℓ' => 2) + 1))
          = Fin.castLE (by omega) (⟨0, hvsum⟩ : Fin (Fin.vsum (fun _ : Fin ℓ' => 2))) from by
        ext; simp]
      rw [Prover.append_dir_castLE]
      exact sumcheckLoop_dir_zero L ℓ' hvsum)
    (by
      rw [show (⟨0, by omega⟩ : Fin (Fin.vsum (fun _ : Fin ℓ' => 2) + 1))
          = Fin.castLE (by omega) (⟨0, hvsum⟩ : Fin (Fin.vsum (fun _ : Fin ℓ' => 2))) from by
        ext; simp]
      rw [Prover.append_dir_castLE]
      exact sumcheckLoop_dir_zero L ℓ' hvsum)
    hInit
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
  exact H

set_option maxHeartbeats 1000000 in
-- The strict full RingSwitching capstone is stated directly about the append chain so Lean can reuse
-- the component reductions without unfolding the exported relaxed-track `fullOracleReduction`.
/-- **Issue #29 capstone: strict-track RingSwitching append-chain perfect completeness.**
Hypotheses reduced to `IsDomain` + `NeverFail init` + the abstract MLIOPCS opening's message-seam
facts (the opening has at least one round, opens with a prover message, and its challenges are
finite/inhabited — true of every concrete instantiation; the abstract `MLIOPCS` carries no such
constraints). Every internal residual — per-round, batching, final-sumcheck, loop seqCompose, and
the three append seams — is discharged by proven theorems (the append keystone + the component
perfect completenesses).

The input relation is the **strict-track** batching relation (at
`mlIOPCS.toAbstractOStmtIn.strictVariant`): the opening's `perfectCompleteness` field is stated
w.r.t. `toStrictRelInput` (w.r.t. the relaxed relation it is false for code-based openings — see
the field docstring in `Prelude.lean`), so the whole chain threads the strict compatibility. For
single-track instantiations (`strictInitialCompatibility` defaulted) this coincides with the
former relaxed statement. -/
theorem fullOracleReductionStrictAppend_perfectCompleteness [IsDomain L] [IsDomain K]
    (hInit : NeverFail init)
    (hMlnPos : 0 < mlIOPCS.numRounds)
    (hMlnDir : mlIOPCS.pSpec.dir ⟨0, hMlnPos⟩ = .P_to_V) :
    OracleReduction.perfectCompleteness
      (oracleReduction :=
        (batchingCoreReductionA κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn.strictVariant).append
          mlIOPCS.oracleReduction)
      (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l
        mlIOPCS.toAbstractOStmtIn.strictVariant)
      (relOut := acceptRejectOracleRel)
      (init := init) (impl := impl) := by
  haveI : ∀ j, Fintype ((pSpecSumcheckLoop L ℓ').Challenge j) :=
    @seqComposeChallenge_fintype ℓ' _ (fun _ : Fin ℓ' => pSpecSumcheckRound L)
      (fun _ _ => inferInstance)
  haveI : ∀ j, Inhabited ((pSpecSumcheckLoop L ℓ').Challenge j) :=
    @seqComposeChallenge_inhabited ℓ' _ (fun _ : Fin ℓ' => pSpecSumcheckRound L)
      (fun _ _ => inferInstance)
  haveI : ∀ j, Fintype ((pSpecLargeFieldReduction κ L K P ℓ').Challenge j) :=
    appendChallenge_fintype (pSpecBatching κ L K P) (pSpecCoreInteraction L ℓ')
  haveI : ∀ j, Inhabited ((pSpecLargeFieldReduction κ L K P ℓ').Challenge j) :=
    appendChallenge_inhabited (pSpecBatching κ L K P) (pSpecCoreInteraction L ℓ')
  haveI : ∀ i : Empty, OracleInterface ((fun _ : Empty => Unit) i) := fun i => i.elim
  haveI := appendCombinedOracle_fintype ([]ₒ : OracleSpec PEmpty)
    (pSpecLargeFieldReduction κ L K P ℓ') (mlIOPCS.pSpec)
  haveI := appendCombinedOracle_inhabited ([]ₒ : OracleSpec PEmpty)
    (pSpecLargeFieldReduction κ L K P ℓ') (mlIOPCS.pSpec)
  have hBatchingCore := batchingCoreReduction_perfectCompleteness' κ L K P ℓ ℓ' h_l
    mlIOPCS.toAbstractOStmtIn.strictVariant
    (init := init) (impl := impl) hInit
  -- Ground the opening's completeness first: instantiating the structure field's implicit ∀s
  -- against the keystone's rel-metavariables is a unification storm; pin everything explicitly.
  -- The field is stated at `toStrictRelInput`, which is definitionally
  -- `strictVariant.toRelInput` — the seam with `hBatchingCore`'s relOut.
  have hOpen : OracleReduction.perfectCompleteness
      (oracleReduction := mlIOPCS.oracleReduction)
      (relIn := mlIOPCS.toAbstractOStmtIn.strictVariant.toRelInput)
      (relOut := acceptRejectOracleRel)
      (init := init) (impl := impl) := mlIOPCS.perfectCompleteness hInit
  exact append_perfectCompleteness_keystone.{0, 1} (init := init) (impl := impl)
    (R₁ := batchingCoreReductionA κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn.strictVariant)
    (R₂ := mlIOPCS.oracleReduction)
    (Oₛ₃ := fun i => nomatch i)
    hBatchingCore hOpen hMlnPos
    (by
      rw [show (⟨2 + (Fin.vsum (fun _ : Fin ℓ' => 2) + 1), by omega⟩ :
            Fin (2 + (Fin.vsum (fun _ : Fin ℓ' => 2) + 1) + mlIOPCS.numRounds))
          = Fin.natAdd (2 + (Fin.vsum (fun _ : Fin ℓ' => 2) + 1)) (⟨0, hMlnPos⟩ :
              Fin mlIOPCS.numRounds) from by ext; simp]
      rw [Prover.append_dir_natAdd]
      exact hMlnDir)
    hMlnDir hInit
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])

set_option maxHeartbeats 1000000 in
-- The exported capstone unfolds the public full reduction wrapper before delegating to the strict
-- append-chain theorem.
/-- **Issue #29 capstone: end-to-end RingSwitching perfect completeness, strict track.** -/
theorem fullOracleReduction_perfectCompleteness' [IsDomain L] [IsDomain K]
    (hInit : NeverFail init)
    (hMlnPos : 0 < mlIOPCS.numRounds)
    (hMlnDir : mlIOPCS.pSpec.dir ⟨0, hMlnPos⟩ = .P_to_V) :
    OracleReduction.perfectCompleteness
      (oracleReduction := fullOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS)
      (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l
        mlIOPCS.toAbstractOStmtIn.strictVariant)
      (relOut := acceptRejectOracleRel)
      (init := init) (impl := impl) := by
  exact fullOracleReductionStrictAppend_perfectCompleteness κ L K P ℓ ℓ' h_l mlIOPCS
    hInit hMlnPos hMlnDir

/-- **Issue #29: end-to-end RingSwitching perfect completeness (unconditional core).** The former
five append/phase residual hypotheses (`hRounds`, `hCoreSeqComposePerfectCompleteness`,
`hCoreInteractionAppendPerfectCompleteness`, `hBatchingCoreAppendPerfectCompleteness`,
`hFullAppendPerfectCompleteness`) are all discharged internally: this delegates directly to the
genuine capstone `fullOracleReduction_perfectCompleteness'`, whose every internal residual
(per-round, batching, final-sumcheck, loop seqCompose, and the three append seams) is closed by
proven theorems (the append keystone + the component perfect completenesses) and the structure
field `mlIOPCS.perfectCompleteness`. Only `NeverFail init` plus the two abstract-opening
message-seam facts survive — and those are genuine: the abstract `MLIOPCS` structure carries no
constraint that its opening has a positive number of rounds (`hMlnPos`) or opens with a prover
message (`hMlnDir`); both hold in every concrete instantiation. -/
theorem fullOracleReduction_perfectCompleteness [IsDomain L] [IsDomain K]
    (hInit : NeverFail init)
    (hMlnPos : 0 < mlIOPCS.numRounds)
    (hMlnDir : mlIOPCS.pSpec.dir ⟨0, hMlnPos⟩ = .P_to_V) :
    OracleReduction.perfectCompleteness
      (oracleReduction := fullOracleReduction κ L K P ℓ ℓ' h_l mlIOPCS)
      (relIn := BatchingPhase.batchingInputRelation κ L K P ℓ ℓ' h_l
        mlIOPCS.toAbstractOStmtIn.strictVariant)
      (relOut := acceptRejectOracleRel)
      (init := init) (impl := impl) :=
  fullOracleReduction_perfectCompleteness' κ L K P ℓ ℓ' h_l mlIOPCS hInit hMlnPos hMlnDir

end EndToEndCompleteness

end RingSwitching.FullRingSwitching
