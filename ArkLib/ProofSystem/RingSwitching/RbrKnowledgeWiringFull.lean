/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.General
import ArkLib.ProofSystem.RingSwitching.RbrKnowledgeWiring
import ArkLib.ProofSystem.RingSwitching.BatchingDeterminism

/-!
# RingSwitching rbr knowledge soundness: the wired end-to-end capstone (issue #29)

Discharges the remaining two seams of the RingSwitching rbr knowledge-soundness chain and lands
the **unconditional end-to-end theorem** in the stateless (`Subsingleton σ`, reachable lossless
`init`) regime:

* `batchingCore_rbrKnowledgeSoundness_wired` — the batching `++` core-interaction seam, by the
  *total*-deterministic message-seam keystone at the batching determinism witness
  (`batchingOracleVerifier_toVerifier_pure`); discharges the
  `hBatchingCoreAppendRbrKnowledgeSoundness` residual of
  `fullOracleVerifier_rbrKnowledgeSoundness`.
* `fullOracleVerifier_rbrKnowledgeSoundness_wired` — the batching-core `++` MLIOPCS seam, by the
  *failing*-deterministic message-seam keystone at the composite witness (batching is pure,
  core interaction is failing-deterministic; failing-determinism composes across seams). Its
  statement **is** the `hFullAppendRbrKnowledgeSoundness` residual — i.e. the full
  round-by-round knowledge soundness of the ring-switching oracle verifier, no append residuals.

Surviving hypotheses (all honest instantiation facts, mirroring the completeness capstone):
`[IsDomain L] [IsDomain K]` (DP24 batching capstone), `[Subsingleton σ]` + `hInit`/`hInitNF`
(the stateless regime; `σ = Unit`, `init = pure ()` in the real `oSpec = []ₒ` instantiations),
`[Inhabited (∀ j, mlIOPCS.toAbstractOStmtIn.OStmtIn j)]` (the abstract oracle-statement pack),
and the abstract opening's message-seam facts `hMlnPos`/`hMlnDir` (the abstract `MLIOPCS`
structure carries no such constraint).
-/

open OracleSpec OracleComp ProtocolSpec
open Sumcheck.Structured
open scoped NNReal

namespace RingSwitching.FullRingSwitching
noncomputable section

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (mlIOPCS : MLIOPCS L ℓ')
variable {σ : Type} (init : ProbComp σ) {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- The MLIOPCS structure carries its own challenge-sampling data (`O_challenges`); expose it as
the instance, so that the full-protocol statements and the keystone applications instantiate at
the *same* (structure-field) instance as the `MLIOPCS.rbrKnowledgeSoundness` field's statement. -/
local instance instMLIOPCSChallengeSampleable :
    ∀ i, SampleableType (mlIOPCS.pSpec.Challenge i) := mlIOPCS.O_challenges

/-- **rbr knowledge soundness of the batching-core composite (batching `++` core interaction),
wired** — the total-deterministic message-seam keystone at the batching determinism witness, with
the core-interaction side supplied by `coreInteraction_rbrKnowledgeSoundness_wired`. The
`Sum.elim` error is definitionally `batchingCoreRbrKnowledgeError`. Discharges the
`hBatchingCoreAppendRbrKnowledgeSoundness` residual of
`fullOracleVerifier_rbrKnowledgeSoundness`. -/
theorem batchingCore_rbrKnowledgeSoundness_wired [IsDomain L] [IsDomain K] [Subsingleton σ]
    [Inhabited (∀ j, mlIOPCS.toAbstractOStmtIn.OStmtIn j)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0) :
    (batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS).rbrKnowledgeSoundness
      (init := init) (impl := impl)
      (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
      (relOut := mlIOPCS.toRelInput)
      (rbrKnowledgeError := batchingCoreRbrKnowledgeError κ L K P ℓ') := by
  have hKey := OracleVerifier.append_rbrKnowledgeSoundness_subsingleton
    (init := init) (impl := impl)
    (V₁ := BatchingPhase.oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn := mlIOPCS.toAbstractOStmtIn))
    (V₂ := SumcheckPhase.coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS.toAbstractOStmtIn)
    (verify := _)
    (hVerify := BatchingPhase.batchingOracleVerifier_toVerifier_pure κ L K P ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn)
    (hInit := hInit) (hInitNF := hInitNF)
    (hNE₂ := ⟨default⟩) (hNEW₂ := ⟨default⟩)
    (hn := Nat.succ_pos _)
    (hDir := pSpecLargeFieldReduction_dir_seam (κ := κ) (L := L) (K := K) (P := P) (ℓ' := ℓ'))
    (hDir₂ := pSpecCoreInteraction_dir_zero (L := L) (ℓ' := ℓ'))
    (h₁ := BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness κ L K P ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn)
    (h₂ := SumcheckPhase.coreInteraction_rbrKnowledgeSoundness_wired κ L K P ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn hInit hInitNF)
  have herr : batchingCoreRbrKnowledgeError κ L K P ℓ'
      = (Sum.elim (BatchingPhase.batchingRBRKnowledgeError (κ := κ) (L := L) (K := K) (P := P))
          (SumcheckPhase.coreInteractionRbrKnowledgeError (L := L) (ℓ' := ℓ'))
          ∘ ⇑ChallengeIdx.sumEquiv.symm) := rfl
  rw [herr]
  exact hKey

/-- **The batching-core composite compiles to a failing-deterministic `toVerifier`**: batching is
total-deterministic (hence failing-deterministic with the always-`some` verdict) and the core
interaction is failing-deterministic; failing-determinism composes across the seam. -/
theorem batchingCore_toVerifier_isFailingDet [IsDomain L] [IsDomain K] :
    (batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS).toVerifier.IsFailingDet := by
  show (OracleVerifier.append
      (BatchingPhase.oracleVerifier κ L K P ℓ ℓ' h_l (aOStmtIn := mlIOPCS.toAbstractOStmtIn))
      (SumcheckPhase.coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l
        mlIOPCS.toAbstractOStmtIn)).toVerifier.IsFailingDet
  rw [OracleReduction.oracleVerifier_append_toVerifier]
  exact (Verifier.IsFailingDet.of_pure _
      (BatchingPhase.batchingOracleVerifier_toVerifier_pure κ L K P ℓ ℓ' h_l
        mlIOPCS.toAbstractOStmtIn)).append
    (SumcheckPhase.coreInteraction_toVerifier_isFailingDet κ L K P ℓ ℓ' h_l
      mlIOPCS.toAbstractOStmtIn)

/-- **Round-by-round knowledge soundness of the full ring-switching oracle verifier, wired** —
no append residuals. This statement is exactly the `hFullAppendRbrKnowledgeSoundness` residual of
`fullOracleVerifier_rbrKnowledgeSoundness`, proven by the failing-deterministic message-seam
keystone at the batching-core composite determinism witness, with the MLIOPCS side supplied by
the structure's own `rbrKnowledgeSoundness` field. The `Sum.elim` error is definitionally
`fullRbrKnowledgeError`. -/
theorem fullOracleVerifier_rbrKnowledgeSoundness_wired [IsDomain L] [IsDomain K] [Subsingleton σ]
    [Inhabited (∀ j, mlIOPCS.toAbstractOStmtIn.OStmtIn j)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hMlnPos : 0 < mlIOPCS.numRounds)
    (hMlnDir : mlIOPCS.pSpec.dir ⟨0, hMlnPos⟩ = .P_to_V) :
    (fullOracleVerifier κ L K P ℓ ℓ' h_l mlIOPCS).rbrKnowledgeSoundness
      (init := init) (impl := impl)
      (relIn := fullInputRelation κ L K P ℓ ℓ' h_l mlIOPCS)
      (relOut := fullOutputRelation)
      (rbrKnowledgeError := fun i => fullRbrKnowledgeError κ L K P ℓ' mlIOPCS i) := by
  obtain ⟨v?, hVerify⟩ := batchingCore_toVerifier_isFailingDet κ L K P ℓ ℓ' h_l mlIOPCS
  have hKey := OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton
    (init := init) (impl := impl)
    (V₁ := batchingCoreVerifier κ L K P ℓ ℓ' h_l mlIOPCS)
    (V₂ := mlIOPCS.oracleReduction.verifier)
    (Oₛ₃ := fun _ => OracleInterface.instDefault)
    (verify? := v?) (hVerify := hVerify)
    (hInit := hInit) (hInitNF := hInitNF)
    (hNEW₂ := ⟨default⟩)
    (hn := hMlnPos)
    (hDir := fullPspec_dir_seam (κ := κ) (L := L) (K := K) (P := P) (ℓ' := ℓ')
      mlIOPCS hMlnPos hMlnDir)
    (hDir₂ := hMlnDir)
    (h₁ := batchingCore_rbrKnowledgeSoundness_wired κ L K P ℓ ℓ' h_l mlIOPCS init hInit hInitNF)
    (h₂ := mlIOPCS.rbrKnowledgeSoundness)
  have herr : (fun i => fullRbrKnowledgeError κ L K P ℓ' mlIOPCS i)
      = (Sum.elim (batchingCoreRbrKnowledgeError κ L K P ℓ') mlIOPCS.rbrKnowledgeError
          ∘ ⇑ChallengeIdx.sumEquiv.symm) := rfl
  rw [herr]
  exact hKey

end
end RingSwitching.FullRingSwitching

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms RingSwitching.FullRingSwitching.batchingCore_rbrKnowledgeSoundness_wired
#print axioms RingSwitching.FullRingSwitching.batchingCore_toVerifier_isFailingDet
#print axioms RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness_wired
