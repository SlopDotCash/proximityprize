/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.SumcheckDeterminism
import ArkLib.ProofSystem.RingSwitching.WiringInstances
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeRbrKnowledgeProof
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeFailingDet

/-!
# RingSwitching rbr knowledge-soundness wiring: sumcheck loop + core interaction (issue #29)

Discharges the first composed seam of the RingSwitching rbr knowledge-soundness chain in the
stateless (`Subsingleton σ`, reachable lossless `init`) regime:

* `sumcheckLoop_rbrKnowledgeSoundness` — the `ℓ'`-fold `seqCompose` of the iterated sumcheck round
  verifiers is rbr knowledge-sound, by a single application of the n-ary
  `OracleVerifier.seqCompose_rbrKnowledgeSoundness_failingDet` (`SeqComposeRbrKnowledgeProof.lean`)
  at the per-round failing-determinism witnesses (`SumcheckDeterminism.lean`) and per-round bounds
  (`SumcheckPhase.lean`).
* `coreInteraction_rbrKnowledgeSoundness_wired` — the loop `++` final-sumcheck seam, by the
  failing-deterministic message-seam keystone with the loop's composite failing-determinism
  witness (`OracleVerifier.seqCompose_toVerifier_isFailingDet`); the resulting `Sum.elim` error is
  definitionally `coreInteractionRbrKnowledgeError`. This is exactly the
  `hCoreInteractionAppendRbrKnowledgeSoundness` residual of
  `FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` (`General.lean`).
* `coreInteraction_toVerifier_isFailingDet` — the core interaction compiles to a
  failing-deterministic `toVerifier` (consumed by the full seam's composite witness).

The only surviving hypotheses are the stateless-regime side conditions and the abstract
oracle-statement pack inhabitation `[Inhabited (∀ j, aOStmtIn.OStmtIn j)]` (the abstract
`AbstractOStmtIn` carries no such constraint; concrete instantiations supply it).
-/

open OracleSpec OracleComp ProtocolSpec
open Sumcheck.Structured
open scoped NNReal

noncomputable section
namespace RingSwitching.SumcheckPhase

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- **rbr knowledge soundness of the iterated-sumcheck loop** (the `ℓ'`-fold `seqCompose` of the
round verifiers), in the stateless regime: one application of the n-ary failing-det `seqCompose`
keystone at the per-round failing-determinism witnesses and per-round bounds. -/
theorem sumcheckLoop_rbrKnowledgeSoundness [IsDomain L] [Subsingleton σ]
    [Inhabited (∀ j, aOStmtIn.OStmtIn j)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0) :
    (sumcheckLoopOracleVerifier κ L K P ℓ ℓ' aOStmtIn).rbrKnowledgeSoundness init impl
      (sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
      (sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
      (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        roundKnowledgeError L ℓ' ij.1) :=
  OracleVerifier.seqCompose_rbrKnowledgeSoundness_failingDet
    (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P))
    (fun _ => aOStmtIn.OStmtIn)
    (fun i => SumcheckWitness L ℓ' i)
    (fun i => iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i)
    (fun i => sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i)
    (fun i _ => roundKnowledgeError L ℓ' i)
    (fun i => ⟨_, iteratedSumcheckOracleVerifier_toVerifier_failingDet κ L K P ℓ ℓ' aOStmtIn i⟩)
    (fun _ => ⟨by omega, pSpecSumcheckRound_dir_zero L⟩)
    (fun _ => ⟨default⟩)
    hInit hInitNF
    (fun i => iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness (κ := κ) (L := L) (K := K)
      (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn)
      (init := init) (impl := impl) i)

/-- **The sumcheck loop compiles to a failing-deterministic `toVerifier`** — the composite
determinism witness for the loop side of the core-interaction seam, by the n-ary
failing-determinism witness at the per-round witnesses. -/
theorem sumcheckLoop_toVerifier_isFailingDet :
    (sumcheckLoopOracleVerifier κ L K P ℓ ℓ' aOStmtIn).toVerifier.IsFailingDet :=
  OracleVerifier.seqCompose_toVerifier_isFailingDet
    (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P))
    (fun _ => aOStmtIn.OStmtIn)
    (fun i => iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i)
    (fun i => ⟨_, iteratedSumcheckOracleVerifier_toVerifier_failingDet κ L K P ℓ ℓ' aOStmtIn i⟩)

variable [IsDomain L] [IsDomain K]

/-- **The core interaction compiles to a failing-deterministic `toVerifier`** (loop `++` final
sumcheck: failing-det composes across the seam) — the composite determinism witness for the
batching-core and full seams. -/
theorem coreInteraction_toVerifier_isFailingDet :
    (coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier.IsFailingDet := by
  show (OracleVerifier.append
      (sumcheckLoopOracleVerifier κ L K P ℓ ℓ' aOStmtIn)
      (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn)).toVerifier.IsFailingDet
  rw [OracleReduction.oracleVerifier_append_toVerifier]
  exact (sumcheckLoop_toVerifier_isFailingDet κ L K P ℓ ℓ' aOStmtIn).append
    ⟨_, finalSumcheckVerifier_toVerifier_failingDet κ L K P ℓ ℓ' h_l aOStmtIn⟩

/-- **rbr knowledge soundness of the core interaction (loop `++` final sumcheck), wired** — the
failing-deterministic message-seam keystone at the loop's composite failing-determinism witness,
with the `Sum.elim` error definitionally equal to `coreInteractionRbrKnowledgeError`. Discharges
the `hCoreInteractionAppendRbrKnowledgeSoundness` residual of
`FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness`. -/
theorem coreInteraction_rbrKnowledgeSoundness_wired [Subsingleton σ]
    [Inhabited (∀ j, aOStmtIn.OStmtIn j)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0) :
    (coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn).rbrKnowledgeSoundness
      (init := init) (impl := impl)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
      (relOut := aOStmtIn.toRelInput)
      (rbrKnowledgeError := coreInteractionRbrKnowledgeError (L := L) (ℓ' := ℓ')) := by
  obtain ⟨v?, hVerify⟩ := sumcheckLoop_toVerifier_isFailingDet κ L K P ℓ ℓ' aOStmtIn
  have hKey := OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton
    (V₁ := sumcheckLoopOracleVerifier κ L K P ℓ ℓ' aOStmtIn)
    (V₂ := finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (verify? := v?) (hVerify := hVerify)
    (hInit := hInit) (hInitNF := hInitNF)
    (hNEW₂ := ⟨default⟩)
    (hn := Nat.one_pos)
    (hDir := pSpecCoreInteraction_dir_seam L ℓ')
    (hDir₂ := pSpecFinalSumcheck_dir_zero L)
    (h₁ := sumcheckLoop_rbrKnowledgeSoundness κ L K P ℓ ℓ' h_l aOStmtIn hInit hInitNF)
    (h₂ := finalSumcheckOracleVerifier_rbrKnowledgeSoundness (κ := κ) (L := L) (K := K) (P := P)
      (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) init impl)
  have herr : (coreInteractionRbrKnowledgeError (L := L) (ℓ' := ℓ'))
      = (Sum.elim
          (fun combinedIdx =>
            letI ij := seqComposeChallengeIdxToSigma combinedIdx
            roundKnowledgeError L ℓ' ij.1)
          (fun _ => finalSumcheckRbrKnowledgeError (L := L))
          ∘ ⇑ChallengeIdx.sumEquiv.symm) := rfl
  rw [herr]
  exact hKey

end RingSwitching.SumcheckPhase
end

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms RingSwitching.SumcheckPhase.sumcheckLoop_rbrKnowledgeSoundness
#print axioms RingSwitching.SumcheckPhase.sumcheckLoop_toVerifier_isFailingDet
#print axioms RingSwitching.SumcheckPhase.coreInteraction_toVerifier_isFailingDet
#print axioms RingSwitching.SumcheckPhase.coreInteraction_rbrKnowledgeSoundness_wired
