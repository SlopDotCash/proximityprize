/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.BCS.Basic
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessMsgProof

/-!
# BCS soundness composition, unconditional in the message-seam case (#62)

`BCSCompiledPhases.toReduction_soundness_of_append` (in `ArkLib/OracleReduction/BCS/Basic.lean`)
composes the soundness of the two BCS phases (committed-interaction + opening) into soundness of the
appended BCS verifier, but it takes the named append-soundness residual
`Verifier.appendSoundnessResidual` as an *unproved* hypothesis (`hAppend`).

This file removes that hypothesis for the **message-first seam** case — the case that actually
arises in the BCS compiler, whose opening phase begins with a prover commitment/opening message.
The keystone is `Verifier.append_soundness_msg'` (proven axiom-clean in
`AppendSoundnessMsgProof.lean`), which proves
`(V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂)` directly from the two per-phase
soundness bounds under the message-seam side conditions. Since the residual
`appendSoundnessResidual V₁ V₂ h₁ h₂` is *definitionally* exactly that conclusion,
`Verifier.append_soundness_msg_residual` discharges it unconditionally, and the BCS bridge
below threads it through
`BCSCompiledPhases.toReduction`.

## What is and is not proved here

The result is unconditional in the sense relevant to issue #62's named-residual bookkeeping: the
BCS soundness-composition theorem below no longer carries `Verifier.appendSoundnessResidual` (the
deep malicious-prover seam-decomposition + union bound) as an opaque assumption — that content is
now a *theorem*. It still takes, as genuine inputs:

* the two per-phase soundness bounds `hInteraction` / `hOpening` (the actual cryptographic content
  of each phase — these are exactly the hypotheses the original theorem takes);
* the message-seam structural facts `hSeamDir` / `hOpeningFirstDir` / `hOpeningPos`, which say the
  seam round and the opening phase's first round are prover messages (true for any
  commitment-opening opening phase, supplied by the caller who knows the concrete opening spec);
* the `impl` side conditions `himplSP` / `himplNF` / `himplVB` (state-preserving / never-failing /
  value-blind), which hold for the honest interactive implementation.

It does *not* prove commitment binding/extractability or the generic query-log compiler; those
remain the separate bricks tracked by `BCSSecurityFrontier`. The point of this file is precisely
that the *append-composition* obligation, previously an unproved `Prop` residual, is now closed for
the message seam.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

namespace OracleReduction

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    {m : ℕ} {nCom : pSpec.MessageIdx → ℕ} {pSpecCom : ∀ i, ProtocolSpec (nCom i)}
    {StmtIn StmtOut WitIn WitOut : Type}

omit Oₘ in
/-- **Unconditional BCS soundness composition, message-seam case.**

This is `BCSCompiledPhases.toReduction_soundness_of_append` with the named residual hypothesis
`hAppend : Verifier.appendSoundnessResidual …` *eliminated*. For the message-first seam (the case
that arises in the BCS compiler) the residual is proved internally from
`Verifier.append_soundness_msg_residual`, so this theorem composes the two per-phase soundness
bounds into soundness of the appended BCS verifier `phases.toReduction.verifier` outright.

The structural hypotheses `hSeamDir` (the seam round of the BCS-transformed spec is a prover
message) and `hOpeningFirstDir` (the opening phase opens with a prover message), together with
`hOpeningPos : 0 < …` on the opening-phase length, hold for any genuine commitment-opening opening
phase and are supplied by the caller. The `impl` conditions `himplSP` / `himplNF` / `himplVB` are
the soundness analogues of the honest-implementation side conditions used throughout #62. -/
theorem BCSCompiledPhases.toReduction_soundness_of_append_msg {StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    [∀ i, SampleableType ((pSpec.renameMessage CommitmentType).Challenge i)]
    [∀ i, SampleableType ((pSpec.BCSOpeningPhase pSpecCom e).Challenge i)]
    [Inhabited StmtMid]
    (phases : BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec) (pSpecCom := pSpecCom)
      (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
      (StmtMid := StmtMid) (WitMid := WitMid) CommitmentType e)
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {langIn : Set StmtIn} {langMid : Set StmtMid} {langOut : Set StmtOut}
    {εInteraction εOpening : ℝ≥0}
    (hInteraction :
      phases.interaction.verifier.soundness init impl langIn langMid εInteraction)
    (hOpening : phases.opening.verifier.soundness init impl langMid langOut εOpening)
    (hOpeningPos : 0 < Fin.vsum (fun j => nCom (e.symm j)))
    (hSeamDir :
      ((pSpec.renameMessage CommitmentType) ++ₚ (pSpec.BCSOpeningPhase pSpecCom e)).dir
        (⟨n, by omega⟩ : Fin (n + Fin.vsum (fun j => nCom (e.symm j)))) = .P_to_V)
    (hOpeningFirstDir :
      (pSpec.BCSOpeningPhase pSpecCom e).dir
        (⟨0, hOpeningPos⟩ : Fin (Fin.vsum (fun j => nCom (e.symm j)))) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    @Verifier.soundness _ oSpec StmtIn StmtOut
      (n + Fin.vsum (fun j => nCom (e.symm j)))
      (pSpec.renameMessage CommitmentType ++ₚ pSpec.BCSOpeningPhase pSpecCom e)
      (fun i => ProtocolSpec.instSampleableTypeChallengeAppend i)
      σ init impl langIn langOut phases.toReduction.verifier (εInteraction + εOpening) := by
  -- The deep `appendSoundnessResidual` is now a *theorem* for the message seam: discharge it via
  -- `Verifier.append_soundness_msg_residual`, then feed it to the existing BCS append-soundness
  -- bridge `BCSCompiledPhases.toReduction_soundness_of_append`.
  exact BCSCompiledPhases.toReduction_soundness_of_append phases hInteraction hOpening
    (_root_.Verifier.append_soundness_msg_residual
      (init := init) (impl := impl)
      (V₁ := phases.interaction.verifier) (V₂ := phases.opening.verifier)
      (lang₁ := langIn) (lang₂ := langMid) (lang₃ := langOut)
      (ε₁ := εInteraction) (ε₂ := εOpening)
      hInteraction hOpening hOpeningPos hSeamDir hOpeningFirstDir himplSP himplNF himplVB)

end OracleReduction

-- Axiom audit: the unconditional BCS message-seam soundness composition must not add `sorryAx`.
#print axioms OracleReduction.BCSCompiledPhases.toReduction_soundness_of_append_msg
