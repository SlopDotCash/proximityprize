/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.BCS.Basic
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessProof

/-!
# BCS transform preserves perfect completeness (Issue #62)

The reduction-level BCS transform `OracleReduction.BCSTransform e interaction opening` is, by
definition, the sequential composition `Reduction.append interaction opening` of the interaction
phase (oracle messages replaced by commitments) and the opening phase (per-message opening proofs).
Its perfect completeness is therefore exactly the perfect completeness of `Reduction.append`, which
is now a genuine, axiom-clean theorem (`Reduction.append_perfectCompleteness_msg_proof`) rather than
a residual. This discharges the completeness half of the BCS preservation obligation (part of #62 /
#433) directly from the per-phase completeness hypotheses — no longer a pass-through.
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleReduction

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [oSpec.Fintype] [oSpec.Inhabited]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    {m : ℕ} {nCom : pSpec.MessageIdx → ℕ} {pSpecCom : ∀ i, ProtocolSpec (nCom i)}
    {StmtIn StmtOut WitIn WitOut StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type}
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Challenge sampler for the BCS-transformed spec. `ProtocolSpec.BCSTransform pSpecCom
CommitmentType e` is *definitionally* `(pSpec.renameMessage CommitmentType) ++ₚ
(pSpec.BCSOpeningPhase pSpecCom e)`, so a `SampleableType` for each phase's challenges (the append
form) is, by `rfl`, a `SampleableType` for the transformed spec's challenges. Providing this as an
instance lets `perfectCompleteness` over the `BCSTransform`-form spec synthesize *the same* instance
the append composition theorem uses, so the two line up syntactically. -/
local instance instSampleableTypeBCSTransformChallenge
    (e : pSpec.MessageIdx ≃ Fin m) {CommitmentType : pSpec.MessageIdx → Type}
    [∀ i, SampleableType ((pSpec.renameMessage CommitmentType).Challenge i)]
    [∀ i, SampleableType ((pSpec.BCSOpeningPhase pSpecCom e).Challenge i)] :
    ∀ i, SampleableType ((pSpec.BCSTransform pSpecCom CommitmentType e).Challenge i) :=
  fun i => inferInstanceAs (SampleableType
    (((pSpec.renameMessage CommitmentType) ++ₚ (pSpec.BCSOpeningPhase pSpecCom e)).Challenge i))

/-- **The BCS transform preserves perfect completeness.** If the interaction phase and the opening
phase are each perfectly complete (for the intermediate relation `relMid`), then the BCS-compiled
reduction `OracleReduction.BCSTransform e interaction opening` is perfectly complete. Proven by
unfolding the transform to `Reduction.append` and invoking the sequential-composition completeness
theorem at the interaction/opening seam. -/
theorem BCSTransform_perfectCompleteness
    (e : pSpec.MessageIdx ≃ Fin m)
    (interaction :
      Reduction oSpec StmtIn WitIn StmtMid WitMid (pSpec.renameMessage CommitmentType))
    (opening :
      Reduction oSpec StmtMid WitMid StmtOut WitOut (pSpec.BCSOpeningPhase pSpecCom e))
    {relIn : Set (StmtIn × WitIn)} {relMid : Set (StmtMid × WitMid)}
    {relOut : Set (StmtOut × WitOut)}
    [∀ i, SampleableType ((pSpec.renameMessage CommitmentType).Challenge i)]
    [∀ i, SampleableType ((pSpec.BCSOpeningPhase pSpecCom e).Challenge i)]
    (h_int : interaction.perfectCompleteness init impl relIn relMid)
    (h_open : opening.perfectCompleteness init impl relMid relOut)
    (hn : 0 < Fin.vsum (fun j => nCom (e.symm j)))
    (hDir : ((pSpec.renameMessage CommitmentType) ++ₚ (pSpec.BCSOpeningPhase pSpecCom e)).dir
        (⟨n, by omega⟩ : Fin (n + Fin.vsum (fun j => nCom (e.symm j)))) = .P_to_V)
    (hDir₂ : (pSpec.BCSOpeningPhase pSpecCom e).dir
        (⟨0, hn⟩ : Fin (Fin.vsum (fun j => nCom (e.symm j)))) = .P_to_V)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftM q : OracleComp oSpec β))
    [(oSpec + [((pSpec.renameMessage CommitmentType) ++ₚ
        (pSpec.BCSOpeningPhase pSpecCom e)).Challenge]ₒ).Fintype]
    [(oSpec + [((pSpec.renameMessage CommitmentType) ++ₚ
        (pSpec.BCSOpeningPhase pSpecCom e)).Challenge]ₒ).Inhabited]
    [(oSpec + [(pSpec.renameMessage CommitmentType).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec.renameMessage CommitmentType).Challenge]ₒ).Inhabited]
    [(oSpec + [(pSpec.BCSOpeningPhase pSpecCom e).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec.BCSOpeningPhase pSpecCom e).Challenge]ₒ).Inhabited] :
    (OracleReduction.BCSTransform e interaction opening).perfectCompleteness init impl relIn relOut := by
  -- `OracleReduction.BCSTransform e interaction opening` is, by definition, the sequential
  -- composition `Reduction.append interaction opening` over the append spec
  -- `(pSpec.renameMessage CommitmentType) ++ₚ (pSpec.BCSOpeningPhase pSpecCom e)`. Apply the
  -- composition completeness theorem with the two phase specs supplied *explicitly* (so the
  -- elaborator never has to whnf-unfold `ProtocolSpec.BCSTransform` to recover them), leaving only a
  -- `rfl`-defeq between the goal's `BCSTransform`-form reduction and `interaction.append opening`.
  exact @Reduction.append_perfectCompleteness_msg_proof ι oSpec _ _
    StmtIn WitIn StmtMid WitMid StmtOut WitOut
    n (Fin.vsum (fun j => nCom (e.symm j)))
    (pSpec.renameMessage CommitmentType) (pSpec.BCSOpeningPhase pSpecCom e) _ _
    σ init impl relIn relMid relOut
    interaction opening h_int h_open hn hDir hDir₂ hInit hImplSupp _ _ _ _ _ _

end OracleReduction
