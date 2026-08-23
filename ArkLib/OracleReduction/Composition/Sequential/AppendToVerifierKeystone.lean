/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessOracle
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ

/-!
# The `toVerifier`/`append` keystone for oracle reductions

This file discharges the last generic obstruction of the sequential-composition append
perfect-completeness keystone (shared by issues #29, #114, #62, #13): the verifier-fusion equation

  `(OracleVerifier.append V₁ V₂).toVerifier = Verifier.append V₁.toVerifier V₂.toVerifier`.

The proof (`oracleVerifier_append_toVerifier`) pushes the combined `simOracle2` through the routed
double-`simulateQ` of `OracleVerifier.Append.verify` using the `simulateQ` fusion law and the two
router collapses (`router1_collapse`, `router2_collapse`), reconciles the split challenge arguments
(`challenges_fst_heq`/`snd_heq`), and matches the output-oracle routing via `mkVerifierOStmtOut_append`
(the combined `append.embed` routing equals the two-stage `mkVerifierOStmtOut` composition).

Consequently `appendToReductionResidual` is discharged for every pair of oracle reductions
(`appendToReductionResidual_proof`), which unblocks `append_perfectCompleteness_msg_proof` to give
unconditional message-seam append perfect completeness.
-/

open OracleComp OracleSpec ProtocolSpec OracleInterface QueryImpl

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)] [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]

theorem mkVerifierOStmtOut_append
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (oStmt : ∀ i, OStmt₁ i) (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (i : ιₛ₃) :
    OracleVerifier.mkVerifierOStmtOut
        (OracleVerifier.append (Oₛ₁:=Oₛ₁) (Oₛ₂:=Oₛ₂) (Oₘ₁:=Oₘ₁) V₁ V₂).embed
        (OracleVerifier.append (Oₛ₁:=Oₛ₁) (Oₛ₂:=Oₛ₂) (Oₘ₁:=Oₘ₁) V₁ V₂).hEq oStmt tr i
      = OracleVerifier.mkVerifierOStmtOut V₂.embed V₂.hEq
          (OracleVerifier.mkVerifierOStmtOut V₁.embed V₁.hEq oStmt tr.fst) tr.snd i := by
  rcases hv2 : V₂.embed i with j | j
  · rcases hv1 : V₁.embed j with k | k
    · have hcomb : (OracleVerifier.append V₁ V₂).embed i = Sum.inl k := by
        simp only [OracleVerifier.Append.append_embed_eq, hv2, hv1, Sum.map_inl, id_eq]
      rw [OracleVerifier.mkVerifierOStmtOut_inl _ _ _ _ _ _ hcomb,
          OracleVerifier.mkVerifierOStmtOut_inl _ _ _ _ _ _ hv2,
          OracleVerifier.mkVerifierOStmtOut_inl _ _ _ _ _ _ hv1]
      apply eq_of_heq
      simp only [eqRec_eq_cast]
      refine HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _)
        (HEq.symm (HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _)
          (HEq.trans (cast_heq _ _) (cast_heq _ _))))))
    · have hcomb : (OracleVerifier.append V₁ V₂).embed i = Sum.inr (MessageIdx.inl k) := by
        simp only [OracleVerifier.Append.append_embed_eq, hv2, hv1, Sum.map_inr]
      rw [OracleVerifier.mkVerifierOStmtOut_inr _ _ _ _ _ _ hcomb,
          OracleVerifier.mkVerifierOStmtOut_inl _ _ _ _ _ _ hv2,
          OracleVerifier.mkVerifierOStmtOut_inr _ _ _ _ _ _ hv1]
      apply eq_of_heq
      simp only [eqRec_eq_cast]
      refine HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _) ?_)
      refine HEq.trans (OracleVerifier.Append.messages_fst_heq tr k).symm ?_
      exact (HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _)
        (HEq.trans (cast_heq _ _) (cast_heq _ _)))).symm
  · have hcomb : (OracleVerifier.append V₁ V₂).embed i = Sum.inr (MessageIdx.inr j) := by
      simp only [OracleVerifier.Append.append_embed_eq, hv2]
    rw [OracleVerifier.mkVerifierOStmtOut_inr _ _ _ _ _ _ hcomb,
        OracleVerifier.mkVerifierOStmtOut_inr _ _ _ _ _ _ hv2]
    apply eq_of_heq
    simp only [eqRec_eq_cast]
    refine HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _) ?_)
    refine HEq.trans (OracleVerifier.Append.messages_snd_heq tr j).symm ?_
    exact (HEq.trans (cast_heq _ _) (cast_heq _ _)).symm

theorem oracleVerifier_append_toVerifier
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
    (OracleVerifier.append (Oₛ₁:=Oₛ₁) (Oₛ₂:=Oₛ₂) (Oₘ₁:=Oₘ₁) V₁ V₂).toVerifier
      = Verifier.append V₁.toVerifier V₂.toVerifier := by
  unfold OracleVerifier.toVerifier Verifier.append
  congr 1
  funext stmtOStmt tr
  obtain ⟨stmt, oStmt⟩ := stmtOStmt
  simp only [OracleVerifier.append, OracleVerifier.Append.verify]
  -- Step 1: push outer simulateQ through the inner OptionT bind.
  rw [simulateQ_optionT_bind]
  -- Step 2: fuse each stage's two simulateQ via simulateQ_compose, then collapse the routers.
  -- Helper closures (work under binders via simp only).
  have hC1 : ∀ (x : OptionT (OracleComp _) Stmt₂),
      simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
          (simulateQ OracleVerifier.Append.router₁ x)
        = simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.fst.messages) x := by
    intro x
    rw [← QueryImpl.simulateQ_compose, OracleVerifier.Append.router1_collapse]
  have hC2 : ∀ (x : OptionT (OracleComp _) Stmt₃),
      simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
          (simulateQ (OracleVerifier.Append.router₂ V₁) x)
        = simulateQ (OracleInterface.simOracle2 oSpec
            (OracleVerifier.mkVerifierOStmtOut V₁.embed V₁.hEq oStmt tr.fst) tr.snd.messages) x := by
    intro x
    rw [← QueryImpl.simulateQ_compose, OracleVerifier.Append.router2_collapse]
  simp only [hC1, hC2]
  -- Step 3: fix the challenge arguments.
  have hch1 : (fun chal => id ((by simpa [ChallengeIdx.inl, ProtocolSpec.append]
        using rfl : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl chal) = pSpec₁.Challenge chal).mp
        (tr.challenges (ChallengeIdx.inl chal)))) = tr.fst.challenges := by
    funext chal
    simp only [id]
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) ?_
    exact (OracleVerifier.Append.challenges_fst_heq tr chal).symm
  have hch2 : (fun chal => id ((by simpa [ChallengeIdx.inr, ProtocolSpec.append]
        using rfl : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr chal) = pSpec₂.Challenge chal).mp
        (tr.challenges (ChallengeIdx.inr chal)))) = tr.snd.challenges := by
    funext chal
    simp only [id]
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) ?_
    exact (OracleVerifier.Append.challenges_snd_heq tr chal).symm
  rw [hch1]
  simp only [hch2]
  -- Step 4: normalize the monadic structure on both sides.
  simp only [bind_assoc, pure_bind, bind_pure]
  -- Step 5: peel the V₁ bind (syntactically identical on both sides).
  refine bind_congr (fun x => ?_)
  -- Step 6: peel the V₂ bind (oracle-stmt args are defeq: mkVerifierOStmtOut = unfolded match).
  refine bind_congr (fun stmtOut => ?_)
  -- Step 7: output routing equality.
  refine congrArg pure ?_
  rw [Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  funext i
  exact mkVerifierOStmtOut_append V₁ V₂ oStmt tr i


/-- **The append-to-reduction residual is discharged for every pair of oracle reductions.** This is
the single named bridge consumed by `OracleReduction.append_perfectCompleteness_msg_proof`; with it
proven, that keystone gives unconditional message-seam append perfect completeness. -/
theorem appendToReductionResidual_proof
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
    appendToReductionResidual (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁ R₂ :=
  (appendToReductionResidual_iff_verifier R₁ R₂).mpr
    (oracleVerifier_append_toVerifier R₁.verifier R₂.verifier)

variable [oSpec.Fintype] [oSpec.Inhabited]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Oracle-level append perfect completeness — UNCONDITIONAL (message seam).** Perfect
completeness of `R₁.append R₂` from the two component perfect-completenesses and the message-seam
direction/`NeverFail`/support facts, with the residual bridge now discharged internally
(`appendToReductionResidual_proof`). This is the keystone consumers (#29/#114/#62/#13) need:
no `appendToReductionResidual`/`hBridge` hypothesis remains. -/
theorem append_perfectCompleteness_keystone
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ :=
  append_perfectCompleteness_msg_proof R₁ R₂ h₁ h₂ hn hDir hDir₂ hInit hImplSupp
    (appendToReductionResidual_proof R₁ R₂)

end OracleReduction
