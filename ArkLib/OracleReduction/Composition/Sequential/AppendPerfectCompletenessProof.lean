/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.ChallengeSeamBridge
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompleteness
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessMsg
import ArkLib.OracleReduction.Composition.Sequential.AppendCompletenessHelper

/-!
# Perfect completeness of sequential composition (message seam) — discharged

`Reduction.append_perfectCompleteness_msg_proof` preserves the public message-seam interface
and delegates to `Reduction.append_perfectCompleteness_message`. Both require perfect
completeness of each phase, a nonempty message-first right phase, never-failing initialization,
and support-faithful oracle execution. Reusing the established theorem avoids maintaining
a second copy of the support and probability proof.

Supporting (all axiom-clean): `LawfulSubSpec` instances for the left/right challenge subspecs (their
`onResponse` is the bijective `range_challenge_append_*` cast), lift-unwrap helpers, and
`none_mem_support_run_of_prover_verifier` (the failure-side analogue of
`mem_support_run_of_prover_verifier`).
-/

open OracleComp OracleSpec ProtocolSpec
namespace Reduction
variable {ι : Type} {oSpec : OracleSpec ι} [∀ t, Fintype ((oSpec).Range t)] [∀ t, Inhabited ((oSpec).Range t)]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

open SubSpec in
instance instLawfulChalSub' {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} :
    [pSpec₁.Challenge]ₒ ˡ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ where
  onResponse_bijective t := by
    have h : (inferInstance : [pSpec₁.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).onResponse t
        = fun r => (by
            show ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range ⟨ChallengeIdx.inl t.1, ()⟩
              = ([pSpec₁.Challenge]ₒ).Range ⟨t.1, ()⟩
            show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl t.1) = pSpec₁.Challenge t.1
            simp [ChallengeIdx.inl, ProtocolSpec.append]) ▸ r := rfl
    rw [h]; exact (Equiv.cast _).bijective

open SubSpec in
instance instLawfulChalSubR' {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} :
    [pSpec₂.Challenge]ₒ ˡ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ where
  onResponse_bijective t := by
    have h : (inferInstance : [pSpec₂.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).onResponse t
        = fun r => (by
            show ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range ⟨ChallengeIdx.inr t.1, ()⟩
              = ([pSpec₂.Challenge]ₒ).Range ⟨t.1, ()⟩
            show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr t.1) = pSpec₂.Challenge t.1
            simp [ChallengeIdx.inr, ProtocolSpec.append]) ▸ r := rfl
    rw [h]; exact (Equiv.cast _).bijective

theorem mem_support_optionT_lift {ι : Type} {S : OracleSpec ι} {α : Type}
    {Y : OracleComp S α} {y : α}
    (hP : some y ∈ support (liftM Y : OracleComp S (Option α))) : y ∈ support Y := by
  simp only [monadLift_self, ← map_eq_pure_bind] at hP
  rw [support_map, Set.mem_image] at hP
  obtain ⟨z, hz, hzy⟩ := hP
  rw [Option.some.injEq] at hzy
  exact hzy ▸ hz

theorem mem_support_liftM_oc {ι τ : Type} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
    [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec] {α : Type} {mx : OracleComp spec α} {y : α}
    (hP : y ∈ support (liftM mx : OracleComp superSpec α)) : y ∈ support mx := by
  change y ∈ support (OracleComp.liftComp mx superSpec) at hP
  rwa [mem_support_liftComp_iff] at hP

theorem none_not_mem_optionT_lift {ι : Type} {S : OracleSpec ι} {α : Type} (Y : OracleComp S α) :
    none ∉ support (liftM Y : OracleComp S (Option α)) := by
  simp only [monadLift_self, ← map_eq_pure_bind]
  simp [support_map]

section NoneRecon
variable {StmtIn WitIn StmtOut WitOut : Type} {N : ℕ} {pSpec : ProtocolSpec N}
theorem none_mem_support_run_of_prover_verifier
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (tr : FullTranscript pSpec) (prv : StmtOut × WitOut)
    (hP : (tr, prv) ∈ support (R.prover.run stmt wit))
    (hV : none ∈ support (OptionT.run (R.verifier.run stmt tr))) :
    none ∈ support (OptionT.run (R.run stmt wit)) := by
  unfold Reduction.run
  simp only [OptionT.run_bind, Option.elimM, bind_assoc, mem_support_bind_iff]
  refine ⟨some (tr, prv), ?_, ?_⟩
  · apply (OptionT.mem_support_iff _ _).mp
    simpa only [OptionT.support_liftM] using hP
  · simp only [Option.elim_some, mem_support_bind_iff]
    refine ⟨some none, ?_, ?_⟩
    · rw [OptionT.run_liftM_run, support_map]
      rw [support_simulateQ_eq_OracleComp_of_superSpec
        (spec := oSpec + [pSpec.Challenge]ₒ) (superSpec := oSpec)
        (fun t => liftM (oSpec.query t)) _ (by
          intro β q
          simp only [QueryImpl.mapQuery, support_map, OracleComp.support_liftM]
          rw [← OracleComp.liftComp_liftM_query (oSpec + [pSpec.Challenge]ₒ),
            OracleComp.support_liftComp, OracleComp.support_liftM]
          simp)]
      exact Set.mem_image_of_mem some hV
    · simp [Option.getM]

end NoneRecon

theorem append_perfectCompleteness_msg_proof
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftM q : OracleComp oSpec β))
    [∀ t, Fintype (((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)).Range t)]
    [∀ t, Inhabited (((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)).Range t)]
    [∀ t, Fintype (((oSpec + [pSpec₁.Challenge]ₒ)).Range t)] [∀ t, Inhabited (((oSpec + [pSpec₁.Challenge]ₒ)).Range t)]
    [∀ t, Fintype (((oSpec + [pSpec₂.Challenge]ₒ)).Range t)] [∀ t, Inhabited (((oSpec + [pSpec₂.Challenge]ₒ)).Range t)] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  exact append_perfectCompleteness_message R₁ R₂ h₁ h₂ hn hDir hDir₂ hInit hImplSupp


end Reduction
#print axioms Reduction.append_perfectCompleteness_msg_proof
