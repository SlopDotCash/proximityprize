/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.ChallengeSeamBridge
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompleteness
import ArkLib.OracleReduction.Composition.Sequential.AppendCompletenessHelper

/-!
# Perfect completeness of sequential composition at a message seam

This module owns the completed `Reduction.append_perfectCompleteness_msg_proof` theorem.
Compatibility names in `AppendPerfectCompletenessMsg` delegate here.

The native support criterion observes every optional run result. Support-faithful simulation
transfers each component's original completeness hypothesis to this criterion. Canonical
`Reduction.run_run_eq_bind` exposes the prover/verifier boundary; `Prover.append_run_msg` pins
left and right challenge inclusions. Component `none` results contradict their respective
completeness hypotheses, while present values yield the output relation and statement agreement.
-/

open OracleComp OracleSpec ProtocolSpec
-- Preserve the finite uniform semantics of this completed composition theorem locally.
private noncomputable local instance (priority := low) appendProofUniformAnswers
    {κ : Type} {spec : OracleSpec κ}
    [∀ q, Fintype (spec.Range q)] [∀ q, Inhabited (spec.Range q)] :
    OracleSpec.UniformAnswerMeasure spec :=
  OracleSpec.UniformAnswerMeasure.ofFiniteNonempty spec

namespace Reduction
variable {ι : Type} {oSpec : OracleSpec ι} [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

open SubSpec in
instance instLawfulChalSub' {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} :
    [pSpec₁.Challenge]ₒ ˡ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ :=
  lawfulSubSpec_challenge_append_left

open SubSpec in
instance instLawfulChalSubR' {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} :
    [pSpec₂.Challenge]ₒ ˡ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ :=
  lawfulSubSpec_challenge_append_right

theorem mem_support_optionT_lift {ι : Type} {S : OracleSpec ι} {α : Type}
    {Y : OracleComp S α} {y : α}
    (hP : some y ∈ support (liftM Y : OracleComp S (Option α))) : y ∈ support Y := by
  have hy : y ∈ support (liftM Y : OptionT (OracleComp S) α) :=
    (MonadAttach.OptionT.canReturn_iff).2 hP
  simpa only [OptionT.support_liftM] using hy

theorem mem_support_liftM_oc {ι τ : Type} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
    [spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec] {α : Type} {mx : OracleComp spec α} {y : α}
    (hP : y ∈ support (liftM mx : OracleComp superSpec α)) : y ∈ support mx := by
  change y ∈ support (OracleComp.liftComp mx superSpec) at hP
  rwa [mem_support_liftComp_iff] at hP

theorem none_not_mem_optionT_lift {ι : Type} {S : OracleSpec ι} {α : Type} (Y : OracleComp S α) :
    none ∉ support (liftM Y : OracleComp S (Option α)) := by
  intro hnone
  simp only [monadLift_self] at hnone
  obtain ⟨a, _, ha⟩ := OracleComp.mem_support_bind_peel _ _ hnone
  have heq := OracleComp.eq_of_mem_support_pure _ ha
  cases heq

section NoneRecon
variable {StmtIn WitIn StmtOut WitOut : Type} {N : ℕ} {pSpec : ProtocolSpec N}
theorem none_mem_support_run_of_prover_verifier
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (tr : FullTranscript pSpec) (prv : StmtOut × WitOut)
    (hP : (tr, prv) ∈ support (R.prover.run stmt wit))
    (hV : none ∈ support (OptionT.run (R.verifier.run stmt tr))) :
    none ∈ support (OptionT.run (R.run stmt wit)) := by
  rw [Reduction.run_run_eq_bind, mem_support_bind_iff]
  refine ⟨(tr, prv), hP, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨none, ?_, ?_⟩
  · simpa only [OracleComp.support_liftComp] using hV
  · simp only [Option.map_none, support_pure, Set.mem_singleton_iff]


end NoneRecon

private theorem support_liftLeft {α : Type}
    (mx : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α) :
    support (liftAppendLeft pSpec₂ mx) = support mx := by
  letI : [pSpec₁.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ :=
    subSpec_challenge_append_left
  change support (liftComp mx (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) = _
  exact OracleComp.support_liftComp mx

private theorem support_liftRight {α : Type}
    (mx : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α) :
    support (liftAppendRight pSpec₁ mx) = support mx := by
  letI : [pSpec₂.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ :=
    subSpec_challenge_append_right
  change support (liftComp mx (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) = _
  exact OracleComp.support_liftComp mx

private theorem support_complete_of_faithful
    {A B C D : Type} {N : ℕ} {p : ProtocolSpec N}
    [∀ i, SampleableType (p.Challenge i)]
    [(oSpec + [p.Challenge]ₒ).UniformAnswerMeasure]
    (R : Reduction oSpec A B C D p) (relA : Set (A × B)) (relB : Set (C × D))
    (hR : R.perfectCompleteness init impl relA relB) (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) =
        support (liftM q : OracleComp oSpec β))
    (stmt : A) (wit : B) (hIn : (stmt, wit) ∈ relA)
    (value : Option ((p.FullTranscript × C × D) × C))
    (hvalue : value ∈ support (R.run stmt wit).run) :
    ∃ result, value = some result ∧ (result.2, result.1.2.2) ∈ relB ∧
      result.1.2.1 = result.2 := by
  rw [perfectCompleteness_eq_prob_one] at hR
  have hp := (OptionT.prEvent_mk_eq_one_iff _ _).1 (hR stmt wit hIn)
  have hs := support_bind_simulateQ_run'_eq init
    (impl.addLift (challengeQueryImpl (pSpec := p))) (R.run stmt wit).run hInit
    (Prover.addLift_challenge_support_faithful impl hImplSupp)
  exact hp value ((congrArg (fun S => value ∈ S) hs).mpr hvalue)

/-- Support-level composition engine shared by message and empty seams. -/
theorem append_perfectCompleteness_of_run_factorization
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hRun : ∀ stmt wit, (R₁.prover.append R₂.prover).run stmt wit = (do
      let ⟨tr₁, s₂, w₂⟩ ← liftAppendLeft pSpec₂ (R₁.prover.run stmt wit)
      let ⟨tr₂, s₃, w₃⟩ ← liftAppendRight pSpec₁ (R₂.prover.run s₂ w₂)
      pure (tr₁ ++ₜ tr₂, s₃, w₃)))
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftM q : OracleComp oSpec β))
    [∀ q, Fintype ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range q)]
    [∀ q, Inhabited ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range q)]
    [∀ q, Fintype ((oSpec + [pSpec₁.Challenge]ₒ).Range q)] [∀ q, Inhabited ((oSpec + [pSpec₁.Challenge]ₒ).Range q)]
    [∀ q, Fintype ((oSpec + [pSpec₂.Challenge]ₒ).Range q)] [∀ q, Inhabited ((oSpec + [pSpec₂.Challenge]ₒ).Range q)] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt wit hIn value hvalue
  have hgood₁ := support_complete_of_faithful R₁ rel₁ rel₂ h₁ hInit hImplSupp stmt wit hIn
  rw [Reduction.run_run_eq_bind, Reduction.append] at hvalue
  simp only [hRun stmt wit, bind_assoc, pure_bind] at hvalue
  obtain ⟨⟨tr₁, s₂, w₂⟩, hP₁, hvalue⟩ := OracleComp.mem_support_bind_peel _ _ hvalue
  obtain ⟨⟨tr₂, s₃, w₃⟩, hP₂, hvalue⟩ := OracleComp.mem_support_bind_peel _ _ hvalue
  have hP₁' : (tr₁, s₂, w₂) ∈ support (R₁.prover.run stmt wit) := by
    simpa only [support_liftLeft] using hP₁
  have hP₂' : (tr₂, s₃, w₃) ∈ support (R₂.prover.run s₂ w₂) := by
    simpa only [support_liftRight] using hP₂
  simp only [Verifier.append_run, FullTranscript.append_fst, FullTranscript.append_snd,
    OptionT.run_bind, Option.elimM, liftComp_bind, liftComp_pure, bind_assoc,
    pure_bind] at hvalue
  obtain ⟨v₁, hV₁, hvalue⟩ := OracleComp.mem_support_bind_peel _ _ hvalue
  have hV₁' : v₁ ∈ support (R₁.verifier.run stmt tr₁).run := by
    simpa only [OracleComp.support_liftComp] using hV₁
  cases v₁ with
  | none =>
    obtain ⟨r, hr, _, _⟩ := hgood₁ none
      (none_mem_support_run_of_prover_verifier R₁ stmt wit tr₁ (s₂, w₂) hP₁' hV₁')
    cases hr
  | some vs₂ =>
    obtain ⟨r₁, hr₁, hRel₂, hEq₂⟩ := hgood₁ (some ((tr₁, s₂, w₂), vs₂))
      (mem_support_run_of_prover_verifier R₁ stmt wit tr₁ (s₂, w₂) vs₂ hP₁' hV₁')
    cases Option.some.inj hr₁
    change s₂ = vs₂ at hEq₂
    subst vs₂
    have hgood₂ := support_complete_of_faithful R₂ rel₂ rel₃ h₂ hInit hImplSupp s₂ w₂ hRel₂
    obtain ⟨v₂, hV₂, hvalue⟩ := OracleComp.mem_support_bind_peel _ _ hvalue
    have hV₂' : v₂ ∈ support (R₂.verifier.run s₂ tr₂).run := by
      simpa only [OracleComp.support_liftComp, Option.elim_some] using hV₂
    cases v₂ with
    | none =>
      obtain ⟨r, hr, _, _⟩ := hgood₂ none
        (none_mem_support_run_of_prover_verifier R₂ s₂ w₂ tr₂ (s₃, w₃) hP₂' hV₂')
      cases hr
    | some vs₃ =>
      obtain ⟨r₂, hr₂, hRel₃, hEq₃⟩ := hgood₂ (some ((tr₂, s₃, w₃), vs₃))
        (mem_support_run_of_prover_verifier R₂ s₂ w₂ tr₂ (s₃, w₃) vs₃ hP₂' hV₂')
      cases Option.some.inj hr₂
      have hv := OracleComp.eq_of_mem_support_pure _ hvalue
      subst value
      exact ⟨_, rfl, hRel₃, hEq₃⟩


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
    [∀ q, Fintype ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range q)]
    [∀ q, Inhabited ((oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Range q)]
    [∀ q, Fintype ((oSpec + [pSpec₁.Challenge]ₒ).Range q)] [∀ q, Inhabited ((oSpec + [pSpec₁.Challenge]ₒ).Range q)]
    [∀ q, Fintype ((oSpec + [pSpec₂.Challenge]ₒ).Range q)] [∀ q, Inhabited ((oSpec + [pSpec₂.Challenge]ₒ).Range q)] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  exact append_perfectCompleteness_of_run_factorization R₁ R₂ h₁ h₂
    (fun stmt wit => Prover.append_run_msg stmt wit hn hDir hDir₂) hInit hImplSupp



end Reduction
#print axioms Reduction.append_perfectCompleteness_msg_proof

#print axioms Reduction.append_perfectCompleteness_of_run_factorization
