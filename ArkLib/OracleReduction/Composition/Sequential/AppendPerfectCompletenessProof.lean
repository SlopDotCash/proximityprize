/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.ChallengeSeamBridge
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompleteness
import ArkLib.OracleReduction.Composition.Sequential.AppendCompletenessHelper

/-!
# Perfect completeness of sequential composition (message seam) — discharged

This file proves `Reduction.append_perfectCompleteness_msg_proof`, the genuine perfect-completeness
theorem for `Reduction.append` at a message seam, discharging the residual that
`AppendPerfectCompleteness.lean` records as a `def : Prop`. It is the completeness half of the
sequential-composition keystone (#433), built on the proven prover-side run factoring
(`Prover.append_run_msg`) and the challenge-oracle seam bridge / support-faithfulness gate from
`ChallengeSeamBridge.lean`.

The proof is the support-decomposition route (no monad commutation): `probEvent_eq_one_iff` splits
into a no-failure obligation and an `∀ x ∈ support, good x` obligation; the support-faithfulness gate
(`Prover.addLift_challenge_support_faithful`) collapses the `simulateQ`/`StateT`/`init` layers to
OracleComp-level `support (run)`; the run factors (`append_run_msg` + `Verifier.append_run`); and the
per-phase hypotheses `h₁`/`h₂` (reduced the same way) close both obligations via the
prover/verifier support reconstruction helpers.

Supporting (all axiom-clean): `LawfulSubSpec` instances for the left/right challenge subspecs (their
`onResponse` is the bijective `range_challenge_append_*` cast), lift-unwrap helpers, and
`none_mem_support_run_of_prover_verifier` (the failure-side analogue of
`mem_support_run_of_prover_verifier`).
-/

open OracleComp OracleSpec ProtocolSpec
namespace Reduction
variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
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
  change some y ∈ support ((fun a => some a) <$> Y) at hP
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
  change none ∉ support ((fun a => some a) <$> Y)
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
  · show some (tr, prv) ∈ support (some <$> R.prover.run stmt wit)
    simp only [support_map, Set.mem_image, Option.some.injEq]; exact ⟨_, hP, rfl⟩
  · simp only [Option.elim_some, mem_support_bind_iff]
    refine ⟨some none, ?_, ?_⟩
    · rw [OptionT.run_liftM_run, support_map,
        support_simulateQ_eq_OracleComp_of_superSpec _ _ (fun _ => rfl)]
      simp only [Set.mem_image, Option.some.injEq]; exact ⟨none, hV, rfl⟩
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
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  rw [perfectCompleteness_eq_prob_one]
  intro stmt wit hmem
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- NeverFails
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    intro hmem0
    rw [mem_support_bind_iff] at hmem0
    obtain ⟨s0, hs0, hmem0⟩ := hmem0
    rw [support_simulateQ_run'_eq (impl.addLift challengeQueryImpl) _ s0
        (Prover.addLift_challenge_support_faithful impl hImplSupp)] at hmem0
    have h₁' : ∀ y ∈ support (OptionT.mk (R₁.run stmt wit)),
        (y.2, y.1.2.2) ∈ rel₂ ∧ y.1.2.1 = y.2 := by
      rw [perfectCompleteness_eq_prob_one] at h₁
      have hh := h₁ stmt wit hmem; rw [probEvent_eq_one_iff] at hh
      obtain ⟨_, hsupp⟩ := hh
      intro y hy; have hy2 := hsupp y
      rw [support_bind_simulateQ_run'_eq_mk init (impl.addLift challengeQueryImpl) _ hInit
            (Prover.addLift_challenge_support_faithful impl hImplSupp)] at hy2
      exact hy2 hy
    have h₁nf : none ∉ support (OptionT.run (R₁.run stmt wit)) := by
      rw [perfectCompleteness_eq_prob_one] at h₁
      have hh := h₁ stmt wit hmem; rw [probEvent_eq_one_iff] at hh
      obtain ⟨hnf, _⟩ := hh
      rw [OptionT.probFailure_eq, OptionT.run_mk] at hnf
      simp only [probFailure_eq_zero, zero_add, probOutput_eq_zero_iff] at hnf
      intro hc; apply hnf; rw [mem_support_bind_iff]
      obtain ⟨s1, hs1⟩ := support_nonempty_of_neverFails init hInit
      exact ⟨s1, hs1, by rwa [support_simulateQ_run'_eq (impl.addLift challengeQueryImpl) _ s1
        (Prover.addLift_challenge_support_faithful impl hImplSupp)]⟩
    have h₂nf : ∀ s₂ w₂, (s₂, w₂) ∈ rel₂ → none ∉ support (OptionT.run (R₂.run s₂ w₂)) := by
      intro s₂ w₂ hm2
      rw [perfectCompleteness_eq_prob_one] at h₂
      have hh := h₂ s₂ w₂ hm2; rw [probEvent_eq_one_iff] at hh
      obtain ⟨hnf, _⟩ := hh
      rw [OptionT.probFailure_eq, OptionT.run_mk] at hnf
      simp only [probFailure_eq_zero, zero_add, probOutput_eq_zero_iff] at hnf
      intro hc; apply hnf; rw [mem_support_bind_iff]
      obtain ⟨s1, hs1⟩ := support_nonempty_of_neverFails init hInit
      exact ⟨s1, hs1, by rwa [support_simulateQ_run'_eq (impl.addLift challengeQueryImpl) _ s1
        (Prover.addLift_challenge_support_faithful impl hImplSupp)]⟩
    rw [Reduction.run, Reduction.append] at hmem0
    simp only [Prover.append_run_msg _ _ hn hDir hDir₂, Verifier.append_run,
      OptionT.run_bind, Option.elimM, bind_assoc, liftM_bind] at hmem0
    obtain ⟨a₁, hP₁, hmem0⟩ := (mem_support_bind_iff _ _ _).mp hmem0
    rcases a₁ with _ | ⟨tr₁, s₂, w₂⟩
    · exact absurd hP₁ (none_not_mem_optionT_lift _)
    obtain ⟨a₂, hP₂, hmem0⟩ := (mem_support_bind_iff _ _ _).mp hmem0
    rcases a₂ with _ | ⟨tr₂, s₃, w₃⟩
    · exact absurd hP₂ (none_not_mem_optionT_lift _)
    obtain ⟨a₃, hpr, hmem0⟩ := (mem_support_bind_iff _ _ _).mp hmem0
    rcases a₃ with _ | pr
    · exact absurd hpr (none_not_mem_optionT_lift _)
    change some pr ∈ support (pure (some (tr₁ ++ₜ tr₂, s₃, w₃))
      : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option _)) at hpr
    simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hpr
    subst hpr
    obtain ⟨a₄, hV₁, hmem0⟩ := (mem_support_bind_iff _ _ _).mp hmem0
    simp only [FullTranscript.append_fst] at hV₁
    rcases a₄ with _ | vo₁
    · change none ∈ support (OracleComp.liftComp ((fun a => some a) <$>
        ((Verifier.run stmt tr₁ R₁.verifier).run)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₁
      simp [mem_support_liftComp_iff, support_map] at hV₁
    have hP₁' : (tr₁, s₂, w₂) ∈ support (R₁.prover.run stmt wit) := by
      change some (tr₁, s₂, w₂) ∈ support ((fun a => some a) <$> (liftM (Prover.run stmt wit R₁.prover)
        : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) at hP₁
      rw [support_map, Set.mem_image] at hP₁
      obtain ⟨z, hz, hzy⟩ := hP₁; rw [Option.some.injEq] at hzy; subst hzy
      rwa [← liftComp_eq_liftM, mem_support_liftComp_iff] at hz
    rcases vo₁ with _ | vs₂
    · exact absurd (none_mem_support_run_of_prover_verifier R₁ stmt wit tr₁ (s₂, w₂) hP₁'
        (by change some none ∈ support (OracleComp.liftComp ((fun a => some a) <$>
              ((Verifier.run stmt tr₁ R₁.verifier).run)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₁
            rw [mem_support_liftComp_iff, support_map, Set.mem_image] at hV₁
            obtain ⟨z, hz, hzy⟩ := hV₁; rw [Option.some.injEq] at hzy; subst hzy; exact hz)) h₁nf
    have hP₂' : (tr₂, s₃, w₃) ∈ support (R₂.prover.run s₂ w₂) := by
      change some (tr₂, s₃, w₃) ∈ support ((fun a => some a) <$> (liftM (Prover.run s₂ w₂ R₂.prover)
        : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) at hP₂
      rw [support_map, Set.mem_image] at hP₂
      obtain ⟨z, hz, hzy⟩ := hP₂; rw [Option.some.injEq] at hzy; subst hzy
      rwa [← liftComp_eq_liftM, mem_support_liftComp_iff] at hz
    have hV₁' : some vs₂ ∈ support (R₁.verifier.run stmt tr₁).run := by
      change some (some vs₂) ∈ support (OracleComp.liftComp ((fun a => some a) <$>
        ((Verifier.run stmt tr₁ R₁.verifier).run)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₁
      rw [mem_support_liftComp_iff, support_map, Set.mem_image] at hV₁
      obtain ⟨z, hz, hzy⟩ := hV₁; rw [Option.some.injEq] at hzy; subst hzy; exact hz
    obtain ⟨hrel₂, hvs₂⟩ := h₁' ((tr₁, s₂, w₂), vs₂)
      (by rw [OptionT.mem_support_iff]
          exact mem_support_run_of_prover_verifier R₁ stmt wit tr₁ (s₂, w₂) vs₂ hP₁' hV₁')
    simp only at hrel₂ hvs₂; subst hvs₂
    simp only [Option.elim_some, liftM_bind, bind_assoc] at hmem0
    obtain ⟨a₅, hV₂, hmem0⟩ := (mem_support_bind_iff _ _ _).mp hmem0
    simp only [FullTranscript.append_snd] at hV₂
    rcases a₅ with _ | vo₂
    · change none ∈ support (OracleComp.liftComp ((fun a => some a) <$>
        ((Verifier.run s₂ tr₂ R₂.verifier).run)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₂
      simp [mem_support_liftComp_iff, support_map] at hV₂
    rcases vo₂ with _ | vs₃
    · exact absurd (none_mem_support_run_of_prover_verifier R₂ s₂ w₂ tr₂ (s₃, w₃) hP₂'
        (by change some none ∈ support (OracleComp.liftComp ((fun a => some a) <$>
              ((Verifier.run s₂ tr₂ R₂.verifier).run)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₂
            rw [mem_support_liftComp_iff, support_map, Set.mem_image] at hV₂
            obtain ⟨z, hz, hzy⟩ := hV₂; rw [Option.some.injEq] at hzy; subst hzy; exact hz))
        (h₂nf s₂ w₂ hrel₂)
    simp only [Option.elim_some, Option.getM_some, pure_bind] at hmem0
    change none ∈ support (pure (some ((tr₁ ++ₜ tr₂, s₃, w₃), vs₃)) : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option _)) at hmem0
    simp at hmem0
  · intro x hx
    have h₁' : ∀ y ∈ support (OptionT.mk (R₁.run stmt wit)),
        (y.2, y.1.2.2) ∈ rel₂ ∧ y.1.2.1 = y.2 := by
      rw [perfectCompleteness_eq_prob_one] at h₁
      have hh := h₁ stmt wit hmem
      rw [probEvent_eq_one_iff] at hh
      obtain ⟨_, hsupp⟩ := hh
      intro y hy
      have hy2 := hsupp y
      rw [support_bind_simulateQ_run'_eq_mk init (impl.addLift challengeQueryImpl) _ hInit
            (Prover.addLift_challenge_support_faithful impl hImplSupp)] at hy2
      exact hy2 hy
    have h₂' : ∀ s₂ w₂, (s₂, w₂) ∈ rel₂ → ∀ y ∈ support (OptionT.mk (R₂.run s₂ w₂)),
        (y.2, y.1.2.2) ∈ rel₃ ∧ y.1.2.1 = y.2 := by
      intro s₂ w₂ hmem₂
      rw [perfectCompleteness_eq_prob_one] at h₂
      have hh := h₂ s₂ w₂ hmem₂
      rw [probEvent_eq_one_iff] at hh
      obtain ⟨_, hsupp⟩ := hh
      intro y hy
      have hy2 := hsupp y
      rw [support_bind_simulateQ_run'_eq_mk init (impl.addLift challengeQueryImpl) _ hInit
            (Prover.addLift_challenge_support_faithful impl hImplSupp)] at hy2
      exact hy2 hy
    rw [support_bind_simulateQ_run'_eq_mk init (impl.addLift challengeQueryImpl) _ hInit
          (Prover.addLift_challenge_support_faithful impl hImplSupp)] at hx
    show (x.2, x.1.2.2) ∈ rel₃ ∧ x.1.2.1 = x.2
    rw [OptionT.mem_support_iff, OptionT.run_mk, Reduction.run, Reduction.append] at hx
    simp only [Prover.append_run_msg _ _ hn hDir hDir₂, Verifier.append_run,
      OptionT.run_bind, Option.elimM, bind_assoc, liftM_bind] at hx
    obtain ⟨a₁, hP₁, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
    rcases a₁ with _ | ⟨tr₁, s₂, w₂⟩
    · simp at hx
    obtain ⟨a₂, hP₂, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
    rcases a₂ with _ | ⟨tr₂, s₃, w₃⟩
    · simp at hx
    obtain ⟨a₃, hpr, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
    rcases a₃ with _ | pr
    · simp at hx
    change some pr ∈ support (pure (some (tr₁ ++ₜ tr₂, s₃, w₃))
      : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option _)) at hpr
    simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hpr
    subst hpr
    obtain ⟨a₄, hV₁, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
    rcases a₄ with _ | vo₁
    · simp at hx
    rcases vo₁ with _ | vs₂
    · simp at hx
    simp only [Option.elim_some, liftM_bind, bind_assoc] at hx
    obtain ⟨a₅, hV₂, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
    rcases a₅ with _ | vo₂
    · simp at hx
    rcases vo₂ with _ | vs₃
    · simp at hx
    simp only [Option.elim_some, Option.getM_some, pure_bind] at hx
    change some x ∈ support (pure (some ((tr₁ ++ₜ tr₂, s₃, w₃), vs₃))
      : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option _)) at hx
    simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hx
    subst hx
    simp only [FullTranscript.append_fst, FullTranscript.append_snd] at hV₁ hV₂
    have hP₁' : (tr₁, s₂, w₂) ∈ support (R₁.prover.run stmt wit) := by
      change some (tr₁, s₂, w₂) ∈ support ((fun a => some a) <$> (liftM (Prover.run stmt wit R₁.prover)
        : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) at hP₁
      rw [support_map, Set.mem_image] at hP₁
      obtain ⟨z, hz, hzy⟩ := hP₁; rw [Option.some.injEq] at hzy; subst hzy
      rwa [← liftComp_eq_liftM, mem_support_liftComp_iff] at hz
    have hP₂' : (tr₂, s₃, w₃) ∈ support (R₂.prover.run s₂ w₂) := by
      change some (tr₂, s₃, w₃) ∈ support ((fun a => some a) <$> (liftM (Prover.run s₂ w₂ R₂.prover)
        : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) at hP₂
      rw [support_map, Set.mem_image] at hP₂
      obtain ⟨z, hz, hzy⟩ := hP₂; rw [Option.some.injEq] at hzy; subst hzy
      rwa [← liftComp_eq_liftM, mem_support_liftComp_iff] at hz
    have hV₁' : some vs₂ ∈ support (R₁.verifier.run stmt tr₁).run := by
      change some (some vs₂) ∈ support (OracleComp.liftComp ((fun a => some a) <$>
        ((Verifier.run stmt tr₁ R₁.verifier).run))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₁
      rw [mem_support_liftComp_iff, support_map, Set.mem_image] at hV₁
      obtain ⟨z, hz, hzy⟩ := hV₁; rw [Option.some.injEq] at hzy; subst hzy; exact hz
    have hV₂' : some vs₃ ∈ support (R₂.verifier.run vs₂ tr₂).run := by
      change some (some vs₃) ∈ support (OracleComp.liftComp ((fun a => some a) <$>
        ((Verifier.run vs₂ tr₂ R₂.verifier).run))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₂
      rw [mem_support_liftComp_iff, support_map, Set.mem_image] at hV₂
      obtain ⟨z, hz, hzy⟩ := hV₂; rw [Option.some.injEq] at hzy; subst hzy; exact hz
    obtain ⟨hrel₂, hvs₂⟩ := h₁' ((tr₁, s₂, w₂), vs₂)
      (by rw [OptionT.mem_support_iff]
          exact mem_support_run_of_prover_verifier R₁ stmt wit tr₁ (s₂, w₂) vs₂ hP₁' hV₁')
    simp only at hrel₂ hvs₂
    subst hvs₂
    obtain ⟨hrel₃, hvs₃⟩ := h₂' s₂ w₂ hrel₂ ((tr₂, s₃, w₃), vs₃)
      (by rw [OptionT.mem_support_iff]
          exact mem_support_run_of_prover_verifier R₂ s₂ w₂ tr₂ (s₃, w₃) vs₃ hP₂' hV₂')
    simp only at hrel₃ hvs₃ ⊢
    exact ⟨hrel₃, hvs₃⟩


end Reduction
#print axioms Reduction.append_perfectCompleteness_msg_proof
