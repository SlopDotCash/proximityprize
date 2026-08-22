/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessProof
import ArkLib.OracleReduction.Composition.Sequential.EmptyAppend

/-!
# Perfect completeness of sequential composition (empty trailing seam) — discharged

This file proves `Reduction.append_perfectCompleteness_empty_proof`, the `n = 0` analogue of
`Reduction.append_perfectCompleteness_msg_proof`: perfect completeness of `R₁.append R₂` when the
trailing protocol `pSpec₂` is empty (`ProtocolSpec 0`).

The proof is *verbatim* the support-decomposition route used for the message seam, with the single
substitution `Prover.append_run_msg ⟶ Prover.append_run_empty` (which is unconditional for the empty
trailing block — no seam-direction hypotheses `hn`/`hDir`/`hDir₂` are needed). Everything else — the
`probEvent_eq_one_iff` split, the support-faithfulness collapse of the `simulateQ`/`StateT`/`init`
layers, the `Verifier.append_run` decomposition, and the per-phase reconstruction via `h₁`/`h₂` — is
identical, because `append_run_empty` produces the same `P₁ ⟶ P₂ ⟶ concat-transcript` run shape as
`append_run_msg`.

This is the empty-tail case of the `hAppend` keystone consumed by
`Reduction.seqCompose_perfectCompleteness_of_append_msg` (it fires at the final induction step, where
the trailing `seqCompose` is over zero remaining components). Together with the message-seam keystone
it yields full multi-round sum-check perfect completeness.
-/

open OracleComp OracleSpec ProtocolSpec
namespace Reduction
variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

set_option maxHeartbeats 1000000 in
/-- **Perfect completeness of `Reduction.append` at an empty trailing seam (`pSpec₂ : ProtocolSpec 0`,
UNCONDITIONAL).** The `n = 0` analogue of `append_perfectCompleteness_msg_proof`. -/
theorem append_perfectCompleteness_empty_proof
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
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
    simp only [Prover.append_run_empty, Verifier.append_run,
      OptionT.run_bind, Option.elimM, bind_assoc, liftM_bind] at hmem0
    obtain ⟨a₁, hP₁, hmem0⟩ := (mem_support_bind_iff _ _ _).mp hmem0
    rcases a₁ with _ | ⟨tr₁, s₂, w₂⟩
    · exact absurd hP₁ (none_not_mem_optionT_lift _)
    obtain ⟨a₂, hP₂, hmem0⟩ := (mem_support_bind_iff _ _ _).mp hmem0
    rcases a₂ with _ | ⟨tr₂, s₃, w₃⟩
    · exact absurd hP₂ (none_not_mem_optionT_lift _)
    obtain ⟨trOpt, hTr, hmem0⟩ := (mem_support_bind_iff _ _ _).mp hmem0
    change trOpt ∈ support (pure (some (tr₁ ++ₜ tr₂, s₃, w₃)) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option _)) at hTr
    rw [support_pure, Set.mem_singleton_iff] at hTr
    subst hTr
    obtain ⟨a₄, hV₁, hmem0⟩ := (mem_support_bind_iff _ _ _).mp hmem0
    simp only [FullTranscript.append_fst] at hV₁
    rcases a₄ with _ | vo₁
    · change none ∈ support (OracleComp.liftComp ((fun a => some a) <$>
        ((Verifier.run stmt tr₁ R₁.verifier).run)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₁
      simp only [mem_support_liftComp_iff, support_map, Set.mem_image, reduceCtorEq, and_false, exists_false] at hV₁
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
      simp only [mem_support_liftComp_iff, support_map, Set.mem_image, reduceCtorEq, and_false, exists_false] at hV₂
    rcases vo₂ with _ | vs₃
    · exact absurd (none_mem_support_run_of_prover_verifier R₂ s₂ w₂ tr₂ (s₃, w₃) hP₂'
        (by change some none ∈ support (OracleComp.liftComp ((fun a => some a) <$>
              ((Verifier.run s₂ tr₂ R₂.verifier).run)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₂
            rw [mem_support_liftComp_iff, support_map, Set.mem_image] at hV₂
            obtain ⟨z, hz, hzy⟩ := hV₂; rw [Option.some.injEq] at hzy; subst hzy; exact hz))
        (h₂nf s₂ w₂ hrel₂)
    simp only [Option.elim_some, Option.getM_some, pure_bind] at hmem0
    change none ∈ support (pure (some ((tr₁ ++ₜ tr₂, s₃, w₃), vs₃)) : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option _)) at hmem0
    simp only [support_pure, Set.mem_singleton_iff, reduceCtorEq] at hmem0
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
    simp only [Prover.append_run_empty, Verifier.append_run,
      OptionT.run_bind, Option.elimM, bind_assoc, liftM_bind] at hx
    obtain ⟨a₁, hP₁, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
    rcases a₁ with _ | ⟨tr₁, s₂, w₂⟩
    · exact absurd hP₁ (none_not_mem_optionT_lift _)
    obtain ⟨a₂, hP₂, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
    rcases a₂ with _ | ⟨tr₂, s₃, w₃⟩
    · exact absurd hP₂ (none_not_mem_optionT_lift _)
    obtain ⟨trOpt, hTr, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
    change trOpt ∈ support (pure (some (tr₁ ++ₜ tr₂, s₃, w₃)) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option _)) at hTr
    rw [support_pure, Set.mem_singleton_iff] at hTr
    subst hTr
    obtain ⟨a₄, hV₁, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
    rcases a₄ with _ | vo₁
    · simp only [FullTranscript.append_fst] at hV₁
      change none ∈ support (OracleComp.liftComp ((fun a => some a) <$>
        ((Verifier.run stmt tr₁ R₁.verifier).run)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₁
      simp only [mem_support_liftComp_iff, support_map, Set.mem_image, reduceCtorEq, and_false,
        exists_false] at hV₁
    rcases vo₁ with _ | vs₂
    · exfalso
      have hP₁'' : (tr₁, s₂, w₂) ∈ support (R₁.prover.run stmt wit) := by
        change some (tr₁, s₂, w₂) ∈ support ((fun a => some a) <$> (liftM (Prover.run stmt wit R₁.prover)
          : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) at hP₁
        rw [support_map, Set.mem_image] at hP₁
        obtain ⟨z, hz, hzy⟩ := hP₁; rw [Option.some.injEq] at hzy; subst hzy
        rwa [← liftComp_eq_liftM, mem_support_liftComp_iff] at hz
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
      refine absurd (none_mem_support_run_of_prover_verifier R₁ stmt wit tr₁ (s₂, w₂) hP₁'' ?_) h₁nf
      simp only [FullTranscript.append_fst] at hV₁
      change some none ∈ support (OracleComp.liftComp ((fun a => some a) <$>
        ((Verifier.run stmt tr₁ R₁.verifier).run)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₁
      rw [mem_support_liftComp_iff, support_map, Set.mem_image] at hV₁
      obtain ⟨z, hz, hzy⟩ := hV₁; rw [Option.some.injEq] at hzy; subst hzy; exact hz
    -- vo₁ = some vs₂: V₁ accepted; derive the phase-1 relation early so it is available below.
    simp only [FullTranscript.append_fst] at hV₁
    have hP₁' : (tr₁, s₂, w₂) ∈ support (R₁.prover.run stmt wit) := by
      change some (tr₁, s₂, w₂) ∈ support ((fun a => some a) <$> (liftM (Prover.run stmt wit R₁.prover)
        : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) at hP₁
      rw [support_map, Set.mem_image] at hP₁
      obtain ⟨z, hz, hzy⟩ := hP₁; rw [Option.some.injEq] at hzy; subst hzy
      rwa [← liftComp_eq_liftM, mem_support_liftComp_iff] at hz
    have hV₁' : some vs₂ ∈ support (R₁.verifier.run stmt tr₁).run := by
      change some (some vs₂) ∈ support (OracleComp.liftComp ((fun a => some a) <$>
        ((Verifier.run stmt tr₁ R₁.verifier).run))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₁
      rw [mem_support_liftComp_iff, support_map, Set.mem_image] at hV₁
      obtain ⟨z, hz, hzy⟩ := hV₁; rw [Option.some.injEq] at hzy; subst hzy; exact hz
    obtain ⟨hrel₂, hvs₂⟩ := h₁' ((tr₁, s₂, w₂), vs₂)
      (by rw [OptionT.mem_support_iff]
          exact mem_support_run_of_prover_verifier R₁ stmt wit tr₁ (s₂, w₂) vs₂ hP₁' hV₁')
    simp only at hrel₂ hvs₂; subst hvs₂
    have hP₂' : (tr₂, s₃, w₃) ∈ support (R₂.prover.run s₂ w₂) := by
      change some (tr₂, s₃, w₃) ∈ support ((fun a => some a) <$> (liftM (Prover.run s₂ w₂ R₂.prover)
        : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) at hP₂
      rw [support_map, Set.mem_image] at hP₂
      obtain ⟨z, hz, hzy⟩ := hP₂; rw [Option.some.injEq] at hzy; subst hzy
      rwa [← liftComp_eq_liftM, mem_support_liftComp_iff] at hz
    have h₂nf : none ∉ support (OptionT.run (R₂.run s₂ w₂)) := by
      rw [perfectCompleteness_eq_prob_one] at h₂
      have hh := h₂ s₂ w₂ hrel₂; rw [probEvent_eq_one_iff] at hh
      obtain ⟨hnf, _⟩ := hh
      rw [OptionT.probFailure_eq, OptionT.run_mk] at hnf
      simp only [probFailure_eq_zero, zero_add, probOutput_eq_zero_iff] at hnf
      intro hc; apply hnf; rw [mem_support_bind_iff]
      obtain ⟨s1, hs1⟩ := support_nonempty_of_neverFails init hInit
      exact ⟨s1, hs1, by rwa [support_simulateQ_run'_eq (impl.addLift challengeQueryImpl) _ s1
        (Prover.addLift_challenge_support_faithful impl hImplSupp)]⟩
    simp only [Option.elim_some, liftM_bind, bind_assoc] at hx
    obtain ⟨a₅, hV₂, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
    simp only [FullTranscript.append_snd] at hV₂
    rcases a₅ with _ | vo₂
    · change none ∈ support (OracleComp.liftComp ((fun a => some a) <$>
        ((Verifier.run s₂ tr₂ R₂.verifier).run)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₂
      simp only [mem_support_liftComp_iff, support_map, Set.mem_image, reduceCtorEq, and_false,
        exists_false] at hV₂
    rcases vo₂ with _ | vs₃
    · exact absurd (none_mem_support_run_of_prover_verifier R₂ s₂ w₂ tr₂ (s₃, w₃) hP₂'
        (by change some none ∈ support (OracleComp.liftComp ((fun a => some a) <$>
              ((Verifier.run s₂ tr₂ R₂.verifier).run)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₂
            rw [mem_support_liftComp_iff, support_map, Set.mem_image] at hV₂
            obtain ⟨z, hz, hzy⟩ := hV₂; rw [Option.some.injEq] at hzy; subst hzy; exact hz)) h₂nf
    -- vo₂ = some vs₃: V₂ accepted; reconstruct the output and discharge via h₂'.
    have hV₂' : some vs₃ ∈ support (R₂.verifier.run s₂ tr₂).run := by
      change some (some vs₃) ∈ support (OracleComp.liftComp ((fun a => some a) <$>
        ((Verifier.run s₂ tr₂ R₂.verifier).run))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) at hV₂
      rw [mem_support_liftComp_iff, support_map, Set.mem_image] at hV₂
      obtain ⟨z, hz, hzy⟩ := hV₂; rw [Option.some.injEq] at hzy; subst hzy; exact hz
    simp only [Option.elim_some, Option.getM_some, pure_bind] at hx
    change some x ∈ support (pure (some ((tr₁ ++ₜ tr₂, s₃, w₃), vs₃))
      : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option _)) at hx
    simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hx
    subst hx
    obtain ⟨hrel₃, hvs₃⟩ := h₂' s₂ w₂ hrel₂ ((tr₂, s₃, w₃), vs₃)
      (by rw [OptionT.mem_support_iff]
          exact mem_support_run_of_prover_verifier R₂ s₂ w₂ tr₂ (s₃, w₃) vs₃ hP₂' hV₂')
    simp only at hrel₃ hvs₃ ⊢
    exact ⟨hrel₃, hvs₃⟩

end Reduction
