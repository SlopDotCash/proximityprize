/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.RbrGame
import ArkLib.ToVCVio.Lemmas

/-! Generic native knowledge transport for pure verifiers. Original `hExt`, carry,
pushforward and false-to-true flip contracts are retained. The challenge proof uses the
canonical shared-state game mixture bound and keeps rejected execution mass explicit.
Provenance: scripts/integration/pure-knowledge-consolidation.json. -/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

set_option backward.isDefEq.respectTransparency false

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut WitIn WitOut : Type}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

section Defs

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- KS pushforward of `relOut` along a pure verifier map. -/
def pureKSPushforward (verify : StmtIn → pSpec.FullTranscript → StmtOut)
    (relOut : Set (StmtOut × WitOut)) : Set (StmtIn × WitIn) :=
  {x | ∃ tr wOut, (verify x.1 tr, wOut) ∈ relOut}

/-- KS carry of `relIn` along a pure verifier map. -/
def pureKSCarry (verify : StmtIn → pSpec.FullTranscript → StmtOut)
    (relIn : Set (StmtIn × WitIn)) : Set (StmtOut × WitOut) :=
  {y | ∀ stmt tr, verify stmt tr = y.1 → ∀ wIn, (stmt, wIn) ∈ relIn}

end Defs

section OneRound

variable {pSpec : ProtocolSpec 1} [∀ i, SampleableType (pSpec.Challenge i)]

theorem rbrKnowledgeSoundness_of_pure_oneRound
    (verify : StmtIn → pSpec.FullTranscript → StmtOut)
    (ext : StmtIn → pSpec.FullTranscript → WitOut → WitIn)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (hExt : ∀ stmt tr wOut, (verify stmt tr, wOut) ∈ relOut → (stmt, ext stmt tr wOut) ∈ relIn) :
    Verifier.rbrKnowledgeSoundness init impl relIn relOut
      (⟨fun stmt tr => pure (verify stmt tr)⟩ : Verifier oSpec StmtIn StmtOut pSpec) 0 := by
  refine ⟨fun _ => WitIn,
    { extractIn := fun _ w => w
      extractMid := fun _ _ _ w => w
      extractOut := fun stmt tr wOut => ext stmt tr wOut },
    { toFun := fun m => match m with
        | ⟨0, _⟩ => fun stmt _ w => (stmt, w) ∈ relIn
        | ⟨1, _⟩ => fun stmt tr w => ∃ wOut, (verify stmt tr, wOut) ∈ relOut ∧ w = ext stmt tr wOut
      toFun_empty := fun _ _ h => h
      toFun_next := fun m hDir stmt tr msg w h => by
        match m with
        | ⟨0, _⟩ =>
          obtain ⟨wOut, hrel, rfl⟩ := h
          exact hExt _ _ _ hrel
      toFun_full := fun stmt tr wOut h => by
        rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff] at h
        obtain ⟨x, hx, hrel⟩ := h
        simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
        obtain ⟨s, _, hx⟩ := hx
        have key : (simulateQ impl
            ((⟨fun stmt tr => pure (verify stmt tr)⟩ :
              Verifier oSpec StmtIn StmtOut pSpec).run stmt tr)).run' s
            = pure (some (verify stmt tr)) := by
          change (simulateQ impl
            (pure (some (verify stmt tr)) : OracleComp oSpec (Option StmtOut))).run' s = _
          rw [simulateQ_pure]
          change Prod.fst <$> (pure (some (verify stmt tr)) : StateT σ ProbComp _).run s = _
          rw [StateT.run_pure]; simp [map_pure]
        rw [key] at hx
        simp only [support_pure, Set.mem_singleton_iff] at hx
        cases (Option.some.inj hx)
        exact ⟨wOut, hrel, rfl⟩ },
    ?_⟩
  intro stmtIn witIn prover i
  rcases i with ⟨⟨iv, hiv⟩, hdir⟩
  match iv, hiv with
  | 0, hiv =>
    refine le_of_eq ?_
    rw [show ((0 : pSpec.ChallengeIdx → NNReal) ⟨⟨0, hiv⟩, hdir⟩ : ENNReal) = 0 by simp]
    rw [OracleComp.prEvent_eq_zero_iff]
    rintro ⟨transcript, challenge, log⟩ _ ⟨w, hnot, hyes⟩
    obtain ⟨wOut, hrel, rfl⟩ := hyes
    exact hnot (hExt _ _ _ hrel)

end OneRound

section ZeroRound

variable {pSpec : ProtocolSpec 0} [∀ i, SampleableType (pSpec.Challenge i)]

theorem rbrKnowledgeSoundness_of_pure_zeroRound
    (verify : StmtIn → pSpec.FullTranscript → StmtOut)
    (ext : StmtIn → pSpec.FullTranscript → WitOut → WitIn)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (hExt : ∀ stmt tr wOut, (verify stmt tr, wOut) ∈ relOut → (stmt, ext stmt tr wOut) ∈ relIn) :
    Verifier.rbrKnowledgeSoundness init impl relIn relOut
      (⟨fun stmt tr => pure (verify stmt tr)⟩ : Verifier oSpec StmtIn StmtOut pSpec) 0 := by
  refine ⟨fun _ => WitIn,
    { extractIn := fun _ w => w
      extractMid := fun m => Fin.elim0 m
      extractOut := fun stmt tr wOut => ext stmt tr wOut },
    { toFun := fun _ stmt _ w => (stmt, w) ∈ relIn
      toFun_empty := fun _ _ h => h
      toFun_next := fun m => Fin.elim0 m
      toFun_full := fun stmt tr wOut h => by
        rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff] at h
        obtain ⟨x, hx, hrel⟩ := h
        simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
        obtain ⟨s, _, hx⟩ := hx
        have key : (simulateQ impl
            ((⟨fun stmt tr => pure (verify stmt tr)⟩ :
              Verifier oSpec StmtIn StmtOut pSpec).run stmt tr)).run' s
            = pure (some (verify stmt tr)) := by
          change (simulateQ impl
            (pure (some (verify stmt tr)) : OracleComp oSpec (Option StmtOut))).run' s = _
          rw [simulateQ_pure]
          change Prod.fst <$> (pure (some (verify stmt tr)) : StateT σ ProbComp _).run s = _
          rw [StateT.run_pure]; simp [map_pure]
        rw [key] at hx
        simp only [support_pure, Set.mem_singleton_iff] at hx
        cases (Option.some.inj hx)
        exact hExt _ _ _ hrel },
    ?_⟩
  intro stmtIn witIn prover i
  exact Fin.elim0 i.1

end ZeroRound

end Verifier

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

section ZeroRoundPure

variable {StmtIn StmtOut : Type}

/-- The trivial rbr extractor for a zero-round reduction with `Unit` witnesses. -/
def zeroRoundPureExtractor :
    Extractor.RoundByRound oSpec StmtIn Unit Unit !p[] (fun _ => Unit) where
  extractIn := fun _ _ => ()
  extractMid := fun i => Fin.elim0 i
  extractOut := fun _ _ _ => ()

/-- Knowledge state function for a zero-round pure verifier `pure ∘ v`, along a relation
transport `relOut ∘ v ⊆ relIn`. -/
def zeroRoundPureKSF (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (v : StmtIn → StmtOut)
    {relIn : Set (StmtIn × Unit)} {relOut : Set (StmtOut × Unit)}
    (hdoom : ∀ stmtIn, (v stmtIn, ()) ∈ relOut → (stmtIn, ()) ∈ relIn) :
    (⟨fun p _tr => pure (v p)⟩ :
      Verifier oSpec StmtIn StmtOut !p[]).KnowledgeStateFunction init impl relIn relOut
      zeroRoundPureExtractor where
  toFun := fun _ stmtIn _ _ => (stmtIn, ()) ∈ relIn
  toFun_empty := fun _ _ h => h
  toFun_next := fun i => Fin.elim0 i
  toFun_full := fun stmtIn tr witOut h => by
    simp only [Verifier.run] at h
    rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have key : (simulateQ impl (pure (v stmtIn) : OptionT (OracleComp oSpec) StmtOut)).run' s =
        pure (some (v stmtIn)) := by
      change (simulateQ impl
        (pure (some (v stmtIn)) : OracleComp oSpec (Option StmtOut))).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$> (pure (some (v stmtIn)) : StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]; simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    cases (Option.some.inj hx)
    exact hdoom stmtIn hrel

/-- **Zero-round pure verifiers are perfectly rbr knowledge-sound along a relation transport.**
Generalizes `Verifier.id_rbrKnowledgeSoundness` from `v = id`, `relIn = relOut` to any
deterministic-total verifier with `relOut ∘ v ⊆ relIn`. -/
theorem rbrKnowledgeSoundness_zeroRound_pure
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (v : StmtIn → StmtOut)
    {relIn : Set (StmtIn × Unit)} {relOut : Set (StmtOut × Unit)}
    (hdoom : ∀ stmtIn, (v stmtIn, ()) ∈ relOut → (stmtIn, ()) ∈ relIn) :
    (⟨fun p _tr => pure (v p)⟩ :
      Verifier oSpec StmtIn StmtOut !p[]).rbrKnowledgeSoundness init impl relIn relOut 0 :=
  ⟨fun _ => Unit, zeroRoundPureExtractor, zeroRoundPureKSF init impl v hdoom,
    fun _ _ _ i => Fin.elim0 i.1⟩

end ZeroRoundPure

section SingleMessagePure

variable {StmtIn StmtOut M : Type}

/-- The trivial rbr extractor for a single-message-round reduction with `Unit` witnesses. -/
def singleMessagePureExtractor :
    Extractor.RoundByRound oSpec StmtIn Unit Unit ⟨!v[.P_to_V], !v[M]⟩ (fun _ => Unit) where
  extractIn := fun _ _ => ()
  extractMid := fun _ _ _ _ => ()
  extractOut := fun _ _ _ => ()

/-- Knowledge state function for a single-message-round pure verifier: the input-relation
membership is carried unchanged through the (adversarial) message, and `hdoom` recovers it from
any output landing in `relOut`. -/
def singleMessagePureKSF (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (v : StmtIn → M → StmtOut)
    {relIn : Set (StmtIn × Unit)} {relOut : Set (StmtOut × Unit)}
    (hdoom : ∀ stmtIn msg, (v stmtIn msg, ()) ∈ relOut → (stmtIn, ()) ∈ relIn) :
    (⟨fun p tr => pure (v p (tr.messages ⟨0, rfl⟩))⟩ :
      Verifier oSpec StmtIn StmtOut ⟨!v[.P_to_V], !v[M]⟩).KnowledgeStateFunction init impl
      relIn relOut singleMessagePureExtractor where
  toFun := fun _ stmtIn _ _ => (stmtIn, ()) ∈ relIn
  toFun_empty := fun _ _ h => h
  toFun_next := fun _ _ _ _ _ _ h => h
  toFun_full := fun stmtIn tr witOut h => by
    simp only [Verifier.run] at h
    rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have key : ∀ out : StmtOut,
        (simulateQ impl (pure out : OptionT (OracleComp oSpec) StmtOut)).run' s =
          pure (some out) := by
      intro out
      change (simulateQ impl (pure (some out) :
        OracleComp oSpec (Option StmtOut))).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$> (pure (some out) : StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]; simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    cases (Option.some.inj hx)
    exact hdoom stmtIn _ hrel

/-- **Single-message-round pure verifiers are perfectly rbr knowledge-sound along a relation
transport.** There is no challenge round, so the error is `0`. -/
theorem rbrKnowledgeSoundness_singleMessage_pure
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (v : StmtIn → M → StmtOut)
    {relIn : Set (StmtIn × Unit)} {relOut : Set (StmtOut × Unit)}
    (hdoom : ∀ stmtIn msg, (v stmtIn msg, ()) ∈ relOut → (stmtIn, ()) ∈ relIn) :
    (⟨fun p tr => pure (v p (tr.messages ⟨0, rfl⟩))⟩ :
      Verifier oSpec StmtIn StmtOut ⟨!v[.P_to_V], !v[M]⟩).rbrKnowledgeSoundness init impl
      relIn relOut 0 := by
  refine ⟨fun _ => Unit, singleMessagePureExtractor,
    singleMessagePureKSF init impl v hdoom, ?_⟩
  intro _stmtIn _witIn _prover ⟨⟨0, _⟩, hdir⟩
  exact absurd hdir (by simp)

end SingleMessagePure

section SingleChallengePure

variable {StmtIn StmtOut C : Type} [SampleableType C]

/-- The trivial rbr extractor for a single-challenge-round reduction with `Unit` witnesses. -/
def singleChallengePureExtractor :
    Extractor.RoundByRound oSpec StmtIn Unit Unit ⟨!v[.V_to_P], !v[C]⟩ (fun _ => Unit) where
  extractIn := fun _ _ => ()
  extractMid := fun _ _ _ _ => ()
  extractOut := fun _ _ _ => ()

/-- Knowledge state function for a single-challenge-round pure verifier: before the challenge,
input-relation membership; after the challenge, output-relation membership of the deterministic
output. -/
def singleChallengePureKSF (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (v : StmtIn → C → StmtOut)
    (relIn : Set (StmtIn × Unit)) (relOut : Set (StmtOut × Unit)) :
    (⟨fun p tr => pure (v p (tr.challenges ⟨0, rfl⟩))⟩ :
      Verifier oSpec StmtIn StmtOut ⟨!v[.V_to_P], !v[C]⟩).KnowledgeStateFunction init impl
      relIn relOut singleChallengePureExtractor where
  toFun
  | ⟨0, _⟩ => fun stmtIn _ _ => (stmtIn, ()) ∈ relIn
  | ⟨1, _⟩ => fun stmtIn tr _ => (v stmtIn (tr.challenges ⟨0, rfl⟩), ()) ∈ relOut
  toFun_empty := fun _ _ h => h
  toFun_next := fun m hdir => by
    exfalso
    have hm : m = 0 := by omega
    subst hm
    simp at hdir
  toFun_full := fun stmtIn tr witOut h => by
    simp only [Verifier.run] at h
    rw [gt_iff_lt, OracleComp.OptionT.prEvent_mk_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have key : ∀ out : StmtOut,
        (simulateQ impl (pure out : OptionT (OracleComp oSpec) StmtOut)).run' s =
          pure (some out) := by
      intro out
      change (simulateQ impl (pure (some out) :
        OracleComp oSpec (Option StmtOut))).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$> (pure (some out) : StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]; simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    cases (Option.some.inj hx)
    exact hrel

/-- **Single-challenge-round pure verifiers are rbr knowledge-sound at the false-to-true flip
probability of the challenge.** The per-round error is any bound on the probability, over a
uniform challenge, that a doomed input statement (`∉ relIn`) is mapped into `relOut`. -/
theorem rbrKnowledgeSoundness_singleChallenge_pure
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (v : StmtIn → C → StmtOut)
    (relIn : Set (StmtIn × Unit)) (relOut : Set (StmtOut × Unit))
    (err : ℝ≥0)
    (hflip : ∀ stmtIn, (stmtIn, ()) ∉ relIn →
      probEvent (fun c : C => (v stmtIn c, ()) ∈ relOut) ($ᵗ C) ≤ err) :
    (⟨fun p tr => pure (v p (tr.challenges ⟨0, rfl⟩))⟩ :
      Verifier oSpec StmtIn StmtOut ⟨!v[.V_to_P], !v[C]⟩).rbrKnowledgeSoundness init impl
      relIn relOut (fun _ => err) := by
  refine ⟨fun _ => Unit, singleChallengePureExtractor,
    singleChallengePureKSF init impl v relIn relOut, ?_⟩
  intro stmtIn witIn prover i
  have hi : i = ⟨⟨0, by decide⟩, rfl⟩ := by
    apply Subtype.ext
    exact Fin.eq_zero i.1
  subst hi
  apply ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le init impl
    (prover.runWithLogToRound (0 : Fin (1 + 1)) stmtIn witIn)
    (⟨⟨0, by decide⟩, rfl⟩ : (⟨!v[.V_to_P], !v[C]⟩ : ProtocolSpec 1).ChallengeIdx)
    (fun tr c => (tr.1.1, c, tr.2))
  intro tr
  change Pr{let c ← $ᵗ C}[
    ∃ _w : Unit, ¬ (stmtIn, ()) ∈ relIn ∧ (v stmtIn c, ()) ∈ relOut] ≤ _
  by_cases hmem : (stmtIn, ()) ∈ relIn
  · simpa only [hmem, not_true_eq_false, false_and, exists_const,
      prEvent_false] using (show (0 : ENNReal) ≤ (err : ENNReal) from _root_.zero_le)
  · simpa only [hmem, not_false_eq_true, true_and, exists_const] using hflip stmtIn hmem

end SingleChallengePure

end Verifier

#print axioms Verifier.rbrKnowledgeSoundness_of_pure_oneRound
#print axioms Verifier.rbrKnowledgeSoundness_of_pure_zeroRound
#print axioms Verifier.rbrKnowledgeSoundness_zeroRound_pure
#print axioms Verifier.rbrKnowledgeSoundness_singleMessage_pure
#print axioms Verifier.rbrKnowledgeSoundness_singleChallenge_pure
