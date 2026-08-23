/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.RunUnroll
import ArkLib.OracleReduction.Security.RoundByRound

/-!
# State collapse: reducing arbitrary-state implementations to `Unit`-state ones

Several seam keystones in the sequential-composition theory (append soundness, append
round-by-round knowledge soundness) are proven under a `[Subsingleton σ]` hypothesis on the
implementation state, because their seam-reorder steps fix the threaded state. This file
provides the **state-collapse transfer**: for a *state-preserving* implementation
`impl : QueryImpl oSpec (StateT σ ProbComp)` and a fixed initial state `s₀`, the collapsed
implementation

* `collapseState impl s₀ : QueryImpl oSpec (StateT Unit ProbComp)`

answers every query by running `impl` from `s₀` and discarding the (unchanged) state. The
master identity `evalDist_simulateQ_run'_collapseState` shows that simulating any computation
against the collapsed implementation from `()` has **the same distribution** as simulating it
against `impl` from `s₀`: state preservation means the threaded state is constantly `s₀`, so
re-running each query from `s₀` is indistinguishable. Since `Unit` is a subsingleton, the
`[Subsingleton σ]` keystones apply to the collapsed side verbatim, and the identity (plus an
averaging step over the initial-state distribution, `probEvent_bind_le_of_forall_le`)
transfers their conclusions back to arbitrary `σ`.

Side-condition bricks: the collapsed implementation is unconditionally state-preserving
(`collapseState_state_preserving`), inherits non-failure (`collapseState_neverFail`), and the
probability-level corollaries (`probEvent_simulateQ_run'_collapseState`,
`probFailure_simulateQ_run'_collapseState`) follow from the master identity since `probEvent`
and `probFailure` are functions of `evalDist`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

open OracleComp OracleSpec
open scoped NNReal ENNReal

namespace StateCollapse

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- Collapse a stateful query implementation to a `Unit`-state one by pinning the state to
`s₀`: every query runs `impl` from `s₀` and discards the result state. For state-preserving
`impl` this is distribution-faithful (`evalDist_simulateQ_run'_collapseState`). -/
def collapseState (impl : QueryImpl spec (StateT σ ProbComp)) (s₀ : σ) :
    QueryImpl spec (StateT Unit ProbComp) :=
  fun t => StateT.lift ((impl t).run' s₀)

/-- The collapsed implementation is unconditionally state-preserving (the state is `Unit`). -/
theorem collapseState_state_preserving
    (impl : QueryImpl spec (StateT σ ProbComp)) (s₀ : σ) :
    ∀ (t : spec.Domain) (u : Unit) (x : spec.Range t × Unit),
      x ∈ support ((collapseState impl s₀ t).run u) → x.2 = u := by
  intro t u x _
  exact Subsingleton.elim _ _

/-- The collapsed implementation runs the original from `s₀` on every query: the `run'`
distributions agree per query. -/
theorem collapseState_run'_apply
    (impl : QueryImpl spec (StateT σ ProbComp)) (s₀ : σ) (t : spec.Domain) (u : Unit) :
    evalDist ((collapseState impl s₀ t).run' u) = evalDist ((impl t).run' s₀) := by
  simp [collapseState, StateT.run'_eq, StateT.run_lift, evalDist_map, Functor.map_map]

/-- The collapsed implementation never fails when the original never fails from `s₀`. -/
theorem collapseState_neverFail
    (impl : QueryImpl spec (StateT σ ProbComp)) (s₀ : σ)
    (himpl : ∀ (t : spec.Domain), Pr[⊥ | (impl t).run s₀] = 0) :
    ∀ (t : spec.Domain) (u : Unit), Pr[⊥ | (collapseState impl s₀ t).run u] = 0 := by
  intro t u
  simp only [collapseState, StateT.run_lift]
  rw [probFailure_bind_eq_zero_iff]
  refine ⟨?_, fun a _ => probFailure_pure (a, u)⟩
  have h := himpl t
  rw [StateT.run'_eq]
  simp [h]

/-- **The master collapse identity**: simulating any computation against the collapsed
implementation (from `()`) has the same distribution as simulating it against the original
state-preserving implementation from the pinned state `s₀`. Induction on the computation;
state preservation keeps the original's threaded state constantly `s₀`, which is exactly what
the collapsed side re-supplies on every query. -/
theorem evalDist_simulateQ_run'_collapseState
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    {α : Type} (X : OracleComp spec α) (s₀ : σ) (u : Unit) :
    evalDist ((simulateQ (collapseState impl s₀) X).run' u)
      = evalDist ((simulateQ impl X).run' s₀) := by
  induction X using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure, StateT.run'_eq, StateT.run_pure]
  | query_bind t oa ih =>
    have hqR : (simulateQ impl (liftM (OracleSpec.query t))).run s₀ = (impl t).run s₀ := by
      simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have hqL : (simulateQ (collapseState impl s₀) (liftM (OracleSpec.query t))).run u
        = (collapseState impl s₀ t).run u := by
      simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have keyR :
        evalDist ((simulateQ impl (liftM (OracleSpec.query t) >>= oa)).run' s₀)
        = (evalDist ((impl t).run' s₀)) >>= fun a =>
            evalDist ((simulateQ impl (oa a)).run' s₀) := by
      rw [StateT.run'_eq,
        OptionTStateT.simulateQ_run_bind_state_fixed impl hso (liftM (OracleSpec.query t)) oa s₀,
        hqR, map_bind, evalDist_bind,
        show (evalDist ((impl t).run' s₀)) = (fun x => x.1) <$> evalDist ((impl t).run s₀) from by
          rw [StateT.run'_eq, evalDist_map],
        bind_map_left]
      refine bind_congr fun p => ?_
      rw [StateT.run'_eq]
    have keyL :
        evalDist ((simulateQ (collapseState impl s₀)
            (liftM (OracleSpec.query t) >>= oa)).run' u)
        = (evalDist ((collapseState impl s₀ t).run' u)) >>= fun a =>
            evalDist ((simulateQ (collapseState impl s₀) (oa a)).run' u) := by
      rw [StateT.run'_eq,
        OptionTStateT.simulateQ_run_bind_state_fixed (collapseState impl s₀)
          (collapseState_state_preserving impl s₀) (liftM (OracleSpec.query t)) oa u,
        hqL, map_bind, evalDist_bind,
        show (evalDist ((collapseState impl s₀ t).run' u))
            = (fun x => x.1) <$> evalDist ((collapseState impl s₀ t).run u) from by
          rw [StateT.run'_eq, evalDist_map],
        bind_map_left]
      refine bind_congr fun p => ?_
      rw [StateT.run'_eq]
    rw [keyL, keyR, collapseState_run'_apply impl s₀ t u]
    exact bind_congr fun a => ih a

/-- `probEvent` is a function of `evalDist`, across monads. -/
private lemma probEvent_congr_evalDist {m m' : Type → Type _}
    [Monad m] [Monad m'] [HasEvalSPMF m] [HasEvalSPMF m'] {α : Type}
    {mx : m α} {my : m' α} (h : evalDist mx = evalDist my) (p : α → Prop) :
    Pr[p | mx] = Pr[p | my] := by
  unfold probEvent
  rw [h]

/-- `probFailure` is a function of `evalDist`, across monads. -/
private lemma probFailure_congr_evalDist {m m' : Type → Type _}
    [Monad m] [Monad m'] [HasEvalSPMF m] [HasEvalSPMF m'] {α : Type}
    {mx : m α} {my : m' α} (h : evalDist mx = evalDist my) :
    Pr[⊥ | mx] = Pr[⊥ | my] := by
  unfold probFailure
  rw [h]

/-- Probability-level collapse identity for events. -/
theorem probEvent_simulateQ_run'_collapseState
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    {α : Type} (X : OracleComp spec α) (s₀ : σ) (u : Unit) (p : α → Prop) :
    Pr[p | (simulateQ (collapseState impl s₀) X).run' u]
      = Pr[p | (simulateQ impl X).run' s₀] :=
  probEvent_congr_evalDist (evalDist_simulateQ_run'_collapseState impl hso X s₀ u) p

/-- Probability-level collapse identity for failure. -/
theorem probFailure_simulateQ_run'_collapseState
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    {α : Type} (X : OracleComp spec α) (s₀ : σ) (u : Unit) :
    Pr[⊥ | (simulateQ (collapseState impl s₀) X).run' u]
      = Pr[⊥ | (simulateQ impl X).run' s₀] :=
  probFailure_congr_evalDist (evalDist_simulateQ_run'_collapseState impl hso X s₀ u)

/-- **Averaging transfer**: a uniform bound on the pinned-state runs bounds the
initial-state-sampled run. This is the step that converts per-`s₀` collapsed conclusions
(obtained via the `[Subsingleton Unit]` keystones) into conclusions for an arbitrary
initial-state distribution `init`. -/
theorem probEvent_init_bind_le_of_forall_collapse_le
    (impl : QueryImpl spec (StateT σ ProbComp))
    (init : ProbComp σ) {α : Type} (X : OracleComp spec α) (p : α × σ → Prop) {ε : ℝ≥0∞}
    (h : ∀ s₀ : σ, Pr[p | (simulateQ impl X).run s₀] ≤ ε) :
    Pr[p | do (simulateQ impl X).run (← init)] ≤ ε := by
  exact probEvent_bind_le_of_forall_le fun s₀ _ => h s₀

/-! ## Transfer of round-by-round knowledge soundness through the collapse

At a point-mass initial state `pure s₀`, round-by-round knowledge soundness against `impl` is
**equivalent** to round-by-round knowledge soundness against the collapsed (`Unit`-state, hence
`Subsingleton`-state) implementation. This converts every `[Subsingleton σ]` seam keystone into
an arbitrary-`σ` statement at point-mass initialization. -/

section RbrTransfer

open ProtocolSpec

variable {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {oSpec : OracleSpec ι}

/-- The collapse commutes with adding the (state-blind) lifted challenge oracle. -/
theorem collapseState_addLift
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (cQI : QueryImpl [pSpec.Challenge]ₒ ProbComp) (s₀ : σ) :
    ((collapseState impl s₀).addLift cQI :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT Unit ProbComp))
      = collapseState (impl.addLift cQI) s₀ := by
  funext t
  rcases t with t | t
  · rfl
  · refine StateT.ext fun u => ?_
    simp [collapseState, QueryImpl.addLift_def, QueryImpl.liftTarget_apply, StateT.run_lift,
      StateT.run'_eq, StateT.run_liftM, map_bind, bind_assoc]

/-- Pinned-state probability identity in the `OptionT.mk`-wrapped form used by
`KnowledgeStateFunction.toFun_full`. -/
theorem probEvent_optionT_mk_collapseState
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hso : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    {α : Type} (X : OracleComp oSpec (Option α)) (s₀ : σ) (p : α → Prop) :
    Pr[p | (OptionT.mk do
        (simulateQ (collapseState impl s₀) X).run' (← (pure () : ProbComp Unit)) :
      OptionT ProbComp α)]
      = Pr[p | (OptionT.mk do (simulateQ impl X).run' (← (pure s₀ : ProbComp σ)) :
          OptionT ProbComp α)] := by
  simp only [pure_bind]
  rw [OptionTStateT.probEvent_optionT_mk, OptionTStateT.probEvent_optionT_mk]
  exact probEvent_congr_evalDist
    (evalDist_simulateQ_run'_collapseState impl hso X s₀ ()) _

variable {WitMid : Fin (n + 1) → Type}

/-- Transfer a knowledge state function from the pinned original implementation to the
collapsed implementation (only `toFun_full` mentions the implementation). -/
def _root_.Verifier.KnowledgeStateFunction.collapse
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {s₀ : σ}
    (hso : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (kSF : verifier.KnowledgeStateFunction (pure s₀) impl relIn relOut extractor) :
    verifier.KnowledgeStateFunction (pure ()) (collapseState impl s₀) relIn relOut
      extractor where
  toFun := kSF.toFun
  toFun_empty := kSF.toFun_empty
  toFun_next := kSF.toFun_next
  toFun_full := fun stmtIn tr witOut h => kSF.toFun_full stmtIn tr witOut (by
    rwa [probEvent_optionT_mk_collapseState impl hso] at h)

/-- Transfer a knowledge state function from the collapsed implementation back to the pinned
original. -/
def _root_.Verifier.KnowledgeStateFunction.ofCollapse
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {s₀ : σ}
    (hso : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (kSF : verifier.KnowledgeStateFunction (pure ()) (collapseState impl s₀) relIn relOut
      extractor) :
    verifier.KnowledgeStateFunction (pure s₀) impl relIn relOut extractor where
  toFun := kSF.toFun
  toFun_empty := kSF.toFun_empty
  toFun_next := kSF.toFun_next
  toFun_full := fun stmtIn tr witOut h => kSF.toFun_full stmtIn tr witOut (by
    rwa [probEvent_optionT_mk_collapseState impl hso])

/-- **Round-by-round knowledge soundness transfers through the state collapse** (point-mass
initial state): soundness against the original state-preserving implementation pinned at `s₀`
is equivalent to soundness against the `Unit`-state collapsed implementation. Apply the
`[Subsingleton σ]` keystones on the right-hand side. -/
theorem rbrKnowledgeSoundness_collapseState_iff
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s₀ : σ)
    (hso : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s) :
    Verifier.rbrKnowledgeSoundness (pure s₀) impl relIn relOut verifier rbrKnowledgeError
      ↔ Verifier.rbrKnowledgeSoundness (pure ()) (collapseState impl s₀) relIn relOut
          verifier rbrKnowledgeError := by
  have hkey : ∀ {α : Type} (X : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) (p : α → Prop),
      Pr[p | do
        (simulateQ ((collapseState impl s₀).addLift challengeQueryImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT Unit ProbComp)) X).run'
          (← (pure () : ProbComp Unit))]
      = Pr[p | do
        (simulateQ (impl.addLift challengeQueryImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) X).run'
          (← (pure s₀ : ProbComp σ))] := by
    intro α X p
    simp only [pure_bind]
    rw [collapseState_addLift impl challengeQueryImpl s₀]
    exact probEvent_congr_evalDist
      (evalDist_simulateQ_run'_collapseState (impl.addLift challengeQueryImpl)
        (OptionTStateT.addLift_state_preserving impl hso) X s₀ ()) p
  constructor
  · rintro ⟨WitMid, extractor, kSF, hbound⟩
    refine ⟨WitMid, extractor, kSF.collapse hso, ?_⟩
    intro stmtIn witIn prover i
    rw [hkey]
    exact hbound stmtIn witIn prover i
  · rintro ⟨WitMid, extractor, kSF, hbound⟩
    refine ⟨WitMid, extractor, kSF.ofCollapse hso, ?_⟩
    intro stmtIn witIn prover i
    rw [← hkey]
    exact hbound stmtIn witIn prover i

/-- Transfer a (plain) state function from the pinned original implementation to the collapsed
implementation (only `toFun_full` mentions the implementation). -/
def _root_.Verifier.StateFunction.collapse
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {s₀ : σ}
    (hso : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (sF : verifier.StateFunction (pure s₀) impl langIn langOut) :
    verifier.StateFunction (pure ()) (collapseState impl s₀) langIn langOut where
  toFun := sF.toFun
  toFun_empty := sF.toFun_empty
  toFun_next := sF.toFun_next
  toFun_full := fun stmt tr h => by
    rw [probEvent_optionT_mk_collapseState impl hso]
    exact sF.toFun_full stmt tr h

/-- Transfer a (plain) state function from the collapsed implementation back to the pinned
original. -/
def _root_.Verifier.StateFunction.ofCollapse
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {s₀ : σ}
    (hso : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (sF : verifier.StateFunction (pure ()) (collapseState impl s₀) langIn langOut) :
    verifier.StateFunction (pure s₀) impl langIn langOut where
  toFun := sF.toFun
  toFun_empty := sF.toFun_empty
  toFun_next := sF.toFun_next
  toFun_full := fun stmt tr h => by
    rw [← probEvent_optionT_mk_collapseState impl hso]
    exact sF.toFun_full stmt tr h

/-- **Round-by-round (plain) soundness transfers through the state collapse** (point-mass
initial state). -/
theorem rbrSoundness_collapseState_iff
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s₀ : σ)
    (hso : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s) :
    Verifier.rbrSoundness (pure s₀) impl langIn langOut verifier rbrSoundnessError
      ↔ Verifier.rbrSoundness (pure ()) (collapseState impl s₀) langIn langOut
          verifier rbrSoundnessError := by
  have hkey : ∀ {α : Type} (X : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) (p : α → Prop),
      Pr[p | do
        (simulateQ ((collapseState impl s₀).addLift challengeQueryImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT Unit ProbComp)) X).run'
          (← (pure () : ProbComp Unit))]
      = Pr[p | do
        (simulateQ (impl.addLift challengeQueryImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) X).run'
          (← (pure s₀ : ProbComp σ))] := by
    intro α X p
    simp only [pure_bind]
    rw [collapseState_addLift impl challengeQueryImpl s₀]
    exact probEvent_congr_evalDist
      (evalDist_simulateQ_run'_collapseState (impl.addLift challengeQueryImpl)
        (OptionTStateT.addLift_state_preserving impl hso) X s₀ ()) p
  constructor
  · rintro ⟨sF, hbound⟩
    refine ⟨sF.collapse hso, ?_⟩
    intro stmtIn hstmt WitIn WitOut witIn prover i
    rw [hkey]
    exact hbound stmtIn hstmt WitIn WitOut witIn prover i
  · rintro ⟨sF, hbound⟩
    refine ⟨sF.ofCollapse hso, ?_⟩
    intro stmtIn hstmt WitIn WitOut witIn prover i
    rw [← hkey]
    exact hbound stmtIn hstmt WitIn WitOut witIn prover i

end RbrTransfer

end StateCollapse

/-! ## Axiom audit — kernel-clean. -/
#print axioms StateCollapse.evalDist_simulateQ_run'_collapseState
#print axioms StateCollapse.probEvent_simulateQ_run'_collapseState
#print axioms StateCollapse.probEvent_init_bind_le_of_forall_collapse_le
#print axioms StateCollapse.rbrKnowledgeSoundness_collapseState_iff
#print axioms StateCollapse.rbrSoundness_collapseState_iff
