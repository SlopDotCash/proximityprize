/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.RunUnroll
import ProximityPrize.Extensions.OracleReduction.Security.RoundByRound

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

/-- Pinning and discarding the state commute for a single query as programs. -/
private theorem collapseState_run'_program
    (impl : QueryImpl spec (StateT σ ProbComp)) (s₀ : σ) (t : spec.Domain) (u : Unit) :
    (collapseState impl s₀ t).run' u = (impl t).run' s₀ := by
  simp [collapseState, StateT.run'_eq, StateT.run_lift, Functor.map_map]

/-- The native per-query measures agree in every measurable output structure. -/
theorem collapseState_run'_apply
    (impl : QueryImpl spec (StateT σ ProbComp)) (s₀ : σ) (t : spec.Domain) (u : Unit)
    [MeasurableSpace (spec.Range t)] :
    evalDist ((collapseState impl s₀ t).run' u) = evalDist ((impl t).run' s₀) :=
  congrArg evalDist (collapseState_run'_program impl s₀ t u)

/-- The collapsed implementation never fails when the original never fails from `s₀`. -/
theorem collapseState_neverFail
    (impl : QueryImpl spec (StateT σ ProbComp)) (s₀ : σ)
    (himpl : ∀ (t : spec.Domain), prFail ((impl t).run s₀) = 0) :
    ∀ (t : spec.Domain) (u : Unit), prFail ((collapseState impl s₀ t).run u) = 0 := by
  intro t u
  exact OracleComp.prFail_eq_zero _

/-- State preservation factors a simulated bind before any probability observation. -/
private theorem simulateQ_run'_bind_fixed
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    {α β : Type} (X : OracleComp spec α) (f : α → OracleComp spec β) (s : σ) :
    (simulateQ impl (X >>= f)).run' s =
      (simulateQ impl X).run' s >>= fun a => (simulateQ impl (f a)).run' s := by
  rw [StateT.run'_eq, OptionTStateT.simulateQ_run_bind_state_fixed impl hso, map_bind]
  rw [StateT.run'_eq, bind_map_left]
  rfl

/-- The collapse preserves the actual simulated program when all reachable states are fixed. -/
private theorem simulateQ_run'_collapse_program
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    {α : Type} (X : OracleComp spec α) (s₀ : σ) (u : Unit) :
    (simulateQ (collapseState impl s₀) X).run' u = (simulateQ impl X).run' s₀ := by
  induction X using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure, StateT.run'_eq, StateT.run_pure]
  | query_bind t oa ih =>
    rw [simulateQ_run'_bind_fixed _ (collapseState_state_preserving impl s₀),
      simulateQ_run'_bind_fixed _ hso]
    have hqR : (simulateQ impl (liftM (OracleSpec.query t))).run' s₀ =
        (impl t).run' s₀ := by
      simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have hqL : (simulateQ (collapseState impl s₀) (liftM (OracleSpec.query t))).run' u =
        (collapseState impl s₀ t).run' u := by
      simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    rw [hqL, hqR, collapseState_run'_program]
    exact congrArg _ (funext ih)

/-- Native output distributions agree under the state collapse. -/
theorem evalDist_simulateQ_run'_collapseState
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    {α : Type} [MeasurableSpace α] (X : OracleComp spec α) (s₀ : σ) (u : Unit) :
    evalDist ((simulateQ (collapseState impl s₀) X).run' u)
      = evalDist ((simulateQ impl X).run' s₀) :=
  congrArg evalDist (simulateQ_run'_collapse_program impl hso X s₀ u)

/-- Event observations agree without choosing an output measurable structure. -/
theorem probEvent_simulateQ_run'_collapseState
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    {α : Type} (X : OracleComp spec α) (s₀ : σ) (u : Unit) (p : α → Prop) :
    probEvent p ((simulateQ (collapseState impl s₀) X).run' u)
      = probEvent p ((simulateQ impl X).run' s₀) :=
  congrArg (probEvent p) (simulateQ_run'_collapse_program impl hso X s₀ u)

/-- Failure observations agree under the same program identity. -/
theorem probFailure_simulateQ_run'_collapseState
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    {α : Type} (X : OracleComp spec α) (s₀ : σ) (u : Unit) :
    prFail ((simulateQ (collapseState impl s₀) X).run' u)
      = prFail ((simulateQ impl X).run' s₀) :=
  congrArg prFail (simulateQ_run'_collapse_program impl hso X s₀ u)

/-- A bound for every pinned state also bounds any sampled initial state. -/
theorem probEvent_init_bind_le_of_forall_collapse_le
    (impl : QueryImpl spec (StateT σ ProbComp))
    (init : ProbComp σ) {α : Type} (X : OracleComp spec α) (p : α × σ → Prop) {ε : ℝ≥0∞}
    (h : ∀ s₀ : σ, probEvent p ((simulateQ impl X).run s₀) ≤ ε) :
    probEvent p (do (simulateQ impl X).run (← init)) ≤ ε := by
  exact prEvent_bind_le_of_forall_le init _ p h

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
    probEvent (p) ((OptionT.mk do
        (simulateQ (collapseState impl s₀) X).run' (← (pure () : ProbComp Unit)) :
      OptionT ProbComp α))
      = probEvent (p) ((OptionT.mk do (simulateQ impl X).run' (← (pure s₀ : ProbComp σ)) :
          OptionT ProbComp α)) := by
  simp only [pure_bind]
  exact congrArg (fun z : ProbComp (Option α) => probEvent p (OptionT.mk z))
    (simulateQ_run'_collapse_program impl hso X s₀ ())

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
    simp only [pure_bind] at h ⊢
    rw [simulateQ_run'_collapse_program impl hso] at h
    exact h)

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
    simp only [pure_bind] at h ⊢
    rw [simulateQ_run'_collapse_program impl hso]
    exact h)

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
  constructor
  · rintro ⟨WitMid, extractor, kSF, hbound⟩
    refine ⟨WitMid, extractor, kSF.collapse hso, ?_⟩
    intro stmtIn witIn prover i
    have hb := hbound stmtIn witIn prover i
    simp only [pure_bind] at hb ⊢
    rw [collapseState_addLift impl challengeQueryImpl s₀,
      simulateQ_run'_collapse_program (impl.addLift challengeQueryImpl)
        (OptionTStateT.addLift_state_preserving impl hso)]
    exact hb
  · rintro ⟨WitMid, extractor, kSF, hbound⟩
    refine ⟨WitMid, extractor, kSF.ofCollapse hso, ?_⟩
    intro stmtIn witIn prover i
    have hb := hbound stmtIn witIn prover i
    simp only [pure_bind] at hb ⊢
    rw [collapseState_addLift impl challengeQueryImpl s₀,
      simulateQ_run'_collapse_program (impl.addLift challengeQueryImpl)
        (OptionTStateT.addLift_state_preserving impl hso)] at hb
    exact hb

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
    have hb := sF.toFun_full stmt tr h
    simp only [pure_bind] at hb ⊢
    rw [simulateQ_run'_collapse_program impl hso]
    exact hb

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
    have hb := sF.toFun_full stmt tr h
    simp only [pure_bind] at hb ⊢
    rw [simulateQ_run'_collapse_program impl hso] at hb
    exact hb

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
  constructor
  · rintro ⟨sF, hbound⟩
    refine ⟨sF.collapse hso, ?_⟩
    intro stmtIn hstmt WitIn WitOut witIn prover i
    have hb := hbound stmtIn hstmt WitIn WitOut witIn prover i
    simp only [pure_bind] at hb ⊢
    rw [collapseState_addLift impl challengeQueryImpl s₀,
      simulateQ_run'_collapse_program (impl.addLift challengeQueryImpl)
        (OptionTStateT.addLift_state_preserving impl hso)]
    exact hb
  · rintro ⟨sF, hbound⟩
    refine ⟨sF.ofCollapse hso, ?_⟩
    intro stmtIn hstmt WitIn WitOut witIn prover i
    have hb := hbound stmtIn hstmt WitIn WitOut witIn prover i
    simp only [pure_bind] at hb ⊢
    rw [collapseState_addLift impl challengeQueryImpl s₀,
      simulateQ_run'_collapse_program (impl.addLift challengeQueryImpl)
        (OptionTStateT.addLift_state_preserving impl hso)] at hb
    exact hb

end RbrTransfer

end StateCollapse

/-! ## Axiom audit — kernel-clean. -/
#print axioms StateCollapse.evalDist_simulateQ_run'_collapseState
#print axioms StateCollapse.probEvent_simulateQ_run'_collapseState
#print axioms StateCollapse.probEvent_init_bind_le_of_forall_collapse_le
#print axioms StateCollapse.rbrKnowledgeSoundness_collapseState_iff
#print axioms StateCollapse.rbrSoundness_collapseState_iff
