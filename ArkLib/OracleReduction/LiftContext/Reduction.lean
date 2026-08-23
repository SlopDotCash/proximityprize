/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.LiftContext.Lens
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ToVCVio.Simulation
import ArkLib.ToMathlib.AppendHelpers
-- import ArkLib.OracleReduction.Security.StateRestoration

/-!
  ## Lifting Reductions to Larger Contexts

  Sequential composition is usually not enough to represent oracle reductions in a modular way. We
  also need to formalize **virtual** oracle reductions, which lift reductions from one (virtual /
  inner) context into the another (real / outer) context.

  This is what is meant when we informally say "apply so-and-so protocol to this quantity (derived
  from the input statement & witness)".

  Put in other words, we define a mapping between the input-output interfaces of two (oracle)
  reductions, without changing anything about the underlying reductions.

  Recall that the input-output interface of an oracle reduction consists of:
  - Input: `OuterStmtIn : Type`, `OuterOStmtIn : ιₛᵢ → Type`, and `OuterWitIn : Type`
  - Output: `OuterStmtOut : Type`, `OuterOStmtOut : ιₛₒ → Type`, and `OuterWitOut : Type`

  The liftContext is defined as the following mappings of projections / lifts:

  - `projStmt : OuterStmtIn → InnerStmtIn`
  - `projOStmt : (simulation involving OuterOStmtIn to produce InnerOStmtIn)`
  - `projWit : OuterWitIn → InnerWitIn`
  - `liftStmt : OuterStmtIn × InnerStmtOut → OuterStmtOut`
  - `liftOStmt : (simulation involving InnerOStmtOut to produce OuterOStmtOut)`
  - `liftWit : OuterWitIn × InnerWitOut → OuterWitOut`

  Note that since completeness & soundness for oracle reductions are defined in terms of the same
  properties after converting to (non-oracle) reductions, we only need to focus our efforts on the
  non-oracle case.

  Note that this _exactly_ corresponds to lenses in programming languages / category theory. Namely,
  liftContext on the inputs correspond to a `view`/`get` operation (our "proj"), while liftContext
  on the output corresponds to a `modify`/`set` operation (our "lift").

  More precisely, the `proj/lift` operations correspond to a Lens between two monomial polyonmial
  functors: `OuterCtxIn y^ OuterCtxOut ⇆ InnerCtxIn y^ InnerCtxOut`.

  All the lens definitions are in `Lens.lean`. This file deals with the lens applied to reductions.
  See `OracleReduction.lean` for the application to oracle reduction.
-/

set_option linter.style.longFile 2100

open OracleSpec OracleComp ProtocolSpec

open scoped NNReal

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}

/-- The outer prover after lifting invokes the inner prover on the projected input, and
  lifts the output -/
def Prover.liftContext
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      Prover oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut pSpec where
  PrvState := fun i => P.PrvState i × OuterStmtIn × OuterWitIn
  input := fun ctxIn => ⟨P.input <| lens.proj ctxIn, ctxIn⟩
  sendMessage := fun i ⟨prvState, stmtIn, witIn⟩ => do
    let ⟨msg, prvState'⟩ ← P.sendMessage i prvState
    return ⟨msg, ⟨prvState', stmtIn, witIn⟩⟩
  receiveChallenge := fun i ⟨prvState, stmtIn, witIn⟩ => do
    let f ← P.receiveChallenge i prvState
    return fun chal => ⟨f chal, stmtIn, witIn⟩
  output := fun ⟨prvState, stmtIn, witIn⟩ => do
    let ⟨innerStmtOut, innerWitOut⟩ ← P.output prvState
    return lens.lift (stmtIn, witIn) (innerStmtOut, innerWitOut)

/-- The outer verifier after lifting invokes the inner verifier on the projected input, and
  lifts the output -/
def Verifier.liftContext
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec) :
      Verifier oSpec OuterStmtIn OuterStmtOut pSpec where
  verify := fun stmtIn transcript => do
    let innerStmtIn := lens.proj stmtIn
    let innerStmtOut ← V.verify innerStmtIn transcript
    return lens.lift stmtIn innerStmtOut

/-- The outer reduction after lifting is the combination of the lifting of the prover and
  verifier -/
def Reduction.liftContext
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      Reduction oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut pSpec where
  prover := R.prover.liftContext lens
  verifier := R.verifier.liftContext lens.stmt

open Verifier in
/-- The outer extractor after lifting invokes the inner extractor on the projected input, and
  lifts the output -/
def Extractor.Straightline.liftContext
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : Extractor.Straightline oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec) :
      Extractor.Straightline oSpec OuterStmtIn OuterWitIn OuterWitOut pSpec :=
  fun outerStmtIn outerWitOut fullTranscript proveQueryLog verifyQueryLog => do
    let ⟨innerStmtIn, innerWitOut⟩ := lens.proj (outerStmtIn, outerWitOut)
    let innerWitIn ← E innerStmtIn innerWitOut fullTranscript proveQueryLog verifyQueryLog
    return lens.wit.lift (outerStmtIn, outerWitOut) innerWitIn

open Verifier in
/-- The outer round-by-round extractor after lifting invokes the inner extractor on the projected
  input, and lifts the output -/
def Extractor.RoundByRound.liftContext
    {WitMid : Fin (n + 1) → Type}
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : Extractor.RoundByRound oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec WitMid) :
      Extractor.RoundByRound oSpec OuterStmtIn OuterWitIn OuterWitOut pSpec
        (fun m =>
          match m with
          | ⟨0, _⟩ => OuterWitIn
          | ⟨j + 1, hj⟩ => WitMid ⟨j + 1, hj⟩ × OuterWitOut) where
  eqIn := rfl
  extractOut := fun outerStmtIn transcript outerWitOut =>
    let innerExtract :=
      E.extractOut (lens.stmt.proj outerStmtIn) transcript
        (lens.wit.proj (outerStmtIn, outerWitOut))
    match hm : Fin.last n with
    | ⟨0, h₀⟩ =>
        let innerWitMid0 : WitMid ⟨0, h₀⟩ := cast (by rw [hm]) innerExtract
        let innerWitIn := cast E.eqIn innerWitMid0
        lens.wit.lift (outerStmtIn, outerWitOut) innerWitIn
    | ⟨j + 1, hj⟩ =>
        let innerWitMid : WitMid ⟨j + 1, hj⟩ := cast (by rw [hm]) innerExtract
        (innerWitMid, outerWitOut)
  extractMid := fun m outerStmtIn transcript =>
    match hm : m with
    | ⟨0, h₀⟩ => fun ⟨witMid, outerWitOut⟩ =>
        let innerWitMid0 : WitMid 0 :=
          E.extractMid ⟨0, h₀⟩ (lens.stmt.proj outerStmtIn) transcript witMid
        let innerWitIn := cast E.eqIn innerWitMid0
        lens.wit.lift (outerStmtIn, outerWitOut) innerWitIn
    | ⟨j + 1, hj⟩ => fun ⟨witMid, outerWitOut⟩ =>
        (E.extractMid ⟨j + 1, hj⟩ (lens.stmt.proj outerStmtIn) transcript witMid, outerWitOut)

/-- Compatibility relation between the outer input statement and the inner output statement,
relative to a verifier.

We require that the inner output statement is a possible output of the verifier on the outer
input statement, for any given transcript. Note that we have to existentially quantify over
transcripts since we only reference the verifier, and there's no way to get the transcript without
a prover. -/
def Verifier.compatStatement
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec) :
      OuterStmtIn → InnerStmtOut → Prop :=
  fun outerStmtIn innerStmtOut =>
    ∃ transcript, innerStmtOut ∈ support (V.run (lens.proj outerStmtIn) transcript)

/-- Compatibility relation between the outer input context and the inner output context, relative
to a reduction.

We require that the inner output context (statement + witness) is a possible output of the reduction
on the outer input context (statement + witness). -/
def Reduction.compatContext
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      (OuterStmtIn × OuterWitIn) → (InnerStmtOut × InnerWitOut) → Prop :=
  fun outerCtxIn innerCtxOut =>
    innerCtxOut ∈
      (Prod.snd ∘ Prod.fst) ''
        support (R.run (lens.stmt.proj outerCtxIn.1) (lens.wit.proj outerCtxIn))

/-- Compatibility relation between the outer input witness and the inner output witness, relative to
  a straightline extractor.

We require that the inner output witness is a possible output of the straightline extractor on the
outer input witness, for a given input statement, transcript, and prover and verifier's query logs.
-/
def Extractor.Straightline.compatWit
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (E : Extractor.Straightline oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec) :
      OuterStmtIn × OuterWitOut → InnerWitIn → Prop :=
  fun ⟨outerStmtIn, outerWitOut⟩ innerWitIn =>
    ∃ stmt tr logP logV, innerWitIn ∈
      support (E stmt (lens.wit.proj (outerStmtIn, outerWitOut)) tr logP logV)

@[simp]
lemma OptionT.simulateQ_map_stateful
    {ι : Type} {spec : OracleSpec ι} {α β σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (f : α → β)
    (mx : OptionT (OracleComp spec) α) :
    simulateQ impl ((f <$> mx : OptionT (OracleComp spec) β)) =
      (f <$> (simulateQ impl (OptionT.run mx) : OptionT (StateT σ ProbComp) α) :
        OptionT (StateT σ ProbComp) β) := by
  ext s
  change StateT.run (simulateQ impl ((f <$> mx).run)) s =
    StateT.run
      (OptionT.run (f <$> (simulateQ impl (OptionT.run mx) : OptionT (StateT σ ProbComp) α))) s
  rw [OptionT.run_map]
  rw [_root_.simulateQ_map (impl := impl) (mx := OptionT.run mx) (f := Option.map f)]
  rw [OptionT.run_map]
  rfl

@[simp]
lemma OptionT.liftM_eq_mk_map_some
    {m : Type _ → Type _} [Monad m] [LawfulMonad m] {α : Type _}
    (x : m α) :
    (liftM x : OptionT m α) = OptionT.mk (some <$> x) := by
  rw [OptionT.liftM_def]
  ext
  rw [OptionT.lift, map_eq_bind_pure_comp]
  rfl

@[simp]
lemma OptionT.mk_run'_map_stateful
    {α β σ : Type}
    (init : ProbComp σ) (f : α → β)
    (mx : OptionT (StateT σ ProbComp) α) :
    OptionT.mk (do
      let s ← init
      (f <$> mx).run' s) =
      (f <$> OptionT.mk (do
        let s ← init
        mx.run' s) : OptionT ProbComp β) := by
  ext
  simp [StateT.run']
  change
    (do
      let s ← init
      (fun x : Option β × σ => x.1) <$> ((f <$> mx).run s)) =
    (do
      let x ← init
      (fun a : Option α × σ => Option.map f a.1) <$> (mx.run x))
  rw [OptionT.run_map]
  congr 1
  funext s
  change
    (fun x : Option β × σ => x.1) <$> StateT.run (Option.map f <$> mx.run) s =
      (fun a : Option α × σ => Option.map f a.1) <$> (mx.run s)
  rw [StateT.run_map (f := Option.map f) (x := mx.run) (s := s)]
  simp [Functor.map_map]
  have hr : mx.run.run s = mx.run s := rfl
  rw [hr]

@[simp]
lemma OptionT.mk_map_run_state
    {α β σ : Type}
    (f : α → β)
    (mx : StateT σ ProbComp (Option α))
    (s : σ) :
    OptionT.mk ((fun x : Option α × σ => Option.map f x.1) <$> mx.run s) =
      (f <$> OptionT.mk ((fun x : Option α × σ => x.1) <$> mx.run s) : OptionT ProbComp β) := by
  ext
  simp [Functor.map_map, Function.comp]

@[simp]
lemma OptionT.run_map_state
    {α β σ : Type}
    (f : α → β)
    (mx : OptionT (StateT σ ProbComp) α)
    (s : σ) :
    (fun x : Option β × σ => x.1) <$> StateT.run (OptionT.run (f <$> mx)) s =
      (fun a : Option α × σ => Option.map f a.1) <$> StateT.run (OptionT.run mx) s := by
  rw [OptionT.run_map]
  rw [StateT.run_map (f := Option.map f) (x := OptionT.run mx) (s := s)]
  simp [Functor.map_map]

@[simp]
lemma OptionT.run_map_prod_mk_state
    {α β γ σ : Type}
    (f : α → β)
    (x : γ)
    (mx : OptionT (StateT σ ProbComp) α)
    (s : σ) :
    (fun a : Option α × σ => Option.map (fun y => (x, f y)) a.1) <$>
        StateT.run (OptionT.run mx) s =
      (fun a : Option β × σ => Option.map (Prod.mk x) a.1) <$>
        StateT.run (OptionT.run (f <$> mx)) s := by
  rw [OptionT.run_map]
  rw [StateT.run_map (f := Option.map f) (x := OptionT.run mx) (s := s)]
  rw [Functor.map_map]
  congr 1
  funext a
  cases a.1 <;> rfl

@[simp]
lemma OptionT.mk_simulateQ_run'_map_stateful
    {ι : Type} {spec : OracleSpec ι} {α β σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (init : ProbComp σ) (f : α → β)
    (mx : OptionT (OracleComp spec) α) :
    OptionT.mk (do
      let s ← init
      (simulateQ impl ((f <$> mx : OptionT (OracleComp spec) β))).run' s) =
      (f <$> OptionT.mk (do
        let s ← init
        (simulateQ impl mx).run' s) : OptionT ProbComp β) := by
  rw [OptionT.simulateQ_map_stateful]
  exact OptionT.mk_run'_map_stateful (init := init) (f := f) (mx := simulateQ impl mx)

@[simp]
lemma simulateQ_addLift_liftM
    [∀ i, SampleableType (pSpec.Challenge i)]
    {α σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec α) :
    simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
      (liftM oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) =
      (simulateQ impl oa : StateT σ ProbComp α) := by
  rw [show (liftM oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) =
      liftComp oa (oSpec + [pSpec.Challenge]ₒ) by rw [liftComp_eq_liftM]]
  rw [QueryImpl.simulateQ_add_liftComp_left]

@[simp]
lemma OptionT.simulateQ_addLift_liftM
    [∀ i, SampleableType (pSpec.Challenge i)]
    {α σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OptionT (OracleComp oSpec) α) :
    simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
      (liftM oa : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α) =
      (simulateQ impl oa : OptionT (StateT σ ProbComp) α) := by
  change
    simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
      (liftM oa.run : OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option α)) =
      (simulateQ impl oa.run : StateT σ ProbComp (Option α))
  simpa using (simulateQ_addLift_liftM (impl := impl) (oa := oa.run))

@[simp]
lemma OptionT.simulateQ_addLift_liftQuery
    [∀ i, SampleableType (pSpec.Challenge i)]
    {α σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OptionT (OracleComp oSpec) α) :
    simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
      (simulateQ
        (fun t ↦
          (liftM (query t : OracleComp oSpec (oSpec.Range t)) :
            OracleComp (oSpec + [pSpec.Challenge]ₒ) (oSpec.Range t))) oa) =
      (simulateQ impl oa : OptionT (StateT σ ProbComp) α) := by
  simpa [liftM_OptionT_eq] using
    (OptionT.simulateQ_addLift_liftM (impl := impl) (oa := oa))

@[simp]
lemma simulateQ_getM_run_some
    {ι : Type} {spec : OracleSpec ι} {α σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (x : α) :
    simulateQ impl (((some x : Option α).getM : OptionT (OracleComp spec) α).run) =
      (pure (some x) : StateT σ ProbComp (Option α)) := by
  simp [Option.getM, Option.elimM, simulateQ_pure]

@[simp]
lemma OptionT.simulateQ_getM_some
    {ι : Type} {spec : OracleSpec ι} {α σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (x : α) :
    simulateQ impl ((some x : Option α).getM : OptionT (OracleComp spec) α) =
      (pure x : OptionT (StateT σ ProbComp) α) := by
  change
    OptionT.mk (simulateQ impl (((some x : Option α).getM : OptionT (OracleComp spec) α).run)) =
      OptionT.mk (pure (some x) : StateT σ ProbComp (Option α))
  rw [simulateQ_getM_run_some (impl := impl) (x := x)]

@[simp]
lemma Option.getM_map_run
    {m : Type _ → Type _} [Monad m] [LawfulMonad m] {α β : Type _}
    (f : α → β) (x : Option α) :
    ((Option.map f x).getM : OptionT m β).run =
      (Option.map f <$> (x.getM : OptionT m α).run) := by
  cases x <;> simp [Option.getM]

@[simp]
lemma Option.map_comp_lambda
    {α β γ : Type _} (f : β → γ) (g : α → β) (x : Option α) :
    Option.map (f ∘ g) x = Option.map (fun y => f (g y)) x := by
  cases x <;> rfl

@[simp]
lemma StateT.run_pure_some_bind_map
    {α β γ σ : Type}
    (s : σ) (x : β)
    (mx : StateT σ ProbComp (Option α))
    (f : α → β → γ) :
    (fun a : Option α × σ => Option.map (fun y => f y x) a.1) <$> mx.run s =
      (do
        let a2 ← (pure (some x) : StateT σ ProbComp (Option β)).run s
        (fun a3 : Option (α × β) × σ => Option.map (fun z => f z.1 z.2) a3.1) <$>
          StateT.run (Option.map (fun y => (y, x)) <$> mx) a2.2) := by
  rw [StateT.run_pure]
  simp [StateT.run_map, pure_bind, Functor.map_map, Function.comp]

@[simp]
lemma StateT.run_simulateQ_optiont_map
    {ι : Type} {spec : OracleSpec ι} {α β σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (f : α → β)
    (mx : OptionT (OracleComp spec) α)
    (s : σ) :
    (simulateQ impl (f <$> mx : OptionT (OracleComp spec) β)).run s =
      ((Option.map f <$> simulateQ impl (OptionT.run mx))).run s := by
  rw [OptionT.simulateQ_map_stateful]
  change OptionT.run
      (f <$> OptionT.mk (simulateQ impl (OptionT.run mx))) s =
    ((Option.map f <$> simulateQ impl (OptionT.run mx))).run s
  rw [OptionT.run_map]
  rfl

@[simp]
lemma StateT.run_optiont_pure_bind_simulateQ_map
    {ι : Type} {spec : OracleSpec ι} {α β σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (x : β)
    (mx : OptionT (OracleComp spec) α)
    (s : σ) :
    ((do
      let y ← (pure x : OptionT (StateT σ ProbComp) β)
      simulateQ impl
        (((fun a : α => (a, y)) <$> mx) :
          OptionT (OracleComp spec) (α × β))
      : OptionT (StateT σ ProbComp) (α × β)).run s) =
      (simulateQ impl
        (((fun a : α => (a, x)) <$> mx) :
          OptionT (OracleComp spec) (α × β))).run s := by
  rw [OptionT.run_bind, OptionT.run_pure]
  simp only [Option.elimM, StateT.run_pure, pure_bind, Option.elim_some]
  rfl

@[simp]
lemma OptionT.simulateQ_run_map_writer
    {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {ω α β : Type} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (impl : QueryImpl spec (WriterT ω (OracleComp spec')))
    (f : α → β)
    (mx : OptionT (OracleComp spec) α) :
    (simulateQ impl ((f <$> mx : OptionT (OracleComp spec) β))).run =
      (Prod.map (Option.map f) id <$> (simulateQ impl (OptionT.run mx)).run :
        OracleComp spec' (Option β × ω)) := by
  change (simulateQ impl ((f <$> mx : OptionT (OracleComp spec) β)).run).run =
    (Prod.map (Option.map f) id <$> (simulateQ impl (OptionT.run mx)).run :
      OracleComp spec' (Option β × ω))
  rw [OptionT.run_map]
  rw [_root_.simulateQ_map (impl := impl) (mx := OptionT.run mx) (f := Option.map f)]
  rw [WriterT.run_map']

lemma support_simulateQ_run'_subset_liftContext
    {oSpec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec α) (s : σ) :
    support ((simulateQ impl oa).run' s) ⊆ support oa := by
  intro y hy
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
      simpa [simulateQ_pure, StateT.run'_pure_lib] using hy
  | query_bind t oa ih =>
      simp only [simulateQ_query_bind, StateT.run'_bind_lib, support_bind,
        Set.mem_iUnion, exists_prop] at hy
      rcases hy with ⟨⟨x, s'⟩, hPair, hTail⟩
      have hHead : x ∈ support (query t : OracleComp oSpec _) :=
        OracleComp.mem_support_query t x
      simp only [support_bind, Set.mem_iUnion, exists_prop]
      exact ⟨x, hHead, ih x s' hTail⟩

lemma OptionT.mem_support_run_simulateQ_run'_subset
    {oSpec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OptionT (OracleComp oSpec) α) (s : σ) {x : α}
    (hx : some x ∈ support ((simulateQ impl oa).run' s)) :
    some x ∈ support (OptionT.run oa) := by
  simpa using
    (support_simulateQ_run'_subset_liftContext
      (impl := impl) (oa := OptionT.run oa) (s := s) hx)

lemma mem_support_loggingOracle_run_fst
    {oSpec : OracleSpec ι} {α : Type}
    (oa : OracleComp oSpec α) {x : α} {log : oSpec.QueryLog}
    (hx : (x, log) ∈ support (WriterT.run (simulateQ loggingOracle oa))) :
    x ∈ support oa := by
  have hxFst : x ∈ support (Prod.fst <$> WriterT.run (simulateQ loggingOracle oa)) := by
    rw [support_map]
    exact ⟨(x, log), hx, rfl⟩
  rwa [loggingOracle.fst_map_run_simulateQ] at hxFst

set_option maxHeartbeats 200000 in
theorem Verifier.liftContext_probEvent_le
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (outerStmtIn : OuterStmtIn) (transcript : FullTranscript pSpec) :
    Pr[fun x ↦ x ∈ outerLangOut | OptionT.mk do
      let __do_lift ← init
      (simulateQ impl (run outerStmtIn transcript (liftContext lens V))).run' __do_lift] ≤
      Pr[fun x ↦ x ∈ innerLangOut | OptionT.mk do
        let __do_lift ← init
        (simulateQ impl (run (lens.proj outerStmtIn) transcript V)).run' __do_lift] := by
  have hExecMap :
      OptionT.mk (do
        let __do_lift ← init
        (simulateQ impl (run outerStmtIn transcript (liftContext lens V))).run' __do_lift)
        = lens.lift outerStmtIn <$>
            OptionT.mk (do
              let __do_lift ← init
              (simulateQ impl (run (lens.proj outerStmtIn) transcript V)).run' __do_lift) := by
          rw [Verifier.run, Verifier.liftContext, Verifier.run]
          exact OptionT.mk_simulateQ_run'_map_stateful
            (impl := impl) (init := init)
            (f := lens.lift outerStmtIn)
            (mx := V.verify (lens.proj outerStmtIn) transcript)
  rw [hExecMap, probEvent_map]
  apply probEvent_mono
  intro x hx hOut
  have hxRun :
      some x ∈ support (OptionT.run (run (lens.proj outerStmtIn) transcript V)) := by
    have hxSome :
        some x ∈ support (OptionT.run (OptionT.mk do
          let __do_lift ← init
          (simulateQ impl (run (lens.proj outerStmtIn) transcript V)).run' __do_lift)) := by
      simpa using hx
    change
      some x ∈ support (do
        let __do_lift ← init
        (simulateQ impl (run (lens.proj outerStmtIn) transcript V)).run' __do_lift) at hxSome
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hxSome
    rcases hxSome with ⟨s, hs, hState⟩
    exact OptionT.mem_support_run_simulateQ_run'_subset
      (impl := impl) (oa := run (lens.proj outerStmtIn) transcript V)
      (s := s) hState
  have hCompat : V.compatStatement lens outerStmtIn x :=
    ⟨transcript, hxRun⟩
  contrapose! hOut
  exact lensSound.lift_sound outerStmtIn x hCompat hOut

/-- The outer state function after lifting invokes the inner state function on the projected
  input, and lifts the output -/
def Verifier.StateFunction.liftContext
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (stF : V.StateFunction init impl innerLangIn innerLangOut) :
      (V.liftContext lens).StateFunction init impl outerLangIn outerLangOut
where
  toFun := fun m outerStmtIn transcript =>
    if hm : m = 0 then outerStmtIn ∈ outerLangIn else stF m (lens.proj outerStmtIn) transcript
  toFun_empty := fun stmt => by
    simp
  toFun_next := fun m hDir outerStmtIn transcript hStmt msg => by
    cases n with
    | zero => exact Fin.elim0 m
    | succ n =>
        cases m using Fin.cases with
        | zero =>
          change pSpec.dir 0 = .P_to_V at hDir
          change outerStmtIn ∉ outerLangIn at hStmt
          have hInnerNot : lens.proj outerStmtIn ∉ innerLangIn :=
            lensSound.proj_sound _ hStmt
          have hEmpty : ¬ stF 0 (lens.proj outerStmtIn) default := by
            have hEq := stF.toFun_empty (lens.proj outerStmtIn)
            rw [← hEq]
            exact hInnerNot
          convert stF.toFun_next 0 hDir (lens.proj outerStmtIn) default hEmpty msg using 1 <;>
            simp
        | succ j =>
          convert stF.toFun_next j.succ hDir (lens.proj outerStmtIn) transcript hStmt msg using 1 <;>
            simp
  toFun_full := fun outerStmtIn transcript hStmt => by
    by_cases hn : n = 0
    · subst hn
      change outerStmtIn ∉ outerLangIn at hStmt
      have hOuterNot : outerStmtIn ∉ outerLangIn := by
        exact hStmt
      have hInnerNot : lens.proj outerStmtIn ∉ innerLangIn :=
        lensSound.proj_sound _ hOuterNot
      let defaultTr : Transcript (Fin.last 0) pSpec := by
        change Transcript 0 pSpec
        exact default
      have hTr : transcript = defaultTr := by
        ext i
        exact Fin.elim0 i
      have hEmptyLast : ¬ stF (.last 0) (lens.proj outerStmtIn) transcript := by
        rw [hTr]
        dsimp
        have hEq := stF.toFun_empty (lens.proj outerStmtIn)
        intro hState
        exact hInnerNot (hEq.mpr hState)
      have hInnerFull := stF.toFun_full (lens.proj outerStmtIn)
        transcript hEmptyLast
      rw [hTr]
      rw [hTr] at hInnerFull
      have hLift :=
        Verifier.liftContext_probEvent_le
          (lens := lens) (V := V)
          (outerLangIn := outerLangIn) (outerLangOut := outerLangOut)
          (innerLangIn := innerLangIn) (innerLangOut := innerLangOut)
          (init := init) (impl := impl) outerStmtIn defaultTr
      refine le_antisymm ?_ (zero_le _)
      exact le_trans hLift (by
        rw [hInnerFull])
    · have hInnerNot : ¬ stF (.last n) (lens.proj outerStmtIn) transcript := by
        simp [hn] at hStmt
        exact hStmt
      have hInnerFull := stF.toFun_full (lens.proj outerStmtIn) transcript hInnerNot
      have hLift :=
        Verifier.liftContext_probEvent_le
          (lens := lens) (V := V)
          (outerLangIn := outerLangIn) (outerLangOut := outerLangOut)
          (innerLangIn := innerLangIn) (innerLangOut := innerLangOut)
          (init := init) (impl := impl) outerStmtIn transcript
      refine le_antisymm ?_ (zero_le _)
      exact le_trans hLift (by
        rw [hInnerFull])

section Theorems

/- Theorems about liftContext interacting with reduction execution and security properties -/

namespace Prover

/- Breaking down the intertwining of liftContext and prover execution -/

/-- Lifting the prover intertwines with the process round function -/
theorem liftContext_processRound
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {i : Fin n}
    {P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec}
    {resultRound : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript i.castSucc × (P.liftContext lens).PrvState i.castSucc)} :
      (P.liftContext lens).processRound i resultRound
      = do
        let ⟨transcript, prvState, outerStmtIn, outerWitIn⟩ ← resultRound
        let ⟨newTranscript, newPrvState⟩ ← P.processRound i (do return ⟨transcript, prvState⟩)
        return ⟨newTranscript, ⟨newPrvState, outerStmtIn, outerWitIn⟩⟩ := by
  unfold processRound liftContext
  simp only [bind_pure_comp]
  congr 1; funext ⟨tr, ps, outerStmtIn', outerWitIn'⟩
  simp only [pure_bind]
  split <;> simp [Functor.map_map, Function.comp, liftM_map, map_bind,
    bind_assoc, pure_bind, bind_map_left, bind_pure_comp]


theorem liftContext_runToRound
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn} {i : Fin (n + 1)}
    (P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      (P.liftContext lens).runToRound i outerStmtIn outerWitIn
      = do
        let ⟨transcript, prvState⟩ ←
          (P.runToRound i).uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨transcript, ⟨prvState, outerStmtIn, outerWitIn⟩⟩ := by
  unfold runToRound Function.uncurry
  dsimp
  induction i using Fin.induction with
  | zero => simp [liftContext]
  | succ i ih =>
    simp only [Fin.induction_succ, ih, bind_pure_comp,
      liftContext_processRound, ChallengeIdx, bind_map_left, Prod.mk.eta]
    simp [processRound]

-- Requires more lemmas about `simulateQ` for logging oracles
theorem liftContext_runWithLogToRound
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn} {i : Fin (n + 1)}
    (P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
      (P.liftContext lens).runWithLogToRound i outerStmtIn outerWitIn
      = do
        let ⟨⟨transcript, prvState⟩, queryLog⟩ ←
          (P.runWithLogToRound i).uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨⟨transcript, ⟨prvState, outerStmtIn, outerWitIn⟩⟩, queryLog⟩ := by
  unfold runWithLogToRound
  induction i using Fin.induction with
  | zero => simp [liftContext, Function.uncurry]
  | succ i ih => simp [liftContext_runToRound, Function.uncurry]

/-- Running the lifted outer prover is equivalent to running the inner prover on the projected
  input, and then integrating the output -/
theorem liftContext_run
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    {P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec} :
      (P.liftContext lens).run outerStmtIn outerWitIn
      = do
        let ⟨fullTranscript, innerCtxOut⟩ ←
          P.run.uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨fullTranscript, lens.lift (outerStmtIn, outerWitIn) innerCtxOut⟩ := by
  simp only [run, liftContext_runToRound]
  simp [liftContext, Function.uncurry]

/-- Lifting the prover intertwines with logging queries of the prover -/
theorem liftContext_runWithLog
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    {P : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec} :
      (P.liftContext lens).runWithLog outerStmtIn outerWitIn
      = do
        let ⟨⟨fullTranscript, innerCtxOut⟩, queryLog⟩ ←
          P.runWithLog.uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨⟨fullTranscript, lens.lift (outerStmtIn, outerWitIn) innerCtxOut⟩, queryLog⟩ := by
  rw [runWithLog, liftContext_run]
  simp [Function.uncurry]
  congr

end Prover

namespace Reduction

theorem liftContext_run
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    {R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec} :
      (R.liftContext lens).run outerStmtIn outerWitIn = do
        let ⟨⟨fullTranscript, innerCtxOut⟩, verInnerStmtOut⟩ ←
          R.run.uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨⟨fullTranscript, lens.lift (outerStmtIn, outerWitIn) innerCtxOut⟩ ,
                lens.stmt.lift outerStmtIn verInnerStmtOut⟩ := by
  apply OptionT.ext
  simp [run, liftContext, Prover.liftContext_run, Verifier.liftContext, Verifier.run,
    Function.uncurry, OptionT.run_bind, OptionT.run_map, Functor.map_map, Function.comp]

theorem liftContext_runWithLog
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    {R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec} :
      (R.liftContext lens).runWithLog outerStmtIn outerWitIn = do
        let ⟨⟨⟨fullTranscript, innerCtxOut⟩, verInnerStmtOut⟩, queryLog⟩ ←
          R.runWithLog.uncurry (lens.proj (outerStmtIn, outerWitIn))
        return ⟨⟨⟨fullTranscript, lens.lift (outerStmtIn, outerWitIn) innerCtxOut⟩,
                lens.stmt.lift outerStmtIn verInnerStmtOut⟩, queryLog⟩ := by
  apply OptionT.ext
  simp [runWithLog, liftContext, Prover.liftContext_runWithLog, Verifier.liftContext,
    Verifier.run, Function.uncurry, OptionT.run_bind, OptionT.run_map, Functor.map_map]
  congr 1

end Reduction

variable [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
  {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}

namespace Reduction

variable
    {R : Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec}
    {completenessError : ℝ≥0}
    {lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    [lensComplete : lens.IsComplete outerRelIn innerRelIn outerRelOut innerRelOut
      (R.compatContext lens)]

/-- Lifting the reduction preserves completeness, assuming the lens satisfies its completeness
  conditions
-/
theorem liftContext_completeness
    (h : R.completeness init impl innerRelIn innerRelOut completenessError) :
      (R.liftContext lens).completeness init impl outerRelIn outerRelOut completenessError := by
  unfold completeness at h ⊢
  intro outerStmtIn outerWitIn hRelIn
  let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
    impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl
  let f :
      ((FullTranscript pSpec × InnerStmtOut × InnerWitOut) × InnerStmtOut) →
        ((FullTranscript pSpec × OuterStmtOut × OuterWitOut) × OuterStmtOut) :=
    fun x => ((x.1.1, lens.lift (outerStmtIn, outerWitIn) x.1.2), lens.stmt.lift outerStmtIn x.2)
  have hExecMap :
      OptionT.mk (do
        let __do_lift ← init
        (simulateQ pImpl (((R.liftContext lens).run outerStmtIn outerWitIn).run)).run'
          __do_lift) =
        f <$> OptionT.mk (do
          let __do_lift ← init
          (simulateQ pImpl
            ((R.run (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn))).run)).run'
            __do_lift) := by
    rw [Reduction.liftContext_run]
    change OptionT.mk (do
        let __do_lift ← init
        (simulateQ pImpl
          ((f <$> R.run (lens.stmt.proj outerStmtIn)
            (lens.wit.proj (outerStmtIn, outerWitIn))).run)).run' __do_lift) =
      f <$> OptionT.mk (do
        let __do_lift ← init
        (simulateQ pImpl
          ((R.run (lens.stmt.proj outerStmtIn)
            (lens.wit.proj (outerStmtIn, outerWitIn))).run)).run' __do_lift)
    exact OptionT.mk_simulateQ_run'_map_stateful
      (impl := pImpl)
      (init := init)
      (f := f)
      (mx := R.run (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn)))
  have hR :
      Pr[(fun x ↦
          match x with
          | ((_, prvStmtOut, witOut), stmtOut) => (stmtOut, witOut) ∈ innerRelOut ∧ prvStmtOut = stmtOut) |
          OptionT.mk do
            let __do_lift ← init
            (simulateQ pImpl
              ((R.run (lens.stmt.proj outerStmtIn)
                (lens.wit.proj (outerStmtIn, outerWitIn))).run)).run' __do_lift] ≥
        1 - ↑completenessError := by
    simpa [pImpl] using
      h (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn))
        (lensComplete.proj_complete _ _ hRelIn)
  change
      Pr[(fun x ↦
          match x with
          | ((_, prvStmtOut, witOut), stmtOut) => (stmtOut, witOut) ∈ outerRelOut ∧ prvStmtOut = stmtOut) |
          OptionT.mk do
            let __do_lift ← init
            (simulateQ pImpl (((R.liftContext lens).run outerStmtIn outerWitIn).run)).run'
              __do_lift] ≥ 1 - ↑completenessError
  rw [hExecMap]
  refine le_trans hR ?_
  rw [probEvent_map]
  apply probEvent_mono
  intro x hx
  simp [f]
  intro hInnerRelOut hEqStmt
  have hxRun :
      x ∈ support (R.run (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn))) := by
    have hxSome :
        some x ∈ support (OptionT.run (OptionT.mk do
          let __do_lift ← init
          (simulateQ pImpl
            (R.run (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn)))).run'
              __do_lift)) := by
      exact (OptionT.mem_support_iff _ _).1 hx
    change
      some x ∈ support (do
        let __do_lift ← init
        (simulateQ pImpl
          (R.run (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn)))).run'
            __do_lift) at hxSome
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hxSome
    rcases hxSome with ⟨s, hs, hState⟩
    exact OptionT.mem_support_run_simulateQ_run'_subset
      (impl := pImpl)
      (oa := R.run (lens.stmt.proj outerStmtIn) (lens.wit.proj (outerStmtIn, outerWitIn)))
      (s := s) hState
  refine ⟨?_, ?_⟩
  · have hCompat : compatContext lens R (outerStmtIn, outerWitIn) (x.2, x.1.2.2) := by
      refine ⟨x, hxRun, ?_⟩
      change x.1.2 = (x.2, x.1.2.2)
      ext <;> simp [hEqStmt]
    have hLift :=
      lensComplete.lift_complete _ _ _ _ hCompat hRelIn hInnerRelOut
    have hEqCtx : x.1.2 = (x.2, x.1.2.2) := by
      ext <;> simp [hEqStmt]
    change (lens.stmt.lift outerStmtIn x.2,
        lens.wit.toFunB (outerStmtIn, outerWitIn) (x.2, x.1.2.2)) ∈ outerRelOut at hLift
    have hWitEq :
        lens.wit.toFunB (outerStmtIn, outerWitIn) (x.2, x.1.2.2) =
          lens.wit.toFunB (outerStmtIn, outerWitIn) x.1.2 := by
      rw [← hEqCtx]
    rw [← hWitEq]
    exact hLift
  · exact congrArg (fun t => lens.stmt.lift outerStmtIn t) hEqStmt

theorem liftContext_perfectCompleteness
    (h : R.perfectCompleteness init impl innerRelIn innerRelOut) :
      (R.liftContext lens).perfectCompleteness init impl outerRelIn outerRelOut := by
  exact liftContext_completeness h

-- Can't turn the above into an instance because Lean needs to synthesize `innerRelIn` and
-- `innerRelOut` out of thin air.

-- instance [Reduction.IsComplete innerRelIn innerRelOut R completenessError] :
--     R.liftContext.IsComplete outerRelIn outerRelOut completenessError :=
--   ⟨R.liftContext.completeness⟩

-- instance [R.IsPerfectComplete relIn relOut] :
--     R.liftContext.IsPerfectComplete relIn relOut :=
--   ⟨fun _ => R.liftContext.perfectCompleteness _ _ _⟩

end Reduction

namespace Verifier

/-- Lifting a verifier context preserves soundness, assuming the lens satisfies its soundness
  conditions.

  Proof sketch: given a malicious outer prover `outerP`, build the inner adversary
  `outerP.liftContext` along the constant-projection context lens that replays `outerP` on the
  fixed outer input statement. Both the outer and the inner executions then factor through a
  common core (outer prover + inner verifier), so the two acceptance probabilities compare
  pointwise via `lensSound.lift_sound` (with the compatibility witness extracted from the
  support of the core run). -/
theorem liftContext_soundness [Inhabited InnerStmtOut]
    {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
    {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
    {soundnessError : ℝ≥0}
    {lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (h : V.soundness init impl innerLangIn innerLangOut soundnessError) :
      (V.liftContext lens).soundness init impl outerLangIn outerLangOut soundnessError := by
  unfold soundness at h ⊢
  intro WitIn WitOut witIn outerP outerStmtIn hOuterStmtIn
  let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
    QueryImpl.addLift impl challengeQueryImpl
  -- The inner adversary: replay `outerP` on the fixed `outerStmtIn`.
  let innerPLens : Context.Lens InnerStmtIn InnerStmtOut OuterStmtIn OuterStmtOut
      WitIn WitOut WitIn WitOut := {
    stmt := (fun _ => outerStmtIn) ⇆ (fun _ _ => (default : InnerStmtOut))
    wit := Prod.snd ⇆ (fun _ => Prod.snd)
  }
  let innerP : Prover oSpec InnerStmtIn WitIn InnerStmtOut WitOut pSpec :=
    outerP.liftContext innerPLens
  have h' := h WitIn WitOut witIn innerP (lens.proj outerStmtIn)
    (lensSound.proj_sound _ hOuterStmtIn)
  refine le_trans ?_ h'
  -- Common core: outer prover + inner verifier.
  let core : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
      ((FullTranscript pSpec × OuterStmtOut × WitOut) × InnerStmtOut) := do
    let prResult ← outerP.run outerStmtIn witIn
    let so ← liftM ((V.run (lens.proj outerStmtIn) prResult.1).run)
    return ⟨prResult, ← so.getM⟩
  let fOut : ((FullTranscript pSpec × OuterStmtOut × WitOut) × InnerStmtOut) →
      ((FullTranscript pSpec × OuterStmtOut × WitOut) × OuterStmtOut) :=
    fun x => (x.1, lens.lift outerStmtIn x.2)
  let fIn : ((FullTranscript pSpec × OuterStmtOut × WitOut) × InnerStmtOut) →
      ((FullTranscript pSpec × InnerStmtOut × WitOut) × InnerStmtOut) :=
    fun x => ((x.1.1, (default : InnerStmtOut), x.1.2.2), x.2)
  -- The lifted verifier is the inner verifier followed by the statement lift.
  have hVrun : ∀ tr : FullTranscript pSpec,
      (V.liftContext lens).verify outerStmtIn tr
        = lens.lift outerStmtIn <$> V.verify (lens.proj outerStmtIn) tr := by
    intro tr
    simp only [Verifier.liftContext, bind_pure_comp]
  -- `getM` of a mapped option is the mapped `getM`.
  have hgetM : ∀ (o : Option InnerStmtOut),
      ((Option.map (lens.lift outerStmtIn) o).getM :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) OuterStmtOut)
        = lens.lift outerStmtIn <$> (o.getM :
            OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) InnerStmtOut) := by
    intro o
    cases o with
    | none =>
      apply OptionT.ext
      simp [Option.getM]
    | some a => simp [Option.getM]
  have hOuterRun :
      (Reduction.mk outerP (V.liftContext lens)).run outerStmtIn witIn
        = fOut <$> core := by
    simp only [Reduction.run, Verifier.run, core, fOut, hVrun, OptionT.run_map,
      liftM_map, map_bind, bind_map_left, hgetM, _root_.map_pure]
    simp
  have hInnerRun :
      (Reduction.mk innerP V).run (lens.proj outerStmtIn) witIn
        = fIn <$> core := by
    simp only [Reduction.run, Verifier.run, core, fIn, innerP, innerPLens,
      Prover.liftContext_run, Function.uncurry, map_bind, bind_map_left, _root_.map_pure,
      Context.Lens.lift, Context.Lens.proj]
    apply OptionT.ext
    simp only [bind_pure_comp, liftM_map, OptionT.run_bind, OptionT.run_mk, OptionT.run_map,
      bind_map_left, Option.elimM, Option.elim_some, map_bind]
    congr 1
    funext o
    cases o with
    | none => rfl
    | some pr =>
      simp only [Option.elim]
      congr 1
      funext o2
      cases o2 with
      | none => rfl
      | some so => cases so <;> simp [Option.getM]
  -- Wrapped (probability-level) common core.
  have hExecOut :
      OptionT.mk (do
        let s ← init
        (simulateQ pImpl ((fOut <$> core).run)).run' s)
        = fOut <$> OptionT.mk (do
            let s ← init
            (simulateQ pImpl core.run).run' s) := by
    exact OptionT.mk_simulateQ_run'_map_stateful (impl := pImpl) (init := init)
      (f := fOut) (mx := core)
  have hExecIn :
      OptionT.mk (do
        let s ← init
        (simulateQ pImpl ((fIn <$> core).run)).run' s)
        = fIn <$> OptionT.mk (do
            let s ← init
            (simulateQ pImpl core.run).run' s) := by
    exact OptionT.mk_simulateQ_run'_map_stateful (impl := pImpl) (init := init)
      (f := fIn) (mx := core)
  dsimp only at h' ⊢
  rw [show (Reduction.mk outerP (V.liftContext lens))
      = { prover := outerP, verifier := V.liftContext lens } from rfl] at hOuterRun
  rw [show (Reduction.mk innerP V) = { prover := innerP, verifier := V } from rfl] at hInnerRun
  rw [hOuterRun, hExecOut, hInnerRun, hExecIn]
  rw [probEvent_map, probEvent_map]
  apply probEvent_mono
  intro x hx hOut
  simp only [Function.comp_apply, fIn]
  simp only [Function.comp_apply, fOut] at hOut
  by_contra hNot
  -- Extract the compatibility witness from the support of the core run.
  have hxCore : some x ∈ support (OptionT.run core) := by
    have hxSome : some x ∈ support (OptionT.run (OptionT.mk (do
        let s ← init
        (simulateQ pImpl core.run).run' s))) := (OptionT.mem_support_iff _ _).1 hx
    change some x ∈ support (do
      let s ← init
      (simulateQ pImpl core.run).run' s) at hxSome
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hxSome
    rcases hxSome with ⟨s, _, hState⟩
    exact OptionT.mem_support_run_simulateQ_run'_subset (impl := pImpl) (oa := core)
      (s := s) hState
  have hxV : x.2 ∈ support (V.run (lens.proj outerStmtIn) x.1.1) := by
    have hxInner : some (fIn x) ∈
        support (((Reduction.mk innerP V).run (lens.proj outerStmtIn) witIn)).run := by
      rw [show (Reduction.mk innerP V) = { prover := innerP, verifier := V } from rfl,
        hInnerRun, OptionT.run_map, support_map]
      exact ⟨some x, hxCore, rfl⟩
    have hout := Reduction.verifier_output_mem_run_support
      (reduction := Reduction.mk innerP V) hxInner
    simpa [fIn] using hout
  have hCompat : V.compatStatement lens outerStmtIn x.2 := ⟨x.1.1, hxV⟩
  exact (lensSound.lift_sound outerStmtIn x.2 hCompat hNot) hOut


/-
  Lifting the reduction preserves knowledge soundness, assuming the lens satisfies its knowledge
  soundness conditions

  Note: since knowledge soundness is defined existentially in terms of the extractor, we also cannot
  impose any meaningful compatibility conditions on the witnesses (outer output & inner input),
  hence `compatWit` field is just always true

  (future extensions may define lifting relative to a particular extractor, if needed)
-/
/-
theorem liftContext_knowledgeSoundness [Inhabited InnerStmtOut] [Inhabited InnerWitIn]
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    {knowledgeError : ℝ≥0}
    {stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    {witLens : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    [lensKS : Extractor.Lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (V.compatStatement stmtLens) (fun _ _ => True) ⟨stmtLens, witLens⟩]
    (h : V.knowledgeSoundness init impl innerRelIn innerRelOut knowledgeError) :
      (V.liftContext stmtLens).knowledgeSoundness init impl outerRelIn outerRelOut
        knowledgeError := by
  unfold knowledgeSoundness at h ⊢
  obtain ⟨E, hE⟩ := h
  refine ⟨E.liftContext ⟨stmtLens, witLens⟩, ?_⟩
  intro outerStmtIn outerWitIn outerP
  let innerPLens : Context.Lens InnerStmtIn InnerStmtOut OuterStmtIn OuterStmtOut
      InnerWitIn InnerWitOut OuterWitIn OuterWitOut := {
    stmt := (fun _ => outerStmtIn) ⇆ (fun _ _ => (default : InnerStmtOut))
    wit := (fun _ => outerWitIn) ⇆ (fun _ innerCtxOut =>
      witLens.proj (outerStmtIn, innerCtxOut.2))
  }
  let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
    impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl
  let innerP : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec :=
    outerP.liftContext innerPLens
  let pre :
      OptionT ProbComp
        (((FullTranscript pSpec × OuterStmtOut × OuterWitOut) ×
          QueryLog (oSpec + [pSpec.Challenge]ₒ)) × σ) :=
    OptionT.mk do
      let s ← init
      let a ← (simulateQ pImpl (outerP.runWithLog outerStmtIn outerWitIn)).run s
      pure (some a)
  let sharedRaw :
      (((FullTranscript pSpec × OuterStmtOut × OuterWitOut) ×
          QueryLog (oSpec + [pSpec.Challenge]ₒ)) × σ) →
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (InnerWitIn × InnerStmtOut) :=
    fun a => do
      let ⟨innerStmtOutOpt, verifyQueryLog⟩ ←
        liftM (simulateQ loggingOracle (V.run (stmtLens.proj outerStmtIn) a.1.1.1)).run
      let innerStmtOut ← innerStmtOutOpt.getM
      let innerWitIn ←
        E (stmtLens.proj outerStmtIn)
          (witLens.proj (outerStmtIn, a.1.1.2.2))
          a.1.1.1 a.1.2.fst verifyQueryLog
      return (innerWitIn, innerStmtOut)
  let sharedBranch :
      (((FullTranscript pSpec × OuterStmtOut × OuterWitOut) ×
          QueryLog (oSpec + [pSpec.Challenge]ₒ)) × σ) →
        OptionT ProbComp (InnerWitIn × InnerStmtOut) :=
    fun a =>
      OptionT.mk <| (simulateQ pImpl (sharedRaw a)).run' a.2
  let outerMap :
      (((FullTranscript pSpec × OuterStmtOut × OuterWitOut) ×
          QueryLog (oSpec + [pSpec.Challenge]ₒ)) × σ) →
        InnerWitIn × InnerStmtOut →
          OuterStmtIn × OuterWitIn × OuterStmtOut × OuterWitOut :=
    fun a x =>
      ⟨outerStmtIn,
        witLens.lift (outerStmtIn, a.1.1.2.2) x.1,
        stmtLens.lift outerStmtIn x.2,
        a.1.1.2.2⟩
  let innerMap :
      (((FullTranscript pSpec × OuterStmtOut × OuterWitOut) ×
          QueryLog (oSpec + [pSpec.Challenge]ₒ)) × σ) →
        InnerWitIn × InnerStmtOut →
          InnerStmtIn × InnerWitIn × InnerStmtOut × InnerWitOut :=
    fun a x =>
      ⟨stmtLens.proj outerStmtIn,
        x.1,
        x.2,
        witLens.proj (outerStmtIn, a.1.1.2.2)⟩
  let outerBranch :
      (((FullTranscript pSpec × OuterStmtOut × OuterWitOut) ×
          QueryLog (oSpec + [pSpec.Challenge]ₒ)) × σ) →
        OptionT ProbComp (OuterStmtIn × OuterWitIn × OuterStmtOut × OuterWitOut) :=
    fun a => outerMap a <$> sharedBranch a
  let innerBranch :
      (((FullTranscript pSpec × OuterStmtOut × OuterWitOut) ×
          QueryLog (oSpec + [pSpec.Challenge]ₒ)) × σ) →
        OptionT ProbComp (InnerStmtIn × InnerWitIn × InnerStmtOut × InnerWitOut) :=
    fun a => innerMap a <$> sharedBranch a
  let innerExec :
      OptionT ProbComp (InnerStmtIn × InnerWitIn × InnerStmtOut × InnerWitOut) :=
    OptionT.mk do
      let __do_lift ← init
      (simulateQ pImpl
        (do
          let ⟨⟨⟨transcript, ⟨_, innerWitOut⟩⟩, innerStmtOut⟩, proveQueryLog, verifyQueryLog⟩ ←
            (Reduction.mk innerP V).runWithLog (stmtLens.proj outerStmtIn) (default : InnerWitIn)
          let innerWitIn ←
            E (stmtLens.proj outerStmtIn) innerWitOut transcript proveQueryLog.fst verifyQueryLog
          return (stmtLens.proj outerStmtIn, innerWitIn, innerStmtOut, innerWitOut)).run).run'
            __do_lift
  have hInnerBase := hE (stmtLens.proj outerStmtIn) (default : InnerWitIn) innerP
  have hInner :
      Pr[fun x ↦ (x.1, x.2.1) ∉ innerRelIn ∧ (x.2.2.1, x.2.2.2) ∈ innerRelOut |
          pre >>= innerBranch] ≤ ↑knowledgeError := by
    have hInnerBase' :
        Pr[fun x ↦ (x.1, x.2.1) ∉ innerRelIn ∧ (x.2.2.1, x.2.2.2) ∈ innerRelOut |
            innerExec] ≤ ↑knowledgeError := by
      simpa [innerExec, pImpl] using hInnerBase
    have hInnerExec : innerExec = pre >>= innerBranch := by
      apply OptionT.ext
      simp [innerExec, pre, sharedBranch, innerBranch, innerMap, pImpl, sharedRaw, innerP,
        innerPLens, Reduction.runWithLog, Prover.liftContext_runWithLog, Verifier.run,
        liftM_OptionT_eq, Functor.map_map]
      congr 1
      funext s
      congr 1
      funext a
      erw [simulateQ_bind]
      erw [simulateQ_bind]
      simp [StateT.run_bind]
      congr 1
      funext a_1
      cases hOpt : a_1.1 <;> simp [hOpt, Option.elimM, Functor.map_map, Function.comp]
      rename_i y
      cases hStmt : y.1 with
      | none =>
          simp [hStmt, Option.elimM]
          change pure none =
            (fun a_2 =>
              Option.map
                (fun x =>
                  (stmtLens.proj outerStmtIn, x.1, x.2, witLens.proj (outerStmtIn, a.1.1.2.2)))
                a_2.1) <$>
              (simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
                (pure none :
                  OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option (InnerWitIn × InnerStmtOut)))).run
                a_1.2
          rw [simulateQ_pure]
          simp
      | some innerStmtOut =>
          erw [simulateQ_bind]
          rw [simulateQ_getM_run_some
            (impl := impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
            (x := innerStmtOut)]
          rw [OptionT.simulateQ_getM_some
            (impl := impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
            (x := innerStmtOut)]
          have hRun :=
            StateT.run_pure_some_bind_map
              (s := a_1.2)
              (x := innerStmtOut)
              (mx := simulateQ
                (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
                (OptionT.run
                  (simulateQ
                    (fun t => (liftM (query t) :
                      OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
                    (E (stmtLens.proj outerStmtIn)
                      (witLens.proj (outerStmtIn, a.1.1.2.2))
                      a.1.1.1 a.1.2.fst y.2))))
              (f := fun innerWitIn innerStmtOut =>
                (stmtLens.proj outerStmtIn, innerWitIn, innerStmtOut,
                  witLens.proj (outerStmtIn, a.1.1.2.2)))
          conv_lhs =>
            rw [StateT.run_pure]
            simp only [pure_bind, Option.elim_some]
            erw [_root_.simulateQ_map]
            rw [StateT.run_map]
          conv_rhs =>
            change
              (fun a_2 =>
                Option.map
                  (fun x =>
                    (stmtLens.proj outerStmtIn, x.1, x.2,
                      witLens.proj (outerStmtIn, a.1.1.2.2)))
                  a_2.1) <$>
                ((do
                  let y_1 ← (pure innerStmtOut : OptionT (StateT σ ProbComp) InnerStmtOut)
                  simulateQ
                    (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
                    (((fun innerWitIn : InnerWitIn => (innerWitIn, y_1)) <$>
                      simulateQ
                        (fun t => (liftM (query t) :
                          OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
                        (E (stmtLens.proj outerStmtIn)
                          (witLens.proj (outerStmtIn, a.1.1.2.2))
                          a.1.1.1 a.1.2.fst y.2)) :
                      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
                        (InnerWitIn × InnerStmtOut))
                ).run a_1.2)
            rw [StateT.run_optiont_pure_bind_simulateQ_map
              (impl := impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
              (x := innerStmtOut)
              (mx := simulateQ
                (fun t => (liftM (query t) :
                  OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
                (E (stmtLens.proj outerStmtIn)
                  (witLens.proj (outerStmtIn, a.1.1.2.2))
                  a.1.1.1 a.1.2.fst y.2))
              (s := a_1.2)]
            rw [StateT.run_simulateQ_optiont_map
              (impl := impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
              (f := fun innerWitIn => (innerWitIn, innerStmtOut))
              (mx := simulateQ
                (fun t => (liftM (query t) :
                  OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
                (E (stmtLens.proj outerStmtIn)
                  (witLens.proj (outerStmtIn, a.1.1.2.2))
                  a.1.1.1 a.1.2.fst y.2))
              (s := a_1.2)]
          have hRun' := hRun
          rw [StateT.run_pure] at hRun'
          simp only [pure_bind, Option.elim_some] at hRun'
          conv_lhs =>
            simp only [Functor.map_map, Function.comp]
          exact hRun'
    rw [← hInnerExec]
    exact hInnerBase'
  have hCompare :
      Pr[fun x ↦ (x.1, x.2.1) ∉ outerRelIn ∧ (x.2.2.1, x.2.2.2) ∈ outerRelOut |
          pre >>= outerBranch] ≤
        Pr[fun x ↦ (x.1, x.2.1) ∉ innerRelIn ∧ (x.2.2.1, x.2.2.2) ∈ innerRelOut |
          pre >>= innerBranch] := by
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine ENNReal.tsum_le_tsum fun a => ?_
    by_cases ha : a ∈ support pre
    · refine mul_le_mul' le_rfl ?_
      rw [probEvent_map, probEvent_map]
      apply probEvent_mono
      intro x hx
      simp [outerMap, innerMap]
      intro hOuterIn hOuterOut
      have hxSome :
          some x ∈ support (OptionT.run (sharedBranch a)) := by
        exact (OptionT.mem_support_iff _ _).1 hx
      change
        some x ∈ support ((simulateQ pImpl (sharedRaw a)).run' a.2) at hxSome
      have hxRaw :
          some x ∈ support (OptionT.run (sharedRaw a)) := by
        exact OptionT.mem_support_run_simulateQ_run'_subset
          (impl := pImpl)
          (oa := sharedRaw a)
          (s := a.2) hxSome
      have hCompat : V.compatStatement stmtLens outerStmtIn x.2 := by
        refine ⟨a.1.1.1, ?_⟩
        have hxBind :
            some x ∈ support
              (Option.elimM
                ((liftM (simulateQ loggingOracle
                  (V.run (stmtLens.proj outerStmtIn) a.1.1.1)).run :
                  OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
                    (Option InnerStmtOut × QueryLog oSpec)).run)
                (pure none) fun (y : Option InnerStmtOut × QueryLog oSpec) =>
                Option.elimM
                  ((y.1.getM :
                    OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) InnerStmtOut).run)
                  (pure none) fun innerStmtOut =>
                  (Option.map fun innerWitIn => (innerWitIn, innerStmtOut)) <$>
                    simulateQ (fun t ↦ liftM (query t))
                      (OptionT.run (E (stmtLens.proj outerStmtIn)
                          (witLens.proj (outerStmtIn, a.1.1.2.2))
                          a.1.1.1 a.1.2.fst y.2))) := by
          simpa [sharedRaw, OptionT.run_bind, OptionT.run_liftM_run] using hxRaw
        simp only [Option.elimM] at hxBind
        rw [_root_.mem_support_bind_iff] at hxBind
        rcases hxBind with ⟨y, hy, hxCont⟩
        cases hY : y with
        | none =>
            have : False := by
              simpa [hY] using hxCont
            exact False.elim this
        | some y =>
            rcases y with ⟨innerStmtOutOpt, verifyQueryLog⟩
            have hyBase :
                (innerStmtOutOpt, verifyQueryLog) ∈ support ((simulateQ loggingOracle
                  (V.run (stmtLens.proj outerStmtIn) a.1.1.1)).run) := by
              let verifyRun : OracleComp oSpec (Option InnerStmtOut × QueryLog oSpec) :=
                (simulateQ loggingOracle (V.run (stmtLens.proj outerStmtIn) a.1.1.1)).run
              have hyLiftRun :
                  some (innerStmtOutOpt, verifyQueryLog) ∈ support
                    ((liftM verifyRun :
                      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
                        (Option InnerStmtOut × QueryLog oSpec)).run) := by
                have hy' := hy
                rw [hY] at hy'
                exact hy'
              have hyLiftComp :
                  (innerStmtOutOpt, verifyQueryLog) ∈ support
                    (simulateQ
                      (fun t ↦
                        (liftM (query (spec := oSpec) t) :
                          OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
                      verifyRun) := by
                have hyRunMap := hyLiftRun
                change some (innerStmtOutOpt, verifyQueryLog) ∈ support
                  ((monadLift verifyRun :
                    OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
                      (Option InnerStmtOut × QueryLog oSpec)).run) at hyRunMap
                have hrun :
                    (monadLift verifyRun :
                      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
                        (Option InnerStmtOut × QueryLog oSpec)).run =
                      some <$>
                        simulateQ
                          (fun t ↦
                            (liftM (query (spec := oSpec) t) :
                              OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
                          verifyRun := by
                  change
                    simulateQ
                      (fun t ↦
                        (liftM (query (spec := oSpec) t) :
                          OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
                      ((monadLift verifyRun :
                        OptionT (OracleComp oSpec)
                          (Option InnerStmtOut × QueryLog oSpec)).run) =
                    some <$>
                      simulateQ
                        (fun t ↦
                          (liftM (query (spec := oSpec) t) :
                            OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
                        verifyRun
                  rw [OptionT.run_monadLift
                    (m := OracleComp oSpec)
                    (n := OracleComp oSpec) (x := verifyRun)]
                  erw [_root_.simulateQ_map]
                  rw [monadLift_eq_self]
                rw [hrun] at hyRunMap
                rw [support_map, Set.mem_image] at hyRunMap
                rcases hyRunMap with ⟨u, hu, huEq⟩
                cases huEq
                exact hu
              have hVerifyRunSupport :
                  support
                    (simulateQ
                      (fun t ↦
                        (liftM (query (spec := oSpec) t) :
                          OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
                      verifyRun) = support verifyRun := by
                apply support_simulateQ_eq_OracleComp_of_superSpec
                  (spec := oSpec + [pSpec.Challenge]ₒ)
                  (superSpec := oSpec)
                  (so := fun t ↦
                    (liftM (query (spec := oSpec) t) :
                      OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
                  (oa := verifyRun)
                intro β q
                rw [QueryImpl.mapQuery]
                rfl
              rw [hVerifyRunSupport] at hyLiftComp
              exact hyLiftComp
            cases hStmtOpt : innerStmtOutOpt with
            | none =>
                have : False := by
                  simpa only [hY, hStmtOpt, Option.elim_some, Option.getM_none, OptionT.run_failure,
                    pure_bind, Option.elim_none, support_pure, Set.mem_singleton_iff,
                    reduceCtorEq] using hxCont
                exact False.elim this
            | some innerStmtOut =>
                have hxCont' :
                    some x ∈ support
                      ((Option.map fun innerWitIn => (innerWitIn, innerStmtOut)) <$>
                        simulateQ
                          (fun t ↦
                            (liftM (query (spec := oSpec) t) :
                              OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
                          (OptionT.run (E (stmtLens.proj outerStmtIn)
                            (witLens.proj (outerStmtIn, a.1.1.2.2))
                            a.1.1.1 a.1.2.fst verifyQueryLog))) := by
                  simpa [hY, hStmtOpt] using hxCont
                simp only [support_map, Set.mem_image] at hxCont'
                rcases hxCont' with ⟨innerWitInOpt, _, hxEq⟩
                cases hWitOpt : innerWitInOpt with
                | none =>
                    simp [hWitOpt] at hxEq
                | some innerWitIn =>
                    have hxPair : (innerWitIn, innerStmtOut) = x := by
                      apply Option.some.inj
                      simpa [hWitOpt] using hxEq
                    have hxEqStmt : innerStmtOut = x.2 := by
                      exact congrArg Prod.snd hxPair
                    have hyRun :
                        (some x.2, verifyQueryLog) ∈ support
                          ((simulateQ loggingOracle
                            (V.run (stmtLens.proj outerStmtIn) a.1.1.1)).run) := by
                      simpa [hStmtOpt, hxEqStmt] using hyBase
                    have hxVerify :
                        some x.2 ∈ support (OptionT.run (V.run (stmtLens.proj outerStmtIn) a.1.1.1)) := by
                      exact mem_support_loggingOracle_run_fst
                        (oa := OptionT.run (V.run (stmtLens.proj outerStmtIn) a.1.1.1))
                        (x := some x.2) (log := verifyQueryLog) hyRun
                    exact (OptionT.mem_support_iff _ _).2 hxVerify
      refine ⟨?_, ?_⟩
      · intro hInnerIn
        exact hOuterIn
          (lensKS.lift_knowledgeSound outerStmtIn a.1.1.2.2 x.1 (by simp) hInnerIn)
      · exact lensKS.proj_knowledgeSound outerStmtIn x.2 a.1.1.2.2 hCompat hOuterOut
    · simp [probOutput_eq_zero_of_not_mem_support ha]
  have hOuterExec :
      OptionT.mk (do
        let __do_lift ← init
        (simulateQ pImpl
          (do
            let ⟨⟨⟨transcript, ⟨_, outerWitOut⟩⟩, outerStmtOut⟩,
                proveQueryLog, verifyQueryLog⟩ ←
              (Reduction.mk outerP (V.liftContext stmtLens)).runWithLog outerStmtIn outerWitIn
            let outerWitIn' ←
              (E.liftContext ⟨stmtLens, witLens⟩)
                outerStmtIn outerWitOut transcript proveQueryLog.fst verifyQueryLog
            return (outerStmtIn, outerWitIn', outerStmtOut, outerWitOut)).run).run'
          __do_lift) =
        pre >>= outerBranch := by
    apply OptionT.ext
    simp [pre, outerBranch, outerMap, sharedBranch, sharedRaw, pImpl, Reduction.runWithLog,
      Verifier.liftContext, Verifier.run, Extractor.Straightline.liftContext,
      liftM_OptionT_eq, Functor.map_map]
    congr 1
    funext s
    congr 1
    funext a
    erw [simulateQ_bind]
    erw [simulateQ_bind]
    simp [StateT.run_bind]
    congr 1
    funext a_1
    cases hOpt : a_1.1 <;> simp [hOpt, Option.elimM, Functor.map_map, Function.comp]
    rename_i y
    cases hStmt : y.1 with
    | none =>
        simp [hStmt, Option.elimM]
        change pure none =
          (fun a_2 =>
            Option.map
              (fun x =>
                (outerStmtIn, witLens.lift (outerStmtIn, a.1.1.2.2) x.1,
                  stmtLens.lift outerStmtIn x.2, a.1.1.2.2))
              a_2.1) <$>
            (simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
              (pure none :
                OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option (InnerWitIn × InnerStmtOut)))).run
              a_1.2
        rw [simulateQ_pure]
        simp
    | some innerStmtOut =>
        erw [simulateQ_bind]
        simp
        have hRun :=
          StateT.run_pure_some_bind_map
            (s := a_1.2)
            (x := innerStmtOut)
            (mx := simulateQ
              (impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
              (OptionT.run
                (simulateQ
                  (fun t => (liftM (query t) :
                    OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
                  (E (stmtLens.proj outerStmtIn)
                    (witLens.proj (outerStmtIn, a.1.1.2.2))
                    a.1.1.1 a.1.2.fst y.2))))
            (f := fun innerWitIn innerStmtOut =>
              (outerStmtIn, witLens.lift (outerStmtIn, a.1.1.2.2) innerWitIn,
                stmtLens.lift outerStmtIn innerStmtOut, a.1.1.2.2))
        conv_rhs =>
          erw [_root_.simulateQ_pure]
          rw [StateT.run_pure]
          simp only [pure_bind, Option.elim_some]
          rw [StateT.run_simulateQ_optiont_map
            (impl := impl + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
            (f := fun innerWitIn => (innerWitIn, innerStmtOut))
            (mx := simulateQ
              (fun t => (liftM (query t) :
                OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
              (E (stmtLens.proj outerStmtIn)
                (witLens.proj (outerStmtIn, a.1.1.2.2))
                a.1.1.1 a.1.2.fst y.2))
            (s := a_1.2)]
        have hRun' := hRun
        rw [StateT.run_pure] at hRun'
        simp only [pure_bind, Option.elim_some] at hRun'
        exact hRun'
  change
    Pr[fun x ↦ (x.1, x.2.1) ∉ outerRelIn ∧ (x.2.2.1, x.2.2.2) ∈ outerRelOut |
      OptionT.mk do
        let __do_lift ← init
        (simulateQ pImpl
          (do
            let ⟨⟨⟨transcript, ⟨_, outerWitOut⟩⟩, outerStmtOut⟩,
                proveQueryLog, verifyQueryLog⟩ ←
              (Reduction.mk outerP (V.liftContext stmtLens)).runWithLog outerStmtIn outerWitIn
            let outerWitIn' ←
              (E.liftContext ⟨stmtLens, witLens⟩)
                outerStmtIn outerWitOut transcript proveQueryLog.fst verifyQueryLog
            return (outerStmtIn, outerWitIn', outerStmtOut, outerWitOut)).run).run'
          __do_lift] ≤ ↑knowledgeError
	  rw [hOuterExec]
	  exact le_trans hCompare hInner
-/

/-
  Lifting the reduction preserves round-by-round soundness, assuming the lens satisfies its
  soundness conditions
-/
theorem liftContext_rbr_soundness [Inhabited InnerStmtOut]
    {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
    {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    {lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    -- Future work: figure out the right compatibility relation for the IsSound condition.
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (h : V.rbrSoundness init impl innerLangIn innerLangOut rbrSoundnessError) :
      (V.liftContext lens).rbrSoundness init impl outerLangIn outerLangOut rbrSoundnessError := by
  unfold rbrSoundness at h ⊢
  obtain ⟨stF, h⟩ := h
  simp at h ⊢
  refine ⟨stF.liftContext lens (lensSound := lensSound), ?_⟩
  intro outerStmtIn hOuterStmtIn WitIn WitOut witIn outerP roundIdx hDir
  let innerPLens : Context.Lens InnerStmtIn InnerStmtOut OuterStmtIn OuterStmtOut
      WitIn WitOut WitIn WitOut := {
    stmt := (fun _ => outerStmtIn) ⇆ (fun _ _ => (default : InnerStmtOut))
    wit := Prod.snd ⇆ (fun _ => Prod.snd)
  }
  let innerP : Prover oSpec InnerStmtIn WitIn InnerStmtOut WitOut pSpec :=
    outerP.liftContext innerPLens
  have h' := h (lens.proj outerStmtIn) (lensSound.proj_sound _ hOuterStmtIn)
    WitIn WitOut witIn innerP roundIdx hDir
  refine le_trans ?_ h'
  simp [innerP, innerPLens, Prover.liftContext_runToRound, Verifier.StateFunction.liftContext]
  apply probEvent_mono
  intro x hx hBad
  rcases hBad with ⟨hPrev, hNext⟩
  refine ⟨?_, hNext⟩
  by_cases hZero : roundIdx.castSucc = 0
  · have hInnerNot : lens.proj outerStmtIn ∉ innerLangIn :=
      lensSound.proj_sound _ hOuterStmtIn
    have hEq := stF.toFun_empty (lens.proj outerStmtIn)
    rw! (castMode := .all) [hZero] at hPrev ⊢
    simp at hPrev
    have hTr : hZero ▸ x.1 = default := by
      ext i
      exact Fin.elim0 i
    have hTr' : (hZero ▸ x).1 = default := by
      ext i
      exact Fin.elim0 i
    rw [hTr']
    intro hState
    exact hInnerNot (hEq.mpr hState)
  · simp [hZero] at hPrev
    exact hPrev

/-
  The outer knowledge state function after lifting. The underlying `toFun` dispatches on the
  round index:
  - At round 0, the outer WitMid is `OuterWitIn`, and we check `(outerStmtIn, witMid) ∈ outerRelIn`
  - At round j+1, the outer WitMid is `InnerWitMid (j+1) × OuterWitOut`, and we delegate to the
    inner knowledge state function on the first component.
-/
def KnowledgeStateFunction.liftContext
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    {stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    {witLens : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    [lensKS : Extractor.Lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (V.compatStatement stmtLens) (fun _ _ => True) ⟨stmtLens, witLens⟩]
    {InnerWitMid : Fin (n + 1) → Type}
    (innerE : Extractor.RoundByRound oSpec InnerStmtIn InnerWitIn InnerWitOut pSpec InnerWitMid)
    (innerKSF : V.KnowledgeStateFunction init impl innerRelIn innerRelOut innerE) :
      (V.liftContext stmtLens).KnowledgeStateFunction init impl outerRelIn outerRelOut
        (innerE.liftContext ⟨stmtLens, witLens⟩) where
  toFun := fun m outerStmtIn transcript =>
    match hm : m with
    | ⟨0, _⟩ => fun (outerWitIn : OuterWitIn) => (outerStmtIn, outerWitIn) ∈ outerRelIn
    | ⟨j + 1, hj⟩ => fun (witMid : InnerWitMid ⟨j + 1, hj⟩ × OuterWitOut) =>
        innerKSF ⟨j + 1, hj⟩ (stmtLens.proj outerStmtIn) transcript witMid.1
  toFun_empty := fun outerStmtIn outerWitIn => by
    rfl
  toFun_next := fun m hDir outerStmtIn tr msg => by
    cases n with
    | zero => exact Fin.elim0 m
    | succ n =>
      cases m using Fin.cases with
      | zero =>
        intro ⟨innerWitMid, outerWitOut⟩ hSucc
        -- At round 0 → 1, the outer extractMid returns
        -- `witLens.lift (outerStmtIn, outerWitOut) innerWitIn` where innerWitIn is extracted
        simp only [Extractor.RoundByRound.liftContext]
        -- hSucc : innerKSF 1 (stmtLens.proj outerStmtIn) (tr.concat msg) innerWitMid
        -- Goal: (outerStmtIn, extractMid ... ) ∈ outerRelIn
        -- The extractMid at round 0 produces:
        --   witLens.lift (outerStmtIn, outerWitOut) (cast innerE.eqIn (innerE.extractMid 0 ...))
        have hInner := innerKSF.toFun_next 0 hDir (stmtLens.proj outerStmtIn) tr msg
          innerWitMid hSucc
        -- hInner : innerKSF 0 (stmtLens.proj outerStmtIn) tr (innerE.extractMid 0 ... )
        -- From toFun_empty of innerKSF:
        let defaultTr : Transcript (Fin.castSucc 0) pSpec := by
          intro i
          exact Fin.elim0 i
        have hTr : tr = defaultTr := by
          ext i
          exact Fin.elim0 i
        rw [hTr] at hInner
        have hInnerIn :=
          (innerKSF.toFun_empty (stmtLens.proj outerStmtIn)
            (innerE.extractMid 0 (stmtLens.proj outerStmtIn) (tr.concat msg) innerWitMid)).mpr
              hInner
        -- hInnerIn: (stmtLens.proj outerStmtIn, cast innerE.eqIn ...) ∈ innerRelIn
        exact lensKS.lift_knowledgeSound outerStmtIn outerWitOut
          (cast innerE.eqIn (innerE.extractMid 0 (stmtLens.proj outerStmtIn)
            (tr.concat msg) innerWitMid))
          (by simp)
          hInnerIn
      | succ j =>
        intro ⟨innerWitMid, outerWitOut⟩ hSucc
        simp only [Extractor.RoundByRound.liftContext]
        exact innerKSF.toFun_next j.succ hDir (stmtLens.proj outerStmtIn) tr msg
          innerWitMid hSucc
  toFun_full := fun outerStmtIn tr outerWitOut hProb => by
    -- Need to show: kSF (.last n) outerStmtIn tr (innerE.extractOut ... , outerWitOut)
    -- which is: innerKSF (.last n) (stmtLens.proj outerStmtIn) tr (cast ... innerE.extractOut ...)
    -- The lifted verifier maps output through stmtLens.lift
    -- hProb : probability that (stmtOut, outerWitOut) ∈ outerRelOut is > 0
    --   where stmtOut comes from (V.liftContext stmtLens).run outerStmtIn tr
    -- We need to show: innerKSF (.last n) projects this down
    simp only [Verifier.liftContext, Verifier.run] at hProb
    -- The verifier run of V.liftContext stmtLens produces stmtLens.lift outerStmtIn <$> innerRun
    -- So if (stmtLens.lift outerStmtIn innerStmtOut, outerWitOut) ∈ outerRelOut with positive prob,
    -- by lensKS.proj_knowledgeSound, (innerStmtOut, witLens.proj ...) ∈ innerRelOut
    have hInnerProb :
        Pr[fun stmtOut => (stmtOut, witLens.proj (outerStmtIn, outerWitOut)) ∈ innerRelOut
        | OptionT.mk do (simulateQ impl (V.run (stmtLens.proj outerStmtIn) tr)).run' (← init)]
          > 0 := by
      rw [gt_iff_lt, probEvent_pos_iff] at hProb ⊢
      obtain ⟨outerStmtOut, hMem, hRel⟩ := hProb
      have hMemSome :
          some outerStmtOut ∈
            support
              (OptionT.run (OptionT.mk do
                let __do_lift ← init
                (simulateQ impl ((V.liftContext stmtLens).run outerStmtIn tr)).run' __do_lift)) := by
        exact (OptionT.mem_support_iff _ _).1 hMem
      let innerExec : OptionT ProbComp InnerStmtOut :=
        OptionT.mk do
          let __do_lift ← init
          (simulateQ impl (V.run (stmtLens.proj outerStmtIn) tr)).run' __do_lift
      have hExecMap :
          OptionT.mk (do
            let __do_lift ← init
            (simulateQ impl ((V.liftContext stmtLens).run outerStmtIn tr)).run' __do_lift) =
            stmtLens.lift outerStmtIn <$> innerExec := by
        change
          OptionT.mk (do
            let __do_lift ← init
            (simulateQ impl
              (stmtLens.lift outerStmtIn <$>
                V.run (stmtLens.proj outerStmtIn) tr : OptionT (OracleComp oSpec) OuterStmtOut)).run'
                __do_lift) =
            stmtLens.lift outerStmtIn <$> innerExec
        exact OptionT.mk_simulateQ_run'_map_stateful
          (impl := impl) (init := init)
          (f := stmtLens.lift outerStmtIn)
          (mx := V.verify (stmtLens.proj outerStmtIn) tr)
      obtain ⟨innerStmtOut, hInnerMem, hEqVal⟩ :
          ∃ innerStmtOut ∈ support innerExec,
            stmtLens.lift outerStmtIn innerStmtOut = outerStmtOut := by
        have hMemMap :
            some outerStmtOut ∈ support (OptionT.run (stmtLens.lift outerStmtIn <$> innerExec)) := by
          rw [← hExecMap]
          exact hMemSome
        rw [OptionT.run_map, support_map, Set.mem_image] at hMemMap
        rcases hMemMap with ⟨x, hx, hxEq⟩
        cases hX : x with
        | none =>
            simp [hX] at hxEq
        | some innerStmtOut =>
            refine ⟨innerStmtOut, ?_, ?_⟩
            · change innerStmtOut ∈ support innerExec
              have hxSome : some innerStmtOut ∈ support (OptionT.run innerExec) := by
                rw [hX] at hx
                exact hx
              exact (OptionT.mem_support_iff _ _).2 hxSome
            · simp [hX] at hxEq
              exact hxEq
      refine ⟨innerStmtOut, hInnerMem, ?_⟩
      have hInnerRun :
          innerStmtOut ∈ support (V.run (stmtLens.proj outerStmtIn) tr) := by
        have hInnerSome :
            some innerStmtOut ∈ support (OptionT.run innerExec) := by
          exact (OptionT.mem_support_iff _ _).1 hInnerMem
        change
          some innerStmtOut ∈ support (do
            let __do_lift ← init
            (simulateQ impl (V.run (stmtLens.proj outerStmtIn) tr)).run' __do_lift) at hInnerSome
        simp only [support_bind, Set.mem_iUnion, exists_prop] at hInnerSome
        rcases hInnerSome with ⟨s, hs, hState⟩
        exact OptionT.mem_support_run_simulateQ_run'_subset
          (impl := impl)
          (oa := V.run (stmtLens.proj outerStmtIn) tr)
          (s := s) hState
      have hCompat : V.compatStatement stmtLens outerStmtIn innerStmtOut := by
        exact ⟨tr, hInnerRun⟩
      rw [← hEqVal] at hRel
      exact lensKS.proj_knowledgeSound outerStmtIn innerStmtOut outerWitOut hCompat hRel
    have hInner := innerKSF.toFun_full (stmtLens.proj outerStmtIn) tr
      (witLens.proj (outerStmtIn, outerWitOut)) hInnerProb
    -- Now we need to relate the extracted witness types
    -- The lifted extractOut at Fin.last n produces something that matches
    simp only [Extractor.RoundByRound.liftContext]
    -- Need to match the result of the inner extractOut with what the lifted version produces
    -- at Fin.last n
    -- The lifted extractOut does a match on Fin.last n:
    -- - If n = 0: casts and applies witLens.lift → produces OuterWitIn (WitMid 0)
    -- - If n = j+1: produces (innerWitMid, outerWitOut) (WitMid (j+1) × OuterWitOut)
    -- The goal type at (.last n) is:
    --   match (.last n) with | ⟨0,_⟩ => OuterWitIn | ⟨j+1,hj⟩ => InnerWitMid ⟨j+1,hj⟩ × OuterWitOut
    -- And the kSF at (.last n) asks about innerKSF or outerRelIn membership
    by_cases hn : n = 0
    · subst hn
      -- n = 0: Fin.last 0 = ⟨0, ...⟩
      -- Goal becomes: (outerStmtIn, extractOut result) ∈ outerRelIn
      -- The extractOut at n=0 matches on Fin.last 0 = ⟨0, h⟩, casts, and applies witLens.lift
      -- But the kSF at m=0 just checks outerRelIn membership
      -- hInner: innerKSF (.last 0) ... _ (innerE.extractOut ...)
      -- At n=0, (.last 0) = ⟨0, ...⟩, so innerKSF.toFun 0 checks innerRelIn membership via
      -- toFun_empty
      let defaultTr : Transcript (Fin.last 0) pSpec := by
        change Transcript 0 pSpec
        exact default
      have hTr : tr = defaultTr := by
        ext i
        exact Fin.elim0 i
      rw [hTr] at hInner
      rw [hTr]
      have hInnerEmpty :=
        (innerKSF.toFun_empty (stmtLens.proj outerStmtIn)
          (innerE.extractOut (stmtLens.proj outerStmtIn) defaultTr
            (witLens.proj (outerStmtIn, outerWitOut)))).mpr
      have hInnerRelIn := hInnerEmpty hInner
      exact lensKS.lift_knowledgeSound outerStmtIn outerWitOut _ (by simp) hInnerRelIn
    · -- n = k+1: Fin.last n = ⟨n, ...⟩ with n ≥ 1
      -- The goal at (.last n) with n = k+1: kSF is innerKSF on the first component
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      exact hInner

/-
  Lifting the reduction preserves round-by-round knowledge soundness, assuming the lens
  satisfies its knowledge soundness conditions
-/
set_option maxHeartbeats 200000 in
theorem liftContext_rbr_knowledgeSoundness [Inhabited InnerStmtOut] [Inhabited InnerWitIn]
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)} {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)} {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    {stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
    {witLens : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    [lensKS : Extractor.Lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (V.compatStatement stmtLens) (fun _ _ => True) ⟨stmtLens, witLens⟩]
    (h : V.rbrKnowledgeSoundness init impl innerRelIn innerRelOut rbrKnowledgeError) :
      (V.liftContext stmtLens).rbrKnowledgeSoundness init impl outerRelIn outerRelOut
        rbrKnowledgeError := by
  unfold rbrKnowledgeSoundness at h ⊢
  obtain ⟨InnerWitMid, innerE, innerKSF, hBound⟩ := h
  let outerE := innerE.liftContext ⟨stmtLens, witLens⟩
  let outerKSF := KnowledgeStateFunction.liftContext V (lensKS := lensKS) innerE innerKSF
  refine ⟨_, outerE, outerKSF, ?_⟩
  intro outerStmtIn outerWitIn outerP roundIdx
  -- Construct inner prover by projecting the outer prover
  let innerPLens : Context.Lens InnerStmtIn InnerStmtOut OuterStmtIn OuterStmtOut
      InnerWitIn InnerWitOut OuterWitIn OuterWitOut := {
    stmt := (fun _ => outerStmtIn) ⇆ (fun _ _ => (default : InnerStmtOut))
    wit := (fun _ => outerWitIn) ⇆ (fun _ innerCtxOut =>
      witLens.proj (outerStmtIn, innerCtxOut.2))
  }
  let innerP : Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec :=
    outerP.liftContext innerPLens
  cases n with
  | zero =>
      exact Fin.elim0 roundIdx.1
  | succ n =>
      rcases roundIdx with ⟨roundIdx, hDir⟩
      cases roundIdx using Fin.cases with
      | zero =>
          have hInner := hBound (stmtLens.proj outerStmtIn) default innerP ⟨0, hDir⟩
          refine le_trans ?_ hInner
          simp [innerP, innerPLens, Prover.liftContext_runWithLogToRound,
            outerKSF, KnowledgeStateFunction.liftContext, outerE,
            Extractor.RoundByRound.liftContext]
          apply probEvent_mono
          intro ⟨transcript, challenge, proveQueryLog⟩ hx
          intro ⟨outerWitMid, hNotPrev, hNext⟩
          refine ⟨outerWitMid.1, ?_, hNext⟩
          intro hInnerPrev
          have hTr : transcript = (default : Transcript 0 pSpec) := by
            ext i
            exact Fin.elim0 i
          rw [hTr] at hInnerPrev
          apply hNotPrev
          have hInnerRelIn := (innerKSF.toFun_empty (stmtLens.proj outerStmtIn)
            (innerE.extractMid 0 (stmtLens.proj outerStmtIn)
              (transcript.concat challenge) outerWitMid.1)).mpr hInnerPrev
          exact lensKS.lift_knowledgeSound outerStmtIn outerWitMid.2
            (cast innerE.eqIn (innerE.extractMid 0 (stmtLens.proj outerStmtIn)
              (transcript.concat challenge) outerWitMid.1))
            (by simp)
            hInnerRelIn
      | succ j =>
          have hInner := hBound (stmtLens.proj outerStmtIn) default innerP ⟨j.succ, hDir⟩
          refine le_trans ?_ hInner
          simp [innerP, innerPLens, Prover.liftContext_runWithLogToRound,
            outerKSF, KnowledgeStateFunction.liftContext, outerE,
            Extractor.RoundByRound.liftContext]
          apply probEvent_mono
          intro ⟨transcript, challenge, proveQueryLog⟩ hx
          intro ⟨outerWitMid, hNotPrev, hNext⟩
          exact ⟨outerWitMid.1, hNotPrev, hNext⟩

end Verifier

end Theorems

section Test

open Polynomial

-- Testing out sum-check-like relations

noncomputable section

def OuterStmtIn_Test := ℤ[X] × ℤ[X] × ℤ
def InnerStmtIn_Test := ℤ[X] × ℤ

@[simp]
def outerRelIn_Test : Set (OuterStmtIn_Test × Unit) :=
  setOf (fun ⟨⟨p, q, t⟩, _⟩ => ∑ x ∈ {0, 1}, (p * q).eval x = t)
@[simp]
def innerRelIn_Test : Set (InnerStmtIn_Test × Unit) :=
  setOf (fun ⟨⟨f, t⟩, _⟩ => ∑ x ∈ {0, 1}, f.eval x = t)

def OuterStmtOut_Test := ℤ[X] × ℤ[X] × ℤ × ℤ
def InnerStmtOut_Test := ℤ[X] × ℤ × ℤ

@[simp]
def outerRelOut_Test : Set (OuterStmtOut_Test × Unit) :=
  setOf (fun ⟨⟨p, q, t, r⟩, _⟩ => (p * q).eval r = t)
@[simp]
def innerRelOut_Test : Set (InnerStmtOut_Test × Unit) :=
  setOf (fun ⟨⟨f, t, r⟩, _⟩ => f.eval r = t)

@[simp]
def testStmtLens :
    Statement.Lens OuterStmtIn_Test OuterStmtOut_Test InnerStmtIn_Test InnerStmtOut_Test :=
  ⟨fun ⟨p, q, t⟩ => ⟨p * q, t⟩, fun ⟨p, q, _⟩ ⟨_, t', u⟩ => (p, q, t', u)⟩

@[simp]
def testLens : Context.Lens OuterStmtIn_Test OuterStmtOut_Test InnerStmtIn_Test InnerStmtOut_Test
    Unit Unit Unit Unit where
  stmt := testStmtLens
  wit := Witness.Lens.id

@[simp]
def testLensE : Extractor.Lens OuterStmtIn_Test OuterStmtOut_Test InnerStmtIn_Test InnerStmtOut_Test
    Unit Unit Unit Unit where
  stmt := testStmtLens
  wit := Witness.InvLens.id

instance instTestLensComplete : testLens.IsComplete
      outerRelIn_Test innerRelIn_Test outerRelOut_Test innerRelOut_Test
      (fun ⟨⟨p, q, _⟩, _⟩ ⟨⟨f, _⟩, _⟩ => p * q = f) where
  proj_complete := fun ⟨p, q, t⟩ () hRelIn => by simp_all
  lift_complete := fun ⟨p, q, t⟩ _ ⟨f, t', r⟩ _ hCompat hRelIn hRelOut' => by
    simp_all only [outerRelIn_Test, eval_mul, Finset.mem_singleton, zero_ne_one,
      not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, Set.mem_setOf_eq,
      innerRelOut_Test, outerRelOut_Test, testLens, testStmtLens]
    simp [← hRelOut', ← hCompat]

def instTestLensKnowledgeSound : testLensE.IsKnowledgeSound
    outerRelIn_Test innerRelIn_Test outerRelOut_Test innerRelOut_Test
      (fun ⟨p, q, _⟩ ⟨f, _⟩ => p * q = f) (fun _ _ => True) where
  proj_knowledgeSound := fun ⟨p, q, t⟩ ⟨f, t', r⟩ _ h h' => by
    simp_all only [outerRelOut_Test, eval_mul, Statement.Lens.lift,
      testLensE, testStmtLens, Set.mem_setOf_eq, innerRelOut_Test]
    simp [← h', ← h]
  lift_knowledgeSound := fun ⟨p, q, t⟩ _ _ _ _ => by
    simp_all

end

end Test
