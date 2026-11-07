/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.LiftContext.Reduction

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.OracleReduction.LiftContext.Lens
import ProximityPrize.Extensions.OracleReduction.Security.RoundByRound
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


open OracleSpec OracleComp ProtocolSpec

open scoped NNReal

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}

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
  have hquery (t : oSpec.Domain) :
      (liftM (query t : OracleComp oSpec (oSpec.Range t)) :
        OracleComp (oSpec + [pSpec.Challenge]ₒ) (oSpec.Range t)) =
      (liftM (OracleSpec.query t) : OracleComp (oSpec + [pSpec.Challenge]ₒ) _) := by
    rw [← OracleComp.liftComp_eq_liftM]
    exact OracleComp.liftComp_liftM_query _ t
  simp_rw [hquery]
  simpa only [liftM_OptionT_eq] using
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
theorem Verifier.liftContext_probEvent_le_of_not_mem
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (outerStmtIn : OuterStmtIn) (transcript : FullTranscript pSpec)
    (hOuter : outerStmtIn ∉ outerLangIn) :
    probEvent (fun x ↦ x ∈ outerLangOut) (OptionT.mk do
      let __do_lift ← init
      (simulateQ impl (run outerStmtIn transcript (liftContext lens V))).run' __do_lift) ≤
      probEvent (fun x ↦ x ∈ innerLangOut) (OptionT.mk do
        let __do_lift ← init
        (simulateQ impl (run (lens.proj outerStmtIn) transcript V)).run' __do_lift) := by
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
  rw [hExecMap]
  unfold probEvent
  rw [prEvent_map]
  apply prEvent_mono_of_support
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
  exact lensSound.lift_sound outerStmtIn x hOuter hCompat hOut

section Theorems

/- Theorems about liftContext interacting with reduction execution and security properties -/

namespace Prover

/- Breaking down the intertwining of liftContext and prover execution -/

end Prover

namespace Reduction

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

end Reduction

namespace Verifier

end Verifier

end Theorems

section Test

open Polynomial

-- Testing out sum-check-like relations

noncomputable section

end

end Test
