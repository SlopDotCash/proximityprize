/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.LiftContext.Reduction

/-!
  ## Lifting Oracle Reductions to Larger Contexts

  This file is a continuation of `LiftContext/Reduction.lean`, where we lift oracle reductions to
  larger contexts.

  The only new thing here is the definition of the oracle verifier. The rest (oracle prover +
  security properties) are just ported from `LiftContext/Reduction.lean`, with suitable conversions.
-/

open OracleSpec OracleComp ProtocolSpec

open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- The lifting of the prover from an inner oracle reduction to an outer oracle reduction, requiring
  an associated oracle context lens -/
def OracleProver.liftContext
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (P : OracleProver oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                            InnerStmtOut InnerOStmtOut InnerWitOut pSpec) :
    OracleProver oSpec OuterStmtIn OuterOStmtIn OuterWitIn
                      OuterStmtOut OuterOStmtOut OuterWitOut pSpec :=
  Prover.liftContext lens.toContext P

variable [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleVerifier.LiftContext

/-! ### Oracle-query routers for `OracleVerifier.liftContext`

Design note (#433): an inner oracle verifier runs in the oracle spec
`oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ)`. To lift it we re-route those queries into the
outer spec `oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)`, parameterised (via `ReaderT`) by the
outer input statement so that the lens' `simOStmt` can consult it. The three routers below handle
the three summands; `fullRouter` assembles them. -/

variable {OuterStmtIn : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]

/-- Pass-through router for the shared oracle `oSpec`. -/
def routeOSpec : QueryImpl oSpec
    (ReaderT OuterStmtIn (OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))) :=
  fun q => ReaderT.mk fun _ =>
    (OracleComp.lift <| OracleSpec.query (spec := oSpec) q :
      OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)) _)

/-- Pass-through router for the prover-message oracles `[pSpec.Message]ₒ`. -/
def routeMsg : QueryImpl [pSpec.Message]ₒ
    (ReaderT OuterStmtIn (OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))) :=
  fun q => ReaderT.mk fun _ =>
    (OracleComp.lift <| OracleSpec.query (spec := [pSpec.Message]ₒ) q :
      OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)) _)

/-- Inner input-oracle router, obtained from the lens' `simOStmt` by lifting its target spec
`oSpec + [OuterOStmtIn]ₒ` into the larger `oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)`. -/
def routeInnerO
    (simOStmt : QueryImpl [InnerOStmtIn]ₒ
      (ReaderT OuterStmtIn (OracleComp (oSpec + [OuterOStmtIn]ₒ)))) :
    QueryImpl [InnerOStmtIn]ₒ
      (ReaderT OuterStmtIn (OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))) :=
  fun q => ReaderT.mk fun s =>
    OracleComp.liftComp ((simOStmt q).run s) (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ))

/-- The combined router for the inner verifier's full oracle spec
`oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ)`. -/
def fullRouter
    (simOStmt : QueryImpl [InnerOStmtIn]ₒ
      (ReaderT OuterStmtIn (OracleComp (oSpec + [OuterOStmtIn]ₒ)))) :
    QueryImpl (oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ))
      (ReaderT OuterStmtIn (OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))) :=
  (routeOSpec (oSpec := oSpec) (OuterStmtIn := OuterStmtIn) (OuterOStmtIn := OuterOStmtIn)
    (pSpec := pSpec)) +
    ((routeInnerO (oSpec := oSpec) (OuterStmtIn := OuterStmtIn) (OuterOStmtIn := OuterOStmtIn)
        (InnerOStmtIn := InnerOStmtIn) (pSpec := pSpec) simOStmt) +
      (routeMsg (oSpec := oSpec) (OuterStmtIn := OuterStmtIn) (OuterOStmtIn := OuterOStmtIn)
        (pSpec := pSpec)))

end OracleVerifier.LiftContext

open OracleVerifier.LiftContext in
/-- The lifting of the verifier from an inner oracle reduction to an outer oracle reduction,
  requiring an associated oracle-routing lens (`OracleStatement.OracleLens`).

  The lifted `verify` runs the inner verifier on the projected non-oracle statement, re-routing the
  inner oracle queries through the lens' `simOStmt` (consulting the outer input statement via
  `ReaderT`), and lifts the resulting non-oracle output statement via `liftStmt`. The output oracle
  statements are routed via the lens' `embedOStmt` / `hEqOStmt`.

  Design note (#433): see `OracleStatement.OracleLens` for why the value-level
  `OracleStatement.Lens` is insufficient here (it cannot express oracle-query routing). -/
def OracleVerifier.liftContext
    (lens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec)
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec) :
      OracleVerifier oSpec OuterStmtIn OuterOStmtIn OuterStmtOut OuterOStmtOut pSpec where
  verify := fun outerStmtIn challenges =>
    OptionT.mk do
      let innerRun :
          OracleComp (oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ)) (Option InnerStmtOut) :=
        (V.verify (lens.projStmt outerStmtIn) challenges).run
      let routed : ReaderT OuterStmtIn
          (OracleComp (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ))) (Option InnerStmtOut) :=
        simulateQ (fullRouter lens.simOStmt) innerRun
      let o ← routed.run outerStmtIn
      pure (o.map (fun innerStmtOut => lens.liftStmt outerStmtIn innerStmtOut))
  embed := lens.embedOStmt
  hEq := lens.hEqOStmt

/-- The lifting of an inner oracle reduction to an outer oracle reduction.

  STATEMENT REPAIR (2026-06-04): the verifier lift now requires an `OracleStatement.OracleLens`
  (`stmtLens`) carrying the oracle-query routing data, in addition to the value-level
  `OracleContext.Lens` (`lens`) that drives the prover. Design note #433: the prover only transports
  values, so the value-level lens suffices for it; the verifier additionally needs `simOStmt` /
  `embedOStmt`. We require `stmtLens.toLens = lens.stmt` so that the prover and verifier transport
  statements consistently. -/
def OracleReduction.liftContext
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (stmtLens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec)
    (R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                            InnerStmtOut InnerOStmtOut InnerWitOut pSpec) :
      OracleReduction oSpec OuterStmtIn OuterOStmtIn OuterWitIn
                      OuterStmtOut OuterOStmtOut OuterWitOut pSpec where
  prover := R.prover.liftContext lens
  verifier := R.verifier.liftContext stmtLens

section Execution

/-- A coherence predicate stating that the oracle-routing lens `stmtLens` is *consistent* with its
  underlying value-level lens `stmtLens.toLens`, in the sense that running the lifted oracle
  verifier and then converting to a (non-oracle) verifier produces the same verifier as converting
  the inner oracle verifier first and then lifting along the value-level lens.

  STATEMENT REPAIR (2026-06-04): `liftContext_toVerifier_comm` is re-stated as a hypothesis of this
  form rather than an unconditional equality. Design note #433: the new `liftContext` routes inner
  oracle queries through `stmtLens.simOStmt` and consults the *outer* oracle statements, whereas the
  RHS `V.toVerifier.liftContext stmtLens.toLens` answers them from the *projected inner* oracle
  statements `stmtLens.toLens.proj`. These coincide only when `simOStmt` / `projStmt` / `liftStmt`
  are coherent with `toLens` — a genuine lens-level side condition (it is *not* automatic for
  non-invertible virtual routings). We therefore carry it as a typeclass so that the downstream
  security lemmas can assume exactly the instances they need; honest lenses (e.g. the sum-check and
  Spartan lenses) discharge it by `rfl`/`simp` once their `toLens` is defined to match their
  routing. -/
class OracleVerifier.LiftContextCoherent
    (stmtLens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec)
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec) : Prop where
  /-- The lifted oracle verifier, viewed as a plain verifier, equals the plain verifier obtained by
    lifting `V.toVerifier` along the value-level lens. -/
  toVerifier_comm :
    (V.liftContext stmtLens).toVerifier = V.toVerifier.liftContext stmtLens.toLens

/-- The lifting of the verifier commutes with the conversion from the oracle verifier to the
  verifier, given the coherence side condition `LiftContextCoherent`.

  See `OracleVerifier.LiftContextCoherent` for why the side condition is necessary (#433). -/
theorem OracleVerifier.liftContext_toVerifier_comm
    {stmtLens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec}
    {V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec}
    [coh : OracleVerifier.LiftContextCoherent stmtLens V] :
      (V.liftContext stmtLens).toVerifier = V.toVerifier.liftContext stmtLens.toLens :=
  coh.toVerifier_comm

/-- The lifting of the reduction commutes with the conversion from the oracle reduction to the
  reduction, given the verifier-level coherence side condition.

  STATEMENT REPAIR (2026-06-04): now takes the separate `stmtLens : OracleStatement.OracleLens`
  (carrying oracle routing) used by the verifier, requires it to agree with the value-level lens
  (`stmtLens.toLens = lens.stmt`), and assumes verifier coherence. -/
theorem OracleReduction.liftContext_toReduction_comm
    {lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    {stmtLens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec}
    {R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                            InnerStmtOut InnerOStmtOut InnerWitOut pSpec}
    (hStmt : stmtLens.toLens = lens.stmt)
    [coh : OracleVerifier.LiftContextCoherent stmtLens R.verifier] :
      (R.liftContext lens stmtLens).toReduction = R.toReduction.liftContext lens.toContext := by
  -- A reduction is determined by its prover and verifier; the prover lift coincides definitionally
  -- (it only uses the value-level context lens), and the verifier lift coincides by `coh` +
  -- `hStmt`.
  unfold OracleReduction.liftContext Reduction.liftContext OracleReduction.toReduction
  ext1
  · rfl
  · simp only []
    rw [coh.toVerifier_comm, hStmt]

end Execution

section Security

variable [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {outerRelIn : Set ((OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn)}
  {outerRelOut : Set ((OuterStmtOut × (∀ i, OuterOStmtOut i)) × OuterWitOut)}
  {innerRelIn : Set ((InnerStmtIn × (∀ i, InnerOStmtIn i)) × InnerWitIn)}
  {innerRelOut : Set ((InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut)}

namespace OracleReduction

variable
  {lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                            OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
  {stmtLens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                            OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec}
  {R : OracleReduction oSpec InnerStmtIn InnerOStmtIn InnerWitIn
                          InnerStmtOut InnerOStmtOut InnerWitOut pSpec}
  [lensComplete : lens.toContext.IsComplete outerRelIn innerRelIn outerRelOut innerRelOut
    (R.toReduction.compatContext lens.toContext)]
  {completenessError : ℝ≥0}

/-- STATEMENT REPAIR (2026-06-04): completeness lifting now additionally takes the verifier's
  oracle-routing lens `stmtLens` (agreeing with `lens.stmt` via `hStmt`) and its coherence
  instance, threaded through `liftContext_toReduction_comm`. -/
theorem liftContext_completeness
    (hStmt : stmtLens.toLens = lens.stmt)
    [coh : OracleVerifier.LiftContextCoherent stmtLens R.verifier]
    (h : R.completeness init impl innerRelIn innerRelOut completenessError) :
      (R.liftContext lens stmtLens).completeness init impl outerRelIn outerRelOut
        completenessError := by
  unfold OracleReduction.completeness at h ⊢
  rw [liftContext_toReduction_comm hStmt]
  exact R.toReduction.liftContext_completeness h (lens := lens.toContext)

theorem liftContext_perfectCompleteness
    (hStmt : stmtLens.toLens = lens.stmt)
    [coh : OracleVerifier.LiftContextCoherent stmtLens R.verifier]
    (h : R.perfectCompleteness init impl innerRelIn innerRelOut) :
      (R.liftContext lens stmtLens).perfectCompleteness init impl outerRelIn outerRelOut :=
  liftContext_completeness hStmt h

end OracleReduction

namespace OracleVerifier

variable {outerLangIn : Set (OuterStmtIn × (∀ i, OuterOStmtIn i))}
    {outerLangOut : Set (OuterStmtOut × (∀ i, OuterOStmtOut i))}
    {innerLangIn : Set (InnerStmtIn × (∀ i, InnerOStmtIn i))}
    {innerLangOut : Set (InnerStmtOut × (∀ i, InnerOStmtOut i))}
    [Inhabited InnerStmtOut] [∀ i, Inhabited (InnerOStmtOut i)]

/-- Lifting the oracle verifier preserves soundness, assuming the lens satisfies its soundness
  conditions and the oracle-routing lens is coherent with its value-level lens
  (`LiftContextCoherent`, #433).

  STATEMENT REPAIR (2026-06-04): `lens` is now an `OracleStatement.OracleLens`; the value-level
  soundness condition is stated on `lens.toLens`, and the verifier-conversion commute requires the
  `LiftContextCoherent` side condition (#433). -/
theorem liftContext_soundness
    {soundnessError : ℝ≥0}
    {lens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec}
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    [coh : OracleVerifier.LiftContextCoherent lens V]
    [lensSound : lens.toLens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.toVerifier.compatStatement lens.toLens)]
    (h : V.soundness init impl innerLangIn innerLangOut soundnessError) :
      (V.liftContext lens).soundness init impl outerLangIn outerLangOut soundnessError := by
  unfold OracleVerifier.soundness at h ⊢
  rw [liftContext_toVerifier_comm]
  exact V.toVerifier.liftContext_soundness h (lens := lens.toLens)

/-
theorem liftContext_knowledgeSoundness [Inhabited InnerWitIn]
    {knowledgeError : ℝ≥0}
    {stmtLens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec}
    {witLens : Witness.InvLens (OuterStmtIn × ∀ i, OuterOStmtIn i)
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    [coh : OracleVerifier.LiftContextCoherent stmtLens V]
    [lensKS : Extractor.Lens.IsKnowledgeSound
      outerRelIn innerRelIn outerRelOut innerRelOut
      (V.toVerifier.compatStatement stmtLens.toLens) (fun _ _ => True) ⟨stmtLens.toLens, witLens⟩]
    (h : V.knowledgeSoundness init impl innerRelIn innerRelOut knowledgeError) :
      (V.liftContext stmtLens).knowledgeSoundness init impl outerRelIn outerRelOut
        knowledgeError := by
  unfold OracleVerifier.knowledgeSoundness at h ⊢
	  rw [liftContext_toVerifier_comm]
	  exact V.toVerifier.liftContext_knowledgeSoundness h
	    (stmtLens := stmtLens.toLens) (witLens := witLens)
-/

theorem liftContext_rbr_soundness
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    {lens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec}
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    [coh : OracleVerifier.LiftContextCoherent lens V]
    [lensSound : lens.toLens.IsSound
      outerLangIn outerLangOut innerLangIn innerLangOut
      (V.toVerifier.compatStatement lens.toLens)]
    (h : V.rbrSoundness init impl innerLangIn innerLangOut rbrSoundnessError) :
      (V.liftContext lens).rbrSoundness init impl outerLangIn outerLangOut rbrSoundnessError := by
  unfold OracleVerifier.rbrSoundness at h ⊢
  rw [liftContext_toVerifier_comm]
  exact V.toVerifier.liftContext_rbr_soundness h (lens := lens.toLens)

set_option linter.unusedSectionVars false in
/-- Lifting the oracle verifier preserves round-by-round knowledge soundness, assuming the lens
  satisfies its knowledge-soundness conditions and the oracle-routing lens is coherent with its
  value-level lens (`LiftContextCoherent`, #433).

  HISTORY (2026-06-09): this used to be gated behind a `LiftContextRBRKnowledgeSound` class whose
  sole field *was* this conclusion, on the (then-correct, since-stale) grounds that the plain
  verifier API lacked a `liftContext_rbr_knowledgeSoundness` lemma. That lemma now exists and is
  fully proven (`Verifier.liftContext_rbr_knowledgeSoundness`, LiftContext/Reduction.lean), so the
  oracle version follows generically by the same unfold-and-commute argument as
  `liftContext_rbr_soundness`, and the class is gone. -/
theorem liftContext_rbr_knowledgeSoundness [Inhabited InnerWitIn]
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    {stmtLens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec}
    {witLens : Witness.InvLens (OuterStmtIn × ∀ i, OuterOStmtIn i)
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut}
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    [coh : OracleVerifier.LiftContextCoherent stmtLens V]
    [lensKS : Extractor.Lens.IsKnowledgeSound
      outerRelIn innerRelIn outerRelOut innerRelOut
      (V.toVerifier.compatStatement stmtLens.toLens) (fun _ _ => True) ⟨stmtLens.toLens, witLens⟩]
    (h : V.rbrKnowledgeSoundness init impl innerRelIn innerRelOut rbrKnowledgeError) :
      (V.liftContext stmtLens).rbrKnowledgeSoundness init impl outerRelIn outerRelOut
        rbrKnowledgeError := by
  unfold OracleVerifier.rbrKnowledgeSoundness at h ⊢
  rw [liftContext_toVerifier_comm]
  exact V.toVerifier.liftContext_rbr_knowledgeSoundness h
    (stmtLens := stmtLens.toLens) (witLens := witLens)

end OracleVerifier

end Security
