/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.LiftContext.OracleReduction

/-!
# Oracle-routing coherence core for `LiftContextCoherent` (design note #433)

When an oracle verifier is lifted along an `OracleStatement.OracleLens`, its inner oracle queries
are re-routed through the lens' `simOStmt` and answered against the *outer* oracle statements
(consulting the outer input statement via `ReaderT`). Converting the lifted verifier back to a plain
verifier (`toVerifier`) then simulates those routed queries under the honest *outer* oracle
(`simOracle2`). The coherence condition
`OracleVerifier.LiftContextCoherent.toVerifier_comm` requires
this to coincide with simulating the *inner* verifier directly against the *projected inner* oracle
statements.

This module proves the heart of that coincidence — the **nested-`simulateQ` agreement**:

* `fullRouter_simOracle2_agree`: routing a whole computation through `fullRouter simOStmt`,
  evaluating
  the resulting `ReaderT` at the outer input statement, and simulating under the honest outer oracle
  equals simulating the original computation under the honest inner oracle — *given* a per-query
  coherence equation (`combinedRouter = simOracle2 …`).

* `combinedRouter_eq_simOracle2`: that per-query coherence equation reduces to a single faithfulness
  condition on the inner oracle queries (the two passthrough summands — the shared `oSpec` and the
  prover messages — are automatic).

Together these turn the open `toVerifier_comm` obligation into a single, checkable per-inner-query
faithfulness statement, which an honest virtual lens (e.g. the sum-check / Spartan lenses)
discharges
by reconstructing each inner oracle evaluation from the outer oracle queries.

The two genuinely-content lemmas are axiom-clean (`propext`, `Quot.sound` only).
-/

open OracleComp OracleSpec OracleInterface

namespace OracleVerifier.LiftContext

variable {ι : Type} {oSpec : OracleSpec ι}
    {OuterStmtIn : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, OracleInterface (pSpec.Message i)]

/-- **Doubly-lifted-to-singly simulated.** Simulating a `(oSpec + [fam]ₒ)`-computation lifted up
into `oSpec + ([fam]ₒ + [Msg]ₒ)` under the two-family honest oracle `simOracle2` coincides with
simulating it directly under the single-family honest oracle `simOracle`. This is the standard tool
for discharging the per-inner-query faithfulness condition of a concrete lens: it strips the
prover-message summand that the lens' `simOStmt` never touches. -/
lemma simulateQ_simOracle2_liftComp
    {ιf : Type} {fam : ιf → Type} [∀ i, OracleInterface (fam i)]
    {ιm : Type} {Msg : ιm → Type} [∀ i, OracleInterface (Msg i)]
    (oos : ∀ i, fam i) (msgs : ∀ i, Msg i) {α : Type}
    (Y : OracleComp (oSpec + [fam]ₒ) α) :
    simulateQ (simOracle2 oSpec oos msgs) (OracleComp.liftComp Y (oSpec + ([fam]ₒ + [Msg]ₒ)))
      = simulateQ (simOracle oSpec oos) Y := by
  rw [OracleComp.liftComp_def, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rw [QueryImpl.apply_compose]
  rcases t with q | q <;> rfl

/-- The combined per-query implementation underlying the nested simulation: route an inner-big query
through `fullRouter simOStmt`, evaluate the resulting `ReaderT` at the outer input statement `s`,
then
simulate under the honest outer oracle `simOracle2`. -/
noncomputable def combinedRouter
    (simOStmt : QueryImpl [InnerOStmtIn]ₒ
      (ReaderT OuterStmtIn (OracleComp (oSpec + [OuterOStmtIn]ₒ))))
    (outerOStmt : ∀ i, OuterOStmtIn i) (msgs : ∀ i, pSpec.Message i) (s : OuterStmtIn) :
    QueryImpl (oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ)) (OracleComp oSpec) :=
  fun t => simulateQ (simOracle2 oSpec outerOStmt msgs)
    ((fullRouter (OuterOStmtIn := OuterOStmtIn) simOStmt t).run s)

/-- The composite `simulateQ simOracle2-outer ∘ (·.run s) ∘ simulateQ (fullRouter simOStmt)` is a
monad morphism out of the free monad, hence equals `simulateQ` of the combined per-query
implementation `combinedRouter`. Pure plumbing — no faithfulness needed. -/
lemma simulateQ_fullRouter_run_eq_simulateQ_combinedRouter
    (simOStmt : QueryImpl [InnerOStmtIn]ₒ
      (ReaderT OuterStmtIn (OracleComp (oSpec + [OuterOStmtIn]ₒ))))
    (outerOStmt : ∀ i, OuterOStmtIn i) (msgs : ∀ i, pSpec.Message i) (s : OuterStmtIn)
    {γ : Type} (comp : OracleComp (oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ)) γ) :
    simulateQ (simOracle2 oSpec outerOStmt msgs)
        ((simulateQ (fullRouter (OuterOStmtIn := OuterOStmtIn) simOStmt) comp).run s)
      = simulateQ (combinedRouter simOStmt outerOStmt msgs s) comp := by
  induction comp using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih =>
      conv_rhs => rw [simulateQ_bind, simulateQ_spec_query]
      conv_lhs => rw [simulateQ_bind, simulateQ_spec_query, ReaderT.run_bind, simulateQ_bind]
      exact bind_congr fun u => ih u

/-- **Nested-`simulateQ` agreement.** Given the per-query coherence equation
`combinedRouter simOStmt outerOStmt msgs s = simOracle2 oSpec innerOStmt msgs`, routing a
computation
through `fullRouter simOStmt` and simulating under the honest *outer* oracle agrees with
simulating it
directly under the honest *inner* oracle. -/
theorem fullRouter_simOracle2_agree
    (simOStmt : QueryImpl [InnerOStmtIn]ₒ
      (ReaderT OuterStmtIn (OracleComp (oSpec + [OuterOStmtIn]ₒ))))
    (outerOStmt : ∀ i, OuterOStmtIn i) (innerOStmt : ∀ i, InnerOStmtIn i)
    (msgs : ∀ i, pSpec.Message i) (s : OuterStmtIn)
    (hcoh : combinedRouter simOStmt outerOStmt msgs s = simOracle2 oSpec innerOStmt msgs)
    {γ : Type} (comp : OracleComp (oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ)) γ) :
    simulateQ (simOracle2 oSpec outerOStmt msgs)
        ((simulateQ (fullRouter (OuterOStmtIn := OuterOStmtIn) simOStmt) comp).run s)
      = simulateQ (simOracle2 oSpec innerOStmt msgs) comp := by
  rw [simulateQ_fullRouter_run_eq_simulateQ_combinedRouter, hcoh]

/-- **Coherence builder.** The per-query coherence equation reduces to a single faithfulness
condition on the inner oracle queries: the shared-`oSpec` and prover-message summands route through
identically on both sides and are discharged automatically. -/
theorem combinedRouter_eq_simOracle2
    (simOStmt : QueryImpl [InnerOStmtIn]ₒ
      (ReaderT OuterStmtIn (OracleComp (oSpec + [OuterOStmtIn]ₒ))))
    (outerOStmt : ∀ i, OuterOStmtIn i) (innerOStmt : ∀ i, InnerOStmtIn i)
    (msgs : ∀ i, pSpec.Message i) (s : OuterStmtIn)
    (hfaith : ∀ (q : OracleSpec.Domain [InnerOStmtIn]ₒ),
      simulateQ (simOracle2 oSpec outerOStmt msgs)
          (OracleComp.liftComp ((simOStmt q).run s)
            (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))
        = simOracle2 oSpec innerOStmt msgs (Sum.inr (Sum.inl q))) :
    combinedRouter simOStmt outerOStmt msgs s = simOracle2 oSpec innerOStmt msgs := by
  funext t
  rcases t with q | q | q
  · simp [combinedRouter, fullRouter, routeOSpec, simOracle2, QueryImpl.addLift]
  · simpa [combinedRouter, fullRouter, routeInnerO] using hfaith q
  · simp [combinedRouter, fullRouter, routeMsg, simOracle2, QueryImpl.addLift, QueryImpl.add]

/-- **Faithfulness ⇒ agreement.** Combining the two lemmas: a single per-inner-query faithfulness
condition implies the full nested-`simulateQ` agreement for every computation. This is the form a
concrete lens uses to discharge `LiftContextCoherent.toVerifier_comm`. -/
theorem fullRouter_simOracle2_agree_of_faithful
    (simOStmt : QueryImpl [InnerOStmtIn]ₒ
      (ReaderT OuterStmtIn (OracleComp (oSpec + [OuterOStmtIn]ₒ))))
    (outerOStmt : ∀ i, OuterOStmtIn i) (innerOStmt : ∀ i, InnerOStmtIn i)
    (msgs : ∀ i, pSpec.Message i) (s : OuterStmtIn)
    (hfaith : ∀ (q : OracleSpec.Domain [InnerOStmtIn]ₒ),
      simulateQ (simOracle2 oSpec outerOStmt msgs)
          (OracleComp.liftComp ((simOStmt q).run s)
            (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))
        = simOracle2 oSpec innerOStmt msgs (Sum.inr (Sum.inl q)))
    {γ : Type} (comp : OracleComp (oSpec + ([InnerOStmtIn]ₒ + [pSpec.Message]ₒ)) γ) :
    simulateQ (simOracle2 oSpec outerOStmt msgs)
        ((simulateQ (fullRouter (OuterOStmtIn := OuterOStmtIn) simOStmt) comp).run s)
      = simulateQ (simOracle2 oSpec innerOStmt msgs) comp :=
  fullRouter_simOracle2_agree simOStmt outerOStmt innerOStmt msgs s
    (combinedRouter_eq_simOracle2 simOStmt outerOStmt innerOStmt msgs s hfaith) comp

/-! ## Discharging `LiftContextCoherent.toVerifier_comm`

The nested-`simulateQ` agreement is the oracle-semantics core of `toVerifier_comm`. Assembling it
with the value-level statement coherences (`hproj`, `hlift`) discharges the full verifier-equality.
The two value-level conditions are exactly what an honest lens satisfies by `rfl`/`simp` once its
`toLens` is defined to match its explicit `projStmt` / `liftStmt` / `embedOStmt` routing. -/

section Builder

open ProtocolSpec

variable {InnerStmtIn OuterStmtOut InnerStmtOut : Type}
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]

/-- **Per-input `toVerifier_comm`.** On a single input `(os, oos)` and transcript, the lifted oracle
verifier (viewed as a plain verifier) and the inner verifier lifted along `toLens` produce the same
verification, given the proj/faithfulness/lift coherences. -/
theorem liftContext_toVerifier_comm_verify
    (stmtLens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec)
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    (os : OuterStmtIn) (oos : ∀ i, OuterOStmtIn i) (transcript : FullTranscript pSpec)
    (hproj : (stmtLens.toLens.proj (os, oos)).1 = stmtLens.projStmt os)
    (hfaith : ∀ (q : OracleSpec.Domain [InnerOStmtIn]ₒ),
      simulateQ (simOracle2 oSpec oos transcript.messages)
          (OracleComp.liftComp ((stmtLens.simOStmt q).run os)
            (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))
        = simOracle2 oSpec (stmtLens.toLens.proj (os, oos)).2 transcript.messages
            (Sum.inr (Sum.inl q)))
    (hlift : ∀ (so : InnerStmtOut),
      stmtLens.toLens.lift (os, oos)
          (so, fun i => match h : V.embed i with
            | Sum.inl j => V.hEq i ▸ h ▸ (stmtLens.toLens.proj (os, oos)).2 j
            | Sum.inr j => V.hEq i ▸ h ▸ transcript.messages j)
        = (stmtLens.liftStmt os so, fun i => match h : stmtLens.embedOStmt i with
            | Sum.inl j => stmtLens.hEqOStmt i ▸ h ▸ oos j
            | Sum.inr j => stmtLens.hEqOStmt i ▸ h ▸ transcript.messages j)) :
    ((V.liftContext stmtLens).toVerifier).verify (os, oos) transcript
      = (V.toVerifier.liftContext stmtLens.toLens).verify (os, oos) transcript := by
  simp only [OracleVerifier.toVerifier, OracleVerifier.liftContext, Verifier.liftContext,
    OptionT.mk, simulateQ_bind, simulateQ_pure, bind_assoc]
  rw [fullRouter_simOracle2_agree stmtLens.simOStmt oos (stmtLens.toLens.proj (os, oos)).2
      transcript.messages os
      (combinedRouter_eq_simOracle2 _ _ _ _ _ hfaith), hproj]
  refine OptionT.ext ?_
  simp only [OptionT.run_bind, OptionT.run_pure, Option.elimM, pure_bind]
  change (_ >>= _) >>= _ = _ >>= _
  rw [bind_assoc]
  apply bind_congr
  intro mo
  cases mo with
  | none => simp
  | some so =>
      simp only [pure_bind, Option.map_some, Option.elim_some]
      exact congrArg (fun z => pure (some z)) (hlift so).symm

/-- **`toVerifier_comm` builder.** The full verifier-level coherence equality, from the three
per-input coherence conditions quantified over all inputs. -/
theorem liftContext_toVerifier_comm_of
    (stmtLens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec)
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    (hproj : ∀ (os : OuterStmtIn) (oos : ∀ i, OuterOStmtIn i),
      (stmtLens.toLens.proj (os, oos)).1 = stmtLens.projStmt os)
    (hfaith : ∀ (os : OuterStmtIn) (oos : ∀ i, OuterOStmtIn i) (transcript : FullTranscript pSpec)
        (q : OracleSpec.Domain [InnerOStmtIn]ₒ),
      simulateQ (simOracle2 oSpec oos transcript.messages)
          (OracleComp.liftComp ((stmtLens.simOStmt q).run os)
            (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))
        = simOracle2 oSpec (stmtLens.toLens.proj (os, oos)).2 transcript.messages
            (Sum.inr (Sum.inl q)))
    (hlift : ∀ (os : OuterStmtIn) (oos : ∀ i, OuterOStmtIn i) (transcript : FullTranscript pSpec)
        (so : InnerStmtOut),
      stmtLens.toLens.lift (os, oos)
          (so, fun i => match h : V.embed i with
            | Sum.inl j => V.hEq i ▸ h ▸ (stmtLens.toLens.proj (os, oos)).2 j
            | Sum.inr j => V.hEq i ▸ h ▸ transcript.messages j)
        = (stmtLens.liftStmt os so, fun i => match h : stmtLens.embedOStmt i with
            | Sum.inl j => stmtLens.hEqOStmt i ▸ h ▸ oos j
            | Sum.inr j => stmtLens.hEqOStmt i ▸ h ▸ transcript.messages j)) :
    (V.liftContext stmtLens).toVerifier = V.toVerifier.liftContext stmtLens.toLens := by
  ext1
  funext stmtIn transcript
  obtain ⟨os, oos⟩ := stmtIn
  exact liftContext_toVerifier_comm_verify stmtLens V os oos transcript (hproj os oos)
    (hfaith os oos transcript) (hlift os oos transcript)

/-- **`LiftContextCoherent` instance builder.** Discharges the #433 framework obligation for any
lens
satisfying the three coherence conditions — turning the previously-open `toVerifier_comm` into a
checklist (statement projection + output lift + per-inner-query oracle faithfulness) that honest
virtual lenses satisfy. -/
@[reducible] def liftContextCoherent_of
    (stmtLens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec)
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    (hproj : ∀ (os : OuterStmtIn) (oos : ∀ i, OuterOStmtIn i),
      (stmtLens.toLens.proj (os, oos)).1 = stmtLens.projStmt os)
    (hfaith : ∀ (os : OuterStmtIn) (oos : ∀ i, OuterOStmtIn i) (transcript : FullTranscript pSpec)
        (q : OracleSpec.Domain [InnerOStmtIn]ₒ),
      simulateQ (simOracle2 oSpec oos transcript.messages)
          (OracleComp.liftComp ((stmtLens.simOStmt q).run os)
            (oSpec + ([OuterOStmtIn]ₒ + [pSpec.Message]ₒ)))
        = simOracle2 oSpec (stmtLens.toLens.proj (os, oos)).2 transcript.messages
            (Sum.inr (Sum.inl q)))
    (hlift : ∀ (os : OuterStmtIn) (oos : ∀ i, OuterOStmtIn i) (transcript : FullTranscript pSpec)
        (so : InnerStmtOut),
      stmtLens.toLens.lift (os, oos)
          (so, fun i => match h : V.embed i with
            | Sum.inl j => V.hEq i ▸ h ▸ (stmtLens.toLens.proj (os, oos)).2 j
            | Sum.inr j => V.hEq i ▸ h ▸ transcript.messages j)
        = (stmtLens.liftStmt os so, fun i => match h : stmtLens.embedOStmt i with
            | Sum.inl j => stmtLens.hEqOStmt i ▸ h ▸ oos j
            | Sum.inr j => stmtLens.hEqOStmt i ▸ h ▸ transcript.messages j)) :
    OracleVerifier.LiftContextCoherent stmtLens V :=
  ⟨liftContext_toVerifier_comm_of stmtLens V hproj hfaith hlift⟩

end Builder

end OracleVerifier.LiftContext
