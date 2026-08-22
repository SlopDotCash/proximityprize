/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckBridge
import ArkLib.OracleReduction.LiftContext.Coherence

/-!
# `LiftContextCoherent` for the LogUp embedded-sumcheck lift (issue #13)

**This file proves the full `OracleVerifier.LiftContextCoherent` framework obligation (design note
#433) for the LogUp embedded sumcheck** — `logupSumcheck_liftContextCoherent`, axiom-clean. This is
the keystone that lets the proven generic `Sumcheck.Spec` completeness / round-by-round soundness
transfer through `sumcheckOracleReduction = (logupConcreteSumcheckOracleReduction …).liftContext …`
via `OracleReduction.liftContext_perfectCompleteness` / `liftContext_rbr_soundness`.

The instance assembles three obligations: `hproj` (`rfl`, the projection is the constant initial
sumcheck statement), `hlift` (`rfl` up to the empty output-oracle family `OutputOracleIdx = Fin 0`),
and the genuinely hard `hfaith` — the per-query **faithfulness** condition: under the honest *outer*
LogUp oracles, the lens' virtual-oracle reconstruction `logupSumcheckOracleLens.simOStmt` agrees with
the honest *inner* `Q`-oracle answer (`logupSumcheck_simOStmt_faithful`).

`simOStmt ⟨(), r⟩` queries the outer multiplicity / table / column / helper oracles at the point `r`,
assembles their evaluations into `PointEvaluations`, and returns `qAtPoint … r …` — which equals the
honest `Q`-polynomial evaluation `eval r Q` by `logupSumcheckPolynomial_finalEval` (the assembled
evaluations satisfy `logupPointEvaluationsAgree` by construction, since each honest oracle answer
*is* the corresponding `lagrangeOracleEval`).

`simOStmt ⟨(), r⟩` queries the outer multiplicity / table / column / helper oracles at the point `r`,
assembles their evaluations into `PointEvaluations`, and returns `qAtPoint … r …` — which equals the
honest `Q`-polynomial evaluation `eval r Q` by `logupSumcheckPolynomial_finalEval` (the assembled
evaluations satisfy `logupPointEvaluationsAgree` by construction, since each honest oracle answer
*is* the corresponding `lagrangeOracleEval`).

The proof rests on reusable oracle-simulation **bricks**, mirroring the Spartan first/second-sumcheck
faithfulness developments (`FirstSumcheckFaithful` / `SecondSumcheckFaithful`):

* `simulateQ_simOracle_subspec_query` / `simulateQ_simOracle_liftComp_query`: simulating a single
  honest outer-oracle query (in either the `HasQuery` monad-lift form or the `SubSpec`/`liftComp`
  coercion form the lens emits) under the single-family honest oracle returns the genuine point
  evaluation `answer (oos idx) r`. Proven via `simulateQ_spec_query`.
* `list_mapM_pure`, `simulateQ_mapM_column`, `simulateQ_mapM_helper`: the column / helper `mapM`
  reconstructions. Because the lens emits the `mapM`-internal queries under the `SubSpec` coercion
  inside a `List.mapM` binder — where `simp` does not fire the per-query brick — these are proven by
  a hand-rolled `List.mapM_cons` induction that exposes each query at top level and applies the brick
  by `have`/`exact` (defeq), then collapses with `pure_bind`.

All theorems in this file are axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

open OracleComp OracleSpec OracleInterface OracleVerifier.LiftContext

namespace Logup

section LiftCoherent

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)] [SampleableType F]
variable (n M : ℕ) (params : ProtocolParams M)

/-- **Atomic single-query reduction (`HasQuery` form).** Simulating one honest outer-oracle query
(lifted from the family sub-spec via the `HasQuery` monad lift) under the single-family honest oracle
returns the genuine point evaluation. -/
@[simp] theorem simulateQ_simOracle_subspec_query
    (oos : ∀ i, OStmtAfterOuter F n M params i)
    (qi : [OStmtAfterOuter F n M params]ₒ.Domain) :
    simulateQ (simOracle oSpec oos)
        (query (spec := [OStmtAfterOuter F n M params]ₒ) qi :
          OracleComp (oSpec + [OStmtAfterOuter F n M params]ₒ) _)
      = pure (OracleInterface.answer (oos qi.1) qi.2) := by
  erw [simulateQ_spec_query]
  rfl

/-- **Atomic single-query reduction (`SubSpec`/`liftComp` coercion form).** The same fact for the
query shape the lens emits inside a `List.mapM` (the explicit `OracleComp (oSpec + …)` annotation
routes through the sub-spec coercion `liftComp`). -/
@[simp] theorem simulateQ_simOracle_liftComp_query
    (oos : ∀ i, OStmtAfterOuter F n M params i)
    (q : OracleQuery [OStmtAfterOuter F n M params]ₒ F) :
    simulateQ (simOracle oSpec oos)
        (OracleComp.liftComp (q : OracleComp [OStmtAfterOuter F n M params]ₒ F)
          (oSpec + [OStmtAfterOuter F n M params]ₒ))
      = pure (q.cont (OracleInterface.answer (oos q.input.1) q.input.2)) := by
  rw [OracleComp.liftComp_query]
  change (q.cont <$>
    simulateQ (simOracle oSpec oos)
      (liftM ((oSpec + [OStmtAfterOuter F n M params]ₒ).query (Sum.inr q.input)))) = _
  erw [simulateQ_spec_query]
  rfl

/-- `mapM` of a pointwise-`pure` function over a list collapses to a `pure` of the mapped list. -/
@[simp] theorem list_mapM_pure {α β : Type} (f : α → β) (l : List α) :
    (l.mapM (fun a => (pure (f a) : OracleComp oSpec β)) : OracleComp oSpec (List β))
      = pure (l.map f) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- **`mapM` reconstruction (column oracles).** Hand-rolled induction exposes each query at top
level and applies the per-query brick by `have`/`exact` (defeq), sidestepping `simp`'s syntactic
match under the `mapM` binder. -/
theorem simulateQ_mapM_column
    (oos : ∀ i, OStmtAfterOuter F n M params i) (r : Fin n → F) (l : List (Fin M)) :
    simulateQ (simOracle oSpec oos)
        (l.mapM (fun a =>
          (query (spec := [OStmtAfterOuter F n M params]ₒ)
            (⟨.input (.column a), r⟩ : [OStmtAfterOuter F n M params]ₒ.Domain) :
            OracleComp (oSpec + [OStmtAfterOuter F n M params]ₒ) F)))
      = pure (l.map (fun a => OracleInterface.answer (oos (.input (.column a))) r)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have he : simulateQ (simOracle oSpec oos)
          (query (spec := [OStmtAfterOuter F n M params]ₒ)
            (⟨.input (.column a), r⟩ : [OStmtAfterOuter F n M params]ₒ.Domain) :
            OracleComp (oSpec + [OStmtAfterOuter F n M params]ₒ) F)
        = pure (OracleInterface.answer (oos (.input (.column a))) r) :=
      simulateQ_simOracle_subspec_query oSpec F n M params oos
        (⟨.input (.column a), r⟩ : [OStmtAfterOuter F n M params]ₒ.Domain)
    rw [List.mapM_cons]
    simp only [simulateQ_bind, simulateQ_pure, ih, pure_bind, List.map_cons]
    exact he ▸ pure_bind _ _

/-- **`mapM` reconstruction (helper oracles).** As `simulateQ_mapM_column`, for the helper queries. -/
theorem simulateQ_mapM_helper
    (oos : ∀ i, OStmtAfterOuter F n M params i) (r : Fin n → F)
    (l : List (Fin params.numGroups)) :
    simulateQ (simOracle oSpec oos)
        (l.mapM (fun a =>
          (query (spec := [OStmtAfterOuter F n M params]ₒ)
            (show [OStmtAfterOuter F n M params]ₒ.Domain from ⟨.helpers, ⟨a, r⟩⟩) :
            OracleComp (oSpec + [OStmtAfterOuter F n M params]ₒ) F)))
      = pure (l.map (fun a =>
          OracleInterface.answer
            (oos (⟨.helpers, ⟨a, r⟩⟩ : [OStmtAfterOuter F n M params]ₒ.Domain).1)
            (⟨.helpers, ⟨a, r⟩⟩ : [OStmtAfterOuter F n M params]ₒ.Domain).2)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have he : simulateQ (simOracle oSpec oos)
          (query (spec := [OStmtAfterOuter F n M params]ₒ)
            (show [OStmtAfterOuter F n M params]ₒ.Domain from ⟨.helpers, ⟨a, r⟩⟩) :
            OracleComp (oSpec + [OStmtAfterOuter F n M params]ₒ) F)
        = pure (OracleInterface.answer
            (oos (⟨.helpers, ⟨a, r⟩⟩ : [OStmtAfterOuter F n M params]ₒ.Domain).1)
            (⟨.helpers, ⟨a, r⟩⟩ : [OStmtAfterOuter F n M params]ₒ.Domain).2) :=
      simulateQ_simOracle_subspec_query oSpec F n M params oos
        (show [OStmtAfterOuter F n M params]ₒ.Domain from ⟨.helpers, ⟨a, r⟩⟩)
    rw [List.mapM_cons]
    simp only [simulateQ_bind, simulateQ_pure, ih, pure_bind, List.map_cons]
    exact he ▸ pure_bind _ _

/-- **`simOStmt` faithfulness.** Under the honest outer oracles, the lens' virtual-oracle
reconstruction simulates to the honest inner `Q`-oracle answer at `r`. -/
theorem logupSumcheck_simOStmt_faithful
    (os : StmtAfterOuter F n M params) (oos : ∀ i, OStmtAfterOuter F n M params i)
    (msgs : ∀ i, (logupSumcheckPSpec F n M params).Message i)
    (r : Fin n → F) :
    simulateQ (simOracle2 oSpec oos msgs)
        (OracleComp.liftComp
          (((logupSumcheckOracleLens oSpec F n M params).simOStmt ⟨(), r⟩).run os)
          (oSpec + ([OStmtAfterOuter F n M params]ₒ + [(logupSumcheckPSpec F n M params).Message]ₒ)))
      = simOracle2 oSpec
          ((logupSumcheckContextLens F n M params).stmt.proj (os, oos)).2 msgs
          (Sum.inr (Sum.inl ⟨(), r⟩)) := by
  classical
  rw [simulateQ_simOracle2_liftComp]
  simp only [logupSumcheckOracleLens, ReaderT.run, ReaderT.mk,
    simulateQ_bind, simulateQ_map, simulateQ_pure,
    simulateQ_simOracle_subspec_query, simulateQ_mapM_column, simulateQ_mapM_helper, map_pure]
  erw [pure_bind, pure_bind, pure_bind, pure_bind]
  simp only [logupSumcheckContextLens, logupSumcheckOracleStmt, OracleContext.Lens.proj,
    simOracle2, QueryImpl.addLift, QueryImpl.add, QueryImpl.liftTarget, OracleInterface.simOracle0]
  -- LHS = `pure (qAtPoint … evals)`, RHS = `pure (eval r Q)`; close via the finalEval identity.
  congr 1
  have hAgree : logupPointEvaluationsAgree F n M params r oos
      { multiplicity := OracleInterface.answer (oos OuterOracleIdx.multiplicity) r
        table := OracleInterface.answer (oos (OuterOracleIdx.input InputOracleIdx.table)) r
        columns := fun i =>
          (List.map (fun a => OracleInterface.answer (oos (OuterOracleIdx.input (InputOracleIdx.column a))) r)
            (List.finRange M)).getD (↑i) 0
        helpers := fun k =>
          (List.map (fun a => OracleInterface.answer
              (oos (⟨.helpers, ⟨a, r⟩⟩ : [OStmtAfterOuter F n M params]ₒ.Domain).1)
              (⟨.helpers, ⟨a, r⟩⟩ : [OStmtAfterOuter F n M params]ₒ.Domain).2)
            (List.finRange params.numGroups)).getD (↑k) 0 } := by
    refine ⟨rfl, rfl, fun i => ?_, fun k => ?_⟩
    · dsimp only
      rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_map, List.getElem_finRange]
      rfl
    · dsimp only
      rw [List.getD_eq_getElem _ _ (by simp [k.isLt]), List.getElem_map, List.getElem_finRange]
      rfl
  exact (logupSumcheckPolynomial_finalEval (F := F) (n := n) (M := M) (params := params)
    (stmt := os) (oStmt := oos) r _ hAgree).symm

/-- **`LiftContextCoherent` for the LogUp embedded-sumcheck lift (issue #13, design note #433).**
The virtual-oracle reconstruction `logupSumcheckOracleLens.simOStmt` is coherent with the inner
generic-sumcheck verifier's honest oracle answers, so the proven generic `Sumcheck.Spec`
completeness / RBR-soundness transfer through `sumcheckOracleReduction = (… ).liftContext` via
`OracleReduction.liftContext_perfectCompleteness` / `liftContext_rbr_soundness`.

* `hproj` — the non-oracle projection is the constant initial sumcheck statement, so `rfl`;
* `hfaith` — the proven faithfulness `logupSumcheck_simOStmt_faithful` (all inner queries have the
  form `⟨(), r⟩` since the inner oracle family is `Unit`-indexed);
* `hlift` — the output oracle family is empty (`OutputOracleIdx = Fin 0`), so `rfl`. -/
@[reducible] noncomputable def logupSumcheck_liftContextCoherent :
    OracleVerifier.LiftContextCoherent (logupSumcheckOracleLens oSpec F n M params)
      (logupConcreteSumcheckOracleReduction oSpec F n M params Fact.out).verifier :=
  liftContextCoherent_of (logupSumcheckOracleLens oSpec F n M params)
    (logupConcreteSumcheckOracleReduction oSpec F n M params Fact.out).verifier
    (fun _ _ => rfl)
    (fun os oos transcript q => by
      obtain ⟨⟨⟩, r⟩ := q
      exact logupSumcheck_simOStmt_faithful.{0} oSpec F n M params os oos transcript.messages r)
    (fun _ _ _ _ => Prod.ext rfl (funext fun i => i.elim0))

end LiftCoherent

end Logup

#print axioms Logup.simulateQ_mapM_column
#print axioms Logup.simulateQ_mapM_helper
#print axioms Logup.simulateQ_simOracle_subspec_query
#print axioms Logup.simulateQ_simOracle_liftComp_query
#print axioms Logup.list_mapM_pure
#print axioms Logup.logupSumcheck_simOStmt_faithful
#print axioms Logup.logupSumcheck_liftContextCoherent
