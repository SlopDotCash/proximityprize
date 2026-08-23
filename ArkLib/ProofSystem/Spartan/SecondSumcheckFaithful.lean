/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.SecondSumcheckReduction
import ArkLib.ProofSystem.Spartan.SecondSumcheckSimOStmt
import ArkLib.OracleReduction.LiftContext.Coherence

/-!
# Faithfulness of the lifted second sum-check `simOStmt` (issue #114)

The Spartan second sum-check oracle reduction is built by lifting the proven sum-check oracle
reduction onto the virtual polynomial `ℳ(Y) = ∑ r_idx · M_idx(r_x, Y) · Z(Y)` via
`OracleReduction.liftContext`. To transfer the sum-check's completeness through the lift one must
discharge the `OracleVerifier.LiftContextCoherent` coherence condition (design note #433), whose
mathematical core is the **`simOStmt` faithfulness** of the lens used by the second sum-check:

* `secondSumcheckEvalFromOracles_simOracle` (Step B) — interpreting the inlined oracle
  reconstruction `secondSumcheckEvalFromOracles` under the honest single-family oracle
  `OracleInterface.simOracle` returns exactly `eval point ℳ`. This is the genuine algebra: the
  three matrix oracle queries answer the bivariate `toMLE` evaluations and the Boolean-cube
  `foldlM` reconstructs `Z(point) = eval point (MLE 𝕫)` (reusing the landed
  `Bricks.zEvalPureFold_eq_mle_z`), and the product is `eval point ℳ`.

* `secondSumcheckEvalFromOracles_simOracle2` — the same faithfulness in the exact shape required by
  `OracleVerifier.LiftContext.liftContextCoherent_of`'s `hfaith` hypothesis: the lens' oracle
  reconstruction, lifted into the verifier's full oracle spec `oSpec + ([oStmt]ₒ + [Msg]ₒ)` and
  simulated under the honest two-family oracle `simOracle2`, equals `eval point ℳ`. This is reduced
  to Step B by the routing-plumbing lemma `simulateQ_liftComp_eq_of_apply`.

All results are axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

open MvPolynomial OracleComp OracleSpec OracleInterface OracleVerifier.LiftContext

namespace OracleComp

/-- **Routing plumbing.** Simulating a lifted computation under `impl` equals simulating the
original computation under `impl₀`, provided the two implementations agree per (lifted) query. This
is the general statement behind reducing `simulateQ (simOracle2 …) (liftComp X …)` to a
single-family `simulateQ (simOracle …) X`. -/
lemma simulateQ_liftComp_eq_of_apply
    {ι : Type} {spec : OracleSpec ι} {ι' : Type} {spec' : OracleSpec ι'}
    {m' : Type → Type} [Monad m'] [LawfulMonad m']
    [MonadLiftT (OracleQuery spec) (OracleQuery spec')]
    (impl : QueryImpl spec' m') (impl₀ : QueryImpl spec m')
    (h : ∀ (t : spec.Domain),
      simulateQ impl (liftComp (liftM (spec.query t) : OracleComp spec (spec.Range t)) spec')
        = impl₀ t)
    {α : Type} (oa : OracleComp spec α) :
    simulateQ impl (liftComp oa spec') = simulateQ impl₀ oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
      rw [liftComp_bind, simulateQ_bind, simulateQ_bind, h t, simulateQ_spec_query]
      exact bind_congr fun u => ih u

end OracleComp

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- Collapse the map of a lifted `Id` value (the residual shape after `simulateQ` reduces a single
honest oracle query) to `pure`. -/
@[local simp] lemma map_liftM_Id {ιj : Type} {sp : OracleSpec ιj} {α β : Type} (f : α → β)
    (v : Id α) : (f <$> liftM v : OracleComp sp β) = pure (f v) := rfl

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- Simulating a `foldlM` whose every step simulates to a pure value collapses to the `foldl` of the
pure steps. -/
lemma simulateQ_simOracle_foldlM (oos : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    {β : Type}
    (stepM : R → β → OracleComp (oSpec + [OracleStatement.AfterLinearCombination R pp]ₒ) R)
    (stepPure : R → β → R) (xs : List β) (acc : R)
    (hstep : ∀ a y,
      simulateQ (OracleInterface.simOracle oSpec oos) (stepM a y) = pure (stepPure a y)) :
    simulateQ (OracleInterface.simOracle oSpec oos) (xs.foldlM stepM acc)
      = pure (xs.foldl stepPure acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
      rw [List.foldlM_cons, List.foldl_cons, simulateQ_bind, hstep]
      simpa using ih (stepPure acc y)

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- **`simOStmt` faithfulness (Step B).** The honest simulation, under the single-family oracle
`simOracle`, of the inlined oracle reconstruction `secondSumcheckEvalFromOracles` equals
`eval point ℳ`. The three matrix queries answer the bivariate `toMLE` evaluations and the
Boolean-cube fold reconstructs `Z(point)`. -/
theorem secondSumcheckEvalFromOracles_simOracle
    (oos : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    (stmt : Statement.AfterLinearCombination R pp) (point : Fin pp.ℓ_n → R) :
    simulateQ (OracleInterface.simOracle oSpec oos)
        (secondSumcheckEvalFromOracles pp oSpec stmt point)
      = pure (eval point (secondSumCheckVirtualPolynomial R pp stmt oos)) := by
  classical
  have hfold :
      simulateQ (OracleInterface.simOracle oSpec oos)
          ((Finset.univ : Finset (Fin (2 ^ pp.ℓ_n))).toList.foldlM
            (fun (acc : R) (yEnum : Fin (2 ^ pp.ℓ_n)) => do
              let coeff : R := eval point (eqPolynomial (boolPoint R yEnum))
              let zVal : R ←
                if hy : (yEnum : ℕ) < pp.toSizeR1CS.n_x then
                  (pure (stmt.2.2.2 ⟨(yEnum : ℕ), hy⟩) :
                    OracleComp (oSpec + [OracleStatement.AfterLinearCombination R pp]ₒ) R)
                else
                  (OracleComp.lift <| OracleSpec.query
                    (spec := [OracleStatement.AfterLinearCombination R pp]ₒ)
                    (show [OracleStatement.AfterLinearCombination R pp]ₒ.Domain from
                      ⟨.inr (.inr 0), boolPoint R ⟨(yEnum : ℕ) - pp.toSizeR1CS.n_x, by
                        have hlt := yEnum.isLt
                        have hle : 2 ^ pp.ℓ_w ≤ 2 ^ pp.ℓ_n :=
                          Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
                        have hnx : pp.toSizeR1CS.n_x = 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w := rfl
                        omega⟩⟩) :
                    OracleComp (oSpec + [OracleStatement.AfterLinearCombination R pp]ₒ) R)
              pure (acc + coeff * zVal))
            (0 : R))
        = pure (eval point (MLE (R1CS.𝕫 stmt.2.2.2 (oos (.inr (.inr 0))) ∘ finFunctionFinEquiv))) := by
    rw [simulateQ_simOracle_foldlM pp oSpec oos _
          (Bricks.zEvalPureFoldStep R pp ⟨point, stmt⟩ oos)]
    · rw [show (Finset.univ : Finset (Fin (2 ^ pp.ℓ_n))).toList.foldl
              (Bricks.zEvalPureFoldStep R pp ⟨point, stmt⟩ oos) 0
            = Bricks.zEvalPureFold R pp ⟨point, stmt⟩ oos from rfl]
      rw [Bricks.zEvalPureFold_eq_mle_z R pp ⟨point, stmt⟩ oos]
    · intro a y
      unfold Bricks.zEvalPureFoldStep
      by_cases hy : (y : ℕ) < pp.toSizeR1CS.n_x
      · simp [hy]
      · simp [hy, OracleInterface.simOracle, OracleInterface.simOracle0, OracleInterface.answer,
          map_liftM_Id]
  unfold secondSumcheckEvalFromOracles
  simp only [simulateQ_bind]
  rw [hfold]
  conv_lhs => simp [OracleInterface.simOracle, map_liftM_Id]
  refine congrArg pure ?_
  show (stmt.1 .A * eval point (eval ((C : R →+* MvPolynomial (Fin pp.ℓ_n) R) ∘ stmt.2.1)
          (oos (.inr (.inl .A))).toMLE)
      + stmt.1 .B * eval point (eval ((C : R →+* MvPolynomial (Fin pp.ℓ_n) R) ∘ stmt.2.1)
          (oos (.inr (.inl .B))).toMLE)
      + stmt.1 .C * eval point (eval ((C : R →+* MvPolynomial (Fin pp.ℓ_n) R) ∘ stmt.2.1)
          (oos (.inr (.inl .C))).toMLE))
      * eval point (MLE (R1CS.𝕫 stmt.2.2.2 (oos (.inr (.inr 0))) ∘ finFunctionFinEquiv))
      = eval point (secondSumCheckVirtualPolynomial R pp stmt oos)
  simp only [secondSumCheckVirtualPolynomial, eval_add, eval_mul, eval_C, Function.comp_def,
    Fin.cast_eq_self]
  ring

omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- **`hfaith` for the second sum-check lens.** The lens' oracle reconstruction
`secondSumcheckEvalFromOracles`, lifted into the verifier's full oracle spec and simulated under the
honest two-family oracle `simOracle2`, equals `eval point ℳ`. This is the exact per-inner-query
faithfulness consumed by `OracleVerifier.LiftContext.liftContextCoherent_of`. -/
theorem secondSumcheckEvalFromOracles_simOracle2
    (oos : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    (msgs : ∀ i, (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Message i)
    (stmt : Statement.AfterLinearCombination R pp) (point : Fin pp.ℓ_n → R) :
    simulateQ (OracleInterface.simOracle2 oSpec oos msgs)
        (OracleComp.liftComp (secondSumcheckEvalFromOracles pp oSpec stmt point)
          (oSpec + ([OracleStatement.AfterLinearCombination R pp]ₒ
            + [(Sumcheck.Spec.pSpec R 2 pp.ℓ_n).Message]ₒ)))
      = pure (eval point (secondSumCheckVirtualPolynomial R pp stmt oos)) := by
  rw [OracleComp.simulateQ_liftComp_eq_of_apply
        (OracleInterface.simOracle2 oSpec oos msgs) (OracleInterface.simOracle oSpec oos) ?hq]
  · exact secondSumcheckEvalFromOracles_simOracle pp oSpec oos stmt point
  case hq =>
    intro t
    rcases t with q | q <;>
    · rw [OracleComp.liftComp_query]
      simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
      erw [simulateQ_spec_query]
      rfl

/-- **`LiftContextCoherent` instance for the Spartan second sum-check lens.** Discharges the #433
framework gate (`OracleVerifier.LiftContextCoherent.toVerifier_comm`) for the second sum-check lift,
built from the three coherences via `liftContextCoherent_of`:
* `hproj` — `rfl` (the lens' `projStmt` matches `toLens.proj`'s non-oracle component);
* `hfaith` — the `simOStmt` faithfulness `secondSumcheckEvalFromOracles_simOracle2`;
* `hlift` — `simp` (the lens' output lift discards the inner oracle component).

This is the second-phase instantiation of the framework discharge landed in `LiftContext/Coherence`:
the previously-open `toVerifier_comm` is now a proved instance for the Spartan second sum-check,
unblocking its completeness transfer through `liftContext_perfectCompleteness`. -/
@[reducible] noncomputable def secondSumcheckCoherent :
    OracleVerifier.LiftContextCoherent (secondSumcheckOracleLens pp oSpec)
      (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).verifier :=
  liftContextCoherent_of (secondSumcheckOracleLens pp oSpec) _
    (fun _ _ => rfl)
    (by
      intro os oos transcript q
      obtain ⟨t, stmt⟩ := os
      obtain ⟨idx, point⟩ := q
      refine (secondSumcheckEvalFromOracles_simOracle2 pp oSpec oos transcript.messages stmt
        point).trans ?_
      simp only [secondSumcheckOracleLens, secondSumcheckStmtLens, OracleStatement.Lens.proj,
        OracleInterface.simOracle2, QueryImpl.addLift, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply, OracleInterface.simOracle0,
        OracleInterface.answer]
      rfl)
    (by
      intro os oos transcript so
      obtain ⟨t, stmt⟩ := os
      simp [secondSumcheckOracleLens, secondSumcheckStmtLens, OracleStatement.Lens.lift,
        OracleStatement.Lens.proj])

end Spartan.Spec
