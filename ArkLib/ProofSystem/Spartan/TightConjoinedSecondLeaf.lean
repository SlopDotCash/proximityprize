/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.SecondSumcheckWithTarget
import ArkLib.ProofSystem.Spartan.TightMidLeaves
import ArkLib.OracleReduction.Security.RbrKnowledgeConjoin

/-!
# The conjoined carried second sum-check leaf (issue #329, X-lane, leaf `h₇`)

**The first application of `Verifier.rbrKnowledgeSoundness_conjoin`** (the #114 combinator): the
carried second sum-check leaf (`secondSumcheckWithTarget_rbrKnowledgeSoundness_honest_full`,
per-round error `2/|R|`) is conjoined with the first-terminal binding identity
`e₁ = eq̃(τ)(r_x)·(v_A·v_B − v_C)` as a pass-through statement predicate, at **unchanged error**.

The preservation hypothesis `hPres` is discharged by failing-determinism: the compiled inner
sum-check verifier is failing-deterministic (`sumcheckFull_toVerifier_isFailingDet`), so by
`Verifier.liftContext_failingDet` the lifted verifier's verdict is
`(v? (proj s) tr).map (lift s)` — and the lift forwards the passenger statement and the oracles
untouched, so any positively-probable output satisfying the output binding forces the input
binding.

This is leaf `h₇` of the tight chain: from `tightRelG`-shaped input (the carried sum-check
round-0 claim ∧ binding) to the carried transported terminal relation ∧ binding, error `2/|R|`.
-/

open OracleComp OracleSpec ProtocolSpec Function
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

/-- The first-terminal binding identity at the carried second sum-check's **input** type
`(T, (r, (e₁, (r_x, τ, 𝕩))))` with the post-RLC oracle family. -/
@[reducible]
def bindingAtSecondIn :
    Set ((R × Statement.AfterLinearCombinationWithTarget R pp) ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) :=
  { x | (x.1.2.2, x.2) ∈ evalClaimBindingRel (R := R) pp }

/-- The first-terminal binding identity at the carried second sum-check's **output** type
`((e₂, r_y), (r, (e₁, (r_x, τ, 𝕩))))`. -/
@[reducible]
def bindingAtSecondOut :
    Set (Statement.AfterSecondSumcheckWithTarget R pp ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) :=
  { y | (y.1.2.2, y.2) ∈ evalClaimBindingRel (R := R) pp }

section Conjoined

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option linter.unusedFintypeInType false in
/-- **Leaf `h₇` (tight chain): the conjoined carried second sum-check rbr-KS leaf** at unchanged
per-round error `2/|R|` — the first application of `Verifier.rbrKnowledgeSoundness_conjoin`. -/
theorem secondSumcheckWithTarget_conjoined_rbrKnowledgeSoundness [Subsingleton σ]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0) :
    (secondSumcheckReductionWithTarget (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      ((secondSumcheckWithTargetRbrRelIn (R := R) pp oSpec)
        ∩ {x | x.1 ∈ bindingAtSecondIn (R := R) pp})
      ((secondSumcheckWithTargetRbrRelOut (R := R) pp oSpec)
        ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp})
      (fun _ => (2 : ℝ≥0) / (Fintype.card R)) := by
  have hbase := secondSumcheckWithTarget_rbrKnowledgeSoundness_honest_full
    (R := R) pp oSpec (init := init) (impl := impl) hInit hInitNF
  unfold OracleVerifier.rbrKnowledgeSoundness at hbase ⊢
  refine Verifier.rbrKnowledgeSoundness_conjoin hbase
    (bindingAtSecondIn (R := R) pp) (bindingAtSecondOut (R := R) pp) ?_
  -- `hPres`: a positively-probable output satisfying the output binding forces the input binding.
  intro stmtIn tr hPr
  -- The lifted verifier is failing-deterministic with an explicitly passenger-preserving verdict.
  obtain ⟨v?, hv⟩ := sumcheckFull_toVerifier_isFailingDet
    (R := R) (oSpec := oSpec) 2 (boolEmbedding R) pp.ℓ_n
  have hcomm := (secondSumcheckCoherentWithTarget (R := R) pp oSpec).toVerifier_comm
  have hVeq : (secondSumcheckReductionWithTarget (R := R) pp oSpec).verifier.toVerifier
      = ⟨fun s tr => OptionT.mk (pure ((v?
          ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.proj s) tr).map
          ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.lift s)))⟩ := by
    refine hcomm.trans ?_
    exact Verifier.liftContext_failingDet
      (secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens _ v? hv
  rw [gt_iff_lt, probEvent_pos_iff] at hPr
  obtain ⟨x, hx, hPx⟩ := hPr
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _, hx⟩ := hx
  rw [hVeq] at hx
  have key : (simulateQ impl
      ((⟨fun s tr => OptionT.mk (pure ((v?
          ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.proj s) tr).map
          ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.lift s)))⟩ :
        Verifier oSpec _ _ _).run stmtIn tr)).run' s
      = pure ((v?
          ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.proj stmtIn) tr).map
          ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.lift stmtIn)) := by
    change (simulateQ impl (pure _ : OracleComp oSpec (Option _))).run' s = _
    rw [simulateQ_pure]
    change Prod.fst <$> (pure _ : StateT σ ProbComp _).run s = _
    rw [StateT.run_pure]
    simp [map_pure]
  rw [key] at hx
  simp only [support_pure, Set.mem_singleton_iff] at hx
  -- `some x = verdict.map (lift stmtIn)`: extract the inner output and the lift shape.
  rcases hverd : (v? ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.proj
      stmtIn) tr) with _ | so
  · rw [hverd] at hx
    simp at hx
  · rw [hverd] at hx
    simp only [Option.map_some, Option.some.injEq] at hx
    -- The lift forwards the passenger statement and the oracles: read the binding back.
    obtain ⟨⟨T, stmt⟩, oStmt⟩ := stmtIn
    obtain ⟨⟨t', r_y⟩, innerO⟩ := so
    subst hx
    exact hPx

end Conjoined

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.secondSumcheckWithTarget_conjoined_rbrKnowledgeSoundness
