/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightSecondCompleteness
import ArkLib.ProofSystem.Spartan.TightConjoinedSecondLeaf
import ArkLib.ProofSystem.Sumcheck.Spec.PinnedCompleteness

/-!
# The binding strengthening of the carried-second completeness (issue #329, B7)

The enriched carried-second completeness (`secondSumcheckWithTarget_perfectCompleteness_enriched`)
conjoined with the first-terminal binding identity as a pass-through invariant, at unchanged
honest hypotheses — the completeness-side mirror of the conjoined KS leaf (`h₇`). Drafted by the
B7 workflow's R2 agent; verified and extracted in the take-over pass.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

section Leaves

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option linter.unusedFintypeInType false in
/-- **The binding strengthening of the carried second sum-check completeness** (#329, B7): the
enriched completeness (`secondSumcheckWithTarget_perfectCompleteness_enriched`) conjoined with
the first-terminal binding identity as a pass-through invariant, at the same honest hypotheses.

The pass-through fact is supported on the *whole run support*: the lifted verifier is
failing-deterministic with verdict `(v? (proj s) tr).map (lift s)`
(`sumcheckFull_toVerifier_isFailingDet` + `Verifier.liftContext_failingDet`), and the lift
forwards the passenger statement and the oracles untouched. -/
theorem secondSumcheckWithTarget_perfectCompleteness_enrichedBinding
    [oSpec.Fintype] [oSpec.Inhabited]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl
      ((secondSumcheckWithTargetRbrRelIn (R := R) pp oSpec)
        ∩ {x | x.1 ∈ bindingAtSecondIn (R := R) pp})
      ((secondSumcheckWithTargetRelOutEnriched (R := R) pp)
        ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp}) := by
  have h := secondSumcheckWithTarget_perfectCompleteness_enriched (R := R) pp oSpec
    (init := init) (impl := impl) hInit hImplSupp
  unfold OracleReduction.perfectCompleteness at h ⊢
  refine Reduction.perfectCompleteness_strengthen_support h Set.inter_subset_left ?_
  rintro stmtIn witIn ⟨_, hBind⟩ ⟨⟨td, prv⟩, vOut⟩ hsupp hRel _
  refine ⟨hRel, ?_⟩
  -- Run-support decomposition: the verifier output is in the verifier's own run support.
  have hv : some vOut ∈ support (OptionT.run
      ((secondSumcheckReductionWithTarget (R := R) pp oSpec).verifier.toVerifier.run
        stmtIn td)) :=
    Reduction.mem_support_verifier_run_of_mem_support_run _ stmtIn witIn hsupp
  -- Failing-determinism: the lifted verifier's verdict is `(v? (proj s) tr).map (lift s)`.
  obtain ⟨v?, hvdet⟩ := sumcheckFull_toVerifier_isFailingDet
    (R := R) (oSpec := oSpec) 2 (boolEmbedding R) pp.ℓ_n
  have hcomm := (secondSumcheckCoherentWithTarget (R := R) pp oSpec).toVerifier_comm
  have hVeq : (secondSumcheckReductionWithTarget (R := R) pp oSpec).verifier.toVerifier
      = ⟨fun s tr => OptionT.mk (pure ((v?
          ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.proj s) tr).map
          ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.lift s)))⟩ := by
    refine hcomm.trans ?_
    exact Verifier.liftContext_failingDet
      (secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens _ v? hvdet
  rw [hVeq] at hv
  simp only [Verifier.run, OptionT.run_mk, support_pure, Set.mem_singleton_iff] at hv
  -- Extract the inner output and the lift shape; the lift forwards the passenger data.
  rcases hverd : (v? ((secondSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.proj
      stmtIn) td) with _ | so
  · rw [hverd] at hv
    simp at hv
  · rw [hverd] at hv
    simp only [Option.map_some, Option.some.injEq] at hv
    obtain ⟨⟨T, stmt⟩, oStmt⟩ := stmtIn
    obtain ⟨⟨t', r_y⟩, innerO⟩ := so
    rw [hv]
    exact hBind


end Leaves

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.secondSumcheckWithTarget_perfectCompleteness_enrichedBinding
