/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Spartan.SecondSumcheckReduction
import ArkLib.ProofSystem.Spartan.SecondSumcheckRelIn
import ArkLib.ProofSystem.Spartan.SecondSumcheckFaithful
import ArkLib.ProofSystem.Sumcheck.Spec.OracleCompletenessUncondCorrect

/-!
# Spartan second sum-check phase completeness, fully bridge-free (#114)

The symmetric twin of `FirstSumcheckBridgeFree`: re-points Spartan's **second** sum-check phase
completeness onto the proven bridge-free inner completeness
`Sumcheck.Spec.oracleReduction_perfectCompleteness_unconditional`
(`OracleCompletenessUncondCorrect.lean`, "via proven CubeFiber, no false bridge"), so the only
hypotheses are the irreducible execution-model side conditions `hInit`/`hImplSupp` — **no `hBridge`**.

**Why a separate module (and why it routes around `SecondSumcheckComplete`).** Two reasons stack:
(1) this keeps the bridge-free dependency chain isolated from the older bridge-gated theorem; and
(2) `SecondSumcheckComplete.lean` (which holds the second-sum-check relations / lens-completeness /
transfer) currently fails to build — its `secondSumcheck_rbrKnowledgeSoundness` theorem is missing an
`Extractor.Lens.IsKnowledgeSound` instance and an `open scoped NNReal` (so `ℝ≥0` mis-parses), which
makes the whole file unimportable. This module therefore imports **only** the clean chain
(`SecondSumcheckReduction`, `SecondSumcheckRelIn`, `SecondSumcheckFaithful`) + the bridge-free
completeness, never `SecondSumcheckComplete` nor the gated `OracleCompleteness`, and restates the
relations / lens-completeness instance / transfer under fresh `BF` names. The completeness deliverable
is thus achievable bridge-free even while the soundness theorem in `SecondSumcheckComplete` is WIP.
-/

open MvPolynomial OracleComp Sumcheck
open scoped NNReal

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- Outer input relation of the second sum-check phase (restated, bridge-free module). -/
def secondSumcheckRelInBF :
    Set (((R × Statement.AfterLinearCombination R pp) ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2.2.2
          (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0)))
        ∧ x.1.1.1 = ∑ idx, x.1.1.2.1 idx *
            evalClaimValue R pp x.1.1.2.2 (fun i => x.1.2 (.inr i)) idx }

/-- Outer output relation of the second sum-check phase (restated, bridge-free module). -/
def secondSumcheckRelOutBF :
    Set ((Statement.AfterSecondSumcheck R pp ×
        (∀ i, OracleStatement.AfterSecondSumcheck R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2.2.2
      (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0))) }

/-- `OracleContext.Lens.IsComplete` for the second sum-check lens (restated, bridge-free module). -/
instance secondSumcheckLensCompleteBF :
    (secondSumcheckContextLens pp).toContext.IsComplete
      (secondSumcheckRelInBF pp)
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
      (secondSumcheckRelOutBF pp)
      (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))
      ((Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).toReduction.compatContext
        (secondSumcheckContextLens pp).toContext) where
  proj_complete := by
    rintro ⟨⟨t, stmt⟩, oStmt⟩ ⟨⟩ hRelIn
    simp only [secondSumcheckRelInBF, Set.mem_setOf_eq] at hRelIn
    obtain ⟨_hR1CS, ht⟩ := hRelIn
    rw [ht]
    exact Bricks.secondSC_relationRound_zero pp stmt oStmt
      ⟨secondSumCheckVirtualPolynomial R pp stmt oStmt, secondSCVP_mem_restrictDegree pp stmt oStmt⟩
      rfl
  lift_complete := by
    rintro ⟨⟨t, stmt⟩, oStmt⟩ ⟨⟩ ⟨⟨t_out, r_y⟩, oStmt'⟩ ⟨⟩ _hCompat hRelIn _hRelOut
    simp only [secondSumcheckRelInBF, Set.mem_setOf_eq] at hRelIn
    simpa only [secondSumcheckRelOutBF, Set.mem_setOf_eq] using hRelIn.1

/-- Second sum-check phase perfect completeness (restated transfer), given inner completeness. -/
theorem secondSumcheck_perfectCompletenessBF
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (h_inner :
      (Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec).perfectCompleteness
        init impl
        (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
        (Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))) :
    (secondSumcheckReduction pp oSpec).perfectCompleteness init impl
      (secondSumcheckRelInBF (R := R) pp) (secondSumcheckRelOutBF (R := R) pp) := by
  haveI := secondSumcheckCoherent (R := R) pp oSpec
  exact OracleReduction.liftContext_perfectCompleteness
    (R := Sumcheck.Spec.oracleReduction R 2 (boolEmbedding R) pp.ℓ_n oSpec)
    (lens := secondSumcheckContextLens pp)
    (stmtLens := secondSumcheckOracleLens pp oSpec)
    (outerRelIn := secondSumcheckRelInBF (R := R) pp)
    (innerRelIn := Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (0 : Fin (pp.ℓ_n + 1)))
    (outerRelOut := secondSumcheckRelOutBF (R := R) pp)
    (innerRelOut := Sumcheck.Spec.relationRound R pp.ℓ_n 2 (boolEmbedding R) (Fin.last pp.ℓ_n))
    rfl h_inner

/-- **Second sum-check phase perfect completeness, FULLY bridge-free (#114).** Discharges the inner
multi-round sum-check completeness from the proven bridge-free
`Sumcheck.Spec.oracleReduction_perfectCompleteness_unconditional`, so the *only* hypotheses are the
irreducible execution-model side conditions `hInit`/`hImplSupp` — **no `hBridge`**. The second
sum-check completeness deliverable of #114, made unconditional, routing around the build-broken
`SecondSumcheckComplete`. -/
theorem secondSumcheck_perfectCompleteness_bridgeFree
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    [Inhabited R] [oSpec.Fintype] [oSpec.Inhabited]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (secondSumcheckReduction pp oSpec).perfectCompleteness init impl
      (secondSumcheckRelInBF (R := R) pp) (secondSumcheckRelOutBF (R := R) pp) :=
  secondSumcheck_perfectCompletenessBF pp oSpec
    (Sumcheck.Spec.oracleReduction_perfectCompleteness_unconditional hInit hImplSupp)

end Spartan.Spec
