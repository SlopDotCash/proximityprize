/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Spartan.FirstSumcheckReduction
import ArkLib.ProofSystem.Spartan.FirstSumcheckRelComplete
import ArkLib.ProofSystem.Sumcheck.Spec.OracleCompletenessUncondCorrect

/-!
# Spartan first sum-check phase completeness, fully bridge-free (#114)

`SpartanSumcheckUnconditional.firstSumcheck_perfectCompleteness_unconditional` discharges the inner
multi-round sum-check completeness from
`Sumcheck.Spec.oracleReduction_perfectCompleteness_of_bridge`, the **bridge-gated** version
(`OracleCompleteness.lean`): it still threads the explicit verifier-fusion residual
`hBridge : oracleReductionToReductionResidual`.

The bridge-free unconditional inner completeness
`Sumcheck.Spec.oracleReduction_perfectCompleteness_unconditional`
(`OracleCompletenessUncondCorrect.lean`, "via proven CubeFiber, no false bridge") needs **only** the
irreducible execution-model side conditions `hInit`/`hImplSupp` — its per-round lens coherence is
discharged internally by the proven `CubeFiber`. This module re-points Spartan's first sum-check
phase onto it, yielding `firstSumcheck_perfectCompleteness_bridgeFree` with **no `hBridge`
obligation** — the first sum-check completeness deliverable of #114 made unconditional.

**Why a separate module.** This module imports **only** the clean lens/relation chain
(`FirstSumcheckReduction`, `FirstSumcheckRelComplete`) plus `OracleCompletenessUncondCorrect`, never
the bridge-gated `OracleCompleteness`, and restates the relations / lens-completeness instance /
transfer under fresh `BF` names (exactly as `SpartanSumcheckUnconditional` restates them to avoid
mid-refactor deps). The old short-name collision between the bridge-gated and threaded sum-check
theorems has been removed; the separation here is now just dependency hygiene.
-/

open MvPolynomial OracleComp OracleSpec Sumcheck

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- Outer input relation of the first sum-check phase (restated, bridge-free module). -/
def firstSumcheckRelInBF :
    Set ((Statement.AfterFirstChallenge R pp ×
        (∀ i, OracleStatement.AfterFirstChallenge R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2
      (fun idx => x.1.2 (.inl idx)) (x.1.2 (.inr 0)) }

/-- Outer output relation of the first sum-check phase (restated, bridge-free module). -/
def firstSumcheckRelOutBF :
    Set ((Statement.AfterFirstSumcheck R pp ×
        (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2
      (fun idx => x.1.2 (.inl idx)) (x.1.2 (.inr 0)) }

/-- `OracleContext.Lens.IsComplete` for the first sum-check lens (restated, bridge-free module). -/
instance firstSumcheckLensCompleteBF :
    (firstSumcheckContextLens pp).toContext.IsComplete
      (firstSumcheckRelInBF pp)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
      (firstSumcheckRelOutBF pp)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
      ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).toReduction.compatContext
        (firstSumcheckContextLens pp).toContext) where
  proj_complete := by
    rintro ⟨⟨τ, 𝕩⟩, oStmt⟩ ⟨⟩ hRelIn
    simp only [firstSumcheckRelInBF, Set.mem_setOf_eq] at hRelIn
    exact firstSumcheck_proj_mem_relationRound pp τ 𝕩 oStmt hRelIn
  lift_complete := by
    rintro ⟨⟨τ, 𝕩⟩, oStmt⟩ ⟨⟩ ⟨⟨t_out, r_x⟩, oStmt'⟩ ⟨⟩ _hCompat hRelIn _hRelOut
    simp only [firstSumcheckRelInBF, Set.mem_setOf_eq] at hRelIn
    simpa only [firstSumcheckRelOutBF, Set.mem_setOf_eq] using hRelIn

/-- First sum-check phase perfect completeness (restated transfer), given inner completeness. -/
theorem firstSumcheck_perfectCompletenessBF
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (h_inner :
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).perfectCompleteness
        init impl
        (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
        (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))) :
    (firstSumcheckReduction pp oSpec).perfectCompleteness init impl
      (firstSumcheckRelInBF (R := R) pp) (firstSumcheckRelOutBF (R := R) pp) := by
  haveI := firstSumcheckCoherent (R := R) pp oSpec
  exact OracleReduction.liftContext_perfectCompleteness
    (R := Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec)
    (lens := firstSumcheckContextLens pp)
    (stmtLens := firstSumcheckOracleLens pp oSpec)
    (outerRelIn := firstSumcheckRelInBF (R := R) pp)
    (innerRelIn := Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
    (outerRelOut := firstSumcheckRelOutBF (R := R) pp)
    (innerRelOut := Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
    rfl h_inner

/-- **First sum-check phase perfect completeness, FULLY bridge-free (#114).** Discharges the inner
multi-round sum-check completeness from the proven bridge-free
`Sumcheck.Spec.oracleReduction_perfectCompleteness_unconditional`, so the *only* hypotheses are the
irreducible execution-model side conditions `hInit`/`hImplSupp` — **no `hBridge`** verifier-fusion
obligation remains on the caller. This is the first sum-check completeness deliverable of #114, made
unconditional (the bridge→threaded re-point that `firstSumcheck_perfectCompleteness_unconditional`
left open). -/
theorem firstSumcheck_perfectCompleteness_bridgeFree
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    [Inhabited R] [oSpec.Fintype] [oSpec.Inhabited]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (firstSumcheckReduction pp oSpec).perfectCompleteness init impl
      (firstSumcheckRelInBF (R := R) pp) (firstSumcheckRelOutBF (R := R) pp) :=
  firstSumcheck_perfectCompletenessBF pp oSpec
    (Sumcheck.Spec.oracleReduction_perfectCompleteness_unconditional hInit hImplSupp)

end Spartan.Spec
