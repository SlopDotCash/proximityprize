/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FirstSumcheckReduction
import ArkLib.ProofSystem.Spartan.FirstSumcheckRelComplete
import ArkLib.ProofSystem.Sumcheck.Spec.OracleCompleteness

/-!
# Spartan first sum-check phase completeness, with the inner oracle completeness discharged (#114)

`FirstSumcheckComplete.firstSumcheck_perfectCompleteness` transfers the perfect completeness of the
**generic multi-round sum-check oracle reduction** through the Spartan `liftContext`, but it takes
that inner completeness `h_inner` as a *hypothesis*. This module re-derives the transfer (with its
input/output relations and the lens-completeness instance, copied from `FirstSumcheckComplete`) and
discharges `h_inner` from the bridge-gated
`Sumcheck.Spec.oracleReduction_perfectCompleteness_of_bridge`,
yielding `firstSumcheck_perfectCompleteness_unconditional`.

This file imports only the **clean** First sum-check dependency files
(`FirstSumcheckReduction`, `FirstSumcheckRelComplete`) plus `Sumcheck.Spec.OracleCompleteness`, so
it does not depend on the parts of `FirstSumcheckComplete`/`SpartanBricks` that are mid-refactor;
the relations and lens-completeness instance are therefore restated here under fresh names
(`firstSumcheckRelIn'`, `firstSumcheckRelOut'`, `firstSumcheckLensComplete'`).

## What is and is not unconditional (legacy route)

`Sumcheck.Spec.oracleReduction_perfectCompleteness_of_bridge` is stated modulo the explicit
bridge

  `hBridge : (oracleReduction R deg D n oSpec).toReduction = reduction R deg D n oSpec`

(`Sumcheck.Spec.oracleReductionToReductionResidual`), together with the standard execution-side side
conditions `hInit : NeverFail init` and `hImplSupp` (the implementation routes oracle queries with
the bare-oracle support). Accordingly `firstSumcheck_perfectCompleteness_unconditional` keeps
`hBridge` as an explicit hypothesis; despite its name it is a conditional, legacy theorem.

**Status of `hBridge` (updated).** The general verifier-fusion layer is no longer open: binary
verifier fusion is proved (`binaryVerifierFusion_proof` in `OracleCompletenessUncond.lean`) and
lifts to `seqCompose` (`OracleVerifier.seqCompose_toVerifier_of_binary`), so
`Sumcheck.Spec.oracleReductionToReductionResidual_of_binary` reduces `hBridge` to the per-round
equation `(SingleRound.oracleReduction i).toReduction = SingleRound.reduction i`. That per-round
equation is the documented suspected-false `oracleReduction_eq_reduction` (the oracle and plain
verifiers check different objects; see the `oracleReductionToReductionResidual` docstring), so
`hBridge` should not be expected to be supplied. The live, bridge-free result is
`FirstSumcheckBridgeFree.firstSumcheck_perfectCompleteness_bridgeFree`, which needs only
`hInit`/`hImplSupp` (via `Sumcheck.Spec.oracleReduction_perfectCompleteness_unconditional`). The
relations, lens-completeness instance and transfer proof below duplicate those of
`FirstSumcheckComplete` and `FirstSumcheckBridgeFree`; the primed names are used only in this
file.
-/

open MvPolynomial OracleComp OracleSpec Sumcheck

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- **Outer input relation of the first sum-check phase** (restated; identical to
`FirstSumcheckComplete.firstSumcheckRelIn`). The R1CS instance is satisfied; the recorded
first-challenge `τ` is irrelevant to satisfiability. -/
def firstSumcheckRelIn' :
    Set ((Statement.AfterFirstChallenge R pp ×
        (∀ i, OracleStatement.AfterFirstChallenge R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2
      (fun idx => x.1.2 (.inl idx)) (x.1.2 (.inr 0)) }

/-- **Outer output relation of the first sum-check phase** (restated; identical to
`FirstSumcheckComplete.firstSumcheckRelOut`). The same R1CS satisfiability, carried through the
sum-check (only `r_x` is added). -/
def firstSumcheckRelOut' :
    Set ((Statement.AfterFirstSumcheck R pp ×
        (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2
      (fun idx => x.1.2 (.inl idx)) (x.1.2 (.inr 0)) }

/-- **`OracleContext.Lens.IsComplete` for the first sum-check lens** (restated; identical proof to
`FirstSumcheckComplete.firstSumcheckLensComplete`). `proj_complete` via
`firstSumcheck_proj_mem_relationRound`, `lift_complete` via R1CS pass-through. -/
instance firstSumcheckLensComplete' :
    (firstSumcheckContextLens pp).toContext.IsComplete
      (firstSumcheckRelIn' pp)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
      (firstSumcheckRelOut' pp)
      (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
      ((Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).toReduction.compatContext
        (firstSumcheckContextLens pp).toContext) where
  proj_complete := by
    rintro ⟨⟨τ, 𝕩⟩, oStmt⟩ ⟨⟩ hRelIn
    simp only [firstSumcheckRelIn', Set.mem_ofPred_eq] at hRelIn
    exact firstSumcheck_proj_mem_relationRound pp τ 𝕩 oStmt hRelIn
  lift_complete := by
    rintro ⟨⟨τ, 𝕩⟩, oStmt⟩ ⟨⟩ ⟨⟨t_out, r_x⟩, oStmt'⟩ ⟨⟩ _hCompat hRelIn _hRelOut
    simp only [firstSumcheckRelIn', Set.mem_ofPred_eq] at hRelIn
    exact hRelIn

/-- **First sum-check phase perfect completeness (restated), given inner completeness `h_inner`.**
Identical to `FirstSumcheckComplete.firstSumcheck_perfectCompleteness`, against the restated
relations and lens-completeness instance. -/
theorem firstSumcheck_perfectCompleteness'
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (h_inner :
      (Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec).perfectCompleteness
        init impl
        (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
        (Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))) :
    (firstSumcheckReduction pp oSpec).perfectCompleteness init impl
      (firstSumcheckRelIn' (R := R) pp) (firstSumcheckRelOut' (R := R) pp) := by
  have := firstSumcheckCoherent (R := R) pp oSpec
  exact OracleReduction.liftContextLegacy_perfectCompleteness
    (R := Sumcheck.Spec.oracleReduction R 3 (boolEmbedding R) pp.ℓ_m oSpec)
    (lens := firstSumcheckContextLens pp)
    (stmtLens := firstSumcheckOracleLens pp oSpec)
    (outerRelIn := firstSumcheckRelIn' (R := R) pp)
    (innerRelIn := Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (0 : Fin (pp.ℓ_m + 1)))
    (outerRelOut := firstSumcheckRelOut' (R := R) pp)
    (innerRelOut := Sumcheck.Spec.relationRound R pp.ℓ_m 3 (boolEmbedding R) (Fin.last pp.ℓ_m))
    rfl h_inner

/-- **First sum-check phase perfect completeness, with the inner completeness discharged (#114).**
The inner multi-round sum-check oracle perfect completeness `h_inner` is supplied by
`Sumcheck.Spec.oracleReduction_perfectCompleteness_of_bridge` specialized at `deg = 3`,
`D = boolEmbedding R`,
`n = pp.ℓ_m`. It remains stated modulo the explicit bridge `hBridge`
(`oracleReductionToReductionResidual`, a legacy hypothesis whose per-round form is suspected
false; see the module docstring) plus the execution-model side conditions `hInit`/`hImplSupp`.
Use `firstSumcheck_perfectCompleteness_bridgeFree` (`FirstSumcheckBridgeFree.lean`) for the
bridge-free statement. -/
theorem firstSumcheck_perfectCompleteness_unconditional
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    [Inhabited R] [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
    (hBridge : Sumcheck.Spec.oracleReductionToReductionResidual R 3 (boolEmbedding R) pp.ℓ_m oSpec)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (firstSumcheckReduction pp oSpec).perfectCompleteness init impl
      (firstSumcheckRelIn' (R := R) pp) (firstSumcheckRelOut' (R := R) pp) :=
  firstSumcheck_perfectCompleteness' pp oSpec
    (Sumcheck.Spec.oracleReduction_perfectCompleteness_of_bridge hBridge hInit hImplSupp)

end Spartan.Spec
