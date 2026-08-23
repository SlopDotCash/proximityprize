/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckLiftCoherent

/-!
# LogUp Protocol 2 — discharging `SumcheckCompletenessResidual` (issue #13, brick B)

`Logup.SumcheckCompletenessResidual` (defined in `Security/SubPhaseSplit.lean`) is the
perfect-completeness (error-`0`) obligation for the LogUp embedded sum-check phase:

```
(sumcheckOracleReduction oSpec F n M params).completeness init impl
  (midRelation F n M params) outputRelation 0
```

Since `OracleReduction.perfectCompleteness := completeness … 0` and
`sumcheckOracleReduction = (logupConcreteSumcheckOracleReduction …).liftContext
  (logupSumcheckContextLens) (logupSumcheckOracleLens)`, this brick transfers the inner
generic multi-round sum-check perfect completeness through the context lift via
`OracleReduction.liftContext_perfectCompleteness`, exactly mirroring the Spartan
`firstSumcheck_perfectCompleteness` development.

The transfer consumes three ingredients:

* `Logup.logupSumcheck_liftContextCoherent` — the proven (axiom-clean) `LiftContextCoherent`
  instance (design note #433), supplied locally via `haveI`.

* `hInner` — the perfect completeness of the inner concrete sum-check oracle reduction
  `logupConcreteSumcheckOracleReduction` (= `Sumcheck.Spec.oracleReduction …`) between the
  round-`0` and round-`last` sum-check relations. The multi-round generic sum-check perfect
  completeness exists at the `Reduction` level (`Sumcheck.Spec.reduction_perfectCompleteness`,
  axiom-clean); its *oracle*-level multi-round packaging is the sequential-composition keystone
  still being assembled in the framework layer, so it is taken here as an explicit named
  hypothesis (a later brick supplies it — same convention as Spartan's `h_inner`).

* `sumcheckLensComplete` — the `OracleContext.Lens.IsComplete` instance for
  `logupSumcheckContextLens`, an *instance argument* of `liftContext_perfectCompleteness`. Its
  `lift_complete` half is *trivial* because the outer output relation `outputRelation` is
  `Set.univ` (the full LogUp protocol returns only success/failure, so every lifted output
  statement is in-relation). Its `proj_complete` half — an outer `midRelation` statement projects
  into the round-`0` sum-check relation `relationRound … 0` — is taken as the named hypothesis
  `hProj`; with the corrected claim-true `midRelation` (issue #13) it is discharged
  unconditionally by `SumcheckLensProjComplete_unconditional`
  (`Security/SumcheckLensProjComplete.lean`), since the `midRelation` premise *is* the zero-sum
  claim that `logupSumcheckRelationInput_of_rowsAgree` consumes.

No `sorry`/`admit`. The two genuine upstream gaps are the named hypotheses `hInner` and
`hProj`; everything mechanical (the lift, the coherence threading, the trivial `lift_complete`)
is proven.
-/

open OracleComp ProtocolSpec

namespace Logup

section SumcheckCompletenessClose

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`); mirrors the local instance used elsewhere in the LogUp
completeness development.  The explicit name avoids environment-merge clashes when this module is
co-imported with the soundness close. -/
local instance instInhabitedFieldSumcheckCompletenessClose : Inhabited F := ⟨0⟩

/-- The inner round-`0` sum-check relation for LogUp's embedded sum-check (degree
`logupSumcheckDegree`, sign domain). The input relation of `logupConcreteSumcheckOracleReduction`. -/
abbrev innerSumcheckRelIn :
    Set (((LogupSumcheckStmtIn F n M params) ×
        (∀ i, LogupSumcheckOracleStatement F n M params i)) × Unit) :=
  Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params)
    (signDomain F (Fact.out : (-1 : F) ≠ 1)) (0 : Fin (n + 1))

/-- The inner round-`last` sum-check relation for LogUp's embedded sum-check. The output relation
of `logupConcreteSumcheckOracleReduction`. -/
abbrev innerSumcheckRelOut :
    Set (((LogupSumcheckStmtOut F n M params) ×
        (∀ i, LogupSumcheckOracleStatement F n M params i)) × Unit) :=
  Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params)
    (signDomain F (Fact.out : (-1 : F) ≠ 1)) (Fin.last n)

/-- **The `proj_complete` half of `OracleContext.Lens.IsComplete` for the LogUp sum-check lens.**

Every outer `midRelation` statement-witness pair projects (under `logupSumcheckContextLens`) into
the round-`0` sum-check relation `innerSumcheckRelIn`. With the corrected claim-true `midRelation`
(issue #13) the premise *is* the zero-sum claim, so this holds unconditionally — discharged by
`SumcheckLensProjComplete_unconditional` in `Security/SumcheckLensProjComplete.lean` via
`logupSumcheckRelationInput_of_rowsAgree`.

Stated directly with `lens.stmt.proj` / `lens.wit.proj` (the exact fields the `IsComplete`
`proj_complete` obligation uses), universe-pinned to `0` to match `sumcheckOracleReduction`. -/
def SumcheckLensProjComplete : Prop :=
  ∀ (stmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) (witIn : Unit),
    (stmtIn, witIn) ∈ midRelation F n M params →
    ((logupSumcheckContextLens.{0} F n M params).stmt.proj stmtIn,
      (logupSumcheckContextLens.{0} F n M params).wit.proj (stmtIn, witIn))
      ∈ innerSumcheckRelIn F n M params

/-- **`OracleContext.Lens.IsComplete` for the LogUp embedded sum-check lens**, assembled from the
named projection hypothesis `hProj` (genuine algebraic gap) and the trivial `lift_complete` (the
outer output relation `outputRelation` is `Set.univ`).

Marked `@[reducible]` so it can serve as the `lensComplete` instance argument of
`liftContext_perfectCompleteness`. Universe-pinned to `0` to match `sumcheckOracleReduction`. -/
@[reducible] def sumcheckLensComplete (hProj : SumcheckLensProjComplete F n M params) :
    (logupSumcheckContextLens.{0} F n M params).toContext.IsComplete
      (midRelation F n M params)
      (innerSumcheckRelIn F n M params)
      (outputRelation)
      (innerSumcheckRelOut F n M params)
      ((logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).toReduction.compatContext
        (logupSumcheckContextLens.{0} F n M params).toContext) where
  proj_complete := hProj
  lift_complete := by
    intro _ _ _ _ _ _ _
    -- `outputRelation = Set.univ`, so every lifted output statement is in-relation.
    exact Set.mem_univ _

/-- **`SumcheckCompletenessResidual` holds.** The LogUp embedded sum-check phase is perfectly
complete (error `0`) from `midRelation` to `outputRelation`, given:

* `hInner` — perfect completeness of the inner concrete sum-check oracle reduction
  (the oracle-level multi-round sum-check keystone, taken as a named hypothesis), and
* `hProj` — the `proj_complete` algebraic obligation (the LogUp grand-sum claim vanishes on the
  hypercube for the projected statement), taken as a named hypothesis.

The transfer is `OracleReduction.liftContext_perfectCompleteness` with the proven coherence
instance `logupSumcheck_liftContextCoherent` and the lens-completeness instance assembled from
`hProj`; `hStmt = rfl` because `logupSumcheckOracleLens.toLens := logupSumcheckContextLens.stmt`
by construction. -/
theorem sumcheckCompletenessResidual_holds
    (hProj : SumcheckLensProjComplete F n M params)
    (hInner :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).perfectCompleteness init impl
        (innerSumcheckRelIn F n M params)
        (innerSumcheckRelOut F n M params)) :
    SumcheckCompletenessResidual oSpec F n M params init impl := by
  haveI := logupSumcheck_liftContextCoherent oSpec F n M params
  haveI := sumcheckLensComplete oSpec F n M params hProj
  -- `SumcheckCompletenessResidual` is `(…).completeness … 0`, defeq to `(…).perfectCompleteness`.
  -- `sumcheckOracleReduction = (logupConcreteSumcheckOracleReduction …).liftContext lens stmtLens`.
  exact OracleReduction.liftContext_perfectCompleteness
    (R := logupConcreteSumcheckOracleReduction oSpec F n M params (Fact.out : (-1 : F) ≠ 1))
    (lens := logupSumcheckContextLens.{0} F n M params)
    (stmtLens := logupSumcheckOracleLens.{0} oSpec F n M params)
    (outerRelIn := midRelation F n M params)
    (innerRelIn := innerSumcheckRelIn F n M params)
    (outerRelOut := outputRelation)
    (innerRelOut := innerSumcheckRelOut F n M params)
    rfl hInner

end SumcheckCompletenessClose

end Logup

#print axioms Logup.sumcheckCompletenessResidual_holds
