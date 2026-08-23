/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SumcheckCompletenessClose

/-!
# LogUp Protocol 2 — discharging `SumcheckLensProjComplete` (issue #13, residual RA-projComplete)

This file discharges the named projection hypothesis `hProj` consumed by
`Logup.sumcheckCompletenessResidual_holds`
(in `Security/SumcheckCompletenessClose.lean`):

```
def SumcheckLensProjComplete : Prop :=
  ∀ (stmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) (witIn : Unit),
    (stmtIn, witIn) ∈ midRelation F n M params →
    ((logupSumcheckContextLens.{0} F n M params).stmt.proj stmtIn,
      (logupSumcheckContextLens.{0} F n M params).wit.proj (stmtIn, witIn))
      ∈ innerSumcheckRelIn F n M params
```

## What the obligation really says

The context lens `logupSumcheckContextLens` projects an outer transcript
`stmtIn = (stmt, oStmt)` to the inner generic-sumcheck input statement
`(logupInitialSumcheckStatement, logupSumcheckOracleStmt stmt oStmt)` and the inner witness `()`
(both `stmt.proj` and `wit.proj` are the *first projections* of the lens's `PFunctor.Lens`
components, evaluated definitionally). Membership in `innerSumcheckRelIn`
(`= Sumcheck.Spec.relationRound … 0`) is, by `unfold`, **exactly** the `Prop`
`Logup.logupSumcheckRelationInput F n M params (Fact.out) stmt oStmt`, i.e. the round-`0`
sum-check claim "`Σ over the sign-hypercube of the LogUp sum-check polynomial = target(=0)`".

With the corrected claim-true `midRelation` (`{p | logupOuterSumcheckClaim … = 0}`, issue #13),
the `(stmtIn, witIn) ∈ midRelation` premise **is** the zero-sum claim, so the obligation closes
unconditionally (`SumcheckLensProjComplete_unconditional` below). Two ingredients drive the proof,
provided by the in-tree, already-proven bridge:

* **Row-agreement** (`logupSumcheckPolynomialRowsAgree_of_signsDistinct`): the packaged sum-check
  polynomial agrees with `qOnHypercube` on the sign-hypercube. This is *unconditional* given
  `(-1 : F) ≠ 1` (supplied here by the ambient `Fact`), and is discharged inside this file.

* **Zero-sum** (`logupOuterSumcheckClaim … = 0`): the LogUp grand-sum claim vanishes on the
  hypercube. This is exactly the `midRelation` membership premise of `SumcheckLensProjComplete`,
  so it is supplied by the obligation itself — no extra hypothesis.

The bridge from row-agreement + zero-sum to the `relationRound 0` membership is the proven
`Logup.logupSumcheckRelationInput_of_rowsAgree`.

**Removed conditional forms (issue #13, dmvt audit).** The historical conditional variants
(`SumcheckLensProjComplete_holds` with a *globally* quantified `hClaimZero`, and
`…_holds_of_honest` / `sumcheckCompletenessResidual_of_honest` with the *globally* quantified
honest-support package `hHonest`) had **unsatisfiable** hypotheses: they quantified over **all**
after-outer statements `stmtIn`, but a `stmtIn` whose `.multiplicity` oracle is corrupted has no
honest preimage (the `.input`-slot equations force the preimage, which then pins
`honestMultiplicity`), and an adversarial `xChallenge` falsifies pole-freeness. Any theorem
consuming them was uninstantiable. They have been deleted; the unconditional theorem strictly
supersedes them.

No `sorry` / `admit`, and no residual sub-hypothesis: `SumcheckLensProjComplete` is a theorem.
-/

open OracleComp ProtocolSpec

namespace Logup

section SumcheckLensProjComplete

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable (n M : ℕ)
variable (params : ProtocolParams M)

local instance instInhabitedFieldSumcheckLensProjComplete : Inhabited F := ⟨0⟩

omit [Fintype F] [DecidableEq F] in
/-- **Key defeq.** The lens projection of an outer transcript `stmtIn = (stmt, oStmt)`, paired with
the projected (trivial) witness, lands in `innerSumcheckRelIn` **iff** the round-`0` LogUp sum-check
input relation `logupSumcheckRelationInput` holds for `stmt`/`oStmt`.

Both `(logupSumcheckContextLens).stmt.proj stmtIn` and `(…).wit.proj (stmtIn, witIn)` are the
*first projections* of the lens's `PFunctor.Lens` fields (`.toFunA`), which by construction are
`fun ctx => (logupInitialSumcheckStatement, logupSumcheckOracleStmt ctx.1 ctx.2)` and `fun _ => ()`
respectively. Hence the membership is definitionally `logupSumcheckRelationInput`. -/
theorem lensProj_mem_innerRel_iff_relationInput
    (stmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))
    (witIn : Unit) :
    (((logupSumcheckContextLens.{0} F n M params).stmt.proj stmtIn,
        (logupSumcheckContextLens.{0} F n M params).wit.proj (stmtIn, witIn))
        ∈ innerSumcheckRelIn F n M params)
      ↔
    logupSumcheckRelationInput F n M params (Fact.out : (-1 : F) ≠ 1) stmtIn.1 stmtIn.2 :=
  Iff.rfl

omit [Fintype F] [DecidableEq F] in
/-- **`SumcheckLensProjComplete` holds unconditionally (issue #13, de-larped).**

With the corrected claim-true `midRelation` (`{p | logupOuterSumcheckClaim … = 0}`, matching the
soundness-side `midLanguage`), the `(stmtIn, witIn) ∈ midRelation` premise *is* the zero-sum claim,
so the projection obligation closes by construction: row-agreement is unconditional from
`(-1 : F) ≠ 1` (the ambient `Fact`), and `logupSumcheckRelationInput_of_rowsAgree` bridges
row-agreement + the claim to the round-`0` relation membership. No honest-support hypothesis, no
`hClaimZero` — the `proj_complete` half of the lens completeness is now a theorem. -/
theorem SumcheckLensProjComplete_unconditional :
    SumcheckLensProjComplete F n M params := by
  intro stmtIn _witIn hMid
  -- Reduce the lens-projected membership to the round-`0` input relation (definitional).
  rw [lensProj_mem_innerRel_iff_relationInput F n M params stmtIn _witIn]
  -- `hMid` *is* the zero-sum claim for the corrected `midRelation`; bridge via row-agreement.
  exact logupSumcheckRelationInput_of_rowsAgree
    (F := F) (n := n) (M := M) (params := params)
    (logupSumcheckPolynomialRowsAgree_of_signsDistinct
      (F := F) (n := n) (M := M) (params := params) (Fact.out : (-1 : F) ≠ 1)
      stmtIn.1 stmtIn.2)
    hMid

/-- **`SumcheckCompletenessResidual` from the inner completeness alone (issue #13, de-larped).**

With `hProj` now a theorem (`SumcheckLensProjComplete_unconditional`, by construction from the
corrected claim-true `midRelation`), the embedded sum-check completeness residual needs only the
inner multi-round oracle sum-check completeness `hInner` — no honest-support hypothesis. -/
theorem sumcheckCompletenessResidual_of_inner
    {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype]
    [SampleableType F]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hInner :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).perfectCompleteness init impl
        (innerSumcheckRelIn F n M params)
        (innerSumcheckRelOut F n M params)) :
    SumcheckCompletenessResidual oSpec F n M params init impl :=
  sumcheckCompletenessResidual_holds oSpec F n M params init impl
    (SumcheckLensProjComplete_unconditional F n M params) hInner

end SumcheckLensProjComplete

end Logup

#print axioms Logup.lensProj_mem_innerRel_iff_relationInput
#print axioms Logup.SumcheckLensProjComplete_unconditional
#print axioms Logup.sumcheckCompletenessResidual_of_inner
