/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessClose
import ArkLib.ProofSystem.Logup.Security.SumcheckLensProjComplete
import ArkLib.ProofSystem.Logup.Security.BridgeAndAppendResiduals
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone

/-!
# LogUp Protocol 2 — most-unconditional completeness (issue #13, keystone K-compFull)

This file assembles the **most-unconditional** LogUp Protocol 2 completeness statement attainable
through the *per-round bridge* route, by discharging the inner multi-round sum-check oracle
completeness `hInner` with the **now-proven** binary verifier-fusion keystone
`OracleReduction.oracleVerifier_append_toVerifier` (in
`Composition/Sequential/AppendToVerifierKeystone.lean`, sorry-free), threaded through the existing
reduction chain.

## The chain

1. **Binary verifier fusion is proven.** The named residual
   `OracleVerifier.BinaryVerifierFusion oSpec` (the verifier analogue of `Prover.append_run`,
   from `BridgeAndAppendResiduals.lean`) is *exactly*
   `(OracleVerifier.append V₁ V₂).toVerifier = Verifier.append V₁.toVerifier V₂.toVerifier`
   for all appendable pairs — which is the keystone
   `OracleReduction.oracleVerifier_append_toVerifier`. So `binaryVerifierFusion_holds` discharges it
   with no residual.

2. **Inner multi-round sum-check oracle completeness, modulo the per-round bridge.** From the binary
   fusion, the proven `Sumcheck.Spec.oracleReductionToReductionResidual_of_binary` reduces the
   unbounded-round Sumcheck bridge `oracleReductionToReductionResidual` to the single per-round
   single-round bridge `hPerRound`
   (`(SingleRound.oracleReduction i).toReduction = SingleRound.reduction i`, a `liftContext`
   commutation fact orthogonal to the seqCompose fusion). Feeding that bridge into
   `Sumcheck.Spec.oracleReduction_perfectCompleteness_of_bridge` (which discharges everything else
   via the proven `reduction_perfectCompleteness`) yields the inner perfect completeness `hInner`
   for `logupConcreteSumcheckOracleReduction` between `innerSumcheckRelIn` and
   `innerSumcheckRelOut`.

3. **Embedded sum-check phase completeness — no honest-support hypothesis.** With `hInner`
   discharged, the `proj_complete` algebraic obligation is the **theorem**
   `SumcheckLensProjComplete_unconditional`: the corrected claim-true `midRelation`
   (`{p | logupOuterSumcheckClaim … = 0}`) makes the membership premise *be* the zero-sum claim, so
   `Logup.sumcheckCompletenessResidual_of_inner` yields `SumcheckCompletenessResidual` outright.

4. **End-to-end completeness.** Feeding the outer half (proven in-tree from `NeverFail init`), the
   discharged sum-check half, and the append-composition brick `hAppend` into
   `Logup.logup_completeness_full` gives the headline LogUp completeness.

## Residual surface (`logup_completeness_uncond`)

The smallest honest residual set on this route:

* `hInit : NeverFail init` — the standard completeness initialization assumption.
* `hPerRound` — the per-round single-round `liftContext`-commutation bridge for the inner sum-check.
  (NOTE: the CubeFiber route — `sumcheckCompletenessResidual_unconditional` in
  `SumcheckCompletenessUncond.lean`, consumed by `logup_completeness_final` — avoids even this,
  and `OracleCompletenessThreaded.lean` documents why the bridge route should be considered
  superseded: the analogous unbounded-round `toReduction = reduction` equation is false in general.)
* `hImplSupp` — the standard oracle-implementation support-faithfulness condition (shared by every
  `*_perfectCompleteness` brick in-tree).
* `hAppend` — the non-perfect outer⊕sumcheck append-composition completeness (dischargeable via
  `appendCompletenessResidual_wired` in `LogupCompletenessWired.lean`).

## Removed (issue #13, dmvt audit)

* The honest-support hypothesis `hHonest` formerly threaded through every theorem here was
  **unsatisfiable**: it quantified over *all* after-outer statements
  `stmtIn : StmtAfterOuter × (∀ i, OStmtAfterOuter)` and demanded an honest preimage with
  `stmtIn.2 = (honest-form map)` and pole-freeness for `stmtIn.1.xChallenge`. A `stmtIn` whose
  `.multiplicity` component is corrupted has no such preimage (the `.input`-slot equations force
  the preimage oracles, which pin `honestMultiplicity`), and an adversarial `xChallenge` falsifies
  pole-freeness. Every consumer was therefore uninstantiable. With the claim-true `midRelation`,
  the hypothesis is simply unnecessary: the embedded sum-check completeness needs only the
  zero-claim that `midRelation` membership already supplies.
* `logup_completeness_uncond_perfect` hypothesized `logupCompletenessError F n = 0`, which is
  impossible (`logupCompletenessError_ne_zero`: the error is `2^n / |F| > 0` over any finite
  field), so the theorem was vacuous. The genuine non-perfect composition lives in
  `LogupCompletenessWired.lean`.

No `sorry`/`sorryAx`/`admit`: every step is a real proof or an explicitly named hypothesis. The
axiom audit at the bottom confirms axiom-cleanliness (`propext`, `Classical.choice`, `Quot.sound`).
-/

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace Logup

section Uncond

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`); needed for the inner-sum-check `[Inhabited R]` instance and to match
the local instances used throughout the LogUp completeness development. -/
local instance instInhabitedFieldLogupUncond : Inhabited F := ⟨0⟩

/-! ### Step 1: the binary verifier fusion is proven (no residual) -/

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- **The binary verifier-fusion residual is discharged.** `OracleVerifier.BinaryVerifierFusion`
is, by definition, the universally-quantified
`(OracleVerifier.append V₁ V₂).toVerifier = Verifier.append V₁.toVerifier V₂.toVerifier`, which is
exactly the proven keystone `OracleReduction.oracleVerifier_append_toVerifier` (sorry-free in
`AppendToVerifierKeystone.lean`). So the whole unbounded-round verifier fusion — and with it the
Sumcheck `hBridge` — is now unconditional. -/
theorem binaryVerifierFusion_holds : OracleVerifier.BinaryVerifierFusion oSpec := by
  intro Stmt₁ ιₛ₁ OStmt₁ Oₛ₁ Stmt₂ ιₛ₂ OStmt₂ Oₛ₂ Stmt₃ ιₛ₃ OStmt₃ Oₛ₃
    p q pSpec₁ pSpec₂ Oₘ₁ Oₘ₂ V₁ c₁ V₂
  exact OracleReduction.oracleVerifier_append_toVerifier (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁)
    V₁ V₂

/-! ### Step 2: inner multi-round sum-check oracle completeness, modulo the per-round bridge

`logupConcreteSumcheckOracleReduction oSpec F n M params Fact.out` is *definitionally*
`Sumcheck.Spec.oracleReduction F (logupSumcheckDegree M params) (signDomain F Fact.out) n oSpec`, and
`innerSumcheckRelIn` / `innerSumcheckRelOut` are *definitionally* `relationRound … 0` /
`relationRound … (Fin.last n)`. So `Sumcheck.Spec.oracleReduction_perfectCompleteness_of_bridge`
applies on the nose, once its `hBridge` (`oracleReductionToReductionResidual`) is supplied. We supply
that bridge from the proven binary fusion (`binaryVerifierFusion_holds`) plus the per-round bridge
`hPerRound`, via the proven `Sumcheck.Spec.oracleReductionToReductionResidual_of_binary`. -/

/-- **Inner multi-round sum-check oracle perfect completeness, modulo the per-round bridge.**
The only residual is `hPerRound`, the single-round `liftContext`-commutation fact; the deep
unbounded-round verifier fusion is discharged by the proven binary keystone. -/
theorem inner_sumcheck_perfectCompleteness_of_perRound
    (hPerRound : ∀ i,
      (Sumcheck.Spec.SingleRound.oracleReduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).toReduction =
        Sumcheck.Spec.SingleRound.reduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (logupConcreteSumcheckOracleReduction oSpec F n M params
        (Fact.out : (-1 : F) ≠ 1)).perfectCompleteness init impl
      (innerSumcheckRelIn F n M params)
      (innerSumcheckRelOut F n M params) := by
  -- The Sumcheck `hBridge` from the proven binary fusion + the per-round bridge.
  have hBridge :
      Sumcheck.Spec.oracleReductionToReductionResidual F (logupSumcheckDegree M params)
        (signDomain F (Fact.out : (-1 : F) ≠ 1)) n oSpec :=
    Sumcheck.Spec.oracleReductionToReductionResidual_of_binary
      (binaryVerifierFusion_holds oSpec) hPerRound
  -- `logupConcreteSumcheckOracleReduction`, `innerSumcheckRelIn/Out` are definitionally the generic
  -- Sumcheck oracle reduction and its round-`0`/round-`last` relations; apply the oracle-level
  -- completeness keystone (which discharges everything else via `reduction_perfectCompleteness`).
  exact Sumcheck.Spec.oracleReduction_perfectCompleteness_of_bridge
    (R := F) (deg := logupSumcheckDegree M params)
    (D := signDomain F (Fact.out : (-1 : F) ≠ 1)) (n := n) (oSpec := oSpec)
    hBridge hInit hImplSupp

/-! ### Step 3: embedded sum-check phase completeness — no honest-support hypothesis -/

/-- **`SumcheckCompletenessResidual` discharged, modulo the per-round bridge.**
Chains `inner_sumcheck_perfectCompleteness_of_perRound` (the inner oracle completeness) with the
proven `sumcheckCompletenessResidual_of_inner`, whose `proj_complete` obligation is the theorem
`SumcheckLensProjComplete_unconditional` (the claim-true `midRelation` membership *is* the zero-sum
claim). The only residuals are `hPerRound`, `hInit`, `hImplSupp` — **no** honest-support
hypothesis (the historical `hHonest` was unsatisfiable; see the module docstring). -/
theorem sumcheckCompletenessResidual_of_perRound
    (hPerRound : ∀ i,
      (Sumcheck.Spec.SingleRound.oracleReduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).toReduction =
        Sumcheck.Spec.SingleRound.reduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    SumcheckCompletenessResidual oSpec F n M params init impl :=
  sumcheckCompletenessResidual_of_inner F n M params oSpec init impl
    (inner_sumcheck_perfectCompleteness_of_perRound oSpec F n M params init impl
      hPerRound hInit hImplSupp)

/-! ### Step 4: end-to-end most-unconditional completeness -/

/-- **Most-unconditional LogUp Protocol 2 completeness via the per-round bridge (issue #13,
keystone K-compFull).**

The full LogUp oracle reduction is complete with error `logupCompletenessError F n`. The **outer**
pole-rejection half is proven in-tree from `NeverFail init`, and the **embedded sum-check** half is
discharged modulo the per-round bridge (the deep unbounded-round verifier fusion having been closed
by the proven binary keystone, and the `proj_complete` obligation being the theorem
`SumcheckLensProjComplete_unconditional`). The smallest honest residual set:

* `hInit : NeverFail init` — standard completeness initialization;
* `hPerRound` — the per-round single-round `liftContext`-commutation bridge;
* `hImplSupp` — the standard oracle-implementation support-faithfulness condition;
* `hAppend` — the non-perfect outer⊕sumcheck append-composition completeness.

The conclusion is exactly the headline LogUp completeness statement, with no `sorry`. For the
bridge-free, fully-instantiable headline see `logup_completeness_final`
(`LogupCompletenessFinal.lean`). -/
theorem logup_completeness_uncond
    (hInit : NeverFail init)
    (hPerRound : ∀ i,
      (Sumcheck.Spec.SingleRound.oracleReduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).toReduction =
        Sumcheck.Spec.SingleRound.reduction F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (hAppend :
      AppendCompletenessResidual oSpec F n M params init impl
        (outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit)
        (sumcheckCompletenessResidual_of_perRound oSpec F n M params init impl
          hPerRound hInit hImplSupp)) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_full oSpec F n M params init impl hInit
    (sumcheckCompletenessResidual_of_perRound oSpec F n M params init impl
      hPerRound hInit hImplSupp)
    hAppend

end Uncond

end Logup

/- Axiom audit for the most-unconditional LogUp completeness keystone. -/
#print axioms Logup.binaryVerifierFusion_holds
#print axioms Logup.inner_sumcheck_perfectCompleteness_of_perRound
#print axioms Logup.sumcheckCompletenessResidual_of_perRound
#print axioms Logup.logup_completeness_uncond
