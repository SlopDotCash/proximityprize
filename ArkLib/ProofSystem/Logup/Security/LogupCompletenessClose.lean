/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessOracle

/-!
# LogUp Protocol 2 — end-to-end completeness close (issue #13, brick C)

This file assembles the **end-to-end** completeness statement for LogUp Protocol 2,

```
(logupOracleReduction oSpec F n M params).completeness init impl
    (inputRelation F n M) outputRelation (logupCompletenessError F n)
```

by composing the three independently-named completeness obligations exposed by
`Security/SubPhaseSplit.lean`:

* the **outer** pole-rejection half (`OuterCompletenessResidual`, error
  `logupCompletenessError F n`), which is **already a proven theorem in-tree**
  (`outerOracleReduction_completeness` / `outerCompletenessResidual_of_neverFail`, via the pole
  bound `card_poleSet_le` / `probEvent_pole_le` and the per-state agreement `outer_perState_agree`),
  discharged here under the standard `NeverFail init` completeness assumption;
* the embedded **sumcheck** half (`SumcheckCompletenessResidual`, error `0`), a `liftContext` of the
  generic `Sumcheck.Spec` reduction; and
* the **append-composition** brick (`AppendCompletenessResidual`), which bridges the two sub-phase
  completenesses to the completeness of the sequential composition
  `logupOracleReduction = outerOracleReduction.append sumcheckOracleReduction`.

## What is genuinely proven here vs. left as honest residuals

`logupOracleReduction` is *definitionally* the message-seam append
`outerOracleReduction.append sumcheckOracleReduction` (`logupOracleReduction_eq_append`), and the
embedded-sumcheck protocol `logupSumcheckPSpec = Sumcheck.Spec.pSpec` starts with a `P_to_V`
prover message, so the seam *is* a message seam: the proven oracle-level keystone
`OracleReduction.append_perfectCompleteness_msg_proof` is the right composition tool for its
*perfect* (error-`0`) special case.

The **append theorem the LogUp completeness composition actually needs is the non-perfect one**: it
must combine the outer error `logupCompletenessError F n` (≠ 0 over a finite field) with the
sumcheck error `0`. The only *proven* in-tree append-completeness theorem is the perfect-completeness
keystone (both component errors `0`); a general non-perfect Reduction-level append completeness is
not available in-tree. So this brick:

* **proves** the outer half outright (no residual);
* takes the **sumcheck** completeness and the **non-perfect append-composition** completeness as
  explicit, clearly-named `Prop` hypotheses — the two genuine residual gaps, each closable by a later
  brick;
* additionally **sharpens** the append residual, reducing it through the proven verifier-fusion
  bridge `appendToReductionResidual` to a Reduction-level append-completeness statement.

**Removed (issue #13, dmvt audit defect 2):** the historical "perfect special case" lemmas
(`appendCompletenessResidual_of_perfect` / `logup_completeness_full_perfect`) hypothesized
`logupCompletenessError F n = 0`, which is **impossible** — the error is `2^n / |F| > 0` for every
finite field (`logupCompletenessError_ne_zero`, `Security/Completeness.lean`) — so both lemmas were
vacuous. The genuinely non-perfect append composition is discharged by
`OracleReduction.append_completeness_msg_proof` (`LogupCompletenessWired.lean`), which carries the
non-zero outer error through the message seam for real.

No `sorry`/`sorryAx`: every step is a real proof or an explicitly named hypothesis. The axiom audit
at the bottom confirms `logup_completeness_full` is axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped NNReal ENNReal
open OracleComp

namespace Logup

section Close

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances when naming the sub-phase obligations. -/
local instance instInhabitedFieldLogupClose : Inhabited F := ⟨0⟩

/-! ### End-to-end completeness from the (proven) outer half + named sub-bricks -/

/-- **End-to-end LogUp Protocol 2 completeness (issue #13, brick C).**

The full LogUp oracle reduction is complete with error `logupCompletenessError F n =
|Hypercube n| / |F|` (the pole-rejection error; the sumcheck phase is perfectly complete, error `0`).

The **outer** pole-rejection half is discharged in-tree by `outerCompletenessResidual_of_neverFail`
under the standard `NeverFail init` completeness assumption — it is *not* a residual. The two genuine
remaining obligations are taken as explicit named hypotheses:

* `hSumcheck : SumcheckCompletenessResidual` — perfect completeness of the embedded sumcheck phase
  (`liftContext` of `Sumcheck.Spec`; blocked upstream by the missing generic `Sumcheck.Spec`
  seq-compose completeness theorem + the lens `IsComplete` instance);
* `hAppend : AppendCompletenessResidual` — the non-perfect sequential-composition completeness brick
  combining the outer error with the sumcheck error `0` along the message seam.

The conclusion is exactly the headline LogUp completeness statement, with no `sorry`. -/
theorem logup_completeness_full (hInit : NeverFail init)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl)
    (hAppend :
      AppendCompletenessResidual oSpec F n M params init impl
        (outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit) hSumcheck) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_of_sumcheck_append oSpec F n M params init impl hInit hSumcheck hAppend

/-- **Variant taking the outer half as an explicit hypothesis** (instead of deriving it from
`NeverFail init`). Useful for callers that obtain outer completeness by another route. -/
theorem logup_completeness_full_of_outer
    (hOuter : OuterCompletenessResidual oSpec F n M params init impl)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl)
    (hAppend :
      AppendCompletenessResidual oSpec F n M params init impl hOuter hSumcheck) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_of_split oSpec F n M params init impl hOuter hSumcheck hAppend

/-! ### Sharpening the append residual through the proven verifier-fusion bridge

`AppendCompletenessResidual … hOuter hSumcheck` unfolds (by `appendCompletenessResidual` and
`OracleReduction.completeness`) to a `Reduction.completeness` statement about
`(outerOracleReduction.append sumcheckOracleReduction).toReduction`. The proven bridge
`OracleReduction.appendToReductionResidual` collapses that `toReduction` to the *non-oracle* append
`outerOracleReduction.toReduction.append sumcheckOracleReduction.toReduction`. The lemma below makes
this explicit, pinning the residual's remaining content to a plain Reduction-level append
completeness — which is exactly where the (non-perfect) upstream composition wall lives. -/

/-- The append residual rewritten through the verifier-fusion bridge: it is `Reduction`-level
completeness of the *non-oracle* append `outer.toReduction.append sumcheck.toReduction`, at error
`logupCompletenessError F n + 0`. This pins the residual's remaining content to a plain
Reduction-level append completeness — exactly where the (non-perfect) upstream composition wall
lives. -/
theorem appendCompletenessResidual_iff_toReduction
    (hOuter : OuterCompletenessResidual oSpec F n M params init impl)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl)
    (hBridge :
      OracleReduction.appendToReductionResidual
        (outerOracleReduction oSpec F n M params)
        (sumcheckOracleReduction oSpec F n M params)) :
    AppendCompletenessResidual oSpec F n M params init impl hOuter hSumcheck ↔
      Reduction.completeness init impl
        (inputRelation F n M) outputRelation
        ((outerOracleReduction oSpec F n M params).toReduction.append
          (sumcheckOracleReduction oSpec F n M params).toReduction)
        (logupCompletenessError F n + 0) := by
  -- `AppendCompletenessResidual` is, by definition, the `OracleReduction.completeness` of the
  -- appended oracle reduction; `OracleReduction.completeness` is `Reduction.completeness` of
  -- `.toReduction`; the bridge rewrites that `.toReduction` to the non-oracle append.
  unfold AppendCompletenessResidual OracleReduction.appendCompletenessResidual
    OracleReduction.completeness
  rw [show (OracleReduction.append (outerOracleReduction oSpec F n M params)
        (sumcheckOracleReduction oSpec F n M params)).toReduction
      = (outerOracleReduction oSpec F n M params).toReduction.append
          (sumcheckOracleReduction oSpec F n M params).toReduction from hBridge]
  -- After the bridge rewrite both sides are the same `Reduction.completeness` statement.
  exact Iff.rfl

/-! ### Note: no "perfect special case"

This file historically also exposed `appendCompletenessResidual_of_perfect` and
`logup_completeness_full_perfect`, gated on `hErr : logupCompletenessError F n = 0`. That premise
is **unsatisfiable** (`logupCompletenessError_ne_zero`: the error is `2^n / |F| > 0` over any
finite field), so both lemmas were vacuous and have been deleted (issue #13, dmvt audit defect 2).
The genuine non-perfect append composition — carrying the non-zero outer error through the message
seam — is proven in `LogupCompletenessWired.lean`
(`OracleReduction.append_completeness_msg_proof` / `Logup.appendCompletenessResidual_wired`). -/

end Close

end Logup

/- Axiom audit for the LogUp completeness close. -/
#print axioms Logup.logup_completeness_full
#print axioms Logup.logup_completeness_full_of_outer
#print axioms Logup.appendCompletenessResidual_iff_toReduction
