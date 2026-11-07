/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessUncond
import ArkLib.ProofSystem.Sumcheck.Spec.General

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace Logup

section SumcheckCompleteness

variable {ι : Type} (oSpec : OracleSpec ι) [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances used when naming the sub-verifier obligations. -/
local instance instInhabitedFieldSumcheckCompleteness : Inhabited F := ⟨0⟩

/-- **The embedded sum-check completeness residual for LogUp**, discharged modulo the named
single-round bridge.

This is a `sorry`-free *conditional* proof that the LogUp embedded sum-check phase is perfectly
complete (error `0`) from `midRelation` to `outputRelation` under the hypotheses below, obtained by
delegating to the axiom-clean `sumcheckCompletenessResidual_of_perRound`. With the corrected
claim-true `midRelation` (issue #13) the `proj_complete` obligation is the theorem
`SumcheckLensProjComplete_unconditional`, so no honest-support hypothesis appears (the historical,
globally-quantified `hHonest` was unsatisfiable and has been removed tree-wide; see the dmvt audit
on issue #13). The hypotheses are the precisely-typed named `hPerRound`, `hInit`, `hImplSupp`:

* `hPerRound` — the single-round inner sum-check `oracleReduction = reduction` equation. It is
  false for `n ≥ 1`
  (`Sumcheck.Spec.SingleRound.not_forall_oracleReduction_toReduction_eq_reduction`; LogUp's
  two-point sign domain has `(2 : F) ≠ 0`), so this theorem only has content for `n = 0`. The
  bridge-free route `sumcheckCompletenessResidual_unconditional` in
  `SumcheckCompletenessUncond.lean` avoids it;
* `hInit` — `init` never fails;
* `hImplSupp` — the oracle implementation preserves query support.
-/
theorem sumcheckCompletenessResidual_proved
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
  sumcheckCompletenessResidual_of_perRound oSpec F n M params init impl
    hPerRound hInit hImplSupp

end SumcheckCompleteness

end Logup

/-! ## Axiom audit -/
#print axioms Logup.sumcheckCompletenessResidual_proved
