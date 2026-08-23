/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit

/-!
# Discharge of `Logup.OuterCompletenessResidual` (#368)

`SubPhaseSplit.lean` names `OuterCompletenessResidual` — the outer half of the LogUp
Protocol 2 sub-phase completeness, `(outerOracleReduction …).completeness …
(logupCompletenessError F n)` — as an open residual (the in-principle in-tree-closable
half, its failure event being the proven `probEvent_pole_le`).

That conclusion is now a **theorem**: `OuterCompleteness.lean` proves
`outerOracleReduction_completeness (hInit : NeverFail init)` with exactly the
conclusion that `OuterCompletenessResidual` abbreviates. The census still counted the
residual open only because no declaration with `OuterCompletenessResidual` as its
result-type head existed (the proven `outerCompletenessRunResidual_proved` discharges
the distinct *Run*-residual). This file supplies the missing provider — a direct
application of `outerOracleReduction_completeness`.

No `sorry`, no new axioms.
-/

open scoped NNReal

namespace Logup

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instInhabitedFieldOuterDischarge : Inhabited F := ⟨0⟩

/-- **Discharge of `Logup.OuterCompletenessResidual` (#368).** Under `NeverFail init`,
the outer-phase completeness obligation is a theorem, directly from
`outerOracleReduction_completeness`. -/
theorem OuterCompletenessResidual_holds (hInit : NeverFail init) :
    OuterCompletenessResidual oSpec F n M params init impl :=
  outerOracleReduction_completeness oSpec F n M params init impl hInit

end Logup
