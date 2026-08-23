/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SumcheckCompletenessUncond
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessClose

/-! # End-to-end LogUp completeness with the sum-check half internalized (#13)

`logup_completeness_full` (brick C) assembles the headline LogUp completeness from `hInit`,
`hSumcheck` (`SumcheckCompletenessResidual`), and `hAppend` (the outer⊕sum-check append). The
`hSumcheck` half is supplied by the fully unconditional
`sumcheckCompletenessResidual_unconditional` — the proven `CubeFiber` multi-round oracle
completeness plus the claim-true `midRelation` (`{p | logupOuterSumcheckClaim … = 0}`), under
which the `proj_complete` obligation is a theorem. So the end-to-end completeness reduces to
`{hInit, hImplSupp, hAppend}` (`logup_completeness_uncondSumcheck` below); `hAppend` is in turn
discharged for the genuine non-zero error by `appendCompletenessResidual_wired`
(`LogupCompletenessWired.lean`), giving the headline `logup_completeness_final`.

**De-larped (issue #13, dmvt audit):** this theorem previously consumed the honest-support
hypothesis `hHonest`, which was unsatisfiable (statements with corrupted `.multiplicity` oracles
have no honest preimage); it is gone. The historical perfect special case
(`logupCompletenessError F n = 0`) was vacuous (`logupCompletenessError_ne_zero`) and no such
variant is stated. -/

open OracleComp OracleSpec ProtocolSpec
namespace Logup
noncomputable section
variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  [Fact ((-1 : F) ≠ 1)]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **End-to-end LogUp completeness, sum-check half internalized — no honest-support hypothesis.**
Reduced to the standard data facts `hInit`/`hImplSupp` and the genuine deep append residual
`hAppend`. The embedded-sum-check completeness is the unconditional
`sumcheckCompletenessResidual_unconditional` (no `hHonest`, no per-round bridge). -/
theorem logup_completeness_uncondSumcheck
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (hAppend :
      AppendCompletenessResidual oSpec F n M params init impl
        (outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit)
        (sumcheckCompletenessResidual_unconditional oSpec F n M params init impl
          hInit hImplSupp)) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_full oSpec F n M params init impl hInit
    (sumcheckCompletenessResidual_unconditional oSpec F n M params init impl hInit hImplSupp)
    hAppend

end
end Logup

/- Axiom audit. -/
#print axioms Logup.logup_completeness_uncondSumcheck
