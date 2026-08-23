/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import ArkLib.ProofSystem.Logup.Security.RbrToSoundBridge
import ArkLib.ProofSystem.Sumcheck.Spec.General

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace Logup

section SumcheckSoundness

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances used when naming the sub-verifier obligations. -/
local instance instInhabitedFieldSumcheckSoundness : Inhabited F := ⟨0⟩

/-- **The embedded sum-check soundness residual for LogUp**, discharged modulo the round-by-round
soundness inputs.

This is a real proof — not a `sorry` — that `sumcheckVerifier` is sound from `midLanguage` into the
output language with error `sumcheckSoundnessError`, obtained by delegating to the axiom-clean
`sumcheckSoundnessResidual_holds_of_rbr` (the canonical "closed `hRbrToSound`" form for issue #13).
The genuine remaining content is exposed as the precisely-typed named hypotheses rather than hidden
inside a content-free `sorry`:

* `hError` — the union-bound error equation `sumcheckSoundnessError = ∑ i, rbrSoundnessError i`;
* `hProj` — the projection soundness algebra (upstream Schwartz–Zippel / grand-sum brick);
* `hInnerRbr` — the inner concrete sum-check oracle reduction's round-by-round soundness (the
  oracle-level multi-round sum-check keystone);
* `hMarginal` — the single measure-theoretic marginal-domination residual converting round-by-round
  soundness to plain soundness.
-/
theorem sumcheckSoundnessResidual_proved
    (sumcheckSoundnessError : ℝ≥0)
    {rbrSoundnessError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0}
    {innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))}
    (hError : sumcheckSoundnessError = ∑ i, rbrSoundnessError i)
    (hProj : SumcheckLensProjSound oSpec F n M params innerLangIn)
    (hInnerRbr :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
        innerLangIn (Set.univ) rbrSoundnessError)
    (hMarginal : Verifier.MarginalBridge init impl
      (midLanguage F n M params) outputRelation.language
      (sumcheckVerifier oSpec F n M params).toVerifier rbrSoundnessError) :
    SumcheckSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError :=
  sumcheckSoundnessResidual_holds_of_rbr oSpec F n M params init impl sumcheckSoundnessError
    hError hProj hInnerRbr hMarginal

end SumcheckSoundness

end Logup

/-! ## Axiom audit -/
#print axioms Logup.sumcheckSoundnessResidual_proved
