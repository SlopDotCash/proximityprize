/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Extensions.OracleReduction.Security.Basic
import ArkLib.Extensions.OracleReduction.Composition.Sequential.Append
import ArkLib.ProofSystem.Logup.Protocol
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckBridge

/-!
# LogUp Soundness

Main soundness statement for Protocol 2 of `paper.txt`.

## Proof architecture and the named residual

`logupVerifier` is *definitionally* the sequential composition
`OracleVerifier.append outerVerifier sumcheckVerifier` (see `logupVerifier_eq_append`), so its
soundness splits into a composition step and two sub-verifier facts:

* outer-phase soundness for `outerVerifier`, with intermediate language `midLanguage` and error
  `outerSoundnessError` (the two LogUp algebraic-check terms), and
* embedded-sumcheck soundness for `sumcheckVerifier`, with error `sumcheckSoundnessError`.

The two sub-verifier facts are collected into the named residual `SubPhaseSoundnessResidual`;
`Security/SubPhaseSplit.lean` names its halves `OuterSoundnessResidual` and
`SumcheckSoundnessResidual`. The error reconciliation
`outerSoundnessError + sumcheckSoundnessError = logupSoundnessError …` holds by `rfl` because
`logupSoundnessError` is *defined* as that sum.

`logup_soundness_of_residual` below is a legacy interface, not a composition proof: its
`hAppendSoundness` hypothesis is literally its conclusion, and `OracleVerifier.append_soundness`
returns that hypothesis unchanged, so the theorem holds by `hAppendSoundness` alone.

## Current status: restricted dischargers, no unconditional theorem

The outer half, the sumcheck half and the composed headline all have conditional theorems now:

* `outerVerifier_soundness_mid` and the end-to-end headline `logup_soundness_end_to_end` in
  `Security/OuterMaliciousSoundness.lean`;
* `outerSoundnessResidual_holds`, `sumcheckSoundnessResidual_holds_pointwise`,
  `subPhaseSoundnessResidual_holds`, `appendSoundnessResidual_holds` and
  `logupSoundnessBrickResidual_holds` in `Security/LogupResidualDischarge.lean`.

Each holds only under explicit side conditions. The outer half assumes `2 ^ n < Fintype.card F`
and `n ≤ params.numGroups`; the sumcheck half assumes `0 < n` and `[oSpec.Fintype]`,
`[oSpec.Inhabited]`; the bundled and end-to-end results assume all of these; and every one assumes
state-preserving, never-failing and value-blind shared-oracle implementations (`himplSP`,
`himplNF`, `himplVB`). The sumcheck half concerns the in-tree oracle verifier `sumcheckVerifier`
as encoded here, not other sumcheck verifier implementations. So `SubPhaseSoundnessResidual` is
discharged on that regime only: no theorem proves it for arbitrary `F`, `n`, `params`, `init` and
`impl`. The definitional equivalences of `Security/SubPhaseSplit.lean`
(`subPhaseSoundnessResidual_iff_split` and its siblings) prove neither side, so they are not
providers of these residuals.

The final output language is `Set.univ` (`outputRelation_language`), so these soundness
statements are nontrivial acceptance-probability bounds, not vacuous language inclusions.
-/

open scoped NNReal

namespace Logup

section Soundness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances (`instOuterPSpecChallengeSampleable`) used when naming `outerVerifier.soundness`. -/
local instance instInhabitedFieldLogupSoundness : Inhabited F := ⟨0⟩

/-- The two LogUp algebraic-check soundness terms for the outer phase: the pole/grand-sum check
error of Protocol 2. This is the `soundnessError₁` summand of `logupSoundnessError`. -/
noncomputable def outerSoundnessError (F : Type) [Fintype F] (n M : ℕ)
    (params : ProtocolParams M) : ℝ≥0 :=
  ((((M + 1) * Fintype.card (Hypercube n) - 1 : ℕ) : ℝ≥0) /
      ((Fintype.card F - Fintype.card (Hypercube n) : ℕ) : ℝ≥0)) +
    (((params.numGroups + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0))

/-- Paper-shaped soundness error for the LogUp outer checks plus the embedded sumcheck error.

Defined as `outerSoundnessError + sumcheckSoundnessError` so that the
`OracleVerifier.append_soundness` error `soundnessError₁ + soundnessError₂` matches by `rfl`. -/
noncomputable def logupSoundnessError (F : Type) [Fintype F] (n M : ℕ) (params : ProtocolParams M)
    (sumcheckSoundnessError : ℝ≥0) : ℝ≥0 :=
  outerSoundnessError F n M params + sumcheckSoundnessError

/-- The intermediate language threaded between the outer LogUp phase and the embedded sumcheck.
This is the set of intermediate statements whose embedded-sumcheck claim `logupOuterSumcheckClaim`
is true (i.e. zero). This is the exact claim that the embedded sumcheck receives and verifies. -/
def midLanguage : Set (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) :=
  { p | logupOuterSumcheckClaim F n M params p.1 p.2 = 0 }

/-- The full LogUp verifier is, definitionally, the sequential composition of the outer verifier and
the embedded sumcheck verifier. This is the structural fact driving the soundness proof via
`OracleVerifier.append_soundness`. -/
theorem logupVerifier_eq_append :
    logupVerifier oSpec F n M params =
      OracleVerifier.append (outerVerifier oSpec F n M params)
        (sumcheckVerifier oSpec F n M params) := rfl

/-- The two sub-phase soundness obligations of the LogUp composition, stated as a single named
`Prop` residual (not proved in this file).

* The outer phase (`outerVerifier`) is sound with intermediate language `midLanguage` and error
  `outerSoundnessError F n M params`.
* The embedded sumcheck (`sumcheckVerifier`) is sound with error `sumcheckSoundnessError`.

Status: `subPhaseSoundnessResidual_holds` (`Security/LogupResidualDischarge.lean`) proves this
residual under the side conditions listed in the module docstring (`0 < n`,
`2 ^ n < Fintype.card F`, `n ≤ params.numGroups`, finite and inhabited `oSpec`, and
state-preserving, never-failing, value-blind implementations). No theorem proves it for arbitrary
parameters and implementations, and the equivalence `subPhaseSoundnessResidual_iff_split` is a
definitional repackaging, not a proof of it. -/
def SubPhaseSoundnessResidual (sumcheckSoundnessError : ℝ≥0) : Prop :=
    (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midLanguage F n M params)
        (outerSoundnessError F n M params) ∧
      (sumcheckVerifier oSpec F n M params).soundness init impl
        (midLanguage F n M params) outputRelation.language sumcheckSoundnessError

/-- **Legacy interface, not a composition proof.** The conclusion is LogUp Protocol 2 soundness
with error `logupSoundnessError F n M params s = outerSoundnessError F n M params + s` (exactly the
`soundnessError₁ + soundnessError₂` shape of `append_soundness`), but the hypothesis
`hAppendSoundness` is literally that conclusion: the body forwards it through
`OracleVerifier.append_soundness`, whose generic interface returns its residual hypothesis
unchanged, so the sub-phase argument `h` is not needed and the theorem proves no composition fact.
For the restricted end-to-end soundness theorem see `logup_soundness_end_to_end`
(`Security/OuterMaliciousSoundness.lean`) and its side conditions. -/
theorem logup_soundness_of_residual (sumcheckSoundnessError : ℝ≥0)
    (h : SubPhaseSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError)
    (hAppendSoundness :
      (logupVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language outputRelation.language
        (logupSoundnessError F n M params sumcheckSoundnessError)) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) := by
  -- The retained interface requires the actual append bound explicitly. Fresh-init subphase
  -- bounds alone do not imply the canonical continuation-state soundness premise.
  exact hAppendSoundness

end Soundness

end Logup
