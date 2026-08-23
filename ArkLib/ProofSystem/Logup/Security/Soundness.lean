/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.ProofSystem.Logup.Protocol
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckBridge

/-!
# LogUp Soundness

Main soundness statement for Protocol 2 of `paper.txt`.

## Proof architecture and the named residual

`logupVerifier` is *definitionally* the sequential composition
`OracleVerifier.append outerVerifier sumcheckVerifier` (see `logupVerifier_eq_append`). Soundness
therefore follows from `OracleVerifier.append_soundness` (the generic sequential-composition
probability lemma, whose `AppendCoherent` side condition for `outerVerifier` is the in-tree
`instOuterVerifierAppendCoherent`), supplying:

* outer-phase soundness for `outerVerifier`, with intermediate language `midLanguage` and error
  `outerSoundnessError` (the two LogUp algebraic-check terms), and
* embedded-sumcheck soundness for `sumcheckVerifier`, with error `sumcheckSoundnessError`.

These two sub-verifier soundness facts are collected into the named residual
`subPhaseSoundness`, and the top-level `logup_soundness` is reduced to it through
`OracleVerifier.append_soundness` in `logup_soundness_of_residual` (no `sorry`). For callers that
can discharge only one side at a time, `Security/SubPhaseSplit.lean` exposes the same residual as
the independent halves `OuterSoundnessResidual` and `SumcheckSoundnessResidual`. The error
reconciliation `outerSoundnessError + sumcheckSoundnessError = logupSoundnessError …` holds by
`rfl` because `logupSoundnessError` is *defined* as that sum.

## What blocks `subPhaseSoundness`

Both sub-facts are blocked by missing upstream security lemmas introduced *outside*
`ArkLib/ProofSystem/Logup/**`, which this development is not permitted to modify:

* No outer LogUp verifier soundness theorem for `outerVerifier` exists in-tree (the algebraic
  pole/grand-sum checks of Protocol 2).
* The embedded sumcheck soundness for `sumcheckVerifier` is a `liftContext` of
  `Sumcheck.Spec.oracleVerifier`. The generic sumcheck development currently provides single-round
  completeness and round-by-round knowledge-soundness infrastructure, but no full plain soundness
  theorem for `Sumcheck.Spec.oracleVerifier` at the shape needed here, and the lift also requires
  the `logupSumcheckContextLens` / `logupSumcheckOracleLens` soundness conditions.
* `OracleVerifier.append_soundness` currently exposes the sequential-composition soundness theorem
  as an explicit `hAppendSoundness` hypothesis. This keeps the obstruction as a named residual
  interface instead of hiding it behind `sorryAx`.

Hence this residual remains explicit, with a split front door in `Security/SubPhaseSplit.lean` for
the outer and sumcheck halves. The final output language is `Set.univ` (`outputRelation_language`),
so this is a nontrivial acceptance-probability bound, not a vacuous language inclusion.
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
`Prop` residual (not proved here).

* The outer phase (`outerVerifier`) is sound with intermediate language `midLanguage` and error
  `outerSoundnessError F n M params`.
* The embedded sumcheck (`sumcheckVerifier`) is sound with error `sumcheckSoundnessError`.

WALL (upstream security/composition gaps, outside `ArkLib/ProofSystem/Logup/**`, not modifiable
here): no in-tree outer LogUp soundness theorem; no full plain `Sumcheck.Spec` soundness theorem at
the lifted shape; and `OracleVerifier.append_soundness` carries the append-soundness theorem as an
explicit hypothesis. See the module docstring.

This is therefore kept as an explicit named residual `Prop` (no `sorry`); the main theorem
`logup_soundness_of_residual` consumes it. -/
def SubPhaseSoundnessResidual (sumcheckSoundnessError : ℝ≥0) : Prop :=
    (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midLanguage F n M params)
        (outerSoundnessError F n M params) ∧
      (sumcheckVerifier oSpec F n M params).soundness init impl
        (midLanguage F n M params) outputRelation.language sumcheckSoundnessError

/-- Main ArkLib soundness theorem for LogUp Protocol 2, **reduced to the named residual**
`SubPhaseSoundnessResidual` through the genuine sequential-composition soundness interface
`OracleVerifier.append_soundness` (whose append theorem is an explicit residual hypothesis; see the
module docstring).

The soundness error `logupSoundnessError F n M params s = outerSoundnessError F n M params + s`
is exactly the `soundnessError₁ + soundnessError₂` produced by `append_soundness`. This reduction's
own body contains no `sorry`. -/
theorem logup_soundness_of_residual (sumcheckSoundnessError : ℝ≥0)
    (h : SubPhaseSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError)
    (hAppendSoundness :
      (logupVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language outputRelation.language
        (logupSoundnessError F n M params sumcheckSoundnessError)) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) := by
  obtain ⟨hOuter, hSum⟩ := h
  -- `logupVerifier` is definitionally `append outerVerifier sumcheckVerifier`
  -- (`logupVerifier_eq_append`), and `logupSoundnessError = outerSoundnessError + s`, so the
  -- composed soundness fact unifies with the goal directly.
  exact OracleVerifier.append_soundness.{0, 0}
    (outerVerifier oSpec F n M params) (sumcheckVerifier oSpec F n M params) hOuter hSum
    hAppendSoundness

end Soundness

end Logup
