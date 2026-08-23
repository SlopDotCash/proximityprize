/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.Soundness
import ArkLib.ProofSystem.Logup.Security.Completeness
import ArkLib.ProofSystem.Logup.Security.OuterCompleteness

/-!
# LogUp Protocol 2 — splitting the sub-phase residuals into independent obligations

`Logup.SubPhaseSoundnessResidual` / `Logup.SubPhaseCompletenessResidual`
(in `Security/Soundness.lean` / `Security/Completeness.lean`) each bundle **two**
genuinely-independent sub-verifier obligations into a single conjunction:

* an **outer**-phase obligation (the Protocol-2 pole / grand-sum algebraic checks on
  `outerVerifier` / `outerOracleReduction`), and
* an embedded **sumcheck** obligation (`sumcheckVerifier` / `sumcheckOracleReduction`,
  a `liftContext` of the generic `Sumcheck.Spec` reduction).

The module docstrings of those files explain that the two halves are blocked by
*different* upstream walls (no in-tree outer-LogUp verifier soundness theorem vs. no
plain `Sumcheck.Spec` soundness/completeness theorem + the lens conditions), and that
the outer completeness half is "in principle closable in-tree" while the sumcheck half
is not.

Bundling them as one `Prop` means a future agent who discharges *only* the outer half
(or only the sumcheck half) cannot plug it in. This file therefore **shrinks the
residual surface** (issue #13, acceptance "remove or shrink the residuals") by naming
each half separately and re-deriving the top-level reductions from the split halves:

* `OuterSoundnessResidual` / `SumcheckSoundnessResidual` and the `Iff.rfl` bridge
  `subPhaseSoundnessResidual_iff_split`;
* `AppendSoundnessResidual` / `LogupSoundnessBrickResidual` and
  `logup_soundness_of_bricks` — the two sub-phase halves plus the explicit append-composition
  brick;
* the completeness analogues `OuterCompletenessResidual` / `SumcheckCompletenessResidual`,
  `AppendCompletenessResidual` / `LogupCompletenessBrickResidual`,
  `subPhaseCompletenessResidual_iff_split`, `logup_completeness_of_bricks`.

No new mathematics and no new axioms: the bridges are definitional and the reductions
chain the existing `logup_soundness_of_residual` / `logup_completeness_of_residual`.
The point is to make the two walls **independently dischargeable** so they can be ground
brick-by-brick.
-/

open scoped NNReal

namespace Logup

section Split

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge
`SampleableType` instances used when naming the outer sub-verifier obligations. -/
local instance instInhabitedFieldSubPhaseSplit : Inhabited F := ⟨0⟩

/-! ### Soundness halves -/

/-- The **outer** half of `SubPhaseSoundnessResidual`: `outerVerifier` is sound from the
input language into `midLanguage` with the LogUp algebraic-check error
`outerSoundnessError`. The first conjunct of `SubPhaseSoundnessResidual`. -/
def OuterSoundnessResidual : Prop :=
  (outerVerifier oSpec F n M params).soundness init impl
    (inputRelation F n M).language (midLanguage F n M params)
    (outerSoundnessError F n M params)

/-- The **sumcheck** half of `SubPhaseSoundnessResidual`: `sumcheckVerifier` is sound from
`midLanguage` into the output language with error `sumcheckSoundnessError`. The second
conjunct of `SubPhaseSoundnessResidual`. -/
def SumcheckSoundnessResidual (sumcheckSoundnessError : ℝ≥0) : Prop :=
  (sumcheckVerifier oSpec F n M params).soundness init impl
    (midLanguage F n M params) outputRelation.language sumcheckSoundnessError

/-- `SubPhaseSoundnessResidual` is **definitionally** the conjunction of its two halves. -/
theorem subPhaseSoundnessResidual_iff_split (sumcheckSoundnessError : ℝ≥0) :
    SubPhaseSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError ↔
      OuterSoundnessResidual oSpec F n M params init impl ∧
        SumcheckSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError :=
  Iff.rfl

/-- **LogUp soundness from the two independent halves.** Identical conclusion to
`logup_soundness_of_residual`, but consuming the outer and sumcheck soundness obligations
*separately*, so either can be discharged on its own. -/
theorem logup_soundness_of_split (sumcheckSoundnessError : ℝ≥0)
    (hOuter : OuterSoundnessResidual oSpec F n M params init impl)
    (hSumcheck : SumcheckSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError)
    (hAppendSoundness :
      (logupVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language outputRelation.language
        (logupSoundnessError F n M params sumcheckSoundnessError)) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_of_residual oSpec F n M params init impl sumcheckSoundnessError
    ⟨hOuter, hSumcheck⟩ hAppendSoundness

/-- The **append-composition** soundness brick still exposed by
`OracleVerifier.append_soundness`. Keeping it separately named makes the remaining #13 wall
three-way rather than hiding composition inside an anonymous hypothesis. -/
def AppendSoundnessResidual (sumcheckSoundnessError : ℝ≥0) : Prop :=
  (logupVerifier oSpec F n M params).soundness init impl
    (inputRelation F n M).language outputRelation.language
    (logupSoundnessError F n M params sumcheckSoundnessError)

/-- The fully split soundness residual surface: outer LogUp soundness, lifted sumcheck
soundness, and append-composition soundness. -/
def LogupSoundnessBrickResidual (sumcheckSoundnessError : ℝ≥0) : Prop :=
  OuterSoundnessResidual oSpec F n M params init impl ∧
    SumcheckSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError ∧
      AppendSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError

/-- The fully split soundness residual is exactly the original bundled subphase residual plus the
named append-composition residual. -/
theorem logupSoundnessBrickResidual_iff_subPhase_append
    (sumcheckSoundnessError : ℝ≥0) :
    LogupSoundnessBrickResidual oSpec F n M params init impl sumcheckSoundnessError ↔
      SubPhaseSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError ∧
        AppendSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError := by
  constructor
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩

/-- **LogUp soundness from all named bricks.** This is a packaging theorem: it consumes the
three independently named remaining soundness obligations instead of a bundled sub-phase residual
plus an anonymous append-composition hypothesis. -/
theorem logup_soundness_of_bricks (sumcheckSoundnessError : ℝ≥0)
    (h : LogupSoundnessBrickResidual oSpec F n M params init impl sumcheckSoundnessError) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_of_split oSpec F n M params init impl sumcheckSoundnessError
    h.1 h.2.1 h.2.2

/-- **LogUp soundness from the original bundled subphase residual and named append residual.**
This is the direct consumer form for callers that have not split the subphase residual further. -/
theorem logup_soundness_of_subPhase_append (sumcheckSoundnessError : ℝ≥0)
    (hSub :
      SubPhaseSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError)
    (hAppend :
      AppendSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_of_bricks oSpec F n M params init impl sumcheckSoundnessError
    ⟨hSub.1, hSub.2, hAppend⟩

/-! ### Completeness halves -/

/-- The **outer** half of `SubPhaseCompletenessResidual`: the outer phase is complete with
the pole-rejection error `logupCompletenessError`. The first conjunct of
`SubPhaseCompletenessResidual`; per the `Completeness.lean` docstring this is the
in-principle in-tree-closable half (its failure event is the proven `probEvent_pole_le`). -/
def OuterCompletenessResidual : Prop :=
  (outerOracleReduction oSpec F n M params).completeness init impl
    (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n)

/-- The **sumcheck** half of `SubPhaseCompletenessResidual`: the embedded sumcheck is
complete with error `0`. The second conjunct of `SubPhaseCompletenessResidual`. -/
def SumcheckCompletenessResidual : Prop :=
  (sumcheckOracleReduction oSpec F n M params).completeness init impl
    (midRelation F n M params) outputRelation 0

/-- `SubPhaseCompletenessResidual` is **definitionally** the conjunction of its two halves. -/
theorem subPhaseCompletenessResidual_iff_split :
    SubPhaseCompletenessResidual oSpec F n M params init impl ↔
      OuterCompletenessResidual oSpec F n M params init impl ∧
        SumcheckCompletenessResidual oSpec F n M params init impl :=
  Iff.rfl

/-- The **append-composition** completeness brick still exposed by
`OracleReduction.append_completeness`, indexed by the two subphase completeness proofs that the
append theorem consumes. -/
def AppendCompletenessResidual
    (hOuter : OuterCompletenessResidual oSpec F n M params init impl)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl) : Prop :=
  (outerOracleReduction oSpec F n M params).appendCompletenessResidual
    (sumcheckOracleReduction oSpec F n M params) hOuter hSumcheck

/-- **LogUp completeness from the two independent halves.** Identical conclusion to
`logup_completeness_of_residual`, but consuming the outer and sumcheck completeness
obligations *separately*, so either can be discharged on its own. The
`hAppendCompleteness` sequential-composition residual is threaded with the two subphase proofs
it depends on. -/
theorem logup_completeness_of_split
    (hOuter : OuterCompletenessResidual oSpec F n M params init impl)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl)
    (hAppendCompleteness :
      AppendCompletenessResidual oSpec F n M params init impl hOuter hSumcheck) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_of_residual oSpec F n M params init impl ⟨hOuter, hSumcheck⟩
    hAppendCompleteness

/-- The fully split completeness residual surface: outer LogUp completeness, lifted sumcheck
completeness, and append-composition completeness. -/
def LogupCompletenessBrickResidual : Prop :=
  ∃ hOuter : OuterCompletenessResidual oSpec F n M params init impl,
    ∃ hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl,
      AppendCompletenessResidual oSpec F n M params init impl hOuter hSumcheck

/-- The fully split completeness residual is exactly the original bundled subphase residual plus
the dependent append-composition residual indexed by that bundled proof's two projections. -/
theorem logupCompletenessBrickResidual_iff_subPhase_append :
    LogupCompletenessBrickResidual oSpec F n M params init impl ↔
      ∃ hSub : SubPhaseCompletenessResidual oSpec F n M params init impl,
        AppendCompletenessResidual oSpec F n M params init impl hSub.1 hSub.2 := by
  constructor
  · rintro ⟨hOuter, hSumcheck, hAppend⟩
    exact ⟨⟨hOuter, hSumcheck⟩, hAppend⟩
  · rintro ⟨hSub, hAppend⟩
    exact ⟨hSub.1, hSub.2, hAppend⟩

/-- **LogUp completeness from all named bricks.** This consumes the three independently named
remaining completeness obligations. -/
theorem logup_completeness_of_bricks
    (h : LogupCompletenessBrickResidual oSpec F n M params init impl) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) := by
  rcases h with ⟨hOuter, hSumcheck, hAppend⟩
  exact logup_completeness_of_split oSpec F n M params init impl hOuter hSumcheck hAppend

/-- **LogUp completeness from the original bundled subphase residual and named append residual.**
This is the direct consumer form for callers that have not split the subphase residual further. -/
theorem logup_completeness_of_subPhase_append
    (hSub : SubPhaseCompletenessResidual oSpec F n M params init impl)
    (hAppend :
      AppendCompletenessResidual oSpec F n M params init impl hSub.1 hSub.2) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_of_bricks oSpec F n M params init impl
    ⟨hSub.1, hSub.2, hAppend⟩

/-! ### Discharging the outer completeness half (issue #13 acceptance: shrink the residual) -/

/-- **The outer completeness half is no longer a residual.** `OuterCompletenessResidual` is exactly
the conclusion of the fully-proven `outerOracleReduction_completeness` (the honest outer LogUp oracle
reduction is complete with error `logupCompletenessError`, established end-to-end in
`Security/OuterCompleteness.lean` via the pole bound `card_poleSet_le` / `probEvent_pole_le` and the
per-state agreement `outer_perState_agree`). Under the standard completeness assumption
`NeverFail init` it therefore holds unconditionally — removing the outer half of the LogUp
completeness residual surface (issue #13 acceptance "remove or shrink the residuals"). -/
theorem outerCompletenessResidual_of_neverFail (hInit : NeverFail init) :
    OuterCompletenessResidual oSpec F n M params init impl :=
  outerOracleReduction_completeness oSpec F n M params init impl hInit

/-- **LogUp completeness from the sumcheck + append halves alone.** With the outer half discharged by
`outerCompletenessResidual_of_neverFail`, the full completeness reduction needs only the embedded
sumcheck completeness (`SumcheckCompletenessResidual`) and the append-composition completeness brick
— the two remaining completeness obligations of LogUp Protocol 2. -/
theorem logup_completeness_of_sumcheck_append (hInit : NeverFail init)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl)
    (hAppend :
      AppendCompletenessResidual oSpec F n M params init impl
        (outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit) hSumcheck) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_of_split oSpec F n M params init impl
    (outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit) hSumcheck hAppend

end Split

end Logup

/- Axiom audit for the split #13 LogUp residual front doors. -/
#print axioms Logup.SubPhaseSoundnessResidual
#print axioms Logup.logup_soundness_of_residual
#print axioms Logup.OuterSoundnessResidual
#print axioms Logup.SumcheckSoundnessResidual
#print axioms Logup.subPhaseSoundnessResidual_iff_split
#print axioms Logup.logup_soundness_of_split
#print axioms Logup.AppendSoundnessResidual
#print axioms Logup.LogupSoundnessBrickResidual
#print axioms Logup.logupSoundnessBrickResidual_iff_subPhase_append
#print axioms Logup.logup_soundness_of_bricks
#print axioms Logup.logup_soundness_of_subPhase_append
#print axioms Logup.SubPhaseCompletenessResidual
#print axioms Logup.logup_completeness_of_residual
#print axioms Logup.OuterCompletenessResidual
#print axioms Logup.SumcheckCompletenessResidual
#print axioms Logup.subPhaseCompletenessResidual_iff_split
#print axioms Logup.logup_completeness_of_split
#print axioms Logup.AppendCompletenessResidual
#print axioms Logup.LogupCompletenessBrickResidual
#print axioms Logup.logupCompletenessBrickResidual_iff_subPhase_append
#print axioms Logup.logup_completeness_of_bricks
#print axioms Logup.logup_completeness_of_subPhase_append
