/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckLiftCoherent

/-!
# LogUp Protocol 2 — the embedded-sumcheck soundness lift (issue #13, brick E)

`Logup.SumcheckSoundnessResidual` (defined in `Security/SubPhaseSplit.lean`) is the plain-soundness
obligation for the LogUp embedded sum-check phase:

```
(sumcheckVerifier oSpec F n M params).soundness init impl
  (midLanguage F n M params) outputRelation.language sumcheckSoundnessError
```

Since
`sumcheckVerifier = (sumcheckOracleReduction …).verifier
  = (logupConcreteSumcheckOracleReduction …).verifier.liftContext (logupSumcheckOracleLens …)`
(definitionally, `rfl`), this brick transfers the inner generic multi-round sum-check
**round-by-round soundness** through the context lift via `OracleVerifier.liftContext_rbr_soundness`,
and then bridges round-by-round soundness to plain soundness, exactly mirroring (on the soundness
side) the `sumcheckCompletenessResidual_holds` development in `Security/SumcheckCompletenessClose.lean`.

## Structure of the lift

`OracleVerifier.liftContext_rbr_soundness` (in `LiftContext/OracleReduction.lean`) lifts the inner
oracle verifier's round-by-round soundness to the outer one. It consumes:

* `Logup.logupSumcheck_liftContextCoherent` — the proven (axiom-clean) `LiftContextCoherent`
  instance (design note #433), supplied locally via `haveI`.

* a `lens.toLens.IsSound` instance — the **lens-soundness** condition. This is the soundness analogue
  of the completeness `OracleContext.Lens.IsComplete` instance, and is assembled here in
  `sumcheckLensSound`:

  - its `lift_sound` half is *vacuous*: we run the inner sum-check with inner output language
    `Set.univ`, so the premise `innerStmtOut ∉ Set.univ` is never satisfiable — hence nothing to
    prove (this is the soundness mirror of the trivial `lift_complete`, which exploited
    `outputRelation = Set.univ`);

  - its `proj_sound` half — an outer statement outside `midLanguage` projects (under
    `logupSumcheckOracleLens.toLens`) *outside* the inner round-`0` sum-check language — is the
    genuine algebraic soundness content (it asserts the projected sum-check claim is non-zero exactly
    when the outer mid-claim is non-zero). It is taken as the named hypothesis `hProj`
    (`SumcheckLensProjSound`), the genuine residual gap (a later brick discharges it from the
    Schwartz–Zippel / grand-sum algebra in `Security/SoundnessConverse.lean`).

* `hInnerRbr` — the round-by-round soundness of the inner concrete sum-check *oracle* reduction
  `logupConcreteSumcheckOracleReduction` (= `Sumcheck.Spec.oracleReduction …`). The single-round
  generic sum-check RBR knowledge soundness exists in-tree
  (`Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness`, axiom-clean); its *multi-round*
  oracle-level packaging is the sequential-composition keystone still being assembled in the
  framework layer, so it is taken here as an explicit named hypothesis (a later brick supplies it —
  same convention as the completeness brick's `hInner`).

The lift yields `(sumcheckVerifier …).rbrSoundness …`. The final step — the generic
**round-by-round soundness ⇒ plain soundness** marginal/union-bound bridge — has its reusable
combinatorial and probabilistic backbone already in `Security/RoundByRound.lean`
(`exists_challenge_flip_of_false_zero_true_last`, `probEvent_exists_le_sum`,
`probEvent_le_sum_of_imp_exists`, `probEvent_simulateQ_run'_bind_trailing_le`, …) but is not yet
assembled into a single end-to-end theorem. It is therefore taken as the named hypothesis
`hRbrToSound` (the second genuine residual gap).

No `sorry`/`admit`. The three genuine upstream gaps are the named hypotheses `hProj`, `hInnerRbr`,
and `hRbrToSound`; everything mechanical (the lens-soundness assembly, the coherence threading, the
vacuous `lift_sound`, the lift application, and the residual repackaging) is proven and axiom-clean.
-/

open OracleComp ProtocolSpec
open scoped NNReal

namespace Logup

section SumcheckSoundnessLift

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`); mirrors the local instance used in the LogUp completeness
development. -/
local instance instInhabitedFieldSumcheckSoundnessLift : Inhabited F := ⟨0⟩

/-- The inner sum-check *output* statement type `Sumcheck.Spec.StatementRound F n (.last n)` is
inhabited by the zero target and zero challenge vector. Needed for `liftContext_rbr_soundness`. -/
local instance instInhabitedLogupSumcheckStmtOut :
    Inhabited (LogupSumcheckStmtOut F n M params) :=
  ⟨{ target := 0, challenges := fun _ => 0 }⟩

/-- The inner sum-check oracle statement family (the bounded-degree polynomial `Q`, `Unit`-indexed)
is inhabited by the zero polynomial. Needed for `liftContext_rbr_soundness`. -/
noncomputable local instance instInhabitedLogupSumcheckOracleStatement :
    ∀ i, Inhabited (LogupSumcheckOracleStatement F n M params i) :=
  fun _ => ⟨0⟩

/-- **The `proj_sound` half of `OracleStatement.Lens.IsSound` for the LogUp sum-check lens.**

An outer statement outside `midLanguage` (i.e. the LogUp mid-claim `logupOuterSumcheckClaim` is
nonzero) projects — under `logupSumcheckOracleLens.toLens` (`= logupSumcheckContextLens.stmt`),
namely to `(logupInitialSumcheckStatement, logupSumcheckOracleStmt …)` — *outside* the chosen inner
input sum-check language `innerLangIn`. This is the genuine soundness algebra: the projected
zero-sum sum-check claim is satisfiable only when the outer mid-claim vanishes. Left as a named
hypothesis (a later brick discharges it from the grand-sum / Schwartz–Zippel algebra in
`Security/SoundnessConverse.lean`).

Stated directly with `lens.toLens.proj` (the exact field the `IsSound` `proj_sound` obligation uses),
universe-pinned to `0` to match `sumcheckVerifier` / `sumcheckOracleReduction`. -/
def SumcheckLensProjSound
    (innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))) : Prop :=
  ∀ outerStmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i),
    outerStmtIn ∉ midLanguage F n M params →
    (logupSumcheckOracleLens.{0} oSpec F n M params).toLens.proj outerStmtIn ∉ innerLangIn

/-- **`OracleStatement.Lens.IsSound` for the LogUp embedded sum-check lens**, assembled from the
named projection hypothesis `hProj` (genuine soundness algebra) and the *vacuous* `lift_sound`.

The `lift_sound` half is discharged vacuously because the inner output language is `Set.univ`: the
premise `innerStmtOut ∉ Set.univ` is unsatisfiable, so there is nothing to prove. (This is the
soundness mirror of the trivial `lift_complete` in `sumcheckLensComplete`, which exploited
`outputRelation = Set.univ`.)

Marked `@[reducible]` so it can serve as the `lensSound` instance argument of
`liftContext_rbr_soundness`. Universe-pinned to `0` to match `sumcheckVerifier`. -/
@[reducible] def sumcheckLensSound
    (innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i)))
    (hProj : SumcheckLensProjSound oSpec F n M params innerLangIn) :
    (logupSumcheckOracleLens.{0} oSpec F n M params).toLens.IsSound
      (midLanguage F n M params) outputRelation.language
      innerLangIn (Set.univ)
      ((logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.toVerifier.compatStatement
        (logupSumcheckOracleLens.{0} oSpec F n M params).toLens) where
  proj_sound := hProj
  lift_sound := by
    intro _ _ _ hNot
    -- inner output language is `Set.univ`, so `∉ Set.univ` is unsatisfiable.
    exact absurd (Set.mem_univ _) hNot

/-- **Round-by-round soundness of `sumcheckVerifier`** (the lifted embedded sum-check verifier),
obtained by transferring the inner concrete sum-check oracle reduction's round-by-round soundness
through `OracleVerifier.liftContext_rbr_soundness`.

* `hProj` — the `proj_sound` algebraic obligation (named residual gap), threaded into
  `sumcheckLensSound`;
* `hInnerRbr` — the round-by-round soundness of the inner concrete sum-check oracle reduction
  (the oracle-level multi-round sum-check keystone, taken as a named hypothesis).

The coherence instance is the proven `logupSumcheck_liftContextCoherent`; the chosen inner output
language is `Set.univ` (making `lift_sound` vacuous). The output `rbrSoundness` is over the LogUp
sub-phase languages `midLanguage` and `outputRelation.language`, exactly as needed for the soundness
residual. -/
theorem sumcheckVerifier_rbrSoundness
    {rbrSoundnessError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0}
    {innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))}
    (hProj : SumcheckLensProjSound oSpec F n M params innerLangIn)
    (hInnerRbr :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
        innerLangIn (Set.univ) rbrSoundnessError) :
    (sumcheckVerifier oSpec F n M params).rbrSoundness init impl
      (midLanguage F n M params) outputRelation.language rbrSoundnessError := by
  haveI := logupSumcheck_liftContextCoherent oSpec F n M params
  haveI := sumcheckLensSound oSpec F n M params innerLangIn hProj
  -- `sumcheckVerifier = (logupConcreteSumcheckOracleReduction …).verifier.liftContext lens` (`rfl`).
  exact OracleVerifier.liftContext_rbr_soundness
    (lens := logupSumcheckOracleLens.{0} oSpec F n M params)
    (logupConcreteSumcheckOracleReduction oSpec F n M params (Fact.out : (-1 : F) ≠ 1)).verifier
    hInnerRbr

/-- **`SumcheckSoundnessResidual` holds.** The LogUp embedded sum-check phase is sound (error
`sumcheckSoundnessError`) from `midLanguage` to `outputRelation.language`, given:

* `hProj` — the `proj_sound` soundness algebra (the projected zero-sum sum-check claim is outside the
  inner input language whenever the outer mid-claim is nonzero), taken as a named hypothesis;
* `hInnerRbr` — round-by-round soundness of the inner concrete sum-check oracle reduction (the
  oracle-level multi-round sum-check keystone), taken as a named hypothesis;
* `hRbrToSound` — the generic **round-by-round soundness ⇒ plain soundness** marginal/union-bound
  bridge (its reusable backbone is proven in `Security/RoundByRound.lean`; the end-to-end assembly is
  the remaining framework brick), taken as a named hypothesis.

The lift `sumcheckVerifier_rbrSoundness` supplies the round-by-round soundness; `hRbrToSound`
converts it to the plain soundness of `SumcheckSoundnessResidual`. -/
theorem sumcheckSoundnessResidual_holds
    (sumcheckSoundnessError : ℝ≥0)
    {rbrSoundnessError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0}
    {innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))}
    (hProj : SumcheckLensProjSound oSpec F n M params innerLangIn)
    (hInnerRbr :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
        innerLangIn (Set.univ) rbrSoundnessError)
    (hRbrToSound :
      (sumcheckVerifier oSpec F n M params).rbrSoundness init impl
          (midLanguage F n M params) outputRelation.language rbrSoundnessError →
        (sumcheckVerifier oSpec F n M params).soundness init impl
          (midLanguage F n M params) outputRelation.language sumcheckSoundnessError) :
    SumcheckSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError :=
  hRbrToSound
    (sumcheckVerifier_rbrSoundness oSpec F n M params init impl hProj hInnerRbr)

end SumcheckSoundnessLift

end Logup

#print axioms Logup.sumcheckLensSound
#print axioms Logup.sumcheckVerifier_rbrSoundness
#print axioms Logup.sumcheckSoundnessResidual_holds
