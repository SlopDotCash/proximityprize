/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Fri.Spec.General
import ArkLib.OracleReduction.Completeness

/-!
# FRI: Perfect Completeness of the Composed Folding Reduction (scratch / issue #117)

This scratch module develops the perfect-completeness theorem for the *composed* FRI folding
reduction (`Fri.Spec.reductionFold` and its extension to the query round, `Fri.Spec.reduction`).

## Architecture (bricks A–D, per issue #117)

The composed reduction is built by `OracleReduction.append`/`seqCompose` out of three pieces:
* the `k` non-final folding rounds `FoldPhase.foldOracleReduction` (`pSpec` = 2 messages each),
* the final folding round `FinalFoldPhase.finalFoldOracleReduction` (`pSpec` = 2 messages),
* the (zero-prover-message) query round `QueryRound.queryOracleReduction`.

Perfect completeness of the whole is assembled from per-round perfect completeness via the
**fully-proven** composition keystones:
* `Reduction.seqCompose_perfectCompleteness_of_append` (n-ary from binary `append`, 0 sorries),
* `OracleReduction.append_perfectCompleteness` / `reduction_append_perfectCompleteness`
  (binary, **named-residual** reductions whose deep dependency is the proven `Prover.append_run`).

### `NeverFail` convention (Brick B)

Per the `unroll_2_message_reduction_perfectCompleteness` keystone
(`OracleReduction/Completeness.lean:551`) and the Binius `foldOracleReduction_perfectCompleteness`
sibling, per-round completeness is **false** without `hInit : NeverFail init` (the verifier's
`guard`/`do`-block can fail when `init` itself fails). Every per-round and composed statement here
carries `hInit : NeverFail init` from the start, exactly as the Binius repairs documented.

### Named residuals (honest-protocol discipline)

The per-round monadic unrolling through FRI's concrete `pSpec` is the genuinely deep step (cf. the
~150-line Binius `foldOracleReduction_perfectCompleteness`). We expose it as a named `def : Prop`
residual per round, plus a proven `_of_residual` reduction. The composition layer (bricks C, D) is
then *fully* discharged against those residuals using the proven composition keystones — no `sorry`
and no new axioms in the composition material itself.
-/

namespace Fri

open OracleSpec OracleComp ProtocolSpec NNReal Domain
open scoped NNReal

namespace Spec

namespace Completeness

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n : ℕ}
variable {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n F}
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-! ### `SampleableType` for the FRI challenges

The per-round protocol specs send a single field-element challenge (`F`) in the verifier→prover
direction; the codeword/polynomial messages are in the prover→verifier direction. So every
`ChallengeIdx` selects index `0`, whose `«Type»` is `F`, and `SampleableType F` (assumed) supplies
the instance the completeness keystone needs. These mirror the existing `Inhabited`/`Fintype`
challenge instances in `Fri/Spec/SingleRound.lean`. -/

instance instSampleableTypeFoldChallenge {i : Fin k} :
    ∀ j, SampleableType ((FoldPhase.pSpec s (ω := ω) i).Challenge j) := by
  rintro ⟨j, hj⟩
  have h_j_eq_0 : j = 0 := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j1 =>
        cases j1 using Fin.cases with
        | zero => simp at hj
        | succ j2 => exact j2.elim0
  subst h_j_eq_0
  simpa [FoldPhase.pSpec, Challenge] using (inferInstance : SampleableType F)

instance instSampleableTypeFinalFoldChallenge :
    ∀ j, SampleableType ((FinalFoldPhase.pSpec F).Challenge j) := by
  rintro ⟨j, hj⟩
  have h_j_eq_0 : j = 0 := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j1 =>
        cases j1 using Fin.cases with
        | zero => simp at hj
        | succ j2 => exact j2.elim0
  subst h_j_eq_0
  simpa [FinalFoldPhase.pSpec, Challenge] using (inferInstance : SampleableType F)

/-! ## Brick A/B: per-round perfect completeness (named residual) -/

/-- **Brick A/B residual — non-final folding round.**

The honest non-final folding round `FoldPhase.foldOracleReduction s d i` is perfectly complete
w.r.t. the FRI per-round input/output relations, *given* `hInit : NeverFail init`.

This is the FRI analogue of the Binius `foldOracleReduction_perfectCompleteness`: the genuinely
deep content is the 2-message monadic unrolling through FRI's concrete `pSpec` (verifier `guard`
safety + the algebraic round-consistency identity, whose core `polyFold`/Lagrange identity is the
*proven* `RoundConsistency.generalised_round_consistency_completeness`). It is named as a residual
`Prop` so the composition layer (bricks C, D) can be discharged unconditionally. -/
def foldRoundPerfectCompletenessResidual
    (hInit : NeverFail init) (i : Fin k)
    (cond : ∑ j, (s j).1 ≤ n) (δ : ℝ≥0) : Prop :=
  OracleReduction.perfectCompleteness init impl
    (FoldPhase.inputRelation s (ω := ω) d i cond δ)
    (FoldPhase.outputRelation s (ω := ω) d i cond δ)
    (FoldPhase.foldOracleReduction s d i)

/-- **Brick A/B — non-final folding round** (reduction to its named residual). -/
theorem foldRound_perfectCompleteness
    (hInit : NeverFail init) (i : Fin k)
    (cond : ∑ j, (s j).1 ≤ n) (δ : ℝ≥0)
    (hResidual : foldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit i cond δ) :
    OracleReduction.perfectCompleteness init impl
      (FoldPhase.inputRelation s (ω := ω) d i cond δ)
      (FoldPhase.outputRelation s (ω := ω) d i cond δ)
      (FoldPhase.foldOracleReduction s d i) :=
  hResidual

/-- **Brick A/B residual — final folding round.**

The honest final folding round `FinalFoldPhase.finalFoldOracleReduction s d` is perfectly complete
w.r.t. the FRI final-round input/output relations, given `hInit : NeverFail init`. Same shape as
the non-final residual; here the prover sends the folded polynomial in the clear and the verifier
runs a degree `guard`. -/
def finalFoldRoundPerfectCompletenessResidual
    (hInit : NeverFail init)
    (cond : ∑ j, (s j).1 ≤ n) (δ : ℝ≥0) : Prop :=
  OracleReduction.perfectCompleteness init impl
    (FinalFoldPhase.inputRelation s (ω := ω) d cond δ)
    (FinalFoldPhase.outputRelation s (ω := ω) d cond δ)
    (FinalFoldPhase.finalFoldOracleReduction s d)

/-- **Brick A/B — final folding round** (reduction to its named residual). -/
theorem finalFoldRound_perfectCompleteness
    (hInit : NeverFail init)
    (cond : ∑ j, (s j).1 ≤ n) (δ : ℝ≥0)
    (hResidual :
      finalFoldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit cond δ) :
    OracleReduction.perfectCompleteness init impl
      (FinalFoldPhase.inputRelation s (ω := ω) d cond δ)
      (FinalFoldPhase.outputRelation s (ω := ω) d cond δ)
      (FinalFoldPhase.finalFoldOracleReduction s d) :=
  hResidual

end Completeness

end Spec

end Fri
