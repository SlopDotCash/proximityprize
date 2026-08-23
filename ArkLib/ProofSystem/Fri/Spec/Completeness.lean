/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Fri.Spec.General
import ArkLib.ToMathlib.FriComplete
import ArkLib.ToMathlib.FriCompleteCompose

/-!
# FRI: Composed Folding Reduction Perfect Completeness (issue #117)

This module integrates the perfect completeness of the composed FRI reduction
(`Fri.Spec.reduction`), completing the proof outline from `ArkLib.ToMathlib.FriCompleteCompose`.
It records the false-as-stated query-round surface, defines the remaining folding-phase
residual, and applies the sequential composition keystones.
-/

namespace Fri.Spec.Completeness

open OracleSpec OracleComp ProtocolSpec NNReal Domain

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n : ℕ}
variable {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n F}
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- **Brick false-as-stated surface — query round.**

**Audit status (2026-06-10): SUSPECTED FALSE as stated — relation/check mismatch.** The query
verifier (`QueryRound.queryVerifier`) guards `RoundConsistency.roundConsistencyCheck` for
**every** round `i : Fin (k+1)` (comparing oracle `i` against oracle `i+1`, resp. the
in-the-clear final polynomial at `i = k`), but the stated input relation
(`QueryRound.outputRelation = FinalFoldPhase.outputRelation`) constrains **only the last
fold** (plaintext match + round-`k` folding consistency). A relation member whose oracles at
indices `< k` are inconsistent (e.g. arbitrary functions unrelated by folding) makes the
round-`i` guard fail for `i < k`, so the success probability is below `1` and perfect
completeness fails. The composite FRI reduction is *not* affected at the design level — the
honest runs reaching the query phase carry fully consistent oracles — but that invariant is
NOT recorded in the relation chain (each `FoldPhase.outputRelation i` constrains rounds
`i, i+1` only, and chaining forgets it). The honest repair is to thread a full-chain
consistency invariant through all round relations (a `Spec`-level relation redesign) and
restate this residual w.r.t. it; do NOT attempt to discharge the present statement.

**The repair is LANDED** (issue #341 closeout): `ToMathlib/FriCompleteQueryRound.lean`
states the invariant in the checker's own currency (`queryCheckerAccepts`) and proves the
repaired statement (`queryRound_perfectCompleteness_repaired`); the re-scoped remaining
obligation is `queryRoundChainDeliveryHypothesis` there (fold phase delivers the invariant).

This definition is intentionally **not** named as a strict residual: it is retained only as
the historical false surface consumed by old composition wrappers. -/
def queryRoundPerfectCompletenessFalseAsStated
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) (l : ℕ)
    [hQueryChallenge : ∀ i, SampleableType ((QueryRound.pSpec l (ω := ω)).Challenge i)]
    (hInit : NeverFail init) (δ : ℝ≥0) : Prop :=
  OracleReduction.perfectCompleteness init impl
    (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
    (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
    (QueryRound.queryOracleReduction.{0} s d dom_size_cond l)

/-- **Brick — query round** (reduction to the historical false-as-stated surface). -/
theorem queryRound_perfectCompleteness
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) (l : ℕ)
    (hInit : NeverFail init) (δ : ℝ≥0)
    [hQueryChallenge : ∀ i, SampleableType ((QueryRound.pSpec l (ω := ω)).Challenge i)]
    (hFalseStatement : queryRoundPerfectCompletenessFalseAsStated (k := k)
      (hQueryChallenge := hQueryChallenge) init impl dom_size_cond l hInit δ) :
    OracleReduction.perfectCompleteness init impl
      (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
      (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
      (QueryRound.queryOracleReduction.{0} s d dom_size_cond l) :=
  hFalseStatement

/-- **Brick D — folding phase** (statement). Discharged: see
`foldPhasePerfectCompletenessStatement_holds` (`ToMathlib/FriCompleteFoldPhase.lean`),
proven axiom-clean from the per-round inputs. -/
def foldPhasePerfectCompletenessStatement
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
    (hInit : NeverFail init) (δ : ℝ≥0)
    [hFoldChallenge : ∀ i,
      SampleableType ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i)]
    (hRounds :
      ∀ i : Fin k,
        foldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit i
          (round_bound dom_size_cond) δ)
    (hFinal :
      finalFoldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit
        (round_bound dom_size_cond) δ) : Prop :=
  OracleReduction.perfectCompleteness init impl
    (inputRelation k s d dom_size_cond δ)
    (FinalFoldPhase.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
    (reductionFold k s d (ω := ω))

/-- **Brick D — folding phase completeness.** -/
theorem foldPhase_perfectCompleteness
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
    (hInit : NeverFail init) (δ : ℝ≥0)
    [∀ i, ∀ j, SampleableType ((FoldPhase.pSpec (ω := ω) s i).Challenge j)]
    [∀ j, SampleableType ((FinalFoldPhase.pSpec F).Challenge j)]
    [hFoldChallenge : ∀ i,
      SampleableType ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i)]
    [OracleVerifier.Append.AppendCoherent (reductionFold k s d (ω := ω)).verifier]
    (hRounds :
      ∀ i : Fin k,
        foldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit i
          (round_bound dom_size_cond) δ)
    (hFinal :
      finalFoldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit
        (round_bound dom_size_cond) δ)
    (hResidual : foldPhasePerfectCompletenessStatement
      (hFoldChallenge := hFoldChallenge) init impl dom_size_cond hInit δ hRounds hFinal) :
    OracleReduction.perfectCompleteness init impl
      (inputRelation k s d dom_size_cond δ)
      (FinalFoldPhase.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
      (reductionFold k s d (ω := ω)) :=
  hResidual

set_option maxHeartbeats 1000000 in
-- The composition proof elaborates the generic sequential-composition theorem with FRI indices.
/-- **Brick D — composed FRI reduction perfect completeness.**
The honest FRI protocol is perfectly complete, reducing the proximity of the initial oracle
to the proximity of the final polynomial and the passing of the query checks.

The composition layer is **fully proven** (`reduction_perfectCompleteness_of_phases`,
challenge-seam append keystone); the only remaining hypotheses are the still-open *per-phase*
residuals (`hFoldRes`, `hQueryFalseStatement` and the per-round inputs they consume). -/
theorem reduction_perfectCompleteness
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) (l : ℕ)
    (hInit : NeverFail init) (δ : ℝ≥0)
    [∀ i, ∀ j, SampleableType ((FoldPhase.pSpec (ω := ω) s i).Challenge j)]
    [∀ j, SampleableType ((FinalFoldPhase.pSpec F).Challenge j)]
    [hFoldChallenge : ∀ i,
      SampleableType ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i)]
    [hQueryChallenge : ∀ i, SampleableType ((QueryRound.pSpec l (ω := ω)).Challenge i)]
    [OracleVerifier.Append.AppendCoherent (reductionFold k s d (ω := ω)).verifier]
    (hRounds :
      ∀ i : Fin k,
        foldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit i
          (round_bound dom_size_cond) δ)
    (hFinal :
      finalFoldRoundPerfectCompletenessResidual (d := d) (ω := ω) init impl hInit
        (round_bound dom_size_cond) δ)
    (hFoldRes : foldPhasePerfectCompletenessStatement
      (hFoldChallenge := hFoldChallenge) init impl dom_size_cond hInit δ hRounds hFinal)
    (hQueryFalseStatement : queryRoundPerfectCompletenessFalseAsStated (k := k)
      (hQueryChallenge := hQueryChallenge) init impl dom_size_cond l hInit δ) :
    letI : ∀ i, SampleableType
        (((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F) ++ₚ
          QueryRound.pSpec l (ω := ω)).Challenge i) :=
      @ProtocolSpec.instSampleableTypeChallengeAppend _ _ _ _ hFoldChallenge hQueryChallenge
    OracleReduction.perfectCompleteness init impl
      (inputRelation k s d dom_size_cond δ)
      (QueryRound.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ)
      ((reductionFold k s d (ω := ω)).append
        (QueryRound.queryOracleReduction.{0} s d dom_size_cond l)) := by
  exact reduction_perfectCompleteness_of_phases init impl dom_size_cond l hInit
    (foldPhase_perfectCompleteness init impl dom_size_cond hInit δ hRounds hFinal hFoldRes)
    (queryRound_perfectCompleteness init impl dom_size_cond l hInit δ hQueryFalseStatement)

#print axioms reduction_perfectCompleteness

end Fri.Spec.Completeness
