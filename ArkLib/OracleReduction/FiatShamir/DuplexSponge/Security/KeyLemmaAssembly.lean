/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.VerifierReplay
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.SimulatorBudgets

/-!
# CO25 Lemma 5.1 (DSFS Key Lemma) — eager-surface campaign assembly

This module reconciles the parallel campaign lanes into the tightest honest top-level
theorems for the eager key lemma:

- `KeyLemmaHybrids.keyLemmaEager_of_steps` reduced `KeyLemmaEagerResidual` to the four
  per-step TV residuals (Claims 5.21–5.24) **plus** the witness budget residuals M1c/M1d;
- `SimulatorBudgets` has since **proven** M1c/M1d outright
  (`simulatedProverChallengeBudget` / `simulatedProverSharedBudget`);
- `VerifierReplay.hyb34Step_of_strictSplit` reduced the Claim 5.24 step to any Eq. 55
  coupling split `(εA, εB)` through the strict-replay hybrid `Hyb3Strict`.

Wiring these together yields:

- `keyLemmaEager_of_hybSteps` — **the current frontier**: the four hybrid-step residuals
  alone imply the full eager key lemma; every witness-budget obligation of CO25 Lemma 5.1
  (conjuncts (a) and (b)) is discharged.
- `keyLemmaEager_of_steps_strictSplit` — the Claim 5.24 hypothesis replaced by its proven
  Eq. 55 decomposition: Claims 5.21–5.23 plus any strict-split coupling pair summing to
  `claim5_24Bound` imply the eager key lemma.

## Residual census after this campaign round (the honest remaining-work map)

Open residuals **on the eager key-lemma critical path** (each one consumed by
`keyLemmaEager_of_hybSteps`):

1. `KeyLemmaHybrids.Hyb01StepResidual` — CO25 Claim 5.21 (Lemma 5.8 birthday switch,
   `D_DS` permutation → random encoded-challenge functions). Toolkit ready in
   `BirthdayBound` / `BirthdayBoundPaper` (accumulator + collision/landing bounds +
   `lemma5_8Bound_eq_claim5_21Bound`, plus the paper-event honest domination theorem);
   the active open probability core is `BirthdayBoundPaper.Lemma5_8EagerPaperResidual`
   (PRP/RF carrier coupling, event decomposition into capacity-segment families, budget
   recombination).
2. `KeyLemmaHybrids.Hyb12StepResidual` — CO25 Claim 5.22 (codec decoding bias, Eq. 53);
   needs `Codec.decode_isBiased` pushed through the simulator. No lane attacked it this
   round.
3. `KeyLemmaHybrids.Hyb23StepResidual` — CO25 Claim 5.23 (encoded/decoded query-format
   equivalence, exactly `0`); the `tr_i` memo-determinism calculus of `VerifierReplay`
   (`lookupD2SAlgoMemo_*`) plus the codec round-trip bricks are the intended toolkit.
4. `KeyLemmaHybrids.Hyb34StepResidual` — CO25 Claim 5.24 (verifier replay, Eq. 55); its
   deterministic layer is fully proven in `VerifierReplay` (memo commit/replay, table
   coupling keystone, strict split), leaving the two coupling bounds of
   `hyb34Step_of_strictSplit` (consumed here by `keyLemmaEager_of_steps_strictSplit`).

Refuted / superseded residuals **off the active path**:

5. `BirthdayBound.Lemma5_8EagerBirthdayFalseStatement` is false over the deviant in-tree event
   (`Lemma58EagerFalse.lean`). Its paper-faithful replacement is
   `BirthdayBoundPaper.Lemma5_8EagerPaperResidual`.
6. `KeyLemmaFoundations.Lemma5_14HonestFalseStatement` / `Lemma5_16HonestFalseAsStated` are false over
   the deviant in-tree event (`Lemma514ForkFalse.lean`, `Lemma516TimePFalse.lean`). The
   CO25-faithful M2 block is proved over `Paper.EPaper` by `lemma512Paper`,
   `lemma514Paper`, and `lemma516Paper`, and `BirthdayBoundPaper` consumes those theorems
   directly with no M2 residual hypotheses.

**Closed this campaign** (formerly open in `KeyLemmaFoundations`):
`D2sQueryStepGSpecBudgetResidual` (F4), `D2fOuterImplSharedBudgetResidual` (F4b),
`SimulatedProverChallengeBudgetResidual` (M1c), `SimulatedProverSharedBudgetResidual` (M1d)
— all proven in `SimulatorBudgets`.

The legacy `KeyLemma.KeyLemmaResidual` (i.i.d.-oracle surface, `ηStar` with exponent `C+1`)
is numerically over-strong (`KeyLemmaFoundations.ηStar_le_ηStarPaper` direction) and likely
unwitnessable; it is **not** a target of this assembly.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec OracleReduction

-- `[∀ i, DecidableEq (pSpec.Message i)]` is required by the proofs (the `SimulatorBudgets`
-- M1c/M1d theorems carry it) but not by the statements; silencing the type-only linter keeps
-- the hypothesis where the proof needs it (repo precedent: the sibling lane modules).
set_option linter.unusedDecidableInType false

namespace DuplexSpongeFS.KeyLemmaAssembly

open DSTraceStorage TraceTransform ProverTransform KeyLemmaFoundations KeyLemmaHybrids

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]

/-- **Campaign frontier** (CO25 Lemma 5.1, eager surface): the four hybrid-step residuals
(Claims 5.21–5.24) alone imply the full eager key lemma. The witness budget conjuncts
(a)/(b) of Lemma 5.1 are no longer hypotheses — they are discharged by the proven
`SimulatorBudgets.simulatedProverChallengeBudget` (M1c, `θ★ = tₚ`) and
`SimulatorBudgets.simulatedProverSharedBudget` (M1d, 1:1 `oSpec` forwarding). -/
theorem keyLemmaEager_of_hybSteps
    [DecidableEq ι] [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (h01 : Hyb01StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h12 : Hyb12StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h23 : Hyb23StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h34 : Hyb34StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl :=
  keyLemmaEager_of_steps T_H T_P δ Salt oImpl h01 h12 h23 h34
    (SimulatorBudgets.simulatedProverChallengeBudget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P))
    (SimulatorBudgets.simulatedProverSharedBudget (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt) (T_H := T_H) (T_P := T_P))

/-- **Claim 5.24 via the proven Eq. 55 skeleton**: Claims 5.21–5.23 plus any strict-split
coupling pair — `εA` bounding `Δ(Hyb₃, Hyb3Strict)` (the bad-event mass off the replay
path) and `εB` bounding `Δ(Hyb3Strict, Hyb₄)` (the hit-path collapse), summing to
`claim5_24Bound` — imply the full eager key lemma. This composes
`VerifierReplay.hyb34Step_of_strictSplit` with `keyLemmaEager_of_hybSteps`. -/
theorem keyLemmaEager_of_steps_strictSplit
    [DecidableEq ι] [SampleableType U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    [SampleableType (OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [SampleableType (OracleFamily (eSpec (U := U) StmtIn pSpec δ))]
    (Salt : Type) [SaltCodec U δ Salt]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    [SampleableType (OracleFamily (fsChallengeOracle (StmtIn × Salt) pSpec))]
    (oImpl : QueryImpl oSpec ProbComp)
    (h01 : Hyb01StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h12 : Hyb12StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (h23 : Hyb23StepResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ Salt oImpl)
    (εA εB : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hA : ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
      (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StmtIn × pSpec.Messages))
      (tₕ tₚ tₚᵢ L : ℕ),
      pSpec.totalNumPermQueries ≤ L →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
      SPMF.tvDist (Hyb3 T_H T_P δ Salt oImpl V P)
          (VerifierReplay.Hyb3Strict T_H T_P δ Salt oImpl V P)
        ≤ εA tₕ tₚ tₚᵢ L)
    (hB : ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
      (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
        (StmtIn × pSpec.Messages))
      (tₕ tₚ tₚᵢ L : ℕ),
      pSpec.totalNumPermQueries ≤ L →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .hash) tₕ →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .perm) tₚ →
      IsQueryBoundP P (fun j => dsQueryFlavor j = .permInv) tₚᵢ →
      SPMF.tvDist (VerifierReplay.Hyb3Strict T_H T_P δ Salt oImpl V P)
          (Hyb4 oImpl V
            (eagerSimulatedProver (T_H := T_H) (T_P := T_P) (δ' := δ) (Salt' := Salt) P))
        ≤ εB tₕ tₚ tₚᵢ L)
    (hsum : ∀ tₕ tₚ tₚᵢ L : ℕ,
      εA tₕ tₚ tₚᵢ L + εB tₕ tₚ tₚᵢ L ≤ claim5_24Bound U tₕ tₚ tₚᵢ L) :
    KeyLemmaEagerResidual (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) T_H T_P δ oImpl :=
  keyLemmaEager_of_hybSteps T_H T_P δ Salt oImpl h01 h12 h23
    (VerifierReplay.hyb34Step_of_strictSplit T_H T_P δ Salt oImpl εA εB hA hB hsum)

end DuplexSpongeFS.KeyLemmaAssembly

#print axioms DuplexSpongeFS.KeyLemmaAssembly.keyLemmaEager_of_hybSteps
#print axioms DuplexSpongeFS.KeyLemmaAssembly.keyLemmaEager_of_steps_strictSplit

end
