/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.Completeness

/-!
# LogUp Protocol 2 — the honest-run support facts (issue #13)

This file proves the **structural facts about the honest LogUp outer run** that locate the
honest-prover support and fold the pole event into the completeness error budget:

1. **The honest prover emits the honest-form oracle map by construction
   (`honestProver_output_oStmtOut_eq_honestForm`).** The honest LogUp prover's `output` step
   (`outerProver.output`, `Protocol.lean`) — *by definition* — emits exactly the oracle map
   `(.input i → oStmt i, .multiplicity → honestMultiplicity oStmt, .helpers → honestHelpers params
   oStmt x)`. A definitional identity (`rfl` on each `OuterOracleIdx` constructor) of the honest
   run, not an assumption.

2. **The honest-form body holds on every honest output (`honestForm_body_on_honest_output`).**
   For every genuine `inputRelation` input `(stmt₀, oStmt₀)` and every challenge `x` *off the table
   poles*, the honest prover's output statement satisfies — with witness `(stmt₀, oStmt₀)` — the
   existential "honest preimage + pole-free + honest-form oracles" body. I.e. wherever the honest
   run actually lands, the honest-support property is *provably true*.

3. **The pole event is inside the error budget (`poleEvent_le_logupCompletenessError`).** The only
   probabilistic content of the honest run is the table-pole event for the uniformly sampled `x`;
   its probability is `≤ logupCompletenessError F n = |Hypercube n| / |F|` (`probEvent_pole_le`).

## Historical note (issue #13, dmvt audit)

These facts formerly backed an attempted *decomposition of a global hypothesis* `hHonest`
(`HonestFormFact`/`PoleFreeFact` in the deleted `LogupCompletenessHonest.lean`): the headline
completeness theorems quantified the honest-support property over **all** after-outer statements.
That global quantification was **unsatisfiable** — an arbitrary statement with a corrupted
`.multiplicity` oracle has no honest preimage, and an adversarial `xChallenge` falsifies
pole-freeness — so every consumer was uninstantiable, and the whole `hHonest` surface was removed.
The completeness chain now routes through the claim-true `midRelation` instead
(`SumcheckLensProjComplete_unconditional`), needing no honest-support hypothesis at all. The
theorems below survive because they are *true and genuinely about the honest run*: they show the
honest-form property holds on the **reachable support** (the honest outputs), which is exactly the
quantification the removed hypothesis should have used.

No `sorry`/`sorryAx`/`admit`. The axiom audit at the bottom confirms axiom-cleanliness
(`propext`, `Classical.choice`, `Quot.sound`).
-/

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace Logup

section HonestSupport

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)

/-- `F` is inhabited (by `0`); matches the local instance used throughout the LogUp completeness
development. -/
local instance instInhabitedFieldLogupHonestSupport : Inhabited F := ⟨0⟩

/-! ### Step 1: the honest prover's output oracle map *is* the honest form (structural) -/

omit [Fact ((-1 : F) ≠ 1)] [SampleableType F] in
/-- **The honest LogUp prover emits the honest-form oracle map by construction.**

The honest outer prover's `output` step (`outerProver.output`, `Protocol.lean`) on the final state
`(oStmt, x, batch)` produces the oracle-statement map
`(.input i → oStmt i, .multiplicity → honestMultiplicity oStmt, .helpers → honestHelpers params
oStmt x)`. This is established as a definitional identity (`rfl` on each `OuterOracleIdx`
constructor), i.e. the real, build-verified content of the honest run — not an assumed property.

This is the prover-side structural fact behind `outerProver_output_pair_eq_verifier_recompute`
(which additionally shows the verifier recomputes the *same* map from the transcript). -/
theorem honestProver_output_oStmtOut_eq_honestForm
    (oStmt : ∀ i, OStmtIn F n M i) (x : F)
    (batch : BatchingChallenge F n params.numGroups) :
    ((outerProver oSpec F n M params).output (oStmt, x, batch)) =
      pure (({ xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 },
        fun
          | .input i => oStmt i
          | .multiplicity => honestMultiplicity oStmt
          | .helpers => honestHelpers params oStmt x), ()) :=
  rfl

/-! ### Step 2: the honest-form body is genuinely satisfied on honest outputs -/

omit [Fact ((-1 : F) ≠ 1)] [SampleableType F] in
/-- **The honest-support property holds on every honest prover output (no assumption).**

For a genuine `inputRelation` input `(stmt₀, oStmt₀)` and a challenge `x` *off the table poles*, the
honest prover's output statement — `{ xChallenge := x, … }` together with the honest-form oracle map
— satisfies the existential "honest preimage + pole-free + honest-form oracles" body, witnessed by
the very input `(stmt₀, oStmt₀)`.

This is the **reachable-support** form of the honest-support property: it quantifies only over
statements the honest run actually produces, where the property is *provably true*. (The removed
issue-#13 `hHonest` hypothesis instead quantified it over arbitrary, possibly fabricated
statements, which made it unsatisfiable.) -/
theorem honestForm_body_on_honest_output
    (stmt₀ : StmtIn F n M) (oStmt₀ : ∀ i, OStmtIn F n M i)
    (hInput : (((stmt₀, oStmt₀), ()) ∈ inputRelation F n M))
    (x : F)
    (hPole : ∀ u : Hypercube n,
      x + evalOnHypercube (tableOracle oStmt₀) u ≠ 0)
    (zChallenge : Fin n → F)
    (batchingScalars : Fin params.numGroups → F) :
    ∃ (stmtIn₀ : StmtIn F n M) (oStmtIn₀ : ∀ i, OStmtIn F n M i),
      (((stmtIn₀, oStmtIn₀), ()) ∈ inputRelation F n M) ∧
      (∀ u : Hypercube n,
        ({ xChallenge := x, zChallenge := zChallenge,
            batchingScalars := batchingScalars : StmtAfterOuter F n M params }).xChallenge +
          evalOnHypercube (tableOracle oStmtIn₀) u ≠ 0) ∧
      (fun
        | .input i => oStmt₀ i
        | .multiplicity => honestMultiplicity oStmt₀
        | .helpers => honestHelpers params oStmt₀ x : ∀ i, OStmtAfterOuter F n M params i)
        = (fun
            | .input i => oStmtIn₀ i
            | .multiplicity => honestMultiplicity oStmtIn₀
            | .helpers =>
                honestHelpers params oStmtIn₀
                  ({ xChallenge := x, zChallenge := zChallenge,
                      batchingScalars := batchingScalars : StmtAfterOuter F n M params }).xChallenge) :=
  ⟨stmt₀, oStmt₀, hInput, hPole, rfl⟩

/-! ### Step 3: the pole event is already inside the completeness error budget -/

/-- **The pole event is bounded by `logupCompletenessError` (folded into the budget).**

The only probabilistic content of the honest outer run is the table-pole event: the uniformly
sampled challenge `x` hits some pole `-t(u)`. Its probability is `≤ logupCompletenessError F n =
|Hypercube n| / |F|`, the genuinely-proven `probEvent_pole_le_logupCompletenessError`. This is the
probabilistic half of the honest-support story: the pole event's complement is exactly where the
honest run satisfies `honestForm_body_on_honest_output`, and its measure is already accounted for
inside the completeness error. -/
theorem poleEvent_le_logupCompletenessError (oStmt : ∀ i, OStmtIn F n M i)
    [DecidablePred
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)] :
    probEvent (uniformSample F)
      (fun x : F => ∃ u : Hypercube n, x + evalOnHypercube (tableOracle oStmt) u = 0)
      ≤ (logupCompletenessError F n : ℝ≥0∞) :=
  probEvent_pole_le_logupCompletenessError F n M oStmt

end HonestSupport

end Logup

/- Axiom audit for the honest-run support facts. -/
#print axioms Logup.honestProver_output_oStmtOut_eq_honestForm
#print axioms Logup.honestForm_body_on_honest_output
#print axioms Logup.poleEvent_le_logupCompletenessError
