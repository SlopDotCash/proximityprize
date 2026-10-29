/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ProximityPrize.Compatibility.SpartanFirstChallenge
import ArkLib.ProofSystem.Spartan.ComposedCompleteness
import ArkLib.ProofSystem.Spartan.FirstChallengeComplete

/-!
# The `firstChallenge` leaf of the composed Spartan completeness, discharged (#114)

Discharges hypothesis `h₂` of `Spartan.Spec.Bricks.composedCompletenessStatement_of_five_leaves`
(`ComposedCompleteness.lean`): the completed downstream `firstChallenge` phase (`oracleReduction.completedFirstChallenge`) is perfectly complete from the consumer's pinned input relation `firstMessageRelOut` to the
bridge-free first-sumcheck input relation `firstSumcheckRelInBF`.

Both consumer endpoints are *definitionally* the honest endpoints of `FirstChallengeComplete.lean`:

* `firstMessageRelOut` (= `spartanRelIn` with the witness moved into the appended oracle slot)
  is `firstChallengeRelIn` — both say "the R1CS instance `(𝕩, A, B, C, 𝕨)` is satisfied";
* `firstSumcheckRelInBF` is `firstChallengeRelOut` — the same satisfiability with the sampled
  challenge `τ` recorded in (and irrelevant to) the statement.

The leaf reuses the completed native theorem `completedFirstChallenge_perfectCompleteness`,
transported across the two definitional relation bridges below. The canonical inherited
`oracleReduction.firstChallenge` constructor and its admitted interface remain separate.

-/

open OracleComp OracleSpec

namespace Spartan.Spec.Bricks

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- The consumer's `firstChallenge` input relation `firstMessageRelOut` (i.e. `spartanRelIn` with
the witness moved into the appended oracle slot, `ComposedCompleteness.lean`) is definitionally the
honest `firstChallengeRelIn` of `FirstChallengeComplete.lean`. -/
theorem firstMessageRelOut_eq_firstChallengeRelIn :
    firstMessageRelOut (R := R) pp = firstChallengeRelIn (R := R) pp := rfl

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- The honest `firstChallengeRelOut` of `FirstChallengeComplete.lean` is definitionally the
consumer's bridge-free first-sumcheck input relation `firstSumcheckRelInBF`
(`FirstSumcheckBridgeFree.lean`). -/
theorem firstChallengeRelOut_eq_firstSumcheckRelInBF :
    firstChallengeRelOut (R := R) pp = firstSumcheckRelInBF (R := R) pp := rfl

omit [IsDomain R] [Fintype R] [DecidableEq R] in
/-- **Leaf `h₂` of `composedCompletenessStatement_of_five_leaves`, discharged (unconditional).**
The Spartan `firstChallenge` phase is perfectly complete from `firstMessageRelOut` to
`firstSumcheckRelInBF` — exactly the relation endpoints the composed-completeness consumer pins.
No hypotheses beyond the ambient instances: the completed native phase completeness theorem
is transported across two definitional relation equalities. -/
theorem completedFirstChallenge_perfectCompleteness_leaf
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)} :
    (oracleReduction.completedFirstChallenge R pp oSpec).perfectCompleteness init impl
      (firstMessageRelOut (R := R) pp) (firstSumcheckRelInBF (R := R) pp) := by
  rw [firstMessageRelOut_eq_firstChallengeRelIn pp,
    ← firstChallengeRelOut_eq_firstSumcheckRelInBF pp]
  exact completedFirstChallenge_perfectCompleteness pp oSpec

end Spartan.Spec.Bricks

#print axioms Spartan.Spec.Bricks.firstMessageRelOut_eq_firstChallengeRelIn
#print axioms Spartan.Spec.Bricks.firstChallengeRelOut_eq_firstSumcheckRelInBF
#print axioms Spartan.Spec.Bricks.completedFirstChallenge_perfectCompleteness_leaf
