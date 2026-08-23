/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ComposedCompleteness
import ArkLib.ProofSystem.Spartan.ComposedCompletenessLeaves
import ArkLib.ProofSystem.Spartan.FirstChallengeComplete
import ArkLib.ProofSystem.Spartan.LinearCombinationComplete
import ArkLib.ProofSystem.Spartan.FinalCheckLeafComplete

/-!
# Spartan composed PIOP perfect completeness — final assembly (issue #114)

This file discharges **all five** remaining leaf hypotheses of
`composedCompletenessStatement_of_five_leaves`, yielding the composed Spartan PIOP
perfect-completeness obligation `composedCompletenessStatement` with **no leaf
hypotheses left** — only the standard honest-implementation side conditions
(`NeverFail init`, support-faithfulness, state-preservation, no-failure) remain, exactly
as in every other completeness consumer in the tree.

The honesty-threading relation chain (the design fix for the D1 target-`0` mismatch):

* `h₂` — `firstChallenge_perfectCompleteness`, re-pointed across two seams:
  `firstMessageRelOut ⊆ firstChallengeRelIn` (the `SendSingleWitness` pushforward *is*
  R1CS satisfiability with the witness in the oracle slot, proved here) and
  `firstChallengeRelOut ⊆ firstSumcheckRelInBF` (definitionally equal `setOf` bodies).
* `h₄` — the parametric `sendEvalClaim_perfectCompleteness` at
  `relIn := firstSumcheckRelOutBF`; its output relation *carries the eval-claim honesty
  conjunct* — the fact that the bundled claim oracle stores `evalClaimValue`.
* `h₅` — `linearCombination_perfectCompleteness_sendEvalClaimBF`: the RLC round records
  the challenge and passes the honesty-carrying relation through into
  `prependRLCTargetRelIn`.
* `h₆` — `prependRLCTarget_perfectCompleteness_secondSumcheckRelInBF`: the honest
  RLC-target adapter lands in the consumer-pinned `secondSumcheckRelInBF` (the proven D1
  inclusion).
* `h₈` — `finalCheck_perfectCompleteness_leaf`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Spartan.Spec.Bricks

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] [VCVCompatible R] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Seam 1→2:** the `firstMessage` pushforward relation is (an inclusion into) the
`firstChallenge` input relation: membership in `firstMessageRelOut` *is* R1CS satisfiability
with the witness read off the appended oracle slot, which is the defining condition of
`firstChallengeRelIn` (`spartanRelIn` is `@[reducible]`). -/
theorem firstMessageRelOut_subset_firstChallengeRelIn :
    firstMessageRelOut (R := R) pp ⊆ firstChallengeRelIn (R := R) pp :=
  fun _ hx => hx

/-- **Seam 2→3:** the `firstChallenge` output relation coincides with the bridge-free
first-sum-check input relation (definitionally equal `setOf` bodies). -/
theorem firstChallengeRelOut_subset_firstSumcheckRelInBF :
    firstChallengeRelOut (R := R) pp ⊆ firstSumcheckRelInBF (R := R) pp :=
  fun _ hx => hx

/-- **The `firstChallenge` leaf at the consumer endpoints** (`h₂` of
`composedCompletenessStatement_of_five_leaves`): perfect completeness from
`firstMessageRelOut` into `firstSumcheckRelInBF`, by re-pointing
`firstChallenge_perfectCompleteness` across the two seam inclusions. -/
theorem firstChallenge_perfectCompleteness_consumer :
    (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl
      (firstMessageRelOut (R := R) pp) (firstSumcheckRelInBF (R := R) pp) := by
  have h := firstChallenge_perfectCompleteness (R := R) (pp := pp) (oSpec := oSpec)
    (init := init) (impl := impl)
  unfold OracleReduction.perfectCompleteness Reduction.perfectCompleteness at h ⊢
  have h' := Reduction.completeness_relOut_mono init impl
    (firstChallengeRelOut_subset_firstSumcheckRelInBF pp) h
  exact Reduction.completeness_relIn_mono init impl
    (firstMessageRelOut_subset_firstChallengeRelIn pp) h'

/-- **Composed Spartan PIOP perfect completeness, fully discharged (issue #114).**
`composedCompletenessStatement` holds with *no leaf hypotheses*: all eight phase
perfect-completenesses are the in-tree machine-checked theorems, threaded along the
honesty-carrying relation chain. Only the standard honest-implementation side conditions
remain as inputs. -/
theorem composedCompletenessStatement_proven
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    composedCompletenessStatement R pp oSpec (composedPIOP_Rc pp oSpec) init impl :=
  composedCompletenessStatement_of_five_leaves.{0, 0, 0} pp oSpec hm hn
    (firstChallenge_perfectCompleteness_consumer pp oSpec)
    (sendEvalClaim_perfectCompleteness R pp oSpec init impl
      (firstSumcheckRelOutBF (R := R) pp))
    (linearCombination_perfectCompleteness_sendEvalClaimBF pp oSpec)
    (prependRLCTarget_perfectCompleteness_secondSumcheckRelInBF pp oSpec)
    (finalCheck_perfectCompleteness_leaf (R := R) (pp := pp) (oSpec := oSpec)
      (init := init) (impl := impl))
    hInit hImplSupp himplSP himplNF

end Spartan.Spec.Bricks

-- Axiom checks
#print axioms Spartan.Spec.Bricks.firstMessageRelOut_subset_firstChallengeRelIn
#print axioms Spartan.Spec.Bricks.firstChallenge_perfectCompleteness_consumer
#print axioms Spartan.Spec.Bricks.composedCompletenessStatement_proven
