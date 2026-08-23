/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Spartan.ComposedCompleteness
import ArkLib.ProofSystem.Spartan.LinearCombinationComplete

/-!
# Spartan composed completeness residual, reduced to TWO leaves (#114)

`composedCompletenessStatement_of_five_leaves` (`ComposedCompleteness.lean`) leaves five leaf
perfect-completeness obligations. Three of them are now discharged on the canonical relation
chain:

* `h₄` (`sendEvalClaim`) — `sendEvalClaim_perfectCompleteness` at the consumer-pinned
  `relD := firstSumcheckRelOutBF`, emitting
  `relE := sendEvalClaimRelOut … (firstSumcheckRelOutBF …)` (`ComposedCompletenessLeaves.lean`);
* `h₅` (`linearCombination`) — `linearCombination_perfectCompleteness_sendEvalClaimBF`, from that
  `relE` into `relF := prependRLCTargetRelIn` (`LinearCombinationComplete.lean`);
* `h₆` (honest RLC-target adapter) — `prependRLCTarget_perfectCompleteness_secondSumcheckRelInBF`,
  from that `relF` into the consumer-pinned `relG := secondSumcheckRelInBF`
  (`ComposedCompletenessLeaves.lean`).

The composed-completeness residual of `SpartanBricks` therefore reduces to the remaining **two**
leaf obligations:

* `h₂` — the `firstChallenge` phase (an in-tree proof `firstChallenge_perfectCompleteness` exists
  but its module `FirstChallengeComplete.lean` is under repair on `main`);
* `h₈` — the terminal `finalCheck` (`CheckClaim`) phase into `finalCheckRelOut`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Spartan.Spec.Bricks

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **`composedCompletenessStatement` reduced to the two remaining leaf perfect-completenesses**
(`firstChallenge` and `finalCheck`): the `sendEvalClaim`, `linearCombination` and honest
RLC-target leaves are discharged on the canonical chain
`firstSumcheckRelOutBF → sendEvalClaimRelOut … → prependRLCTargetRelIn → secondSumcheckRelInBF`. -/
theorem composedCompletenessStatement_of_two_leaves
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl
      (firstMessageRelOut (R := R) pp) (firstSumcheckRelInBF (R := R) pp))
    (h₈ : (finalCheck R pp oSpec).perfectCompleteness init impl
      (secondSumcheckRelOutBF (R := R) pp) (finalCheckRelOut R pp))
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    composedCompletenessStatement R pp oSpec (composedPIOP_Rc pp oSpec) init impl :=
  composedCompletenessStatement_of_five_leaves.{0, 0, 0} pp oSpec hm hn h₂
    (sendEvalClaim_perfectCompleteness R pp oSpec init impl
      (firstSumcheckRelOutBF (R := R) pp))
    (linearCombination_perfectCompleteness_sendEvalClaimBF pp oSpec)
    (prependRLCTarget_perfectCompleteness_secondSumcheckRelInBF pp oSpec)
    h₈ hInit hImplSupp himplSP himplNF

end Spartan.Spec.Bricks

-- Axiom check
#print axioms Spartan.Spec.Bricks.composedCompletenessStatement_of_two_leaves
