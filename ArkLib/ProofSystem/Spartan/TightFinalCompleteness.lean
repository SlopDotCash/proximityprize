/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightFinalLeaf
import ArkLib.ProofSystem.Spartan.TightSecondCompleteness
import ArkLib.ProofSystem.Spartan.TightSecondBinding
import ArkLib.ProofSystem.Spartan.TightConjoinedSecondLeaf
import ArkLib.ToVCVio.Lemmas
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ
import ProximityPrize.Compatibility.CheckClaimPassThrough

/-!
# Tight terminal completeness: `finalCheckTight` + the binding strengthening (#329, B7, task R2)

The two completeness pieces closing the tail of the tight chain:

1. **The shared oracle-`CheckClaim` completeness** (`ProximityPrize.Compatibility.CheckClaimPassThrough`):
   canonical `CheckClaim` is a pure zero-round pass-through. The legacy predicate argument is
   retained as a relational label in the compatibility laws; it is not executed by the verifier.
   The honest run returns the original statement and oracle family without failure. The shared
   owner preserves the public support and completeness APIs formerly copied into this module.

2. **The Spartan instantiations**:
   * `finalCheckTight_perfectCompleteness_of_enrichedBinding` — the tight terminal check carries
     `(e₂-direct ∧ binding)` into `tightFinalRelOut` (the two relations agree conjunct-by-
     conjunct at the pass-through pair);
   * `secondSumcheckWithTarget_perfectCompleteness_enrichedBinding` — the carried second
     sum-check's enriched completeness (`TightSecondCompleteness.lean`) strengthened by the
     first-terminal binding pass-through, via
     `Reduction.perfectCompleteness_strengthen_support` (`PinnedCompleteness.lean`): the lifted
     verifier is failing-deterministic with verdict `(v? (proj s) tr).map (lift s)`
     (`sumcheckFull_toVerifier_isFailingDet` + `Verifier.liftContext_failingDet`, the
     `TightConjoinedSecondLeaf.lean` `hPres` pattern), and the lift forwards the passenger
     statement and oracles, so `bindingAtSecondIn` rides through to `bindingAtSecondOut` on the
     whole run support.

The output relation of (2) is definitionally the input relation of (1), so together they hand
the completeness fold the last two legs of the honest tight chain.
-/

open OracleComp OracleSpec OracleInterface ProtocolSpec
open scoped NNReal

universe u v




namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

section Leaves

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Completeness leaf for the tight terminal check** (#329, B7): `finalCheckTight` carries the
conjoined `(e₂-direct ∧ binding)` relation — the output of the binding-strengthened carried
second sum-check — into `tightFinalRelOut`.  The implication is conjunct-by-conjunct at the
pass-through pair: `e₂-direct` *is* `tightFinalRelOut`'s first conjunct and the binding is its
second. -/
theorem finalCheckTight_perfectCompleteness_of_enrichedBinding (hInit : NeverFail init) :
    (finalCheckTight (R := R) pp oSpec).perfectCompleteness init impl
      ((secondSumcheckWithTargetRelOutEnriched (R := R) pp)
        ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp})
      (tightFinalRelOut (R := R) pp) :=
  CheckClaim.oracleReduction_perfectCompleteness_passthrough (tightFinalPredicate pp)
    hInit (fun _ hp => ⟨hp.1, hp.2⟩)

end Leaves

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms CheckClaim.oracleProver_run
#print axioms CheckClaim.oracleReduction_perfectCompleteness_passthrough
#print axioms Spartan.Spec.Bricks.finalCheckTight_perfectCompleteness_of_enrichedBinding
#print axioms Spartan.Spec.Bricks.secondSumcheckWithTarget_perfectCompleteness_enrichedBinding
