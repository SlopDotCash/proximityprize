/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.SpartanBricks

/-!
# Spartan RBR Knowledge Soundness with Claim — parameterized end-to-end statement

This module lifts the target-carrying composed RBR knowledge-soundness statement into a single
end-to-end statement for the Spartan PIOP, parameterized on the assembled composed reduction `Rc`
and its end-to-end RBR knowledge-soundness fact `hks`.

Like `SpartanRBRProof.lean`, the unconditional proof is explicitly deferred until the
library-wide challenge-seam append keystone (#25/#433) provides the required RBR composition
over the 8 Spartan phases.
-/

open ProtocolSpec OracleComp OracleSpec Polynomial

namespace Spartan.Spec

open scoped NNReal

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- **Spartan RBR knowledge soundness with claim (end-to-end, parameterized).** Given the assembled
composed target-carrying Spartan oracle reduction `Rc` (over its combined spec `pSpecC`) together
with its end-to-end round-by-round knowledge-soundness fact `hks` from the Spartan input relation
to the terminal target-carrying final-check relation, the named composed RBR-knowledge-soundness
statement holds. A thin delegation to the verified
`Bricks.composedRbrKnowledgeSoundnessWithClaimStatement_of_rbrKnowledgeSoundness`. -/
theorem spartan_rbr_knowledge_soundness_with_claim
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (Bricks.FinalClaimStatement R pp) (Bricks.FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0)
    (hks : Rc.verifier.rbrKnowledgeSoundness init impl
      (Bricks.spartanRelIn R pp) (Bricks.finalCheckWithClaimRelOut R pp) rbrKnowledgeError) :
    Bricks.composedRbrKnowledgeSoundnessWithClaimStatement R pp oSpec Rc init impl
      rbrKnowledgeError :=
  Bricks.composedRbrKnowledgeSoundnessWithClaimStatement_of_rbrKnowledgeSoundness
    R pp oSpec Rc init impl rbrKnowledgeError hks

end Spartan.Spec

#print axioms Spartan.Spec.spartan_rbr_knowledge_soundness_with_claim
