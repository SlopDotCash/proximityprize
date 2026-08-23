/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.SpartanBricks

/-!
# Spartan RBR Knowledge Soundness — parameterized end-to-end statement

This module lifts the composed RBR knowledge-soundness statement into a single end-to-end
statement for the Spartan PIOP (#114), **parameterized on the assembled composed reduction `Rc`**.

> Honesty note.  An earlier revision of this file asserted a
> `spartan_rbr_knowledge_soundness_breakthrough` against a hand-written seven-fold
> `OracleReduction.append` term claimed to *be* the composed Spartan reduction.  That term does
> **not** type-check: iterating `OracleReduction.append` over the seven Spartan phases is gated on
> the per-phase `OracleVerifier.Append.AppendCoherent` instances and the challenge-seam append
> keystone (#25/#433), none of which is available as a leaf instance yet (see the obstruction
> documented in `SpartanBricks.composedPIOPResidual`).  The non-compiling assertion has been
> replaced by the honest *parameterized* statement below: given any assembled composed reduction
> `Rc` together with its end-to-end RBR knowledge-soundness fact `hks`, the named composed statement
> holds.  The only remaining open obligation is the assembly of `Rc` and the supply of `hks` — the
> library-wide append keystones, not Spartan-specific.
-/

open ProtocolSpec OracleComp OracleSpec Polynomial

namespace Spartan.Spec

open scoped NNReal

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- **Spartan RBR knowledge soundness (end-to-end, parameterized).**  Given the assembled composed
Spartan oracle reduction `Rc` (over its combined spec `pSpecC`) together with its end-to-end
round-by-round knowledge-soundness fact `hks` from the Spartan input relation to the terminal
final-check relation, the named composed RBR-knowledge-soundness statement holds.  A thin
delegation to the verified
`Bricks.composedRbrKnowledgeSoundnessStatement_of_rbrKnowledgeSoundness`. -/
theorem spartan_rbr_knowledge_soundness
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (Bricks.FinalStatement R pp) (Bricks.FinalOracleStatement R pp) Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0)
    (hks : Rc.verifier.rbrKnowledgeSoundness init impl
      (Bricks.spartanRelIn R pp) (Bricks.finalCheckRelOut R pp) rbrKnowledgeError) :
    Bricks.composedRbrKnowledgeSoundnessStatement R pp oSpec Rc init impl rbrKnowledgeError :=
  Bricks.composedRbrKnowledgeSoundnessStatement_of_rbrKnowledgeSoundness
    R pp oSpec Rc init impl rbrKnowledgeError hks

end Spartan.Spec

#print axioms Spartan.Spec.spartan_rbr_knowledge_soundness
