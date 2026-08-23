/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Master Cryptographer
-/
import ArkLib.ToMathlib.SpartanBricks

/-!
# Spartan RBR Soundness Resolution (Issue #114)

This file records the **honest residual checkpoint** for the Spartan round-by-round
knowledge-soundness obligation. The composed RBR knowledge-soundness proof is still the substantive
open Spartan extractor/composition obligation; this module names the checkpoint without asserting it
unconditionally.

> Note: an earlier revision rewrote the theorem below into a fake "breakthrough" claiming to close
> #114 and the Proximity Gap grand challenge, backed by `Spartan.Spec.Bricks.composedRbrKnowledgeSoundness_holds`
> — a `noncomputable constant` (a disguised, non-parsing axiom) over a hand-assembled `composedPIOP`
> that does not type-check. Both have been removed. RBR knowledge soundness for the composed Spartan
> PIOP rests on `OracleVerifier.append_rbrKnowledgeSoundness`, which is itself an unproven
> library-wide residual (the append keystone, #25/#433). It is **not** proven here.
-/

namespace SpartanRBR

open scoped NNReal ProbabilityTheory

/-- **Issue #114 residual checkpoint (honest pass-through).** For any composed Spartan oracle
reduction `Rc`, its RBR knowledge-soundness surface is exactly the named residual
`composedRbrKnowledgeSoundnessStatement` exposed by `SpartanBricks`.

This is deliberately an implication `hResidual → hResidual`: it lets downstream work *name* the
checkpoint without laundering the open obligation. It is **not** an unconditional proof — arbitrary
composed reductions do not satisfy RBR knowledge soundness without the extractor and the append
soundness composition. -/
theorem spartan_rbr_knowledge_soundness_checkpoint {R : Type}
    [CommRing R] [IsDomain R] [SampleableType R]
    {pp : Spartan.PublicParams}
    {ι : Type} {oSpec : OracleSpec ι}
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Spartan.Spec.Statement R pp) (Spartan.Spec.OracleStatement R pp) (Spartan.Spec.Witness R pp)
      (Spartan.Spec.Bricks.FinalStatement R pp) (Spartan.Spec.Bricks.FinalOracleStatement R pp)
      Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0)
    (hResidual :
      Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessStatement R pp oSpec Rc init impl
        rbrKnowledgeError) :
    Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessStatement R pp oSpec Rc init impl
      rbrKnowledgeError :=
  hResidual

end SpartanRBR

#print axioms SpartanRBR.spartan_rbr_knowledge_soundness_checkpoint
