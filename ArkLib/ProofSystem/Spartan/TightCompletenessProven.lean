/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightComposedCompleteness
import ArkLib.ProofSystem.Spartan.TightFirstCompleteness
import ArkLib.ProofSystem.Spartan.TightMidCompleteness
import ArkLib.ProofSystem.Spartan.TightSecondBinding
import ArkLib.ProofSystem.Spartan.ComposedCompletenessFinal

/-!
# THE TIGHT COMPOSED SPARTAN PERFECT COMPLETENESS, FULLY DISCHARGED (issue #329, B7 apex)

`composedTightPure_perfectCompleteness`: the paired tight chain `composedPIOPTightPure_Rc` is
perfectly complete from `spartanRelIn` to **`tightFinalRelOut`** — the same chain and the same
endpoint as the tight rbr knowledge soundness (`composedTightPure_rbrKnowledgeSoundness`,
`TightApexPure.lean`). Together they complete issue #329: the composed Spartan PIOP carries
quantitatively tight per-round knowledge errors `(0, ℓ_m/|R|, 3/|R|, 0, 1/|R|, 0, 2/|R|, 0)`
**and** perfect completeness, at a quantifier-free, acceptance-implied terminal relation.

All eight legs are in-tree machine-checked theorems threaded along the honest tight chain:
`spartanRelIn` → (`SendSingleWitness`) → (`firstChallenge`, re-pointed) →
`firstSumcheckWithTargetRelIn` → (enriched carried first sum-check: `+ e₁ = eval r_x F̂`) →
(`sendEvalClaimWithTarget`: `+ binding`) → (`linearCombinationWithTarget`) →
(`prependRLCTargetWithTarget`: `tightRelG = pullback₂ ∩ binding`) →
(carried second sum-check, binding-strengthened: `e₂-direct ∩ binding`) →
(`finalCheckPure`) → `tightFinalRelOut`.
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

/-- **Seam 2→3 (tight):** the `firstChallenge` output relation coincides with the carried
first-sum-check input relation (definitionally equal `setOf` bodies — the carried lens's
projection is unchanged). -/
theorem firstChallengeRelOut_subset_firstSumcheckWithTargetRelIn :
    firstChallengeRelOut (R := R) pp ⊆ firstSumcheckWithTargetRelIn (R := R) pp :=
  fun _ hx => hx

/-- **The `firstChallenge` leaf at the tight consumer endpoints**: perfect completeness from
`firstMessageRelOut` into `firstSumcheckWithTargetRelIn`. -/
theorem firstChallenge_perfectCompleteness_tightConsumer :
    (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl
      (firstMessageRelOut (R := R) pp) (firstSumcheckWithTargetRelIn (R := R) pp) := by
  have h := firstChallenge_perfectCompleteness (R := R) (pp := pp) (oSpec := oSpec)
    (init := init) (impl := impl)
  unfold OracleReduction.perfectCompleteness Reduction.perfectCompleteness at h ⊢
  have h' := Reduction.completeness_relOut_mono init impl
    (firstChallengeRelOut_subset_firstSumcheckWithTargetRelIn pp) h
  exact Reduction.completeness_relIn_mono init impl
    (firstMessageRelOut_subset_firstChallengeRelIn pp) h'

set_option linter.unusedFintypeInType false in
/-- **THE TIGHT COMPOSED SPARTAN PERFECT COMPLETENESS (issue #329).** The paired tight chain is
perfectly complete from `spartanRelIn` to `tightFinalRelOut`, with no leaf hypotheses — only
the standard honest-implementation side conditions. -/
theorem composedTightPure_perfectCompleteness
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    (composedPIOPTightPure_Rc (R := R) pp oSpec).perfectCompleteness init impl
      (spartanRelIn R pp) (tightFinalRelOut (R := R) pp) :=
  composedPIOPTightPure_perfectCompleteness_of_leaves.{0, 0, 0} pp oSpec hm hn
    (SendSingleWitness.oracleReduction_completeness (oSpec := oSpec)
      (Statement := Statement R pp) (OStatement := OracleStatement R pp)
      (Witness := Witness R pp) (init := init) (impl := impl)
      (oRelIn := spartanRelIn R pp) hInit)
    (firstChallenge_perfectCompleteness_tightConsumer pp oSpec)
    (firstSumcheckWithTarget_perfectCompleteness_enriched pp oSpec hInit hImplSupp)
    (sendEvalClaimWithTarget_perfectCompleteness_tight pp oSpec)
    (linearCombinationWithTarget_perfectCompleteness_tight pp oSpec)
    (prependRLCTargetWithTarget_perfectCompleteness_tight pp oSpec)
    (secondSumcheckWithTarget_perfectCompleteness_enrichedBinding pp oSpec hInit hImplSupp)
    (finalCheckPure_perfectCompleteness pp oSpec)
    hInit hImplSupp himplSP himplNF

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.firstChallenge_perfectCompleteness_tightConsumer
#print axioms Spartan.Spec.Bricks.composedTightPure_perfectCompleteness
