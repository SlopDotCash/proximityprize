/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ProximityPrize.Compatibility.SpartanFirstChallenge
import ArkLib.ProofSystem.Spartan.ComposedCompletenessFinal
import ArkLib.ProofSystem.Spartan.TightComposedCompleteness
import ArkLib.ProofSystem.Spartan.TightComposedFull
import ArkLib.ProofSystem.Spartan.TightMidCompleteness
import ArkLib.ProofSystem.Spartan.TightSecondCompleteness
import ArkLib.ProofSystem.Spartan.TightSecondBinding
import ArkLib.ProofSystem.Spartan.FinalCheckTightComplete

/-!
# Perfect completeness of the full tight composed Spartan chain (issue #329, B7 step 5)

The completeness mirror of `composedTightFull_rbrKnowledgeSoundness`
(`TightComposedFull.lean`): the eight-phase tight composition `composedPIOPTightFull_Rc` is
**perfectly complete** from the honest Spartan input relation `spartanRelIn` to the tight final
relation `tightFinalRelOut` (both terminal identities, quantifier-free). Together with the KS
apex has explicit canonical sum-check round-knowledge hypotheses; this module proves the
completeness direction under the original honest execution assumptions.

## The honest tight relation chain (the B7 spec)

* `relA = spartanRelIn` — R1CS satisfiability with the witness in the witness slot;
* `relB = firstMessageRelOut` — R1CS satisfiability with the witness moved into the appended
  oracle slot (`SendSingleWitness` pushforward);
* `relC = firstSumcheckWithTargetRelIn` — R1CS satisfiability after the τ-challenge
  (definitionally `firstSumcheckRelInBF`; the carried chain shares the input relation);
* `relD = firstSumcheckWithTargetRelOutEnriched` — R1CS pass-through **∧ the direct first
  terminal identity `e₁ = eval r_x F̂`** (`TightFirstCompleteness.lean`);
* `relE = tightSendEvalClaimRelOut` — `relD` read back through the claim-oracle split, **∧ the
  pointwise scalar-claim honesty ∧ the first-terminal binding identity**
  (`TightMidCompleteness.lean`);
* `relF = tightLinearCombinationRelOut` — the challenge-stripped pushforward of `relE` (the RLC
  round records the sampled challenge, honest data unchanged);
* `relG = tightRelG = secondSumcheckWithTargetRbrRelIn ∩ bindingAtSecondIn` — the prepended
  target is the *true* RLC `T = ∑ r·v^true` ∧ binding (the honest adapter emits `∑ r·v^sent`,
  and the carried honesty conjunct turns sent into true; seam set-equality
  `tightRelG_eq_conjoined_relIn`, `TightSeamBridge.lean`);
* `relH = secondSumcheckWithTargetRelOutEnriched ∩ bindingAtSecondOut` — **the direct second
  terminal identity `e₂ = eval r_y ℳ`** ∧ the binding, transported through the carried second
  sum-check (`TightSecondCompleteness.lean` + the binding pass-through strengthening proved
  here via `Reduction.perfectCompleteness_strengthen_support`);
* `relI = tightFinalRelOut` — conjunct-for-conjunct the same as `relH` (the zero-round tight
  terminal check forwards the pair unchanged, `FinalCheckTightComplete.lean`).

## Structure

Mirrors the seven-seam fold of `composedPIOP_Rc_perfectCompleteness_of_leaves`
(`ComposedCompleteness.lean`) at the carried reductions: the protocol specs are *identical*
(carried statements change no round structure), so the same append-completeness keystones apply. The relation-generic fold delegates
`TightComposedCompleteness`: the terminal constructors are definitionally the same canonical
pass-through, so the seven seam proofs have one owner.

Main results:
* `secondSumcheckWithTarget_perfectCompleteness_enrichedBinding` — the `h₇` leaf: the enriched
  carried-second completeness conjoined with the binding pass-through;
* `composedPIOPTightFull_perfectCompleteness_of_leaves` — the relation-generic fold;
* `composedTightFull_perfectCompleteness` — **the apex**: unconditional perfect completeness
  from `spartanRelIn` to `tightFinalRelOut`, with only the standard honest-implementation side
  conditions.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option synthInstance.maxSize 512
set_option linter.unusedSectionVars false

open Sumcheck.Spec.SingleRound (appendChalFintype appendChalInhab chalBaseFintypeP
  chalBaseFintypeV chalBaseFintypeE chalBaseInhabP chalBaseInhabV chalBaseInhabE)

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] [VCVCompatible R] (pp : PublicParams)

/-- Universe-pinned local alias of the carried RLC-target adapter (mirror of the KS-side
`prependRLCTargetWTKS`). -/
private abbrev prependRLCTargetWTC {ι : Type} (oSpec : OracleSpec ι) :
    OracleReduction oSpec
      (Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] :=
  prependRLCTargetWithTarget pp oSpec

/-- Universe-pinned local alias of the tight terminal check. -/
private abbrev finalCheckTightC {ι : Type} (oSpec : OracleSpec ι) :
    OracleReduction oSpec
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] :=
  finalCheckTight pp oSpec

/-! ### The seam-adapted completeness leaves -/

section Leaves

variable {ι : Type} (oSpec : OracleSpec ι)
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Leaf `h₂` at the tight chain's endpoints**: the `firstChallenge` phase is perfectly
complete from `firstMessageRelOut` into `firstSumcheckWithTargetRelIn`. The carried chain shares
the input relation of the first sum-check with the target-dropping one (identical `setOf`
bodies, `firstSumcheckRelInBF = firstSumcheckWithTargetRelIn`), so this is the proven
`firstChallenge_perfectCompleteness_consumer` re-pointed across the definitional seam. -/
theorem completedFirstChallenge_perfectCompleteness_consumerTight [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)] :
    (oracleReduction.completedFirstChallenge R pp oSpec).perfectCompleteness init impl
      (firstMessageRelOut (R := R) pp) (firstSumcheckWithTargetRelIn (R := R) pp) := by
  have h := completedFirstChallenge_perfectCompleteness_consumer (R := R) pp oSpec
    (init := init) (impl := impl)
  unfold OracleReduction.perfectCompleteness Reduction.perfectCompleteness at h ⊢
  exact Reduction.completeness_relOut_mono init impl
    (fun x hx => hx :
      firstSumcheckRelInBF (R := R) pp ⊆ firstSumcheckWithTargetRelIn (R := R) pp) h

/-- **Leaf `h₈` at the tight chain's endpoints**: the tight terminal check carries the conjoined
`(e₂-direct ∧ binding)` relation into `tightFinalRelOut`. Instance of the pred-generic
pass-through completeness (`finalCheckTight_perfectCompleteness_any`) with the output relation
relaxed conjunct-for-conjunct. -/
theorem finalCheckTight_perfectCompleteness_tightOut :
    (finalCheckTightC pp oSpec).perfectCompleteness init impl
      ((secondSumcheckWithTargetRelOutEnriched (R := R) pp)
        ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp})
      (tightFinalRelOut (R := R) pp) := by
  have h := finalCheckTight_perfectCompleteness_any (R := R) pp oSpec
    (init := init) (impl := impl)
    ((secondSumcheckWithTargetRelOutEnriched (R := R) pp)
      ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp})
  unfold OracleReduction.perfectCompleteness at h ⊢
  exact Reduction.completeness_relOut_mono init impl
    (fun x hx => ⟨hx.1, hx.2⟩) h

end Leaves

/-! ### The seven-seam completeness fold at the carried reductions -/

variable {ι : Type} (oSpec : OracleSpec ι) [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relA : Set ((Statement R pp × ∀ i, OracleStatement R pp i) × Witness R pp)}
  {relB : Set ((Statement.AfterFirstMessage R pp ×
    ∀ i, OracleStatement.AfterFirstMessage R pp i) × Unit)}
  {relC : Set ((Statement.AfterFirstChallenge R pp ×
    ∀ i, OracleStatement.AfterFirstChallenge R pp i) × Unit)}
  {relD : Set ((Statement.AfterFirstSumcheckWithTarget R pp ×
    ∀ i, OracleStatement.AfterFirstSumcheck R pp i) × Unit)}
  {relE : Set ((Statement.AfterSendEvalClaimWithTarget R pp ×
    ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit)}
  {relF : Set ((Statement.AfterLinearCombinationWithTarget R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relG : Set (((R × Statement.AfterLinearCombinationWithTarget R pp) ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relH : Set ((Statement.AfterSecondSumcheckWithTarget R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relI : Set ((Statement.AfterSecondSumcheckWithTarget R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}

/-- **The relation-generic eight-phase tight completeness fold** (issue #329, B7 step 5).
Seam 1 (`firstMessage ▷ …`) is a **challenge** seam, closed by the challenge-seam keystone;
the other six seams are handled inside the `tightCStep*` lemmas (message / challenge / empty
keystones as dictated by each right block's opening direction — identical seam directions to
the target-dropping chain, since the protocol specs coincide). -/
theorem composedPIOPTightFull_perfectCompleteness_of_leaves
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (h₁ : (oracleReduction.firstMessage R pp oSpec).perfectCompleteness init impl relA relB)
    (h₂ : (oracleReduction.completedFirstChallenge R pp oSpec).perfectCompleteness init impl relB relC)
    (h₃ : (firstSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relC relD)
    (h₄ : (sendEvalClaimWithTarget pp oSpec).perfectCompleteness init impl relD relE)
    (h₅ : (linearCombinationWithTarget pp oSpec).perfectCompleteness init impl relE relF)
    (h₆ : (prependRLCTargetWTC pp oSpec).perfectCompleteness init impl relF relG)
    (h₇ : (secondSumcheckReductionWithTarget pp oSpec).perfectCompleteness init impl relG relH)
    (h₈ : (finalCheckTightC pp oSpec).perfectCompleteness init impl relH relI)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0) :
    (composedPIOPTightFull_Rc (R := R) pp oSpec).perfectCompleteness init impl relA relI := by
  exact composedPIOPTightPure_perfectCompleteness_of_leaves pp oSpec hm hn
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hInit hImplSupp himplSP himplNF

/-! ### THE APEX -/

/-- **THE TIGHT COMPOSED SPARTAN PERFECT COMPLETENESS (issue #329, B7 step 5).** The full
eight-phase tight composition `composedPIOPTightFull_Rc` is perfectly complete from the honest
Spartan input relation `spartanRelIn` to the tight final relation `tightFinalRelOut` (both
terminal identities, quantifier-free). Together with the KS apex
`composedTightFull_rbrKnowledgeSoundness` (`TightComposedFull.lean`), this closes #329's
completeness direction. The companion knowledge theorem retains its canonical round-knowledge
hypotheses. Only the standard honest-implementation side
conditions remain as inputs (exactly those of `composedCompletenessStatement_proven`). -/
theorem composedTightFull_perfectCompleteness
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0) :
    (composedPIOPTightFull_Rc (R := R) pp oSpec).perfectCompleteness init impl
      (spartanRelIn R pp) (tightFinalRelOut (R := R) pp) :=
  composedPIOPTightFull_perfectCompleteness_of_leaves pp oSpec hm hn
    (SendSingleWitness.oracleReduction_completeness (oSpec := oSpec)
      (Statement := Statement R pp) (OStatement := OracleStatement R pp)
      (Witness := Witness R pp) (init := init) (impl := impl)
      (oRelIn := spartanRelIn R pp))
    (completedFirstChallenge_perfectCompleteness_consumerTight pp oSpec)
    (firstSumcheckWithTarget_perfectCompleteness_enriched pp oSpec hInit hImplSupp)
    (sendEvalClaimWithTarget_perfectCompleteness_tight pp oSpec)
    (linearCombinationWithTarget_perfectCompleteness_tight pp oSpec)
    (prependRLCTargetWithTarget_perfectCompleteness_tight pp oSpec)
    (secondSumcheckWithTarget_perfectCompleteness_enrichedBinding pp oSpec hInit hImplSupp)
    (finalCheckTight_perfectCompleteness_tightOut pp oSpec)
    hInit hImplSupp himplSP himplNF

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.completedFirstChallenge_perfectCompleteness_consumerTight
#print axioms Spartan.Spec.Bricks.secondSumcheckWithTarget_perfectCompleteness_enrichedBinding
#print axioms Spartan.Spec.Bricks.finalCheckTight_perfectCompleteness_tightOut
#print axioms Spartan.Spec.Bricks.composedPIOPTightFull_perfectCompleteness_of_leaves
#print axioms Spartan.Spec.Bricks.composedTightFull_perfectCompleteness
