/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightSeamBridge
import ArkLib.ProofSystem.Spartan.TightFinalLeaf
import ArkLib.ProofSystem.Spartan.TightDeterminismWitnesses
import ArkLib.ProofSystem.Spartan.ComposedRbrKnowledgeSoundness
import ArkLib.ProofSystem.Spartan.ComposedTightRbrKnowledge
import ArkLib.ProofSystem.Spartan.SpartanDirFacts

/-!
# THE FULL TIGHT COMPOSED SPARTAN rbr KNOWLEDGE SOUNDNESS (issue #329, X-lane apex)

The end-to-end eight-phase tight composition: all carried rounds, ending at the **tight final
relation** (`tightFinalRelOut` — both terminal identities, quantifier-free, next-stage
checkable), with the per-round error vector

  `(0, ℓ_m/|R|, 3/|R|, 0, **1/|R|**, 0, 2/|R|, 0)`

— Spartan's Lemma A.1 decomposition, formally, with **no `1`-slots**: the proven-forced
`err₅ = 1` of the target-dropping chain is replaced by the Lemma 5.1 kernel bound.

Structure mirrors `ComposedRbrKnowledgeSoundness.lean`'s seven-seam fold at the carried
reductions (the protocol specs are *identical* — the carried statements change no round
structure — so `composedPSpec`, `composedRbrError` and the `sfx*` suffix specs are reused;
the private direction facts are mirrored here once more).

Main results:
* `composedPIOPTightFull_Rc` — the eight-phase tight composed oracle reduction;
* `composedPIOPTightFull_rbrKnowledgeSoundness_of_leaves` — the relation-generic fold;
* `composedTightFull_rbrKnowledgeSoundness` — **the apex**: unconditional, from
  `spartanRelIn` to `tightFinalRelOut`, at the tight error vector.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

/-- Universe-pinned local alias of the carried RLC-target adapter (mirror of
`prependRLCTargetKS`). -/
private abbrev prependRLCTargetWTKS {ι : Type} (oSpec : OracleSpec ι) :
    OracleReduction.{0, 0} oSpec
      (Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombinationWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] :=
  prependRLCTargetWithTarget pp oSpec

private instance {ι : Type} (oSpec : OracleSpec ι) :
    OracleVerifier.Append.AppendCoherent (prependRLCTargetWTKS (R := R) pp oSpec).verifier :=
  inferInstanceAs (OracleVerifier.Append.AppendCoherent
    (prependRLCTargetWithTargetVerifier (R := R) pp oSpec))

/-- Universe-pinned local alias of the tight terminal check. -/
private abbrev finalCheckTightKS {ι : Type} (oSpec : OracleSpec ι) :
    OracleReduction.{0, 0} oSpec
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] :=
  finalCheckTight pp oSpec

-- Direction facts now live in `SpartanDirFacts.lean` (DRY-audit item 8).

/-! ### The eight-phase tight composed reduction -/

variable {ι : Type} (oSpec : OracleSpec ι)

/-- **The full tight composed Spartan PIOP**: all eight phases at the carried statements,
ending at the doubly-carried terminal check. Protocol spec: `composedPSpec` (unchanged). -/
noncomputable def composedPIOPTightFull_Rc :
    OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (composedPSpec (R := R) pp) :=
  (oracleReduction.firstMessage R pp oSpec).append <|
  (oracleReduction.firstChallenge R pp oSpec).append <|
    (firstSumcheckReductionWithTarget pp oSpec).append <|
    (sendEvalClaimWithTarget pp oSpec).append <|
    (linearCombinationWithTarget pp oSpec).append <|
    (prependRLCTargetWTKS pp oSpec).append <|
    (secondSumcheckReductionWithTarget pp oSpec).append <|
    (finalCheckTightKS pp oSpec)

/-! ### The seven-seam fold at the carried reductions -/

variable (FC : OracleReduction.{0, 0} oSpec
    (Statement.AfterSecondSumcheckWithTarget R pp)
    (OracleStatement.AfterLinearCombination R pp) Unit
    (Statement.AfterSecondSumcheckWithTarget R pp)
    (OracleStatement.AfterLinearCombination R pp) Unit !p[])

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
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

private theorem tightStep8
    [Inhabited (Statement.AfterSecondSumcheckWithTarget R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)]
    {err₇ : (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).ChallengeIdx → ℝ≥0}
    {err₈ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0}
    (verify₇? : ((R × Statement.AfterLinearCombinationWithTarget R pp) ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) →
      (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).FullTranscript →
      Option (Statement.AfterSecondSumcheckWithTarget R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hV₇ : (secondSumcheckReductionWithTarget pp oSpec).verifier.toVerifier
      = ⟨fun p tr => OptionT.mk (pure (verify₇? p tr))⟩)
    (hInit : ∃ s, s ∈ support init)
    (h₇ : (secondSumcheckReductionWithTarget pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relG relH err₇)
    (h₈ : FC.verifier.rbrKnowledgeSoundness init impl relH relI err₈) :
    ((secondSumcheckReductionWithTarget pp oSpec).append
        FC).verifier.rbrKnowledgeSoundness init impl relG relI
      (Sum.elim err₇ err₈ ∘ ChallengeIdx.sumEquiv.symm) :=
  OracleVerifier.append_rbrKnowledgeSoundness_failingDet_empty
    (secondSumcheckReductionWithTarget pp oSpec).verifier FC.verifier
    verify₇? hV₇ hInit ⟨()⟩ h₇ h₈

private theorem tightStep7 [Subsingleton σ] (hn : 0 < pp.ℓ_n)
    {err₆ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0}
    {errRest : (sfx6 (R := R) pp).ChallengeIdx → ℝ≥0}
    (verify₆ : (Statement.AfterLinearCombinationWithTarget R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) →
      (!p[] : ProtocolSpec 0).FullTranscript →
      ((R × Statement.AfterLinearCombinationWithTarget R pp) ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hV₆ : (prependRLCTargetWTKS pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₆ p tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE : Nonempty ((R × Statement.AfterLinearCombinationWithTarget R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (h₆ : (prependRLCTargetWTKS pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relF relG err₆)
    (hRest : ((secondSumcheckReductionWithTarget pp oSpec).append
        FC).verifier.rbrKnowledgeSoundness init impl relG relI errRest) :
    ((prependRLCTargetWTKS pp oSpec).append ((secondSumcheckReductionWithTarget pp oSpec).append
        FC)).verifier.rbrKnowledgeSoundness init impl relF relI
      (Sum.elim err₆ errRest ∘ ChallengeIdx.sumEquiv.symm) := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  exact OracleVerifier.append_rbrKnowledgeSoundness_subsingleton
    (prependRLCTargetWTKS pp oSpec).verifier
    ((secondSumcheckReductionWithTarget pp oSpec).append FC).verifier
    verify₆ hV₆ hInit hInitNF hNE ⟨()⟩ (by omega)
    (sfx5_dir_zero pp hn (by omega)) (sfx6_dir_zero pp hn (by omega)) h₆ hRest

private theorem tightStep6 [Subsingleton σ] (hn : 0 < pp.ℓ_n)
    {err₅ : (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {errRest : (sfx5 (R := R) pp).ChallengeIdx → ℝ≥0}
    (verify₅ : (Statement.AfterSendEvalClaimWithTarget R pp ×
        ∀ i, OracleStatement.AfterSendEvalClaim R pp i) →
      (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).FullTranscript →
      (Statement.AfterLinearCombinationWithTarget R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hV₅ : (linearCombinationWithTarget pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₅ p tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE : Nonempty (Statement.AfterLinearCombinationWithTarget R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (h₅ : (linearCombinationWithTarget pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relE relF err₅)
    (hRest : ((prependRLCTargetWTKS pp oSpec).append
        ((secondSumcheckReductionWithTarget pp oSpec).append
          FC)).verifier.rbrKnowledgeSoundness init impl
      relF relI errRest) :
    ((linearCombinationWithTarget pp oSpec).append
        ((prependRLCTargetWTKS pp oSpec).append
          ((secondSumcheckReductionWithTarget pp oSpec).append
            FC))).verifier.rbrKnowledgeSoundness init impl relE relI
      (Sum.elim err₅ errRest ∘ ChallengeIdx.sumEquiv.symm) := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  exact OracleVerifier.append_rbrKnowledgeSoundness_subsingleton
    (linearCombinationWithTarget pp oSpec).verifier
    ((prependRLCTargetWTKS pp oSpec).append ((secondSumcheckReductionWithTarget pp oSpec).append
      FC)).verifier
    verify₅ hV₅ hInit hInitNF hNE ⟨()⟩ (by omega)
    (sfx4_dir_seam pp hn (by omega)) (sfx5_dir_zero pp hn (by omega)) h₅ hRest

private theorem tightStep5 [Subsingleton σ] (hn : 0 < pp.ℓ_n)
    {err₄ : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {errRest : (sfx4 (R := R) pp).ChallengeIdx → ℝ≥0}
    (verify₄ : (Statement.AfterFirstSumcheckWithTarget R pp ×
        ∀ i, OracleStatement.AfterFirstSumcheck R pp i) →
      (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).FullTranscript →
      (Statement.AfterSendEvalClaimWithTarget R pp ×
        ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hV₄ : (sendEvalClaimWithTarget pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₄ p tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE : Nonempty (Statement.AfterSendEvalClaimWithTarget R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (h₄ : (sendEvalClaimWithTarget pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relD relE err₄)
    (hRest : ((linearCombinationWithTarget pp oSpec).append
        ((prependRLCTargetWTKS pp oSpec).append
          ((secondSumcheckReductionWithTarget pp oSpec).append
            FC))).verifier.rbrKnowledgeSoundness init impl
      relE relI errRest) :
    ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append
          ((prependRLCTargetWTKS pp oSpec).append
            ((secondSumcheckReductionWithTarget pp oSpec).append
              FC)))).verifier.rbrKnowledgeSoundness init impl relD relI
      (Sum.elim err₄ errRest ∘ ChallengeIdx.sumEquiv.symm) := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  exact OracleVerifier.append_rbrKnowledgeSoundness_subsingleton_challenge
    (sendEvalClaimWithTarget pp oSpec).verifier
    ((linearCombinationWithTarget pp oSpec).append
      ((prependRLCTargetWTKS pp oSpec).append ((secondSumcheckReductionWithTarget pp oSpec).append
        FC))).verifier
    verify₄ hV₄ hInit hInitNF hNE ⟨()⟩ (by omega)
    (sfx3_dir_seam pp (by omega)) (sfx4_dir_zero pp (by omega)) h₄ hRest

private theorem tightStep4 [Subsingleton σ]
    [Inhabited (Statement.AfterFirstSumcheckWithTarget R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    {err₃ : (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).ChallengeIdx → ℝ≥0}
    {errRest : (sfx3 (R := R) pp).ChallengeIdx → ℝ≥0}
    (verify₃? : (Statement.AfterFirstChallenge R pp ×
        ∀ i, OracleStatement.AfterFirstChallenge R pp i) →
      (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).FullTranscript →
      Option (Statement.AfterFirstSumcheckWithTarget R pp ×
        ∀ i, OracleStatement.AfterFirstSumcheck R pp i))
    (hV₃ : (firstSumcheckReductionWithTarget pp oSpec).verifier.toVerifier
      = ⟨fun p tr => OptionT.mk (pure (verify₃? p tr))⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (h₃ : (firstSumcheckReductionWithTarget pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relC relD err₃)
    (hRest : ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append
          ((prependRLCTargetWTKS pp oSpec).append
            ((secondSumcheckReductionWithTarget pp oSpec).append
              FC)))).verifier.rbrKnowledgeSoundness init impl
      relD relI errRest) :
    ((firstSumcheckReductionWithTarget pp oSpec).append
        ((sendEvalClaimWithTarget pp oSpec).append
          ((linearCombinationWithTarget pp oSpec).append
            ((prependRLCTargetWTKS pp oSpec).append
              ((secondSumcheckReductionWithTarget pp oSpec).append
                FC))))).verifier.rbrKnowledgeSoundness init impl
      relC relI (Sum.elim err₃ errRest ∘ ChallengeIdx.sumEquiv.symm) := by
  exact OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton
    (firstSumcheckReductionWithTarget pp oSpec).verifier
    ((sendEvalClaimWithTarget pp oSpec).append
      ((linearCombinationWithTarget pp oSpec).append
        ((prependRLCTargetWTKS pp oSpec).append
          ((secondSumcheckReductionWithTarget pp oSpec).append
            FC)))).verifier
    verify₃? hV₃ hInit hInitNF ⟨()⟩ (by omega)
    (sfx2_dir_seam pp (by omega)) (sfx3_dir_zero pp (by omega)) h₃ hRest

private theorem tightStep3 [Subsingleton σ] (hm : 0 < pp.ℓ_m)
    {err₂ : (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {errRest : (sfx2 (R := R) pp).ChallengeIdx → ℝ≥0}
    (verify₂ : (Statement.AfterFirstMessage R pp ×
        ∀ i, OracleStatement.AfterFirstMessage R pp i) →
      (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).FullTranscript →
      (Statement.AfterFirstChallenge R pp × ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hV₂ : (oracleReduction.firstChallenge R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₂ p tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relB relC err₂)
    (hRest : ((firstSumcheckReductionWithTarget pp oSpec).append
        ((sendEvalClaimWithTarget pp oSpec).append
          ((linearCombinationWithTarget pp oSpec).append
            ((prependRLCTargetWTKS pp oSpec).append
              ((secondSumcheckReductionWithTarget pp oSpec).append
                FC))))).verifier.rbrKnowledgeSoundness init impl
      relC relI errRest) :
    ((oracleReduction.firstChallenge R pp oSpec).append
        ((firstSumcheckReductionWithTarget pp oSpec).append
          ((sendEvalClaimWithTarget pp oSpec).append
            ((linearCombinationWithTarget pp oSpec).append
              ((prependRLCTargetWTKS pp oSpec).append
                ((secondSumcheckReductionWithTarget pp oSpec).append
                  FC)))))).verifier.rbrKnowledgeSoundness init impl
      relB relI (Sum.elim err₂ errRest ∘ ChallengeIdx.sumEquiv.symm) := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2) := vsum_two_pos hm
  exact OracleVerifier.append_rbrKnowledgeSoundness_subsingleton
    (oracleReduction.firstChallenge R pp oSpec).verifier
    ((firstSumcheckReductionWithTarget pp oSpec).append
      ((sendEvalClaimWithTarget pp oSpec).append
        ((linearCombinationWithTarget pp oSpec).append
          ((prependRLCTargetWTKS pp oSpec).append
            ((secondSumcheckReductionWithTarget pp oSpec).append
              FC))))).verifier
    verify₂ hV₂ hInit hInitNF hNE ⟨()⟩ (by omega)
    (sfx1_dir_seam pp hm (by omega)) (sfx2_dir_zero pp hm (by omega)) h₂ hRest

set_option maxHeartbeats 1000000 in
/-- **The relation-generic eight-phase tight fold.** -/
theorem composedPIOPTightFull_rbrKnowledgeSoundness_of_leaves [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (Statement.AfterSecondSumcheckWithTarget R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)]
    [Inhabited (Statement.AfterFirstSumcheckWithTarget R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    {err₁ : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₂ : (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₃ : (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).ChallengeIdx → ℝ≥0}
    {err₄ : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₅ : (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₆ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0}
    {err₇ : (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).ChallengeIdx → ℝ≥0}
    {err₈ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0}
    (verify₁ : (Statement R pp × ∀ i, OracleStatement R pp i) →
      (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).FullTranscript →
      (Statement.AfterFirstMessage R pp × ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hV₁ : (oracleReduction.firstMessage R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₁ p tr)⟩)
    (verify₂ : (Statement.AfterFirstMessage R pp ×
        ∀ i, OracleStatement.AfterFirstMessage R pp i) →
      (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).FullTranscript →
      (Statement.AfterFirstChallenge R pp × ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hV₂ : (oracleReduction.firstChallenge R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₂ p tr)⟩)
    (verify₃? : (Statement.AfterFirstChallenge R pp ×
        ∀ i, OracleStatement.AfterFirstChallenge R pp i) →
      (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).FullTranscript →
      Option (Statement.AfterFirstSumcheckWithTarget R pp ×
        ∀ i, OracleStatement.AfterFirstSumcheck R pp i))
    (hV₃ : (firstSumcheckReductionWithTarget pp oSpec).verifier.toVerifier
      = ⟨fun p tr => OptionT.mk (pure (verify₃? p tr))⟩)
    (verify₄ : (Statement.AfterFirstSumcheckWithTarget R pp ×
        ∀ i, OracleStatement.AfterFirstSumcheck R pp i) →
      (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).FullTranscript →
      (Statement.AfterSendEvalClaimWithTarget R pp ×
        ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hV₄ : (sendEvalClaimWithTarget pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₄ p tr)⟩)
    (verify₅ : (Statement.AfterSendEvalClaimWithTarget R pp ×
        ∀ i, OracleStatement.AfterSendEvalClaim R pp i) →
      (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).FullTranscript →
      (Statement.AfterLinearCombinationWithTarget R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hV₅ : (linearCombinationWithTarget pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₅ p tr)⟩)
    (verify₆ : (Statement.AfterLinearCombinationWithTarget R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) →
      (!p[] : ProtocolSpec 0).FullTranscript →
      ((R × Statement.AfterLinearCombinationWithTarget R pp) ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hV₆ : (prependRLCTargetWTKS pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₆ p tr)⟩)
    (verify₇? : ((R × Statement.AfterLinearCombinationWithTarget R pp) ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) →
      (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).FullTranscript →
      Option (Statement.AfterSecondSumcheckWithTarget R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hV₇ : (secondSumcheckReductionWithTarget pp oSpec).verifier.toVerifier
      = ⟨fun p tr => OptionT.mk (pure (verify₇? p tr))⟩)
    (h₁ : (oracleReduction.firstMessage R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relA relB err₁)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relB relC err₂)
    (h₃ : (firstSumcheckReductionWithTarget pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relC relD err₃)
    (h₄ : (sendEvalClaimWithTarget pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relD relE err₄)
    (h₅ : (linearCombinationWithTarget pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relE relF err₅)
    (h₆ : (prependRLCTargetWTKS pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relF relG err₆)
    (h₇ : (secondSumcheckReductionWithTarget pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relG relH err₇)
    (h₈ : FC.verifier.rbrKnowledgeSoundness init impl relH relI err₈)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaimWithTarget R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hNE_F : Nonempty (Statement.AfterLinearCombinationWithTarget R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hNE_G : Nonempty ((R × Statement.AfterLinearCombinationWithTarget R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)) :
    ((oracleReduction.firstMessage R pp oSpec).append
      ((oracleReduction.firstChallenge R pp oSpec).append
        ((firstSumcheckReductionWithTarget pp oSpec).append
          ((sendEvalClaimWithTarget pp oSpec).append
            ((linearCombinationWithTarget pp oSpec).append
              ((prependRLCTargetWTKS pp oSpec).append
                ((secondSumcheckReductionWithTarget pp oSpec).append
                  FC))))))).verifier.rbrKnowledgeSoundness init impl
      relA relI (composedRbrError pp err₁ err₂ err₃ err₄ err₅ err₆ err₇ err₈) := by
  have hS8 := tightStep8 pp oSpec FC verify₇? hV₇ hInit h₇ h₈
  have hS7 := tightStep7 pp oSpec FC hn verify₆ hV₆ hInit hInitNF hNE_G h₆ hS8
  have hS6 := tightStep6 pp oSpec FC hn verify₅ hV₅ hInit hInitNF hNE_F h₅ hS7
  have hS5 := tightStep5 pp oSpec FC hn verify₄ hV₄ hInit hInitNF hNE_E h₄ hS6
  have hS4 := tightStep4 pp oSpec FC verify₃? hV₃ hInit hInitNF h₃ hS5
  have hS3 := tightStep3 pp oSpec FC hm verify₂ hV₂ hInit hInitNF hNE_C h₂ hS4
  exact OracleVerifier.append_rbrKnowledgeSoundness_subsingleton_challenge
    (oracleReduction.firstMessage R pp oSpec).verifier
    ((oracleReduction.firstChallenge R pp oSpec).append
      ((firstSumcheckReductionWithTarget pp oSpec).append
        ((sendEvalClaimWithTarget pp oSpec).append
          ((linearCombinationWithTarget pp oSpec).append
            ((prependRLCTargetWTKS pp oSpec).append
              ((secondSumcheckReductionWithTarget pp oSpec).append
                FC)))))).verifier
    verify₁ hV₁ hInit hInitNF hNE_B ⟨()⟩ (by omega)
    (composedPSpec_dir_seam pp (by omega)) (sfx1_dir_zero pp (by omega)) h₁ hS3

/-! ### THE APEX -/

set_option linter.unusedFintypeInType false in
/-- **THE TIGHT COMPOSED SPARTAN rbr KNOWLEDGE SOUNDNESS (issue #329).** The full eight-phase
tight composition is round-by-round knowledge sound from `spartanRelIn` to `tightFinalRelOut`
(both terminal identities, quantifier-free) at the per-round error vector

  `(0, ℓ_m/|R|, 3/|R|, 0, 1/|R|, 0, 2/|R|, 0)`

— Spartan's Lemma A.1 decomposition with the Lemma 5.1 kernel bound at the RLC round, replacing
the proven-forced `err₅ = 1` of the target-dropping chain. Unconditional (no leaf hypotheses);
axiom-clean. -/
theorem composedTightFull_rbrKnowledgeSoundness [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (Statement.AfterSecondSumcheckWithTarget R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)]
    [Inhabited (Statement.AfterFirstSumcheckWithTarget R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaimWithTarget R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hNE_F : Nonempty (Statement.AfterLinearCombinationWithTarget R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hNE_G : Nonempty ((R × Statement.AfterLinearCombinationWithTarget R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)) :
    (composedPIOPTightFull_Rc (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (spartanRelIn R pp) (tightFinalRelOut (R := R) pp)
      (composedRbrError pp
        (0 : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
        (fun _ => (pp.ℓ_m : ℝ≥0) / (Fintype.card R : ℝ≥0))
        (fun _ => (3 : ℝ≥0) / (Fintype.card R))
        (0 : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
        (fun _ => (1 : ℝ≥0) / (Fintype.card R : ℝ≥0))
        (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)
        (fun _ => (2 : ℝ≥0) / (Fintype.card R))
        (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)) := by
  obtain ⟨verify₁, hV₁⟩ := firstMessage_toVerifier_pure (R := R) pp oSpec
  obtain ⟨verify₃?, hV₃⟩ := firstSumcheckWithTarget_toVerifier_isFailingDet (R := R) pp oSpec
  obtain ⟨verify₇?, hV₇⟩ := secondSumcheckWithTarget_toVerifier_isFailingDet (R := R) pp oSpec
  have h₂ : (oracleReduction.firstChallenge.{0} R pp oSpec).verifier.rbrKnowledgeSoundness
      init impl
      (firstMessageRbrRelB (R := R) pp)
      (firstSumcheckWithTargetRbrRelIn (R := R) pp oSpec)
      (fun _ => (pp.ℓ_m : ℝ≥0) / (Fintype.card R : ℝ≥0)) := by
    rw [firstSumcheckWithTargetRbrRelIn_eq_relIn]
    exact firstChallenge_rbrKnowledgeSoundness_schwartzZippel pp oSpec hm
  exact composedPIOPTightFull_rbrKnowledgeSoundness_of_leaves.{0, 0, 0, 0} pp oSpec
    (finalCheckTightKS pp oSpec) hm hn
    verify₁ hV₁
    (fun p tr => ((fun p (c : FirstChallenge R pp) => ((c, p.1), p.2)) p
      (tr.challenges ⟨0, rfl⟩)))
    (firstChallenge_toVerifier_closed pp oSpec)
    verify₃? hV₃
    (fun p tr => sendEvalClaimWithTargetRouteMap (R := R) pp p (tr.messages ⟨0, rfl⟩))
    (sendEvalClaimWithTarget_toVerifier_closed pp oSpec)
    (fun p tr => ((fun p (c : LinearCombinationChallenge R) => ((c, p.1), p.2)) p
      (tr.challenges ⟨0, rfl⟩)))
    (linearCombinationWithTarget_toVerifier_closed pp oSpec)
    (fun p _tr => ((∑ idx, p.1.1 idx * p.2 (.inl 0) idx, p.1), p.2))
    (prependRLCTargetWithTarget_toVerifier_pure pp oSpec)
    verify₇? hV₇
    (firstMessage_rbrKnowledgeSoundness_spartanRelIn pp oSpec)
    h₂
    (firstSumcheckWithTarget_rbrKnowledgeSoundness_honest_full pp oSpec hInit hInitNF)
    (sendEvalClaimWithTarget_rbrKnowledgeSoundness_leaf pp oSpec)
    (linearCombinationWithTarget_rbrKnowledgeSoundness_leaf.{0} pp oSpec)
    (prependRLCTargetWithTarget_rbrKnowledgeSoundness_leaf' pp oSpec)
    (secondSumcheckWithTarget_conjoined_rbrKnowledgeSoundness pp oSpec hInit hInitNF)
    (finalCheckTight_rbrKnowledgeSoundness pp oSpec)
    hInit hInitNF hNE_B hNE_C hNE_E hNE_F hNE_G

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.composedPIOPTightFull_Rc
#print axioms Spartan.Spec.Bricks.composedPIOPTightFull_rbrKnowledgeSoundness_of_leaves
#print axioms Spartan.Spec.Bricks.composedTightFull_rbrKnowledgeSoundness
