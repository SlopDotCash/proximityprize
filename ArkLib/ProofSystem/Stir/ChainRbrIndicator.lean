/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.ChainProof
import ArkLib.ProofSystem.Stir.BlockCompleteness
import ArkLib.ProofSystem.Whir.ThresholdKSF

/-!
# Indicator RBR knowledge soundness of the STIR chain proof (#301)

**Indicator RBR knowledge soundness of the packaged STIR chain proof** —
the WHIR-discharge pattern applied to `stirChainProof`'s verifier via the universal threshold
knowledge-state-function: the δ-closeness predicate on the chain's input oracle is constant
across rounds, so the only possible flip is at the designated final challenge, giving the
indicator budget (1 at `C_fin`, 0 everywhere else). Combined with the proven chain
completeness, this is the STIR mirror of WHIR's `isSecureWithGap_indicator` milestone. -/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The final (repetition) challenge of the full chain spec: the final block's challenge slot,
embedded through the three appends. -/
def stirChainFinalChallengeIdx (M : ℕ) :
    (((stirInitVSpec.toProtocolSpec F) ++ₚ
      (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
        ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
          ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F))))).ChallengeIdx :=
  ChallengeIdx.inr (ChallengeIdx.inr (ChallengeIdx.inr
    ⟨1, stirFinalVSpec_dir_one⟩))

/-- **The input-proximity relation in the `Verifier`-level tuple form** consumed by
`rbrKnowledgeSoundness` (`Unit` witness; the statement carries the oracle). -/
noncomputable def stirChainRelIn (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    Set ((Unit × ∀ i, OStmt ι F i) × Unit) :=
  stirOStmtRel Unit φ deg δ

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **Indicator RBR knowledge soundness of the packaged STIR chain proof** (the WHIR-discharge
pattern): the constant δ-closeness predicate on the chain input yields, via the universal
threshold knowledge-state-function, RBR knowledge soundness of `stirChainProof`'s verifier with
the indicator budget concentrated at the final repetition challenge. -/
theorem stirChainProof_rbrKnowledgeSoundness_indicator
    (φ : ι ↪ F) (deg : ℕ) (M : ℕ) (δ : ℝ≥0) :
    OracleProof.rbrKnowledgeSoundness (pure ()) isEmptyElim
      (stirChainRelIn φ deg δ)
      ((stirChainProof φ deg M).verifier)
      (fun i => if i = stirChainFinalChallengeIdx M then 1 else 0) := by
  unfold OracleProof.rbrKnowledgeSoundness OracleVerifier.rbrKnowledgeSoundness
  exact ThresholdKSF.rbrKnowledgeSoundness_indicator (pure ()) isEmptyElim
    ((stirChainProof φ deg M).verifier.toVerifier)
    (stirChainRelIn φ deg δ) acceptRejectOracleRel
    (fun _ stmtIn _ => (stmtIn, ()) ∈ stirChainRelIn φ deg δ)
    (stirChainFinalChallengeIdx M)
    (fun _ _ => Iff.rfl)
    (fun _ _ _ _ _ h => h)

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirChainProof_rbrKnowledgeSoundness_indicator
