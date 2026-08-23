/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.SubUnitRbr
import ArkLib.ProofSystem.Stir.MultiRoundSpecT
import ArkLib.ProofSystem.Stir.RepWire
import ArkLib.ProofSystem.Stir.ShellRbrIndicator
import ArkLib.ProofSystem.Whir.ThresholdKSFMulti

/-!
# Budget monotonicity for the STIR rbr soundness surfaces (#301, #335, #351)

`ThresholdKSF.rbrKnowledgeSoundness_mono` (the #301 K3 generic half) transfers
round-by-round knowledge soundness to any pointwise-larger budget family. This file wires
that generic onto each named STIR soundness surface, so downstream consumers can quote any
budget above a discharged one instead of the exact discharged budget:

* `stirCheckingRbrSoundness_mono` / `stirMultiRoundRbrSoundness_mono` /
  `stirCheckingRbrSoundnessT_mono` / `stirCheckingRepRbrSoundnessStatement_mono` —
  the four surfaces are monotone in the budget;
* `stirCheckingRbrSoundness_of_epsStar_le` — the checking verifier is sound at every budget
  dominating the discharged `stirEpsStar` (`stirCheckingRbrSoundness_genuine`, #301);
* `stirMultiRoundRbrSoundness_of_indicator_le` — the shell verifier is sound at every budget
  dominating the indicator (`stirMultiRoundRbrSoundness_indicator`, #347); per the shell
  warning this carries no sub-1 security content.

Axiom-clean: audited at end of file.
-/

set_option linter.unusedSectionVars false

namespace StirIOP

namespace MultiRound

open OracleSpec OracleComp ProtocolSpec NNReal VectorIOP
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [Nonempty ι]
variable (M : ℕ) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)

/-- **Budget monotonicity for the checking-verifier soundness surface** (#301): the named
residual transfers to any pointwise-larger rbr budget. -/
theorem stirCheckingRbrSoundness_mono
    {ε ε' : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0}
    (h : stirCheckingRbrSoundnessResidual M φ deg δ ε) (hle : ∀ i, ε i ≤ ε' i) :
    stirCheckingRbrSoundnessResidual M φ deg δ ε' := by
  unfold stirCheckingRbrSoundnessResidual OracleProof.rbrKnowledgeSoundness
    OracleVerifier.rbrKnowledgeSoundness at h ⊢
  exact ThresholdKSF.rbrKnowledgeSoundness_mono _ _ _ _ _ h hle

/-- **Budget monotonicity for the shell-verifier soundness surface**: the named residual
transfers to any pointwise-larger rbr budget. -/
theorem stirMultiRoundRbrSoundness_mono
    {ε ε' : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0}
    (h : stirMultiRoundRbrSoundnessResidual M φ deg δ ε) (hle : ∀ i, ε i ≤ ε' i) :
    stirMultiRoundRbrSoundnessResidual M φ deg δ ε' := by
  obtain ⟨WitMid, ext, kSF, hbound⟩ := h
  exact ⟨WitMid, ext, kSF, fun stmtIn witIn prover i =>
    le_trans (hbound stmtIn witIn prover i) (by exact_mod_cast hle i)⟩

/-- **Budget monotonicity for the t-repetition checking surface** (#335 A1): the named
residual transfers to any pointwise-larger rbr budget. -/
theorem stirCheckingRbrSoundnessT_mono (t : ℕ)
    {ε ε' : ((stirMultiVSpecT M ι t).toProtocolSpec F).ChallengeIdx → ℝ≥0}
    (h : stirCheckingRbrSoundnessResidualT M φ deg t δ ε) (hle : ∀ i, ε i ≤ ε' i) :
    stirCheckingRbrSoundnessResidualT M φ deg t δ ε' := by
  unfold stirCheckingRbrSoundnessResidualT OracleProof.rbrKnowledgeSoundness
    OracleVerifier.rbrKnowledgeSoundness Verifier.rbrKnowledgeSoundness at h ⊢
  obtain ⟨WitMid, ext, kSF, hbound⟩ := h
  exact ⟨WitMid, ext, kSF, fun stmtIn witIn prover i =>
    le_trans (hbound stmtIn witIn prover i) (by exact_mod_cast hle i)⟩

/-- **Budget monotonicity for the rep-spec checking statement** (#335): the proven
statement-former transfers to any pointwise-larger rbr budget. -/
theorem stirCheckingRepRbrSoundnessStatement_mono (t : ℕ)
    {ε ε' : ((stirMultiVSpecRep M ι t).toProtocolSpec F).ChallengeIdx → ℝ≥0}
    (h : stirCheckingRepRbrSoundnessStatement M φ deg δ t ε) (hle : ∀ i, ε i ≤ ε' i) :
    stirCheckingRepRbrSoundnessStatement M φ deg δ t ε' := by
  unfold stirCheckingRepRbrSoundnessStatement OracleProof.rbrKnowledgeSoundness
    OracleVerifier.rbrKnowledgeSoundness at h ⊢
  exact ThresholdKSF.rbrKnowledgeSoundness_mono (pure ()) isEmptyElim
    ((stirCheckingIOPRep M φ deg t).verifier.toVerifier)
    (stirRelation deg φ δ) acceptRejectOracleRel h hle

/-- **The checking verifier is sound at every budget dominating `stirEpsStar`** (#301):
the discharged genuine budget (`stirCheckingRbrSoundness_genuine`) plus monotonicity. -/
theorem stirCheckingRbrSoundness_of_epsStar_le
    {ε : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0}
    (hle : ∀ i, stirEpsStar (F := F) (ι := ι) M δ i ≤ ε i) :
    stirCheckingRbrSoundnessResidual M φ deg δ ε := by
  have h := stirCheckingRbrSoundness_genuine M φ deg δ
  unfold stirCheckingRbrSoundnessResidual OracleProof.rbrKnowledgeSoundness
    OracleVerifier.rbrKnowledgeSoundness at h ⊢
  exact ThresholdKSF.rbrKnowledgeSoundness_mono _ _ _ _ _ h hle

/-- **The shell verifier is sound at every budget dominating the indicator** (#347): the
indicator discharge (`stirMultiRoundRbrSoundness_indicator`) plus monotonicity; per the
shell warning this carries no sub-1 security content. -/
theorem stirMultiRoundRbrSoundness_of_indicator_le
    {ε : (stirMultiVSpec M ι).ChallengeIdx → ℝ≥0}
    (hle : ∀ i, (if i = foldChalIdx (F := F) (ι := ι) M then 1 else 0) ≤ ε i) :
    stirMultiRoundRbrSoundnessResidual M φ deg δ ε := by
  have hg := stirMultiRoundRbrSoundness_indicator (F := F) (ι := ι) M φ deg δ
  unfold stirMultiRoundRbrSoundnessResidual OracleProof.rbrKnowledgeSoundness
    OracleVerifier.rbrKnowledgeSoundness Verifier.rbrKnowledgeSoundness at hg ⊢
  obtain ⟨WitMid, ext, kSF, hbound⟩ := hg
  exact ⟨WitMid, ext, kSF, fun stmtIn witIn prover i =>
    le_trans (hbound stmtIn witIn prover i) (by exact_mod_cast hle i)⟩

end MultiRound

end StirIOP

/-! ## Axiom audit — all kernel-clean. -/
#print axioms StirIOP.MultiRound.stirCheckingRbrSoundness_mono
#print axioms StirIOP.MultiRound.stirMultiRoundRbrSoundness_mono
#print axioms StirIOP.MultiRound.stirCheckingRbrSoundnessT_mono
#print axioms StirIOP.MultiRound.stirCheckingRepRbrSoundnessStatement_mono
#print axioms StirIOP.MultiRound.stirCheckingRbrSoundness_of_epsStar_le
#print axioms StirIOP.MultiRound.stirMultiRoundRbrSoundness_of_indicator_le
