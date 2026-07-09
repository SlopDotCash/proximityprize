/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeChallengeOracleLift
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDet
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDetEmpty
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeMsgCompleteness
import ArkLib.ProofSystem.Spartan.Composition

/-!
# #114 Spartan composed round-by-round knowledge soundness — the seven-seam assembly

The rbr-knowledge mirror of `ComposedCompleteness.lean`'s eight-leaf fold: folds the seven seams
of the composed Spartan PIOP `composedPIOP_Rc` with the per-seam rbr knowledge-soundness append
keystones —

* **message seams** (`firstChallenge ▷ …`, `firstSumcheck ▷ …`, `linearCombination ▷ …`,
  `prependRLCTarget ▷ …`): `OracleVerifier.append_rbrKnowledgeSoundness_subsingleton` (pure-
  deterministic left verifier) / `…_failingDet_subsingleton` (failing-deterministic left
  verifier, the sum-check shape) — both **residual-free** (the inner seam reconciliation is
  proven at message seams, `appendRbrKnowledgePhase2SeamReconcile_proof`);
* **empty seam** (`secondSumcheck ▷ finalCheck`): the residual-free
  `OracleVerifier.append_rbrKnowledgeSoundness_failingDet_empty`;
* **challenge seams** (`firstMessage ▷ …`, `sendEvalClaim ▷ …`):
  `OracleVerifier.append_rbrKnowledgeSoundness_subsingleton_challenge`, whose **single**
  genuinely-open per-seam residual (`hSeamZero` — the flip bound at the seam challenge itself) is
  threaded as the named hypothesis `Verifier.appendRbrKnowledgeSeamZeroResidual` (the former
  `hReconcile` is discharged by `appendRbrKnowledgePhase2SeamReconcile_proof_pos`).

The assembly is stated in the stateless (`Subsingleton σ`, e.g. `σ = Unit`) regime — the canonical
instantiation of the composed Spartan PIOP — and is **relation-chain agnostic** (like the
completeness fold): any chain `relA → … → relI` of intermediate relations threads through.

## What this reduces #114's rbr layer to

`composedRbrKnowledgeSoundnessResidual_of_leaves` discharges the official
`SpartanBricks.composedRbrKnowledgeSoundnessResidual` (at `Rc := composedPIOP_Rc`, error
`composedRbrError`) from:

1. the **eight per-phase rbr knowledge-soundness leaves** (`h₁`–`h₈`);
2. the **seven per-phase verifier determinism witnesses** (`hV₁`–`hV₇`: pure for the forwarding
   phases, failing-deterministic for the two sum-checks — supplied by
   `toVerifier_eq_pure_of_collapse` / `toVerifier_eq_failingDet_of_collapse` style lemmas);
3. the **two challenge-seam `hSeamZero` residuals** (at `firstMessage ▷ …` and
   `sendEvalClaim ▷ …`; one residual per challenge seam — the former `hReconcile` companion is
   discharged in-library).

No other obligation remains: every message/empty seam is discharged unconditionally.

## Honesty

No `sorry`/`axiom`; nothing is asserted beyond the fold. The leaves (1), witnesses (2), and
challenge-seam residuals (3) are open, named hypotheses — exactly the remaining #114 rbr surface.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 512

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

/-- The honest RLC-target adapter pinned to the concrete oracle-interface universe used by the
rbr append keystones (mirror of the private `prependRLCTargetPC` of `ComposedCompleteness.lean`).
-/
private abbrev prependRLCTargetKS {ι : Type} (oSpec : OracleSpec ι) :
    OracleReduction.{0, 0} oSpec
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombination R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] :=
  prependRLCTarget pp oSpec

/-! ### Direction facts (private mirrors of `ComposedCompleteness.lean`'s) -/

/-- Positivity of two-step round counts. -/
private theorem vsum_two_pos {ℓ : ℕ} (h : 0 < ℓ) : 0 < Fin.vsum (fun _ : Fin ℓ => 2) := by
  rcases ℓ with - | k
  · omega
  · rw [Fin.vsum_succ]; omega

/-- The multi-round sum-check protocol opens with the prover's `P_to_V` polynomial message. -/
private theorem sumcheckPSpec_dir_zero (deg n : ℕ)
    (h : 0 < Fin.vsum (fun _ : Fin n => 2)) :
    (Sumcheck.Spec.pSpec R deg n).dir ⟨0, h⟩ = .P_to_V := by
  rcases ProtocolSpec.seqCompose_appendValid
      (pSpec := fun _ : Fin n => Sumcheck.Spec.SingleRound.pSpec R deg)
      (fun _ => ⟨by norm_num, rfl⟩) with hzero | ⟨h', hdir⟩
  · omega
  · exact hdir

/-- `sfx6 = sumcheck₂ ++ₚ !p[]` opens `P_to_V` (second sum-check's leading message). -/
private theorem sfx6_dir_zero (hn : 0 < pp.ℓ_n)
    (h : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0) :
    (sfx6 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  rw [show (⟨0, h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))
      = Fin.castLE (by omega) (⟨0, hv⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2))) from by
    ext; simp]
  rw [Prover.append_dir_castLE]
  exact sumcheckPSpec_dir_zero 2 pp.ℓ_n hv

/-- `sfx5 = !p[] ++ₚ sfx6` opens `P_to_V`. (Also the seam-direction fact for the
`prependRLCTarget ▷ …` append, whose combined spec is literally `sfx5` at seam index `0`.) -/
private theorem sfx5_dir_zero (hn : 0 < pp.ℓ_n)
    (h : 0 < 0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) :
    (sfx5 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have h6 : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0 := by
    have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
    omega
  rw [show (⟨0, h⟩ : Fin (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))
      = Fin.natAdd 0 (⟨0, h6⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx6_dir_zero pp hn h6

/-- `sfx4 = ⟨V_to_P, LinComb⟩ ++ₚ sfx5` opens `V_to_P` (the linear-combination challenge). -/
private theorem sfx4_dir_zero
    (h : 0 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) :
    (sfx4 (R := R) pp).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `linearCombination ▷ sfx5`: the combined spec (= `sfx4`) at the
seam index `1` is `P_to_V`. -/
private theorem sfx4_dir_seam (hn : 0 < pp.ℓ_n)
    (h : 1 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) :
    (sfx4 (R := R) pp).dir ⟨1, h⟩ = .P_to_V := by
  have h5 : 0 < 0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))
      = Fin.natAdd 1 (⟨0, h5⟩ : Fin (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx5_dir_zero pp hn h5

/-- `sfx3 = ⟨P_to_V, EvalClaim⟩ ++ₚ sfx4` opens `P_to_V` (the bundled eval-claim message). -/
private theorem sfx3_dir_zero
    (h : 0 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) :
    (sfx3 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  rw [show (⟨0, h⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `sendEvalClaim ▷ sfx4`: the combined spec (= `sfx3`) at the seam
index `1` is `V_to_P` (the linear-combination challenge). -/
private theorem sfx3_dir_seam
    (h : 1 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) :
    (sfx3 (R := R) pp).dir ⟨1, h⟩ = .V_to_P := by
  have h4 : 0 < 1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))
      = Fin.natAdd 1 (⟨0, h4⟩ : Fin (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx4_dir_zero pp h4

/-- `sfx2 = sumcheck₃ ++ₚ sfx3` opens `P_to_V` (first sum-check's leading message). -/
private theorem sfx2_dir_zero (hm : 0 < pp.ℓ_m)
    (h : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) :
    (sfx2 (R := R) pp).dir ⟨0, h⟩ = .P_to_V := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2) := vsum_two_pos hm
  rw [show (⟨0, h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))
      = Fin.castLE (by omega) (⟨0, hv⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2))) from by
    ext; simp]
  rw [Prover.append_dir_castLE]
  exact sumcheckPSpec_dir_zero 3 pp.ℓ_m hv

/-- Seam-direction fact for `firstSumcheck ▷ sfx3`: the combined spec (= `sfx2`) at the seam
index `vsum 2` is `P_to_V` (the bundled eval-claim message). -/
private theorem sfx2_dir_seam
    (h : Fin.vsum (fun _ : Fin pp.ℓ_m => 2) < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) :
    (sfx2 (R := R) pp).dir ⟨Fin.vsum (fun _ : Fin pp.ℓ_m => 2), h⟩ = .P_to_V := by
  have h3 : 0 < 1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))) := by omega
  rw [show (⟨Fin.vsum (fun _ : Fin pp.ℓ_m => 2), h⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))
      = Fin.natAdd (Fin.vsum (fun _ : Fin pp.ℓ_m => 2))
          (⟨0, h3⟩ : Fin (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx3_dir_zero pp h3

/-- `sfx1 = ⟨V_to_P, FirstChallenge⟩ ++ₚ sfx2` opens `V_to_P`. -/
private theorem sfx1_dir_zero
    (h : 0 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) :
    (sfx1 (R := R) pp).dir ⟨0, h⟩ = .V_to_P := by
  rw [show (⟨0, h⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))))
      = Fin.castLE (by omega) (⟨0, Nat.one_pos⟩ : Fin 1) from by ext; simp]
  rw [Prover.append_dir_castLE]
  rfl

/-- Seam-direction fact for `firstChallenge ▷ sfx2`: the combined spec (= `sfx1`) at the seam
index `1` is `P_to_V` (the first sum-check's leading message). -/
private theorem sfx1_dir_seam (hm : 0 < pp.ℓ_m)
    (h : 1 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) :
    (sfx1 (R := R) pp).dir ⟨1, h⟩ = .P_to_V := by
  have h2 : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))))
      = Fin.natAdd 1 (⟨0, h2⟩ : Fin (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0)))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx2_dir_zero pp hm h2

/-- Seam-direction fact for `firstMessage ▷ sfx1`: the combined spec (= `composedPSpec`) at the
seam index `1` is `V_to_P` (the first challenge). -/
private theorem composedPSpec_dir_seam
    (h : 1 < 1 + (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))) :
    (composedPSpec (R := R) pp).dir ⟨1, h⟩ = .V_to_P := by
  have h1 : 0 < 1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
      + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))) := by omega
  rw [show (⟨1, h⟩ : Fin (1 + (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))))
      = Fin.natAdd 1 (⟨0, h1⟩ : Fin (1 + (Fin.vsum (fun _ : Fin pp.ℓ_m => 2)
        + (1 + (1 + (0 + (Fin.vsum (fun _ : Fin pp.ℓ_n => 2) + 0))))))) from by
    ext; simp]
  rw [Prover.append_dir_natAdd]
  exact sfx1_dir_zero pp h1

/-! ### The folded composed error -/

/-- The folded per-round rbr knowledge error of the composed Spartan PIOP: the eight per-phase
error families combined through `ChallengeIdx.sumEquiv` at each of the seven (right-associated)
seams — exactly the error produced by the keystone fold. For the canonical leaves this is `2/|R|`
on each sum-check round, `0` elsewhere. -/
def composedRbrError
    (err₁ : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (err₂ : (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (err₃ : (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).ChallengeIdx → ℝ≥0)
    (err₄ : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (err₅ : (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (err₆ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)
    (err₇ : (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).ChallengeIdx → ℝ≥0)
    (err₈ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0) :
    (composedPSpec (R := R) pp).ChallengeIdx → ℝ≥0 :=
  Sum.elim err₁
    (Sum.elim err₂
      (Sum.elim err₃
        (Sum.elim err₄
          (Sum.elim err₅
            (Sum.elim err₆
              (Sum.elim err₇ err₈ ∘ ChallengeIdx.sumEquiv.symm)
              ∘ ChallengeIdx.sumEquiv.symm)
            ∘ ChallengeIdx.sumEquiv.symm)
          ∘ ChallengeIdx.sumEquiv.symm)
        ∘ ChallengeIdx.sumEquiv.symm)
      ∘ ChallengeIdx.sumEquiv.symm)
    ∘ ChallengeIdx.sumEquiv.symm

/-! ### The seven-seam rbr fold -/

variable {ι : Type} (oSpec : OracleSpec ι)
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relA : Set ((Statement R pp × ∀ i, OracleStatement R pp i) × Witness R pp)}
  {relB : Set ((Statement.AfterFirstMessage R pp ×
    ∀ i, OracleStatement.AfterFirstMessage R pp i) × Unit)}
  {relC : Set ((Statement.AfterFirstChallenge R pp ×
    ∀ i, OracleStatement.AfterFirstChallenge R pp i) × Unit)}
  {relD : Set ((Statement.AfterFirstSumcheck R pp ×
    ∀ i, OracleStatement.AfterFirstSumcheck R pp i) × Unit)}
  {relE : Set ((Statement.AfterSendEvalClaim R pp ×
    ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit)}
  {relF : Set ((Statement.AfterLinearCombination R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relG : Set (((R × Statement.AfterLinearCombination R pp) ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}
  {relH : Set ((FinalStatement R pp × ∀ i, FinalOracleStatement R pp i) × Unit)}
  {relI : Set ((FinalStatement R pp × ∀ i, FinalOracleStatement R pp i) × Unit)}

/-- Seam 7 (`secondSumcheck ▷ finalCheck`, empty trailing seam; failing-deterministic left
verifier). Residual-free: no `Subsingleton σ`, no direction facts. -/
private theorem rbrStep8
    [Inhabited (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i)]
    {err₇ : (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).ChallengeIdx → ℝ≥0}
    {err₈ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0}
    (verify₇? : ((R × Statement.AfterLinearCombination R pp) ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) →
      (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).FullTranscript →
      Option (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i))
    (hV₇ : (secondSumcheckReduction pp oSpec).verifier.toVerifier
      = ⟨fun p tr => OptionT.mk (pure (verify₇? p tr))⟩)
    (hInit : ∃ s, s ∈ support init)
    (h₇ : (secondSumcheckReduction pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relG relH err₇)
    (h₈ : (finalCheck R pp oSpec).verifier.rbrKnowledgeSoundness init impl relH relI err₈) :
    ((secondSumcheckReduction pp oSpec).append
        (finalCheck R pp oSpec)).verifier.rbrKnowledgeSoundness init impl relG relI
      (Sum.elim err₇ err₈ ∘ ChallengeIdx.sumEquiv.symm) :=
  OracleVerifier.append_rbrKnowledgeSoundness_failingDet_empty
    (secondSumcheckReduction pp oSpec).verifier (finalCheck R pp oSpec).verifier
    verify₇? hV₇ hInit ⟨()⟩ h₇ h₈

/-- Seam 6 (`prependRLCTarget ▷ …`, message seam through the 0-round left adapter;
pure-deterministic left verifier). Residual-free under `Subsingleton σ`. -/
private theorem rbrStep7 [Subsingleton σ] (hn : 0 < pp.ℓ_n)
    {err₆ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0}
    {errRest : (sfx6 (R := R) pp).ChallengeIdx → ℝ≥0}
    (verify₆ : (Statement.AfterLinearCombination R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) →
      (!p[] : ProtocolSpec 0).FullTranscript →
      ((R × Statement.AfterLinearCombination R pp) ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hV₆ : (prependRLCTargetKS pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₆ p tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE : Nonempty ((R × Statement.AfterLinearCombination R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (h₆ : (prependRLCTargetKS pp oSpec).verifier.rbrKnowledgeSoundness init impl relF relG err₆)
    (hRest : ((secondSumcheckReduction pp oSpec).append
        (finalCheck R pp oSpec)).verifier.rbrKnowledgeSoundness init impl relG relI errRest) :
    ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
        (finalCheck R pp oSpec))).verifier.rbrKnowledgeSoundness init impl relF relI
      (Sum.elim err₆ errRest ∘ ChallengeIdx.sumEquiv.symm) := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  exact OracleVerifier.append_rbrKnowledgeSoundness_subsingleton
    (prependRLCTargetKS pp oSpec).verifier
    ((secondSumcheckReduction pp oSpec).append (finalCheck R pp oSpec)).verifier
    verify₆ hV₆ hInit hInitNF hNE ⟨()⟩ (by omega)
    (sfx5_dir_zero pp hn (by omega)) (sfx6_dir_zero pp hn (by omega)) h₆ hRest

/-- Seam 5 (`linearCombination ▷ …`, message seam; pure-deterministic left verifier).
Residual-free under `Subsingleton σ`. -/
private theorem rbrStep6 [Subsingleton σ] (hn : 0 < pp.ℓ_n)
    {err₅ : (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {errRest : (sfx5 (R := R) pp).ChallengeIdx → ℝ≥0}
    (verify₅ : (Statement.AfterSendEvalClaim R pp ×
        ∀ i, OracleStatement.AfterSendEvalClaim R pp i) →
      (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).FullTranscript →
      (Statement.AfterLinearCombination R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hV₅ : (oracleReduction.linearCombination R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₅ p tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE : Nonempty (Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (h₅ : (oracleReduction.linearCombination R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relE relF err₅)
    (hRest : ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
        (finalCheck R pp oSpec))).verifier.rbrKnowledgeSoundness init impl relF relI errRest) :
    ((oracleReduction.linearCombination R pp oSpec).append
        ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
          (finalCheck R pp oSpec)))).verifier.rbrKnowledgeSoundness init impl relE relI
      (Sum.elim err₅ errRest ∘ ChallengeIdx.sumEquiv.symm) := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  exact OracleVerifier.append_rbrKnowledgeSoundness_subsingleton
    (oracleReduction.linearCombination R pp oSpec).verifier
    ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
      (finalCheck R pp oSpec))).verifier
    verify₅ hV₅ hInit hInitNF hNE ⟨()⟩ (by omega)
    (sfx4_dir_seam pp hn (by omega)) (sfx5_dir_zero pp hn (by omega)) h₅ hRest

/-- Seam 4 (`sendEvalClaim ▷ …`, **challenge** seam; pure-deterministic left verifier). The
single open challenge-seam residual (`hSeamZero`) is threaded as a named hypothesis. -/
private theorem rbrStep5 [Subsingleton σ] (hn : 0 < pp.ℓ_n)
    {err₄ : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {errRest : (sfx4 (R := R) pp).ChallengeIdx → ℝ≥0}
    (verify₄ : (Statement.AfterFirstSumcheck R pp ×
        ∀ i, OracleStatement.AfterFirstSumcheck R pp i) →
      (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).FullTranscript →
      (Statement.AfterSendEvalClaim R pp × ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hV₄ : (oracleReduction.sendEvalClaim R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₄ p tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE : Nonempty (Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (h₄ : (oracleReduction.sendEvalClaim R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relD relE err₄)
    (hRest : ((oracleReduction.linearCombination R pp oSpec).append
        ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
          (finalCheck R pp oSpec)))).verifier.rbrKnowledgeSoundness init impl relE relI errRest)
    (hSeamZero : Verifier.appendRbrKnowledgeSeamZeroResidual (init := init) (impl := impl)
      (oracleReduction.sendEvalClaim R pp oSpec).verifier.toVerifier
      ((oracleReduction.linearCombination R pp oSpec).append
        ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
          (finalCheck R pp oSpec)))).verifier.toVerifier
      relD relE relI verify₄ hV₄ hInit errRest) :
    ((oracleReduction.sendEvalClaim R pp oSpec).append
        ((oracleReduction.linearCombination R pp oSpec).append
          ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
            (finalCheck R pp oSpec))))).verifier.rbrKnowledgeSoundness init impl relD relI
      (Sum.elim err₄ errRest ∘ ChallengeIdx.sumEquiv.symm) := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_n => 2) := vsum_two_pos hn
  exact OracleVerifier.append_rbrKnowledgeSoundness_subsingleton_challenge
    (oracleReduction.sendEvalClaim R pp oSpec).verifier
    ((oracleReduction.linearCombination R pp oSpec).append
      ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
        (finalCheck R pp oSpec)))).verifier
    verify₄ hV₄ hInit hInitNF hNE ⟨()⟩ (by omega)
    (sfx3_dir_seam pp (by omega)) (sfx4_dir_zero pp (by omega)) h₄ hRest hSeamZero

/-- Seam 3 (`firstSumcheck ▷ …`, message seam; **failing**-deterministic left verifier, the
sum-check shape). Residual-free under `Subsingleton σ`. -/
private theorem rbrStep4 [Subsingleton σ]
    [Inhabited (Statement.AfterFirstSumcheck R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    {err₃ : (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).ChallengeIdx → ℝ≥0}
    {errRest : (sfx3 (R := R) pp).ChallengeIdx → ℝ≥0}
    (verify₃? : (Statement.AfterFirstChallenge R pp ×
        ∀ i, OracleStatement.AfterFirstChallenge R pp i) →
      (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).FullTranscript →
      Option (Statement.AfterFirstSumcheck R pp ×
        ∀ i, OracleStatement.AfterFirstSumcheck R pp i))
    (hV₃ : (firstSumcheckReduction pp oSpec).verifier.toVerifier
      = ⟨fun p tr => OptionT.mk (pure (verify₃? p tr))⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (h₃ : (firstSumcheckReduction pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relC relD err₃)
    (hRest : ((oracleReduction.sendEvalClaim R pp oSpec).append
        ((oracleReduction.linearCombination R pp oSpec).append
          ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
            (finalCheck R pp oSpec))))).verifier.rbrKnowledgeSoundness init impl
      relD relI errRest) :
    ((firstSumcheckReduction pp oSpec).append ((oracleReduction.sendEvalClaim R pp oSpec).append
        ((oracleReduction.linearCombination R pp oSpec).append
          ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
            (finalCheck R pp oSpec)))))).verifier.rbrKnowledgeSoundness init impl relC relI
      (Sum.elim err₃ errRest ∘ ChallengeIdx.sumEquiv.symm) := by
  exact OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton
    (firstSumcheckReduction pp oSpec).verifier
    ((oracleReduction.sendEvalClaim R pp oSpec).append
      ((oracleReduction.linearCombination R pp oSpec).append
        ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
          (finalCheck R pp oSpec))))).verifier
    verify₃? hV₃ hInit hInitNF ⟨()⟩ (by omega)
    (sfx2_dir_seam pp (by omega)) (sfx3_dir_zero pp (by omega)) h₃ hRest

/-- Seam 2 (`firstChallenge ▷ …`, message seam; pure-deterministic left verifier).
Residual-free under `Subsingleton σ`. -/
private theorem rbrStep3 [Subsingleton σ] (hm : 0 < pp.ℓ_m)
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
    (hRest : ((firstSumcheckReduction pp oSpec).append
        ((oracleReduction.sendEvalClaim R pp oSpec).append
          ((oracleReduction.linearCombination R pp oSpec).append
            ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
              (finalCheck R pp oSpec)))))).verifier.rbrKnowledgeSoundness init impl
      relC relI errRest) :
    ((oracleReduction.firstChallenge R pp oSpec).append ((firstSumcheckReduction pp oSpec).append
        ((oracleReduction.sendEvalClaim R pp oSpec).append
          ((oracleReduction.linearCombination R pp oSpec).append
            ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
              (finalCheck R pp oSpec))))))).verifier.rbrKnowledgeSoundness init impl relB relI
      (Sum.elim err₂ errRest ∘ ChallengeIdx.sumEquiv.symm) := by
  have hv : 0 < Fin.vsum (fun _ : Fin pp.ℓ_m => 2) := vsum_two_pos hm
  exact OracleVerifier.append_rbrKnowledgeSoundness_subsingleton
    (oracleReduction.firstChallenge R pp oSpec).verifier
    ((firstSumcheckReduction pp oSpec).append
      ((oracleReduction.sendEvalClaim R pp oSpec).append
        ((oracleReduction.linearCombination R pp oSpec).append
          ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
            (finalCheck R pp oSpec)))))).verifier
    verify₂ hV₂ hInit hInitNF hNE ⟨()⟩ (by omega)
    (sfx1_dir_seam pp hm (by omega)) (sfx2_dir_zero pp hm (by omega)) h₂ hRest

/-- **Composed Spartan PIOP round-by-round knowledge soundness, reduced to the eight per-phase
rbr-KS leaves** (issue #114), in the stateless (`Subsingleton σ`) regime. Seam 1
(`firstMessage ▷ …`) and seam 4 (`sendEvalClaim ▷ …`) are **challenge** seams: their single
genuinely-open per-seam residual is threaded as the two named hypotheses
`hSeamZero₁`/`hSeamZero₄` (the former `hReconcile` companions are discharged in-library). All
five remaining seams (four message, one empty) are discharged **residual-free** by the proven
keystones. -/
theorem composedPIOP_Rc_rbrKnowledgeSoundness_of_leaves [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i)]
    [Inhabited (Statement.AfterFirstSumcheck R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    {err₁ : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₂ : (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₃ : (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).ChallengeIdx → ℝ≥0}
    {err₄ : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₅ : (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₆ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0}
    {err₇ : (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).ChallengeIdx → ℝ≥0}
    {err₈ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0}
    -- determinism witnesses for the seven left operands
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
      Option (Statement.AfterFirstSumcheck R pp ×
        ∀ i, OracleStatement.AfterFirstSumcheck R pp i))
    (hV₃ : (firstSumcheckReduction pp oSpec).verifier.toVerifier
      = ⟨fun p tr => OptionT.mk (pure (verify₃? p tr))⟩)
    (verify₄ : (Statement.AfterFirstSumcheck R pp ×
        ∀ i, OracleStatement.AfterFirstSumcheck R pp i) →
      (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).FullTranscript →
      (Statement.AfterSendEvalClaim R pp × ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hV₄ : (oracleReduction.sendEvalClaim R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₄ p tr)⟩)
    (verify₅ : (Statement.AfterSendEvalClaim R pp ×
        ∀ i, OracleStatement.AfterSendEvalClaim R pp i) →
      (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).FullTranscript →
      (Statement.AfterLinearCombination R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hV₅ : (oracleReduction.linearCombination R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₅ p tr)⟩)
    (verify₆ : (Statement.AfterLinearCombination R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) →
      (!p[] : ProtocolSpec 0).FullTranscript →
      ((R × Statement.AfterLinearCombination R pp) ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hV₆ : (prependRLCTargetKS pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₆ p tr)⟩)
    (verify₇? : ((R × Statement.AfterLinearCombination R pp) ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) →
      (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).FullTranscript →
      Option (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i))
    (hV₇ : (secondSumcheckReduction pp oSpec).verifier.toVerifier
      = ⟨fun p tr => OptionT.mk (pure (verify₇? p tr))⟩)
    -- the eight per-phase rbr knowledge-soundness leaves
    (h₁ : (oracleReduction.firstMessage R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relA relB err₁)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relB relC err₂)
    (h₃ : (firstSumcheckReduction pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relC relD err₃)
    (h₄ : (oracleReduction.sendEvalClaim R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relD relE err₄)
    (h₅ : (oracleReduction.linearCombination R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relE relF err₅)
    (h₆ : (prependRLCTargetKS pp oSpec).verifier.rbrKnowledgeSoundness init impl relF relG err₆)
    (h₇ : (secondSumcheckReduction pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relG relH err₇)
    (h₈ : (finalCheck R pp oSpec).verifier.rbrKnowledgeSoundness init impl relH relI err₈)
    -- side conditions and nonemptiness
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hNE_F : Nonempty (Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hNE_G : Nonempty ((R × Statement.AfterLinearCombination R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    -- the two challenge-seam residuals (seam 1: firstMessage ▷ …; seam 4: sendEvalClaim ▷ …)
    (hSeamZero₄ : Verifier.appendRbrKnowledgeSeamZeroResidual (init := init) (impl := impl)
      (oracleReduction.sendEvalClaim R pp oSpec).verifier.toVerifier
      ((oracleReduction.linearCombination R pp oSpec).append
        ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
          (finalCheck R pp oSpec)))).verifier.toVerifier
      relD relE relI verify₄ hV₄ hInit
      (Sum.elim err₅ (Sum.elim err₆ (Sum.elim err₇ err₈ ∘ ChallengeIdx.sumEquiv.symm)
        ∘ ChallengeIdx.sumEquiv.symm) ∘ ChallengeIdx.sumEquiv.symm))
    (hSeamZero₁ : Verifier.appendRbrKnowledgeSeamZeroResidual (init := init) (impl := impl)
      (oracleReduction.firstMessage R pp oSpec).verifier.toVerifier
      ((oracleReduction.firstChallenge R pp oSpec).append
        ((firstSumcheckReduction pp oSpec).append
          ((oracleReduction.sendEvalClaim R pp oSpec).append
            ((oracleReduction.linearCombination R pp oSpec).append
              ((prependRLCTargetKS pp oSpec).append
                ((secondSumcheckReduction pp oSpec).append
                  (finalCheck R pp oSpec))))))).verifier.toVerifier
      relA relB relI verify₁ hV₁ hInit
      (Sum.elim err₂ (Sum.elim err₃ (Sum.elim err₄ (Sum.elim err₅ (Sum.elim err₆
        (Sum.elim err₇ err₈ ∘ ChallengeIdx.sumEquiv.symm) ∘ ChallengeIdx.sumEquiv.symm)
        ∘ ChallengeIdx.sumEquiv.symm) ∘ ChallengeIdx.sumEquiv.symm)
        ∘ ChallengeIdx.sumEquiv.symm) ∘ ChallengeIdx.sumEquiv.symm)) :
    (composedPIOP_Rc (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl relA relI
      (composedRbrError pp err₁ err₂ err₃ err₄ err₅ err₆ err₇ err₈) := by
  have hS8 := rbrStep8 pp oSpec verify₇? hV₇ hInit h₇ h₈
  have hS7 := rbrStep7 pp oSpec hn verify₆ hV₆ hInit hInitNF hNE_G h₆ hS8
  have hS6 := rbrStep6 pp oSpec hn verify₅ hV₅ hInit hInitNF hNE_F h₅ hS7
  have hS5 := rbrStep5 pp oSpec hn verify₄ hV₄ hInit hInitNF hNE_E h₄ hS6 hSeamZero₄
  have hS4 := rbrStep4 pp oSpec verify₃? hV₃ hInit hInitNF h₃ hS5
  have hS3 := rbrStep3 pp oSpec hm verify₂ hV₂ hInit hInitNF hNE_C h₂ hS4
  exact OracleVerifier.append_rbrKnowledgeSoundness_subsingleton_challenge
    (oracleReduction.firstMessage R pp oSpec).verifier
    ((oracleReduction.firstChallenge R pp oSpec).append ((firstSumcheckReduction pp oSpec).append
      ((oracleReduction.sendEvalClaim R pp oSpec).append
        ((oracleReduction.linearCombination R pp oSpec).append
          ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
            (finalCheck R pp oSpec))))))).verifier
    verify₁ hV₁ hInit hInitNF hNE_B ⟨()⟩ (by omega)
    (composedPSpec_dir_seam pp (by omega)) (sfx1_dir_zero pp (by omega)) h₁ hS3
    hSeamZero₁

/-- **`composedRbrKnowledgeSoundnessResidual` reduced to the eight per-phase rbr-KS leaves** (+
the seven determinism witnesses + the two challenge-seam `hSeamZero` residuals): the official
composed rbr knowledge-soundness obligation of `SpartanBricks`, with input relation `spartanRelIn`
and output relation `finalCheckRelOut`, holds — at `Rc := composedPIOP_Rc`, with the folded error
`composedRbrError` — as soon as the eight phases are rbr knowledge sound along *any* chain of
intermediate relations. -/
theorem composedRbrKnowledgeSoundnessResidual_of_leaves [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i)]
    [Inhabited (Statement.AfterFirstSumcheck R pp ×
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
      Option (Statement.AfterFirstSumcheck R pp ×
        ∀ i, OracleStatement.AfterFirstSumcheck R pp i))
    (hV₃ : (firstSumcheckReduction pp oSpec).verifier.toVerifier
      = ⟨fun p tr => OptionT.mk (pure (verify₃? p tr))⟩)
    (verify₄ : (Statement.AfterFirstSumcheck R pp ×
        ∀ i, OracleStatement.AfterFirstSumcheck R pp i) →
      (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).FullTranscript →
      (Statement.AfterSendEvalClaim R pp × ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hV₄ : (oracleReduction.sendEvalClaim R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₄ p tr)⟩)
    (verify₅ : (Statement.AfterSendEvalClaim R pp ×
        ∀ i, OracleStatement.AfterSendEvalClaim R pp i) →
      (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).FullTranscript →
      (Statement.AfterLinearCombination R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hV₅ : (oracleReduction.linearCombination R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₅ p tr)⟩)
    (verify₆ : (Statement.AfterLinearCombination R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) →
      (!p[] : ProtocolSpec 0).FullTranscript →
      ((R × Statement.AfterLinearCombination R pp) ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hV₆ : (prependRLCTargetKS pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₆ p tr)⟩)
    (verify₇? : ((R × Statement.AfterLinearCombination R pp) ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) →
      (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).FullTranscript →
      Option (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i))
    (hV₇ : (secondSumcheckReduction pp oSpec).verifier.toVerifier
      = ⟨fun p tr => OptionT.mk (pure (verify₇? p tr))⟩)
    (h₁ : (oracleReduction.firstMessage R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (spartanRelIn R pp) relB err₁)
    (h₂ : (oracleReduction.firstChallenge R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relB relC err₂)
    (h₃ : (firstSumcheckReduction pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relC relD err₃)
    (h₄ : (oracleReduction.sendEvalClaim R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relD relE err₄)
    (h₅ : (oracleReduction.linearCombination R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relE relF err₅)
    (h₆ : (prependRLCTargetKS pp oSpec).verifier.rbrKnowledgeSoundness init impl relF relG err₆)
    (h₇ : (secondSumcheckReduction pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relG relH err₇)
    (h₈ : (finalCheck R pp oSpec).verifier.rbrKnowledgeSoundness init impl relH
      (finalCheckRelOut R pp) err₈)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hNE_F : Nonempty (Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hNE_G : Nonempty ((R × Statement.AfterLinearCombination R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hSeamZero₄ : Verifier.appendRbrKnowledgeSeamZeroResidual (init := init) (impl := impl)
      (oracleReduction.sendEvalClaim R pp oSpec).verifier.toVerifier
      ((oracleReduction.linearCombination R pp oSpec).append
        ((prependRLCTargetKS pp oSpec).append ((secondSumcheckReduction pp oSpec).append
          (finalCheck R pp oSpec)))).verifier.toVerifier
      relD relE (finalCheckRelOut R pp) verify₄ hV₄ hInit
      (Sum.elim err₅ (Sum.elim err₆ (Sum.elim err₇ err₈ ∘ ChallengeIdx.sumEquiv.symm)
        ∘ ChallengeIdx.sumEquiv.symm) ∘ ChallengeIdx.sumEquiv.symm))
    (hSeamZero₁ : Verifier.appendRbrKnowledgeSeamZeroResidual (init := init) (impl := impl)
      (oracleReduction.firstMessage R pp oSpec).verifier.toVerifier
      ((oracleReduction.firstChallenge R pp oSpec).append
        ((firstSumcheckReduction pp oSpec).append
          ((oracleReduction.sendEvalClaim R pp oSpec).append
            ((oracleReduction.linearCombination R pp oSpec).append
              ((prependRLCTargetKS pp oSpec).append
                ((secondSumcheckReduction pp oSpec).append
                  (finalCheck R pp oSpec))))))).verifier.toVerifier
      (spartanRelIn R pp) relB (finalCheckRelOut R pp) verify₁ hV₁ hInit
      (Sum.elim err₂ (Sum.elim err₃ (Sum.elim err₄ (Sum.elim err₅ (Sum.elim err₆
        (Sum.elim err₇ err₈ ∘ ChallengeIdx.sumEquiv.symm) ∘ ChallengeIdx.sumEquiv.symm)
        ∘ ChallengeIdx.sumEquiv.symm) ∘ ChallengeIdx.sumEquiv.symm)
        ∘ ChallengeIdx.sumEquiv.symm) ∘ ChallengeIdx.sumEquiv.symm)) :
    composedRbrKnowledgeSoundnessResidual R pp oSpec (composedPIOP_Rc pp oSpec) init impl
      (composedRbrError pp err₁ err₂ err₃ err₄ err₅ err₆ err₇ err₈) :=
  composedPIOP_Rc_rbrKnowledgeSoundness_of_leaves pp oSpec hm hn
    verify₁ hV₁ verify₂ hV₂ verify₃? hV₃ verify₄ hV₄ verify₅ hV₅ verify₆ hV₆ verify₇? hV₇
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hInit hInitNF hNE_B hNE_C hNE_E hNE_F hNE_G
    hSeamZero₄ hSeamZero₁


/-! ### Determinism witnesses for the forwarding phase verifiers

Four of the seven left-operand determinism witnesses of the fold are discharged here: the pure
forwarding phases compile (`toVerifier`) to pure-deterministic verifiers, by
`OracleVerifier.toVerifier_eq_pure_of_collapse` + `simulateQ_pure`. The remaining three
(`firstSumcheck`/`secondSumcheck` — failing-deterministic, the sum-check `else failure` shape —
and the oracle-querying `prependRLCTarget`) are open, named obligations of the wiring layer. -/

/-- The `firstMessage` (`SendSingleWitness`) verifier compiles to a pure-deterministic verifier:
its `verify` is `pure stmt`. Supplies `verify₁`/`hV₁` of the fold. -/
theorem firstMessage_toVerifier_pure :
    ∃ verify : (Statement R pp × ∀ i, OracleStatement R pp i) →
        (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).FullTranscript →
        (Statement.AfterFirstMessage R pp × ∀ i, OracleStatement.AfterFirstMessage R pp i),
      (oracleReduction.firstMessage R pp oSpec).verifier.toVerifier
        = ⟨fun p tr => pure (verify p tr)⟩ :=
  ⟨_, OracleVerifier.toVerifier_eq_pure_of_collapse
    (oracleReduction.firstMessage R pp oSpec).verifier (fun p _ => p.1)
    (fun _ _ _ => by
      simp only [oracleReduction.firstMessage, SendSingleWitness.oracleReduction,
        SendSingleWitness.oracleVerifier]
      exact simulateQ_pure _ _)⟩

/-- The `firstChallenge` (lifted `RandomQuery`) verifier compiles to a pure-deterministic
verifier: the inner `RandomQuery` verify is `pure (chal 0)`, and the lens routing is query-free.
Supplies `verify₂`/`hV₂` of the fold. -/
theorem firstChallenge_toVerifier_pure :
    ∃ verify : (Statement.AfterFirstMessage R pp ×
        ∀ i, OracleStatement.AfterFirstMessage R pp i) →
        (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).FullTranscript →
        (Statement.AfterFirstChallenge R pp × ∀ i, OracleStatement.AfterFirstChallenge R pp i),
      (oracleReduction.firstChallenge R pp oSpec).verifier.toVerifier
        = ⟨fun p tr => pure (verify p tr)⟩ :=
  ⟨_, OracleVerifier.toVerifier_eq_pure_of_collapse
    (oracleReduction.firstChallenge R pp oSpec).verifier
    (fun p tr => (tr.challenges ⟨0, rfl⟩, p.1))
    (fun _ _ _ => by
      simp [oracleReduction.firstChallenge, OracleReduction.liftContext,
        OracleVerifier.liftContext, RandomQuery.oracleReduction, RandomQuery.oracleVerifier,
        firstChallengeOracleLens, firstChallengeStmtLens, OptionT.mk, ReaderT.run]
      rfl)⟩

/-- The `sendEvalClaim` verifier compiles to a pure-deterministic verifier: its `verify` is
`pure stmt`. Supplies `verify₄`/`hV₄` of the fold. -/
theorem sendEvalClaim_toVerifier_pure :
    ∃ verify : (Statement.AfterFirstSumcheck R pp ×
        ∀ i, OracleStatement.AfterFirstSumcheck R pp i) →
        (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).FullTranscript →
        (Statement.AfterSendEvalClaim R pp × ∀ i, OracleStatement.AfterSendEvalClaim R pp i),
      (oracleReduction.sendEvalClaim R pp oSpec).verifier.toVerifier
        = ⟨fun p tr => pure (verify p tr)⟩ :=
  ⟨_, OracleVerifier.toVerifier_eq_pure_of_collapse
    (oracleReduction.sendEvalClaim R pp oSpec).verifier (fun p _ => p.1)
    (fun _ _ _ => by
      simp only [oracleReduction.sendEvalClaim, sendEvalClaimVerifier]
      exact simulateQ_pure _ _)⟩

/-- The `linearCombination` verifier compiles to a pure-deterministic verifier: its `verify`
returns the challenge paired with the statement. Supplies `verify₅`/`hV₅` of the fold. -/
theorem linearCombination_toVerifier_pure :
    ∃ verify : (Statement.AfterSendEvalClaim R pp ×
        ∀ i, OracleStatement.AfterSendEvalClaim R pp i) →
        (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1).FullTranscript →
        (Statement.AfterLinearCombination R pp ×
          ∀ i, OracleStatement.AfterLinearCombination R pp i),
      (oracleReduction.linearCombination R pp oSpec).verifier.toVerifier
        = ⟨fun p tr => pure (verify p tr)⟩ :=
  ⟨_, OracleVerifier.toVerifier_eq_pure_of_collapse
    (oracleReduction.linearCombination R pp oSpec).verifier
    (fun p tr => (tr.challenges ⟨0, rfl⟩, p.1))
    (fun _ _ _ => by
      simp only [oracleReduction.linearCombination, linearCombinationVerifier]
      exact simulateQ_pure _ _)⟩

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.composedRbrError
#print axioms Spartan.Spec.Bricks.composedPIOP_Rc_rbrKnowledgeSoundness_of_leaves
#print axioms Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessResidual_of_leaves
#print axioms Spartan.Spec.Bricks.firstMessage_toVerifier_pure
#print axioms Spartan.Spec.Bricks.firstChallenge_toVerifier_pure
#print axioms Spartan.Spec.Bricks.sendEvalClaim_toVerifier_pure
#print axioms Spartan.Spec.Bricks.linearCombination_toVerifier_pure
