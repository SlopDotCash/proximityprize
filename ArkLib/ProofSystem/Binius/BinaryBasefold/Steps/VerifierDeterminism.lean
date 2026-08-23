/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Fold
import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Relay
import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Commit
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeOracleLift
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDet

/-!
# Determinism witnesses for the Binius Binary Basefold step verifiers (issue #313)

The rbr knowledge-soundness append/seqCompose keystones consume determinism witnesses for the
left verifier of each seam:

* total-deterministic: `V.toVerifier = ⟨fun p tr => pure (v p tr, …)⟩`
  (`toVerifier_eq_pure_of_collapse`);
* failing-deterministic: `V.toVerifier = ⟨fun p tr => OptionT.mk (pure ((v? p tr).map …))⟩`
  (`toVerifier_eq_failingDet_of_collapse`).

This file supplies them for the three Binary Basefold step verifiers, in the convention of
`RingSwitching/BatchingDeterminism.lean`:

* `relayOracleVerifier` and `commitOracleVerifier` are `pure stmtIn` — total-deterministic with
  the identity verdict;
* `foldOracleVerifier` queries its round message and then `guard`s the sumcheck check — failing-
  deterministic with verdict `if verifierCheck then some verifierOut else none`.

These are the item-③ bricks of the #313 wiring map, feeding the C2/C4/A2 composition chain via
`IsFailingDet.append` / `append_pure_failingDet` / the seqCompose determinism combinators.
-/

open OracleSpec OracleComp ProtocolSpec
open scoped NNReal

noncomputable section

namespace Binius.BinaryBasefold

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [SampleableType L]
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

namespace CoreInteraction

/-- The relay verifier's compiled `toVerifier` is literally pure: its verdict is the unchanged
input statement (with the deterministic oracle routing riding along). -/
theorem relayOracleVerifier_toVerifier_pure (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) hNCR).toVerifier
      = ⟨fun p tr => pure (p.1,
          fun j => match h : (relayOracleVerifier 𝔽q β (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) hNCR).embed j with
            | Sum.inl k =>
                ((relayOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (i := i) hNCR).hEq j ▸ h ▸ p.2 k)
            | Sum.inr k =>
                ((relayOracleVerifier 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (i := i) hNCR).hEq j ▸ h ▸ tr.messages k))⟩ :=
  OracleVerifier.toVerifier_eq_pure_of_collapse _ (fun p _ => p.1)
    (fun stmt oStmt tr => by
      simp only [relayOracleVerifier, simulateQ_pure]
      rfl)

/-- The commit verifier's compiled `toVerifier` is literally pure: its verdict is the unchanged
input statement. -/
theorem commitOracleVerifier_toVerifier_pure (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (i := i) hCR).toVerifier
      = ⟨fun p tr => pure (p.1,
          fun j => match h : (commitOracleVerifier (mp := mp) 𝔽q β (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (i := i) hCR).embed j with
            | Sum.inl k =>
                ((commitOracleVerifier (mp := mp) 𝔽q β (ϑ := ϑ)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (i := i) hCR).hEq j ▸ h ▸ p.2 k)
            | Sum.inr k =>
                ((commitOracleVerifier (mp := mp) 𝔽q β (ϑ := ϑ)
                  (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (i := i) hCR).hEq j ▸ h ▸
                    tr.messages k))⟩ :=
  OracleVerifier.toVerifier_eq_pure_of_collapse _ (fun p _ => p.1)
    (fun stmt oStmt tr => by
      simp only [commitOracleVerifier, simulateQ_bind, simulateQ_pure, pure_bind]
      rfl)

/-- The fold verifier's deterministic option-valued verdict: read the round-polynomial message
from the transcript, run the sumcheck `verifierCheck`, and emit `verifierOut` on success. -/
def foldVerifyFn (i : Fin ℓ)
    (p : Statement (L := L) Context i.castSucc ×
      ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    (tr : FullTranscript (pSpecFold (L := L))) :
    Option (Statement (L := L) Context i.succ) :=
  let logic := foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (mp := mp) i
  let t := FullTranscript.mk2 (tr.messages ⟨0, by rfl⟩) (tr.challenges ⟨1, by rfl⟩)
  if logic.verifierCheck p.1 t then some (logic.verifierOut p.1 t) else none

/-- **Failing-determinism witness for the fold verifier.** Its compiled `toVerifier` is the
failing-deterministic verifier on `foldVerifyFn`: the round-message query is answered from the
transcript and the `guard` is the only failure source. -/
theorem foldOracleVerifier_toVerifier_failingDet (i : Fin ℓ) :
    (foldOracleVerifier (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (i := i)).toVerifier
      = ⟨fun p tr => OptionT.mk (pure
          ((foldVerifyFn (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (𝓑 := 𝓑) i p tr).map (fun s => (s,
            fun j => match h : (foldOracleVerifier (mp := mp) 𝔽q β (ϑ := ϑ)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (i := i)).embed j with
              | Sum.inl k =>
                  ((foldOracleVerifier (mp := mp) 𝔽q β (ϑ := ϑ)
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (i := i)).hEq j ▸ h ▸ p.2 k)
              | Sum.inr k =>
                  ((foldOracleVerifier (mp := mp) 𝔽q β (ϑ := ϑ)
                    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (i := i)).hEq j ▸ h ▸
                      tr.messages k)))))⟩ :=
  OracleVerifier.toVerifier_eq_failingDet_of_collapse _
    (foldVerifyFn (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i)
    (fun stmt oStmt tr => by
      classical
      simp only [foldOracleVerifier, foldVerifyFn]
      rw [simulateQ_bind, simulateQ_query]
      simp only [OracleInterface.simOracle2, simulateQ_bind, simulateQ_pure, pure_bind,
        FullTranscript.mk2]
      by_cases hchk : (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑 := 𝓑) (mp := mp) i).verifierCheck stmt
        (FullTranscript.mk2 (tr.messages ⟨0, by rfl⟩) (tr.challenges ⟨1, by rfl⟩))
      · simp [hchk, guard, FullTranscript.mk2]
      · simp [hchk, guard, FullTranscript.mk2])

end CoreInteraction

end Binius.BinaryBasefold

end

#print axioms Binius.BinaryBasefold.CoreInteraction.relayOracleVerifier_toVerifier_pure
#print axioms Binius.BinaryBasefold.CoreInteraction.commitOracleVerifier_toVerifier_pure
#print axioms Binius.BinaryBasefold.CoreInteraction.foldOracleVerifier_toVerifier_failingDet
