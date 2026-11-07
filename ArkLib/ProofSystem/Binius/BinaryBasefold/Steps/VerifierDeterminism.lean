/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Steps.Fold
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Steps.Relay
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Steps.Commit
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeOracleLift
import ArkLib.OracleReduction.Composition.Sequential.KnowledgeFailure
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
variable [hdiv : Fact (ϑ ∣ ℓ)]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [SampleableType L]
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

namespace CoreInteraction

/-- The native relay verifier preserves the statement and materializes its output oracles. -/
theorem relayOracleVerifier_toVerifier_pure (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (relayOracleVerifier (Context := Context) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR).toVerifier =
      ⟨fun p tr => pure (p.1,
        (relayOracleVerifier (Context := Context) 𝔽q β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR).materializeOutput
          tr.challenges p.2 tr.messages)⟩ := rfl

/-- The native commit verifier preserves the statement and materializes its output oracles. -/
theorem commitOracleVerifier_toVerifier_pure (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (commitOracleVerifier (Context := Context) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR).toVerifier =
      ⟨fun p tr => pure (p.1,
        (commitOracleVerifier (Context := Context) 𝔽q β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR).materializeOutput
          tr.challenges p.2 tr.messages)⟩ := rfl

/-- The fold verifier's actual guard and verdict, projected to the output statement. -/
def foldVerifyFn (i : Fin ℓ)
    (p : Statement (L := L) Context i.castSucc ×
      ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j)
    (tr : FullTranscript (pSpecFold (L := L))) :
    Option (Statement (L := L) Context i.succ) :=
  let G := foldOracleVerifierGuardedForm 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := mp.multpoly) i
  if G.check p tr then some (G.out p tr).1 else none

/-- The fold verifier has exactly the optional native guard verdict; rejection remains failure. -/
theorem foldOracleVerifier_toVerifier_failingDet (i : Fin ℓ) :
    (foldOracleVerifier (multpoly := mp.multpoly) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i).toVerifier =
      ⟨fun p tr => OptionT.mk (pure
        ((foldVerifyFn (mp := mp) 𝔽q β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i p tr).map fun s =>
          (s, (foldOracleVerifier (multpoly := mp.multpoly) 𝔽q β (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i).materializeOutput
            tr.challenges p.2 tr.messages)))⟩ := by
  classical
  let G := foldOracleVerifierGuardedForm 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (multpoly := mp.multpoly) i
  apply Verifier.ext
  funext p tr
  rw [G.verify_eq p tr]
  by_cases hc : G.check p tr = true
  · simp [foldVerifyFn, G, hc]
    rw [foldOracleVerifierGuardedForm_out (multpoly := mp.multpoly) 𝔽q β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i p tr]
    rfl
  · simp [foldVerifyFn, G, hc]
    rfl

end CoreInteraction
end Binius.BinaryBasefold
end

#print axioms Binius.BinaryBasefold.CoreInteraction.relayOracleVerifier_toVerifier_pure
#print axioms Binius.BinaryBasefold.CoreInteraction.commitOracleVerifier_toVerifier_pure
#print axioms Binius.BinaryBasefold.CoreInteraction.foldOracleVerifier_toVerifier_failingDet
