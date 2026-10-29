/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.General

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.QueryPhase
import ArkLib.OracleReduction.Composition.Sequential.AppendOracleAdapters
import ArkLib.OracleReduction.Composition.Sequential.KnowledgeFailure
/-!
## Full Binary Basefold Protocol

Sequential composition of:
1. Core Interaction Phase (ℓ rounds of sumcheck + folding, and a final sumcheck)
2. Query Phase (final non-interactive proximity testing)

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
-/

set_option backward.isDefEq.respectTransparency false

open AdditiveNTT Polynomial

namespace Binius.BinaryBasefold.FullBinaryBasefold
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT

/-- Left-boundary direction transport for appended protocols: the appended protocol's direction
at the seam index `m` is `pSpec₂`'s direction at its round `0`. -/
private lemma append_dir_seam {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {d : Direction} (hn : 0 < n) (h : pSpec₂.dir ⟨0, hn⟩ = d) :
    (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = d := by
  rw [show (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m (⟨0, hn⟩ : Fin n) from by ext; simp]
  rw [Prover.append_dir_natAdd]
  exact h

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]


open CoreInteraction QueryPhase
/-- The full Binary Basefold protocol as a Proof -/
@[reducible]
noncomputable def fullOracleProof :
  OracleProof []ₒ
    (Statement := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) 0)
    (OStatement := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (Witness := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) 0)
    (pSpec:=fullPSpec 𝔽q β γ_repetitions (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  fullOracleReduction 𝔽q β γ_repetitions (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)

/-!
## Security Properties
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

open scoped NNReal ProbabilityTheory

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

section Wired

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}


/-- **Perfect completeness of the full Binary Basefold protocol, wired.** The
core-interaction ⋈ query seam is discharged by the proven challenge-seam keystone; the query
phase is the proven `queryOracleProof_perfectCompleteness_native`. Only the core-interaction phase
completeness (the existing `coreInteractionOracleReduction_perfectCompleteness` surface)
survives as a hypothesis. -/
theorem fullOracleReduction_perfectCompleteness_wired
    (hInit : NeverFail init)
    (hCoreInteractionPerfectCompleteness :
      OracleReduction.perfectCompleteness
        (pSpec := pSpecCoreInteraction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (relIn := strictRoundRelation (multpoly := multiplier) 𝔽q β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
        (relOut := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (oracleReduction := coreInteractionOracleReduction 𝔽q β (ϑ:=ϑ) (𝓑:=𝓑))
        (init := init)
        (impl := impl)) :
    OracleReduction.perfectCompleteness (Oₛₒ := fun i : Empty => nomatch i)
      (oracleReduction := fullOracleReduction 𝔽q β γ_repetitions (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑))
      (relIn := strictRoundRelation (multpoly := multiplier) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
      (relOut := acceptRejectOracleRel)
      (init := init)
      (impl := impl) := by
  have hQuery := queryOracleProof_perfectCompleteness_native 𝔽q β γ_repetitions
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) init hInit impl
  exact OracleReduction.append_perfectCompleteness_challenge_keystone
    (Oₛ₃ := fun i : Empty => nomatch i)
    (R₁ := coreInteractionOracleReduction 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑))
    (R₂ := queryOracleReduction 𝔽q β γ_repetitions (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (h₁ := hCoreInteractionPerfectCompleteness)
    (h₂ := hQuery)
    (hn := Nat.one_pos)
    (hDir := append_dir_seam Nat.one_pos rfl)
    (hDir₂ := rfl)
    (himplSP := fun t => t.elim)
    (himplNF := fun t => t.elim)
    (hInit := hInit)

/-- **Round-by-round knowledge soundness of the full Binary Basefold oracle verifier, wired**
(stateless regime). The core-interaction ⋈ query seam is discharged by the proven
failing-deterministic challenge-seam keystone; the query phase is the proven
`queryOracleVerifier_rbrKnowledgeSoundness`. Surviving hypotheses: the core-interaction phase
rbr knowledge soundness (the existing `coreInteractionOracleVerifier_rbrKnowledgeSoundness`
surface) and the failing-determinism witness `verify?`/`hVerify` for the compiled
core-interaction verifier (step bricks in `Steps/VerifierDeterminism.lean`; composite assembly
pending). -/
theorem fullOracleVerifier_rbrKnowledgeSoundness_wired [Subsingleton σ]
    [Inhabited (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : prFail init = 0)
    (verify? : (Statement (L := L) (SumcheckBaseContext L ℓ) 0 ×
        ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j) →
      (pSpecCoreInteraction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).FullTranscript →
      Option (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
        ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))
    (hVerify : (coreInteractionOracleVerifier 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)).toVerifier
      = ⟨fun p tr => OptionT.mk (pure (verify? p tr))⟩)
    (hCoreInteractionRbrKnowledgeSoundness :
      (coreInteractionOracleVerifier 𝔽q β (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
        (pSpec := pSpecCoreInteraction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (relIn := roundRelation (multpoly := multiplier) 𝔽q β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
        (relOut := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (rbrKnowledgeError := coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))) :
    (fullOracleVerifier 𝔽q β γ_repetitions (ϑ:=ϑ) (𝓑 := 𝓑)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).rbrKnowledgeSoundness init impl (Oₛₒ := fun i : Empty => nomatch i)
      (relIn := roundRelation (multpoly := multiplier) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
      (relOut := acceptRejectOracleRel)
      (rbrKnowledgeError := fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  have hKey := OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge
    (Oₛ₃ := fun i : Empty => nomatch i)
    (init := init) (impl := impl)
    (V₁ := coreInteractionOracleVerifier 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑))
    (V₂ := queryOracleVerifier 𝔽q β γ_repetitions (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (verify? := verify?) (hVerify := hVerify)
    (hInit := hInit) (hInitNF := hInitNF)
    (hNEW₂ := ⟨()⟩)
    (hn := Nat.one_pos)
    (hDir := append_dir_seam Nat.one_pos rfl)
    (hDir₂ := rfl)
    (h₁ := hCoreInteractionRbrKnowledgeSoundness)
    (h₂ := queryOracleVerifier_rbrKnowledgeSoundness 𝔽q β γ_repetitions
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) init impl)
  have herr : fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      = (Sum.elim
          (coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ:=ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
          (queryRbrKnowledgeError 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
          ∘ ⇑ChallengeIdx.sumEquiv.symm) := rfl
  rw [herr]
  exact hKey

end Wired

end Binius.BinaryBasefold.FullBinaryBasefold

#print axioms Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof
#print axioms Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness_wired
#print axioms Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness_wired
