/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase
import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase
import ArkLib.OracleReduction.Composition.Sequential.AppendChallengeKeystoneOracle
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDetChallenge

/-!
## Full Binary Basefold Protocol

Sequential composition of:
1. Core Interaction Phase (ℓ rounds of sumcheck + folding, and a final sumcheck)
2. Query Phase (final non-interactive proximity testing)

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
-/

open AdditiveNTT Polynomial

namespace Binius.BinaryBasefold.FullBinaryBasefold
open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT

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

instance {_ : Empty} : OracleInterface (Unit) := OracleInterface.instDefault

open CoreInteraction QueryPhase
/-- The oracle verifier for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleVerifier :
  OracleVerifier (oSpec:=[]ₒ)
    (StmtIn := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) 0)
    (OStmtIn:= OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (Stmt₁ := Statement (L := L) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (Stmt₃ := Bool)
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := pSpecCoreInteraction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₁ := CoreInteraction.coreInteractionOracleVerifier 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ) (𝓑:=𝓑))
    (V₂ := QueryPhase.queryOracleVerifier 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))

/-- The reduction for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleReduction :
  OracleReduction (oSpec:=[]ₒ)
    (StmtIn := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) 0)
    (OStmtIn:= OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) 0)
    (WitOut := Unit)
    (pSpec := fullPSpec 𝔽q β γ_repetitions (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.append (oSpec:=[]ₒ)
    (Stmt₁ := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (Stmt₃ := Bool)
    (Wit₁ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) 0)
    (Wit₂ := Unit)
    (Wit₃ := Unit)
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := pSpecCoreInteraction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (R₁ := CoreInteraction.coreInteractionOracleReduction 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ) (𝓑:=𝓑))
    (R₂ := QueryPhase.queryOracleReduction 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))

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

/-- Perfect completeness for the full Binary Basefold protocol (reduction) -/
theorem fullOracleReduction_perfectCompleteness (hInit : NeverFail init)
    (hFullProtocolCompleteness : OracleReduction.perfectCompleteness
    (oracleReduction := fullOracleReduction 𝔽q β γ_repetitions (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑))
    (relIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl)) :
    OracleReduction.perfectCompleteness
    (oracleReduction := fullOracleReduction 𝔽q β γ_repetitions (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑))
    (relIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl) := by
  exact hFullProtocolCompleteness

open scoped NNReal

/-- Combined RBR knowledge soundness error for the full protocol -/
noncomputable def fullRbrKnowledgeError (i : (fullPSpec 𝔽q β γ_repetitions (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 :=
  Sum.elim (f := CoreInteraction.coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (g := QueryPhase.queryRbrKnowledgeError 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (ChallengeIdx.sumEquiv.symm i)

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Round-by-round knowledge soundness for the full Binary Basefold oracle verifier -/
theorem fullOracleVerifier_rbrKnowledgeSoundness
    (hFullProtocolRbrKnowledgeSoundness :
      (fullOracleVerifier 𝔽q β γ_repetitions (ϑ:=ϑ) (𝓑 := 𝓑)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)  0)
      (relOut := acceptRejectOracleRel)
      (rbrKnowledgeError := fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))) :
    (fullOracleVerifier 𝔽q β γ_repetitions (ϑ:=ϑ) (𝓑 := 𝓑)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).rbrKnowledgeSoundness init impl
    (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)  0)
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  exact hFullProtocolRbrKnowledgeSoundness

/-!
## Wired front-door theorems (issues #313 / #317)

The two theorems above are identity wrappers: they take the full-protocol security statement as
a hypothesis. The `_wired` theorems below replace that monolithic hypothesis with the *component*
statements, discharging the `coreInteraction ⋈ queryPhase` seam by the proven challenge-seam
append keystones (`pSpecQuery` opens with the verifier challenge `V_to_P`, so the seam is a
challenge seam):

* completeness: `OracleReduction.append_perfectCompleteness_challenge_keystone`
  (unconditional; the `[]ₒ` implementation side conditions are vacuous since `[]ₒ.Domain = PEmpty`),
  with the query-phase side supplied by the **proven** `queryOracleProof_perfectCompleteness`;
* rbr knowledge soundness:
  `OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge`
  (stateless regime), with the query-phase side supplied by the **proven**
  `queryOracleVerifier_rbrKnowledgeSoundness`.

What remains hypothetical is exactly the still-open core-interaction phase surface:

* `hCoreInteractionPerfectCompleteness` / `hCoreInteractionRbrKnowledgeSoundness` — the
  CoreInteractionPhase front doors (themselves identity wrappers pending the C2/C4/A2
  block-composition chain of the #313 wiring map);
* `verify?`/`hVerify` (rbr only) — the failing-determinism witness for the compiled
  core-interaction verifier; the step-level bricks live in `Steps/VerifierDeterminism.lean`,
  their `append`/`seqCompose` assembly is not yet done.

These are honest external assumptions, NOT new conclusions-as-hypotheses: each is strictly
smaller than the full-protocol statement it replaces, and the query phase + composition are
proven.
-/

section Wired

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Left-boundary direction transport for appended protocols: the appended protocol's direction
at the seam index `m` is `pSpec₂`'s direction at its round `0`. -/
private lemma append_dir_seam {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {d : Direction} (hn : 0 < n) (h : pSpec₂.dir ⟨0, hn⟩ = d) :
    (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = d := by
  rw [show (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m (⟨0, hn⟩ : Fin n) from by ext; simp]
  rw [Prover.append_dir_natAdd]
  exact h

/-- **Perfect completeness of the full Binary Basefold protocol, wired.** The
core-interaction ⋈ query seam is discharged by the proven challenge-seam keystone; the query
phase is the proven `queryOracleProof_perfectCompleteness`. Only the core-interaction phase
completeness (the existing `coreInteractionOracleReduction_perfectCompleteness` surface)
survives as a hypothesis. -/
theorem fullOracleReduction_perfectCompleteness_wired
    (hInit : NeverFail init)
    (hCoreInteractionPerfectCompleteness :
      OracleReduction.perfectCompleteness
        (pSpec := pSpecCoreInteraction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (relIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
        (relOut := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (oracleReduction := coreInteractionOracleReduction 𝔽q β (ϑ:=ϑ) (𝓑:=𝓑))
        (init := init)
        (impl := impl)) :
    OracleReduction.perfectCompleteness
      (oracleReduction := fullOracleReduction 𝔽q β γ_repetitions (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑))
      (relIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
      (relOut := acceptRejectOracleRel)
      (init := init)
      (impl := impl) := by
  have hQuery := queryOracleProof_perfectCompleteness 𝔽q β γ_repetitions
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) init hInit impl
  exact OracleReduction.append_perfectCompleteness_challenge_keystone
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
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
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
        (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
        (relOut := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (rbrKnowledgeError := coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))) :
    (fullOracleVerifier 𝔽q β γ_repetitions (ϑ:=ϑ) (𝓑 := 𝓑)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
      (relOut := acceptRejectOracleRel)
      (rbrKnowledgeError := fullRbrKnowledgeError 𝔽q β γ_repetitions (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  have hKey := OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge
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
