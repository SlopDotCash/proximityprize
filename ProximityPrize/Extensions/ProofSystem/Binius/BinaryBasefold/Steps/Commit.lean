/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.Commit

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.Steps.Fold
import ArkLib.OracleReduction.Composition.Sequential.ChallengeOracleFintype

/-!
# Binary Basefold Commit Step

The commitment round of the Binary Basefold core interaction as an oracle reduction. Defines the
prover (`commitOracleProver`), verifier (`commitOracleVerifier`), and reduction
(`commitOracleReduction`), proves its perfect completeness, and provides the round-by-round
knowledge extractor (`commitRbrExtractor`) and knowledge-state function.
-/

namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold
open scoped NNReal ProbabilityTheory

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

section SingleIteratedSteps
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context

section CommitStep

/-- Compatibility name for the canonical commit prover state. -/
abbrev commitPrvState (i : Fin ℓ) :=
  CommitProverState (Context := Context) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-!
Perfect completeness for the commit step oracle reduction.

This theorem proves that the honest prover-verifier interaction for the commit step
always succeeds (with probability 1) and produces valid outputs.

**Proof Strategy:**
The proof follows the same pattern as `foldOracleReduction_perfectCompleteness`:
1. Unroll the 1-message reduction to convert probabilistic statement to logical statement
2. Split into safety (no failures) and correctness (valid outputs)
3. For safety: prove the verifier never crashes (trivial - no verification)
4. For correctness: apply the logic completeness lemma

**Key Difference from Fold Step:**
- No challenges (1-message protocol)
- No verification check
- Just extends the oracle with the new function
-/
open scoped NNReal

/-! The historical predicate uses newest-first challenges and its original bad-event branch.
It is not identified with the canonical knowledge invariant. -/
namespace Historical

def commitKStateProp (i : Fin ℓ) (m : Fin (1 + 1))
    (stmtIn : Statement (L := L) Context i.succ)
  (witMid : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
  (oStmtIn : (i_1 : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
    OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc i_1)
  (tr : Transcript m (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
  : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    masterKStateCore (mp := mp) (𝓑 := 𝓑) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.succ) (oracleIdx := i.castSucc)
      (h_le := by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtIn)
  | ⟨1, _⟩ => -- implied by relOut: use transcript message as oracle (what verifier sees)
    -- The verifier sees tr.messages ⟨0, rfl⟩ as the new oracle, not witMid.f
    let newOracle := tr.messages ⟨0, rfl⟩
    let oStmtOut := snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (oStmtIn := oStmtIn) (newOracleFn := newOracle) (h_destIdx := by rfl)
    masterKStateCore (mp := mp) (𝓑 := 𝓑) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (stmtIdx := i.succ) (oracleIdx := i.succ)
      (h_le := le_rfl)
      (stmt := stmtIn) (wit := witMid) (oStmt := oStmtOut)

end Historical

/-- The authoritative native commit knowledge-state function. -/
noncomputable abbrev commitKState_native := @commitKnowledgeStateFunction

#print axioms commitKState_native

end CommitStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
