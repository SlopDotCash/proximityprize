/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase
import ArkLib.ProofSystem.Binius.FRIBinius.CoreInteractionPhase
import ArkLib.ProofSystem.RingSwitching.BatchingPhase
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.Implications
import ArkLib.OracleReduction.Composition.Sequential.AppendChallengeKeystoneOracle
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDetChallenge

/-!
# FRI-Binius IOPCS

The FRI-Binius IOPCS consists of the following phases:
1. **Batching Phase**: polynomial packing and batching via tensor algebra operations
2. **Core Interaction Phase**: Interactive sumcheck + FRI folding over ℓ' rounds
3. **Query Phase**: FRI-style proximity testing with γ repetitions

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).
  Statement numbering follows the archived revision of [DP24].
-/

namespace Binius.FRIBinius.FullFRIBinius
noncomputable section

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Module
  Binius Verifier
open Binius.BinaryBasefold RingSwitching Binius.FRIBinius.CoreInteractionPhase

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar K))] [hF₂ : Fact (Fintype.card K = 2)]
variable [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L)
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable (ℓ ℓ' 𝓡 ϑ γ_repetitions : ℕ) [NeZero ℓ] [NeZero ℓ'] [NeZero 𝓡] [NeZero ϑ]
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)
variable (h_l : ℓ = ℓ' + κ)
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ')]

section Pspec

def batchingCorePspec := (RingSwitching.pSpecBatching κ L K) ++ₚ
  (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

def fullPspec := (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate) ++ₚ
  (BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, OracleInterface ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Message j) :=
  instOracleInterfaceMessageAppend (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, SampleableType ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).Challenge j) :=
  instSampleableTypeChallengeAppend (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂ := BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, OracleInterface ((fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions
    h_ℓ_add_R_rate).Message j) :=
  instOracleInterfaceMessageAppend (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

instance : ∀ j, SampleableType ((fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions
    h_ℓ_add_R_rate).Challenge j) :=
  instSampleableTypeChallengeAppend (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))

end Pspec

def batchingCoreVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:= RingSwitching.BatchingPhase.batchingOracleVerifier κ (L := L) (K := K) (𝓑 := 𝓑)
      (β:=booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
      (aOStmtIn :=  (BinaryBasefoldAbstractOStmtIn (β := β) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))))
    (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂:=BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (V₂:= FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier κ (L := L) (K := K) (β := β)
      (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))

def batchingCoreReduction :=
  OracleReduction.append (oSpec:=[]ₒ)
    (R₁ := RingSwitching.BatchingPhase.batchingOracleReduction κ (L := L) (K := K) (𝓑 := 𝓑)
      (β:=booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
      (aOStmtIn :=  (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))))
    (pSpec₁ := RingSwitching.pSpecBatching κ L K)
    (pSpec₂:=BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (R₂ := FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction κ L K
      β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))

/-- The oracle verifier for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleVerifier :
  OracleVerifier (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStmtIn := (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (Stmt₁ := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (Stmt₂ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (Stmt₃ := Bool)
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₁ := batchingCoreVerifier κ (L := L) (K := K) (𝓑 := 𝓑) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₂ := QueryPhase.queryOracleVerifier K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))

/-- The reduction for the full Binary Basefold protocol -/
@[reducible]
noncomputable def fullOracleReduction :
  OracleReduction (oSpec:=[]ₒ)
    (StmtIn := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStmtIn := (BinaryBasefoldAbstractOStmtIn (β := β)
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitIn := BatchingWitIn L K ℓ ℓ')
    (WitOut := Unit)
    (pSpec := fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.append (oSpec:=[]ₒ)
    (Stmt₁ := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (Stmt₂ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (Stmt₃ := Bool)
    (Wit₁ := BatchingWitIn L K ℓ ℓ')
    (Wit₂ := Unit)
    (Wit₃ := Unit)
    (OStmt₁ := (BinaryBasefoldAbstractOStmtIn (β := β)
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := fun _ : Empty => Unit)
    (pSpec₁ := batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (pSpec₂ := BinaryBasefold.pSpecQuery K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (R₁ := batchingCoreReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
    )
    (R₂ := QueryPhase.queryOracleReduction K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))

/-- The full Binary Basefold protocol as a Proof -/
@[reducible]
noncomputable def fullOracleProof :
  OracleProof []ₒ
    (Statement := BatchingStmtIn (L := L) (ℓ:=ℓ))
    (OStatement := (BinaryBasefoldAbstractOStmtIn (β := β)
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn)
    (Witness := BatchingWitIn L K ℓ ℓ')
    (pSpec:= fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  fullOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑:=𝓑)

/-!
## Security Properties
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

section CanonicalB

variable [h_B01 : Fact (𝓑 0 = 0 ∧ 𝓑 1 = 1)]

/-- Perfect completeness for the full Binary Basefold protocol (reduction) -/
theorem fullOracleReduction_perfectCompleteness (hInit : NeverFail init)
    (hAppendPerfectCompleteness :
      OracleReduction.perfectCompleteness
        (oracleReduction := fullOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑:=𝓑))
        (relIn := BatchingPhase.strictBatchingInputRelation κ L K
          (β:=booleanHypercubeBasis κ L K β)
          ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn (β := β)
            (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
        (relOut := acceptRejectOracleRel)
        (init := init)
        (impl := impl)) :
  OracleReduction.perfectCompleteness
    (oracleReduction := fullOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑:=𝓑))
    (relIn := BatchingPhase.strictBatchingInputRelation κ L K (β:=booleanHypercubeBasis κ L K β)
      ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (relOut := acceptRejectOracleRel)
    (init := init)
    (impl := impl) :=
  hAppendPerfectCompleteness

open scoped NNReal

/-- Combined RBR knowledge error for batching + core interaction. -/
def batchingCoreRbrKnowledgeError
    (i : (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := fun _ => RingSwitching.BatchingPhase.batchingRBRKnowledgeError (κ := κ) (L := L))
    (g := FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError
      (κ := κ) (L := L) (K := K) (β := β) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (ChallengeIdx.sumEquiv.symm i)

/-- Combined RBR knowledge error for full FRI-Binius. -/
def fullRbrKnowledgeError
    (i : (fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (g := QueryPhase.queryRbrKnowledgeError K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (ChallengeIdx.sumEquiv.symm i)

open FRIBinius.CoreInteractionPhase in
/-- Round-by-round knowledge soundness for the full FRI-Binius oracle verifier. -/
theorem fullOracleVerifier_rbrKnowledgeSoundness
    (hAppendRbrKnowledgeSoundness :
      (fullOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
        (relIn := BatchingPhase.batchingInputRelation κ L K (β := booleanHypercubeBasis κ L K β)
          ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn (β := β)
            (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
        (relOut := acceptRejectOracleRel)
        (rbrKnowledgeError := fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))) :
  (fullOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
    (relIn := BatchingPhase.batchingInputRelation κ L K (β := booleanHypercubeBasis κ L K β)
      ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn (β := β)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  hAppendRbrKnowledgeSoundness

/-!
## Concrete Knowledge Soundness Error

The concrete **soundness** (and matching KS scalar target) for FRI-Binius (**Construction 5.1**) is
given in Diamond–Posen (ePrint 2024/504) **§5.2, equation (43)**. The paper derives it from the
proofs of **Theorem 3.5** (ring-switching compiler) and **Theorem 4.17** (binary BaseFold / FRI
folding, **Construction 4.12**); the middle and right summands come from **Propositions 4.23** and
**4.24** respectively (see §5.2 text after (43)).

Closed form:

  (κ + 2 · ℓ') / |L| + 2^(ℓ' + 𝓡) / |L| + (1/2 + 1/(2 · 2^𝓡))^γ

Decomposition:
- `(κ + 2 · ℓ') / |L|` — ring-switching batching + sumcheck (§5.2; see also **Protocol 3.1** total
  `(2·ℓ'+κ)/|L|` in the paper’s efficiency discussion)
- `2^(ℓ' + 𝓡) / |L|` — aggregated fold-step bad events (**Proposition 4.23**)
- `(1/2 + 1/(2 · 2^𝓡))^γ` — query-phase / proximity acceptance (**Proposition 4.24**)

Audit note: DP24 presents this scalar as a soundness bound; this formalization proves the stronger
knowledge-soundness statement while keeping the scalar error exactly the same.
-/

/-- Single-repetition proximity testing error: `1/2 + 1/(2 · 2^𝓡)` (third factor of DP24 §5.2 (43)). -/
def querySingleRepetitionError : ℝ≥0 :=
  (1 / 2 : ℝ≥0) + 1 / (2 * 2 ^ 𝓡)

/-- Concrete KS upper bound for full FRI-Binius matching **DP24 §5.2 eq. (43)** / **Construction 5.1**
concrete soundness. -/
def concreteFRIBiniusKnowledgeError : ℝ≥0 :=
  ((κ : ℝ≥0) + 2 * (ℓ' : ℝ≥0)) / (Fintype.card L : ℝ≥0)
    + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0)
    + querySingleRepetitionError (𝓡 := 𝓡) ^ γ_repetitions

/-- `∑ᵢ εᵢ` for the full verifier is at most **DP24 §5.2 eq. (43)** (same decomposition as
**Theorem 4.17** / **Propositions 4.23–4.24** in the soundness analysis of **Construction 4.12**,
plus the **Theorem 3.5** / ring-switching front encoded in batching+core RBR errors).

Proof sketch:
- Batching contributes `κ / |L|` (single challenge round in `pSpecBatching`)
- Core interaction sumcheck rounds contribute `2 · ℓ' / |L|`
- Core interaction fold bad-event mass is **at most** the display `2^(ℓ' + 𝓡) / |L|` from
  **Proposition 4.23** (may be strict vs. the formal per-round `foldKnowledgeError` schedule; see
  `BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError_le`)
- Query phase contributes `(1/2 + 1/(2 · 2^𝓡))^γ` (**Proposition 4.24**)
-/
theorem fullRbrKnowledgeError_sum_le_concrete :
    (∑ i : (fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate).ChallengeIdx,
      fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate i)
    ≤ concreteFRIBiniusKnowledgeError κ L ℓ' 𝓡 γ_repetitions := by
  classical
  have h_full :
      (∑ i : (fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate).ChallengeIdx,
        fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate i)
      =
      (∑ i : (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx,
        batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate i)
      + (∑ i : (BinaryBasefold.pSpecQuery K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        QueryPhase.queryRbrKnowledgeError K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
    unfold fullRbrKnowledgeError
    let f :
        ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx
          ⊕ (BinaryBasefold.pSpecQuery K β γ_repetitions
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) → ℝ≥0 :=
      Sum.elim
        (batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
        (QueryPhase.queryRbrKnowledgeError K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    change (∑ i : (fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate).ChallengeIdx,
        f (ChallengeIdx.sumEquiv.symm i))
      =
      (∑ i : (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx,
        batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate i)
      + (∑ i : (BinaryBasefold.pSpecQuery K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        QueryPhase.queryRbrKnowledgeError K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    have hsum :
        (∑ i : (fullPspec κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate).ChallengeIdx,
          f (ChallengeIdx.sumEquiv.symm i))
          =
        (∑ i : ((batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx
            ⊕ (BinaryBasefold.pSpecQuery K β γ_repetitions
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx),
          f i) := by
      exact Equiv.sum_comp (e := Equiv.symm ChallengeIdx.sumEquiv) (g := f)
    rw [hsum]
    rw [Fintype.sum_sum_type]
    simp only [f, Sum.elim_inl, Sum.elim_inr]
  rw [h_full]
  have h_batchingCore :
      (∑ i : (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx,
        batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate i)
        =
      (∑ i : (RingSwitching.pSpecBatching κ L K).ChallengeIdx,
        RingSwitching.BatchingPhase.batchingRBRKnowledgeError (κ := κ) (L := L))
        +
      (∑ i : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
          h_ℓ_add_R_rate i) := by
    unfold batchingCoreRbrKnowledgeError
    let f :
        ((RingSwitching.pSpecBatching κ L K).ChallengeIdx
          ⊕ (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) → ℝ≥0 :=
      Sum.elim
        (fun _ => RingSwitching.BatchingPhase.batchingRBRKnowledgeError (κ := κ) (L := L))
        (FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
          h_ℓ_add_R_rate)
    change (∑ i : (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx,
        f (ChallengeIdx.sumEquiv.symm i))
      =
      (∑ i : (RingSwitching.pSpecBatching κ L K).ChallengeIdx,
        RingSwitching.BatchingPhase.batchingRBRKnowledgeError (κ := κ) (L := L))
        +
      (∑ i : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
          h_ℓ_add_R_rate i)
    have hsum :
        (∑ i : (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).ChallengeIdx,
          f (ChallengeIdx.sumEquiv.symm i))
          =
        (∑ i : ((RingSwitching.pSpecBatching κ L K).ChallengeIdx
            ⊕ (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx),
          f i) := by
      exact Equiv.sum_comp (e := Equiv.symm ChallengeIdx.sumEquiv) (g := f)
    rw [hsum]
    rw [Fintype.sum_sum_type]
    simp only [f, Sum.elim_inl, Sum.elim_inr]
  rw [h_batchingCore]
  have h_batching :
      (∑ i : (RingSwitching.pSpecBatching κ L K).ChallengeIdx,
        RingSwitching.BatchingPhase.batchingRBRKnowledgeError (κ := κ) (L := L))
      = (κ : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
    have h_batching_card : Fintype.card ((RingSwitching.pSpecBatching κ L K).ChallengeIdx) = 1 := by
      change Fintype.card { i // ![Direction.P_to_V, Direction.V_to_P] i = Direction.V_to_P } = 1
      decide
    rw [Finset.sum_const]
    simp [h_batching_card, RingSwitching.BatchingPhase.batchingRBRKnowledgeError]
  rw [h_batching]
  have h_core_le :
      (∑ i : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
          h_ℓ_add_R_rate i)
      ≤ 2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0)
          + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0) :=
    FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError_le
      (κ := κ) (L := L) (K := K) (β := β) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  have h_query :
      (∑ i : (BinaryBasefold.pSpecQuery K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        QueryPhase.queryRbrKnowledgeError K β γ_repetitions
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      = querySingleRepetitionError (𝓡 := 𝓡) ^ γ_repetitions := by
    simp [QueryPhase.queryRbrKnowledgeError, QueryPhase.queryRbrKnowledgeError_singleRepetition,
      querySingleRepetitionError, BinaryBasefold.pSpecQuery, ChallengeIdx]
  have h_le_mid :
      (κ : ℝ≥0) / (Fintype.card L : ℝ≥0)
        + (∑ i : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
            FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
              h_ℓ_add_R_rate i)
        + (∑ i : (BinaryBasefold.pSpecQuery K β γ_repetitions
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
            QueryPhase.queryRbrKnowledgeError K β γ_repetitions
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      ≤ concreteFRIBiniusKnowledgeError κ L ℓ' 𝓡 γ_repetitions := by
    have hx :
        (κ : ℝ≥0) / (Fintype.card L : ℝ≥0)
          + (∑ i : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
              FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
                h_ℓ_add_R_rate i)
          + (∑ i : (BinaryBasefold.pSpecQuery K β γ_repetitions
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
              QueryPhase.queryRbrKnowledgeError K β γ_repetitions
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
        ≤ (κ : ℝ≥0) / (Fintype.card L : ℝ≥0)
            + (2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0)
                + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0))
            + querySingleRepetitionError (𝓡 := 𝓡) ^ γ_repetitions := by
      have hκ_core :=
        add_le_add (le_refl ((κ : ℝ≥0) / (Fintype.card L : ℝ≥0))) h_core_le
      exact
        add_le_add hκ_core
          (le_of_eq h_query)
    have h_div :
        (κ : ℝ≥0) / (Fintype.card L : ℝ≥0)
          + 2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0)
        = ((κ : ℝ≥0) + 2 * (ℓ' : ℝ≥0)) / (Fintype.card L : ℝ≥0) := by
      rw [← add_div]
    have h_rhs :
        (κ : ℝ≥0) / (Fintype.card L : ℝ≥0)
          + (2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0)
              + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0))
          + querySingleRepetitionError (𝓡 := 𝓡) ^ γ_repetitions
        = concreteFRIBiniusKnowledgeError κ L ℓ' 𝓡 γ_repetitions := by
      rw [concreteFRIBiniusKnowledgeError]
      calc
        (κ : ℝ≥0) / (Fintype.card L : ℝ≥0)
            + (2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0)
                + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0))
            + querySingleRepetitionError (𝓡 := 𝓡) ^ γ_repetitions
            = ((κ : ℝ≥0) / (Fintype.card L : ℝ≥0)
                + 2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0))
                + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0)
                + querySingleRepetitionError (𝓡 := 𝓡) ^ γ_repetitions := by
                rw [← add_assoc]
        _ = ((κ : ℝ≥0) + 2 * (ℓ' : ℝ≥0)) / (Fintype.card L : ℝ≥0)
              + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0)
              + querySingleRepetitionError (𝓡 := 𝓡) ^ γ_repetitions := by
              rw [h_div]
    exact hx.trans (le_of_eq h_rhs)
  exact h_le_mid

/-- Scalar KS for the full stack with error **`concreteFRIBiniusKnowledgeError`**, i.e. **DP24 §5.2
(43)** / **Construction 5.1** concrete soundness (lifted to KS via OracleReduction; Diamond–Posen
ePrint 2024/504). Aligns with §5.2 “Concrete soundness” (Theorems **3.5**, **4.17**;
**Propositions 4.23**, **4.24**).

Proof strategy:
1. `fullOracleVerifier_rbrKnowledgeSoundness` gives RBR-KS (on OracleVerifier)
2. RBR-KS → KS via `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness` on `toVerifier`
3. `fullRbrKnowledgeError_sum_le_concrete` bounds `∑ εᵢ` by **(43)** for
   `Verifier.knowledgeSoundness_error_mono`
4. `Verifier.knowledgeSoundness_error_mono` inflates to the concrete bound
-/
theorem fullOracleVerifier_knowledgeSoundness :
    (fullOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).toVerifier.knowledgeSoundness init impl
    (relIn := BatchingPhase.batchingInputRelation κ L K (booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
      (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate))
    (relOut := acceptRejectOracleRel)
    (knowledgeError := concreteFRIBiniusKnowledgeError κ L ℓ' 𝓡 γ_repetitions) := by
  -- Same `relIn` / `fullOracleVerifier` / error spine as the elaborated
  -- `fullOracleVerifier_rbrKnowledgeSoundness`.
  let relInFull :=
    BatchingPhase.batchingInputRelation κ L K (booleanHypercubeBasis κ L K β) ℓ ℓ' h_l
      (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
  let fullV := fullOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
  let εFull := fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate
  -- Step 1: RBR-KS on `toVerifier` — defeq to `OracleVerifier.rbrKnowledgeSoundness`.
  have h_rbr : fullV.toVerifier.rbrKnowledgeSoundness init impl relInFull acceptRejectOracleRel εFull := by
    change OracleVerifier.rbrKnowledgeSoundness init impl relInFull acceptRejectOracleRel fullV εFull
    exact fullOracleVerifier_rbrKnowledgeSoundness
      (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
      (γ_repetitions := γ_repetitions) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
      (𝓑 := 𝓑) (init := init) (impl := impl)
  -- Step 2: `rbrKS ⇒ KS` is a function `(rbrKS → KS)` after fixing `relIn`, `relOut`, `verifier`,
  -- `ε`.
  have h_ks : fullV.toVerifier.knowledgeSoundness init impl relInFull acceptRejectOracleRel
      (∑ i, εFull i) :=
    (Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness (init := init) (impl := impl)
      relInFull acceptRejectOracleRel fullV.toVerifier εFull)
      h_rbr
  -- Step 3: Inflate ∑ εᵢ to the concrete DP24 bound.
  have h_mono := Verifier.knowledgeSoundness_error_mono
    (init := init) (impl := impl)
    (hε := fullRbrKnowledgeError_sum_le_concrete (κ := κ) (L := L) (K := K) (β := β)
      (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (γ_repetitions := γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    h_ks
  exact h_mono

/-! ## Wired front-door theorems (issue #313)

The two identity-wrapper front doors above (`fullOracleReduction_perfectCompleteness`,
`fullOracleVerifier_rbrKnowledgeSoundness`) take the *entire* full-protocol security statement as
a single hypothesis. The `_wired` theorems below replace that monolithic hypothesis with the
*component* obligations across the `batchingCore ⋈ query` seam:

* The seam itself is discharged by the proven challenge-seam append keystones
  (`OracleReduction.append_perfectCompleteness_challenge_keystone` /
  `OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge`).
* The **query phase** side is supplied by the *proven* BinaryBasefold keystones
  (`queryOracleProof_perfectCompleteness` / `queryOracleVerifier_rbrKnowledgeSoundness`) — exactly
  the wiring requested by the #313 close-out.

What survives as a hypothesis is strictly smaller than the full-protocol statement it replaces:
only the `batchingCore` phase (batching ⋈ core-interaction) completeness / rbr-KS, plus the
failing-determinism witness for the compiled `batchingCore` verifier (rbr-KS only). This mirrors
`BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness_wired`. -/

section Wired

open BinaryBasefold

/-- Left-boundary direction transport for appended protocols: the appended protocol's direction
at the seam index `m` is `pSpec₂`'s direction at its round `0`. -/
private lemma append_dir_seam {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {d : Direction} (hn : 0 < n) (h : pSpec₂.dir ⟨0, hn⟩ = d) :
    (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = d := by
  rw [show (⟨m, by omega⟩ : Fin (m + n)) = Fin.natAdd m (⟨0, hn⟩ : Fin n) from by ext; simp]
  rw [Prover.append_dir_natAdd]
  exact h

/-- **Perfect completeness of the full FRI-Binius protocol, wired (issue #313).** The
`batchingCore ⋈ query` seam is discharged by the proven challenge-seam keystone; the query phase
is the proven `BinaryBasefold.queryOracleProof_perfectCompleteness`. Only the `batchingCore` phase
completeness (the existing `batchingCoreReduction` surface) survives as a hypothesis. -/
theorem fullOracleReduction_perfectCompleteness_wired (hInit : NeverFail init)
    (hBatchingCorePerfectCompleteness :
      OracleReduction.perfectCompleteness
        (oracleReduction := batchingCoreReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
        (relIn := BatchingPhase.strictBatchingInputRelation κ L K
          (β:=booleanHypercubeBasis κ L K β)
          ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn (β := β)
            (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
        (relOut := BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (init := init)
        (impl := impl)) :
    OracleReduction.perfectCompleteness
      (oracleReduction := fullOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑:=𝓑))
      (relIn := BatchingPhase.strictBatchingInputRelation κ L K (β:=booleanHypercubeBasis κ L K β)
        ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn (β := β)
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
      (relOut := acceptRejectOracleRel)
      (init := init)
      (impl := impl) := by
  have hQuery := BinaryBasefold.QueryPhase.queryOracleProof_perfectCompleteness K β γ_repetitions
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) init hInit impl
  exact OracleReduction.append_perfectCompleteness_challenge_keystone
    (R₁ := batchingCoreReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    (R₂ := QueryPhase.queryOracleReduction K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))
    (h₁ := hBatchingCorePerfectCompleteness)
    (h₂ := hQuery)
    (hn := Nat.one_pos)
    (hDir := append_dir_seam Nat.one_pos rfl)
    (hDir₂ := rfl)
    (himplSP := fun t => t.elim)
    (himplNF := fun t => t.elim)
    (hInit := hInit)

/-- **Round-by-round knowledge soundness of the full FRI-Binius oracle verifier, wired (issue
#313, stateless regime).** The `batchingCore ⋈ query` seam is discharged by the proven
failing-deterministic challenge-seam keystone; the query phase is the proven
`BinaryBasefold.queryOracleVerifier_rbrKnowledgeSoundness`. Surviving hypotheses: the `batchingCore`
phase rbr knowledge soundness, and the failing-determinism witness `verify?`/`hVerify` for the
compiled `batchingCore` verifier. -/
theorem fullOracleVerifier_rbrKnowledgeSoundness_wired [Subsingleton σ]
    [Inhabited (BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ') ×
      ∀ j, BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
        (Fin.last ℓ') j)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (verify? : (BatchingStmtIn (L := L) (ℓ:=ℓ) ×
        ∀ j, (BinaryBasefoldAbstractOStmtIn (β := β) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).OStmtIn j) →
      (batchingCorePspec κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).FullTranscript →
      Option (BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ') ×
        ∀ j, BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
          (Fin.last ℓ') j))
    (hVerify : (batchingCoreVerifier κ (L := L) (K := K) (𝓑 := 𝓑) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
        (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).toVerifier
      = ⟨fun p tr => OptionT.mk (pure (verify? p tr))⟩)
    (hBatchingCoreRbrKnowledgeSoundness :
      (batchingCoreVerifier κ (L := L) (K := K) (𝓑 := 𝓑) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
        (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).rbrKnowledgeSoundness
        (init := init) (impl := impl)
        (relIn := BatchingPhase.batchingInputRelation κ L K (β := booleanHypercubeBasis κ L K β)
          ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn (β := β)
            (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
        (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (rbrKnowledgeError := batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)) :
    (fullOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (relIn := BatchingPhase.batchingInputRelation κ L K (β := booleanHypercubeBasis κ L K β)
        ℓ ℓ' h_l (BinaryBasefoldAbstractOStmtIn (β := β)
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
      (relOut := acceptRejectOracleRel)
      (rbrKnowledgeError := fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  have hKey := OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge
    (init := init) (impl := impl)
    (V₁ := batchingCoreVerifier κ (L := L) (K := K) (𝓑 := 𝓑) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₂ := QueryPhase.queryOracleVerifier K β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))
    (verify? := verify?) (hVerify := hVerify)
    (hInit := hInit) (hInitNF := hInitNF)
    (hNEW₂ := ⟨()⟩)
    (hn := Nat.one_pos)
    (hDir := append_dir_seam Nat.one_pos rfl)
    (hDir₂ := rfl)
    (h₁ := hBatchingCoreRbrKnowledgeSoundness)
    (h₂ := BinaryBasefold.QueryPhase.queryOracleVerifier_rbrKnowledgeSoundness K β γ_repetitions
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) init impl)
  have herr : fullRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ γ_repetitions h_ℓ_add_R_rate
      = (Sum.elim
          (batchingCoreRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
          (QueryPhase.queryRbrKnowledgeError K β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
          ∘ ⇑ChallengeIdx.sumEquiv.symm) := rfl
  rw [herr]
  exact hKey

end Wired

end CanonicalB

end
end Binius.FRIBinius.FullFRIBinius
