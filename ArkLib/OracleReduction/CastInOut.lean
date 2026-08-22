/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.Cast

/-!
  # Statement-level casts for oracle reductions and oracle verifiers

  This file defines casts of `OracleReduction` and `OracleVerifier` across equalities of the
  *statement* (and witness / oracle-statement index) types, keeping the protocol specification
  fixed. This complements `OracleReduction/Cast.lean`, which casts across equalities of
  `ProtocolSpec`s while keeping the statement types fixed.

  We provide:
  - `OracleReduction.castInOut` / `OracleVerifier.castInOut`: fully generalized casts allowing
    changes to input/output statements, witnesses, oracle statement index types (via `HEq`), and
    oracle interface instances (via `HEq`).
  - `OracleReduction.castOutSimple` / `OracleVerifier.castOutSimple`: casts of only the output
    types, keeping index types fixed.
  - Security transfer lemmas: (perfect) completeness transfers across the casts of oracle
    reductions, and round-by-round knowledge soundness transfers across the casts of oracle
    verifiers, given that the relations are transported along the same equalities.
-/

open OracleComp NNReal ProtocolSpec

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

/-- Fully generalized cast for OracleReduction.
    Handles changes to Indices, Statements, Witnesses, and Instances using HEq. -/
def castInOut
    -- 1. Input Types
    {StmtIn₁ StmtIn₂ : Type}
    {ιₛᵢ₁ ιₛᵢ₂ : Type} {OStmtIn₁ : ιₛᵢ₁ → Type} {OStmtIn₂ : ιₛᵢ₂ → Type}
    -- Take both instances
    [Oₛᵢ₁ : ∀ i, OracleInterface (OStmtIn₁ i)]
    [Oₛᵢ₂ : ∀ i, OracleInterface (OStmtIn₂ i)]
    {WitIn₁ WitIn₂ : Type}
    -- 2. Output Types
    {StmtOut₁ StmtOut₂ : Type}
    {ιₛₒ₁ ιₛₒ₂ : Type} {OStmtOut₁ : ιₛₒ₁ → Type} {OStmtOut₂ : ιₛₒ₂ → Type}
    {WitOut₁ WitOut₂ : Type}
    -- 3. Reduction
    (R : OracleReduction oSpec StmtIn₁ OStmtIn₁ WitIn₁ StmtOut₁ OStmtOut₁ WitOut₁ pSpec)
    -- 4. Equalities
    (h_stmtIn : StmtIn₁ = StmtIn₂)
    (h_stmtOut : StmtOut₁ = StmtOut₂)
    (h_witIn : WitIn₁ = WitIn₂)
    (h_witOut : WitOut₁ = WitOut₂)
    (h_idxIn : ιₛᵢ₁ = ιₛᵢ₂)             -- Index equality
    (h_idxOut : ιₛₒ₁ = ιₛₒ₂)           -- Index equality
    (h_ostmtIn : HEq OStmtIn₁ OStmtIn₂)     -- Heterogeneous equality
    (h_ostmtOut : HEq OStmtOut₁ OStmtOut₂)  -- Heterogeneous equality
    -- 5. Instance Compatibility
    (h_Oₛᵢ : HEq Oₛᵢ₁ Oₛᵢ₂) :               -- Heterogeneous equality
    -- Return type uses destination types 2
    @OracleReduction ι oSpec StmtIn₂ ιₛᵢ₂ OStmtIn₂ WitIn₂ StmtOut₂ ιₛₒ₂ OStmtOut₂ WitOut₂ n pSpec
      (by exact Oₛᵢ₂) -- Use destination instance
      Oₘ := by
  -- 1. Unify Indices
  subst h_idxIn h_idxOut
  -- 2. Convert HEq to Eq for statements & instances
  simp only [heq_iff_eq] at h_ostmtIn h_ostmtOut
  -- 3. Unify Statements & Witnesses
  subst h_stmtIn h_stmtOut h_ostmtIn h_ostmtOut h_witIn h_witOut
  simp only [heq_iff_eq] at h_Oₛᵢ
  -- 4. Unify Instances
  have h_inst : Oₛᵢ₂ = Oₛᵢ₁ := h_Oₛᵢ.symm
  subst h_inst
  exact R

@[simp]
theorem castInOut_id
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {WitIn : Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    {WitOut : Type}
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
    R.castInOut rfl rfl rfl rfl rfl rfl (HEq.rfl) (HEq.rfl) (HEq.rfl) = R := rfl

/-- Cast only the output types of an OracleReduction, keeping the protocol spec and input types
    unchanged. This is useful when you need to transport outputs through type equalities without
    changing the underlying protocol structure.

    This version assumes the oracle statement index types remain the same. -/
def castOutSimple
    {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {WitIn : Type}
    {StmtOut₁ StmtOut₂ : Type}
    {ιₛₒ : Type} {OStmtOut₁ OStmtOut₂ : ιₛₒ → Type}
    [∀ i, OracleInterface (OStmtOut₁ i)] [∀ i, OracleInterface (OStmtOut₂ i)]
    {WitOut₁ WitOut₂ : Type}
    [∀ i, OracleInterface (pSpec.Message i)]
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut₁ OStmtOut₁ WitOut₁ pSpec)
    (h_stmt : StmtOut₁ = StmtOut₂)
    (h_ostmt : OStmtOut₁ = OStmtOut₂)
    (h_wit : WitOut₁ = WitOut₂) :
    OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut₂ OStmtOut₂ WitOut₂ pSpec :=
  -- Call castInOut directly with rfl for indices and inputs
  castInOut (R := R) (h_stmtIn := rfl) (h_stmtOut := h_stmt) (h_witIn := rfl) (h_witOut := h_wit)
    (h_idxIn := rfl) (h_idxOut := rfl) (h_ostmtIn := HEq.rfl) (h_ostmtOut := heq_iff_eq.mpr h_ostmt)
    (h_Oₛᵢ := HEq.rfl)

@[simp]
theorem castOutSimple_id {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    {WitIn : Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
    {WitOut : Type}
    [∀ i, OracleInterface (pSpec.Message i)]
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
    R.castOutSimple rfl rfl rfl = R := rfl

@[simp]
theorem castOutSimple_perfectCompleteness
    {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    {WitIn : Type}
    {StmtOut₁ StmtOut₂ : Type}
    {ιₛₒ : Type} {OStmtOut₁ OStmtOut₂ : ιₛₒ → Type}
    [∀ i, OracleInterface (OStmtOut₁ i)] [∀ i, OracleInterface (OStmtOut₂ i)]
    {WitOut₁ WitOut₂ : Type}
    [∀ i, OracleInterface (pSpec.Message i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
    {relOut₁ : Set ((StmtOut₁ × ∀ i, OStmtOut₁ i) × WitOut₁)}
    {relOut₂ : Set ((StmtOut₂ × ∀ i, OStmtOut₂ i) × WitOut₂)}
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut₁ OStmtOut₁ WitOut₁ pSpec)
    (h_stmt : StmtOut₁ = StmtOut₂)
    (h_ostmt : OStmtOut₁ = OStmtOut₂)
    (h_wit : WitOut₁ = WitOut₂)
    (h_rel : relOut₁ = cast (by subst_vars; rfl) relOut₂)
    (hPC : R.perfectCompleteness init impl relIn relOut₁) :
    (R.castOutSimple h_stmt h_ostmt h_wit).perfectCompleteness init impl relIn relOut₂ := by
  subst_vars
  exact hPC

@[simp]
theorem castOutSimple_completeness
    {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    {WitIn : Type}
    {StmtOut₁ StmtOut₂ : Type}
    {ιₛₒ : Type} {OStmtOut₁ OStmtOut₂ : ιₛₒ → Type}
    [∀ i, OracleInterface (OStmtOut₁ i)] [∀ i, OracleInterface (OStmtOut₂ i)]
    {WitOut₁ WitOut₂ : Type}
    [∀ i, OracleInterface (pSpec.Message i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
    {relOut₁ : Set ((StmtOut₁ × ∀ i, OStmtOut₁ i) × WitOut₁)}
    {relOut₂ : Set ((StmtOut₂ × ∀ i, OStmtOut₂ i) × WitOut₂)}
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut₁ OStmtOut₁ WitOut₁ pSpec)
    (h_stmt : StmtOut₁ = StmtOut₂)
    (h_ostmt : OStmtOut₁ = OStmtOut₂)
    (h_wit : WitOut₁ = WitOut₂)
    (ε : ℝ≥0)
    (h_rel : relOut₁ = cast (by subst_vars; rfl) relOut₂)
    (hC : R.completeness init impl relIn relOut₁ ε) :
    (R.castOutSimple h_stmt h_ostmt h_wit).completeness init impl relIn relOut₂ ε := by
  subst_vars
  exact hC

@[simp]
theorem castInOut_perfectCompleteness
    {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    -- 1. Generalized Inputs
    {StmtIn₁ StmtIn₂ : Type}
    {ιₛᵢ₁ ιₛᵢ₂ : Type} {OStmtIn₁ : ιₛᵢ₁ → Type} {OStmtIn₂ : ιₛᵢ₂ → Type}
    [Oₛᵢ₁ : ∀ i, OracleInterface (OStmtIn₁ i)]
    [Oₛᵢ₂ : ∀ i, OracleInterface (OStmtIn₂ i)]
    {WitIn₁ WitIn₂ : Type}
    -- 2. Generalized Outputs
    {StmtOut₁ StmtOut₂ : Type}
    {ιₛₒ₁ ιₛₒ₂ : Type} {OStmtOut₁ : ιₛₒ₁ → Type} {OStmtOut₂ : ιₛₒ₂ → Type}
    {WitOut₁ WitOut₂ : Type}
    -- 3. Context
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn₁ : Set ((StmtIn₁ × ∀ i, OStmtIn₁ i) × WitIn₁)}
    {relIn₂ : Set ((StmtIn₂ × ∀ i, OStmtIn₂ i) × WitIn₂)}
    {relOut₁ : Set ((StmtOut₁ × ∀ i, OStmtOut₁ i) × WitOut₁)}
    {relOut₂ : Set ((StmtOut₂ × ∀ i, OStmtOut₂ i) × WitOut₂)}
    (R : OracleReduction oSpec StmtIn₁ OStmtIn₁ WitIn₁ StmtOut₁ OStmtOut₁ WitOut₁ pSpec)
    -- 4. Equalities
    (h_stmtIn : StmtIn₁ = StmtIn₂)
    (h_stmtOut : StmtOut₁ = StmtOut₂)
    (h_witIn : WitIn₁ = WitIn₂)
    (h_witOut : WitOut₁ = WitOut₂)
    (h_idxIn : ιₛᵢ₁ = ιₛᵢ₂)
    (h_idxOut : ιₛₒ₁ = ιₛₒ₂)
    (h_ostmtIn : HEq OStmtIn₁ OStmtIn₂)
    (h_ostmtOut : HEq OStmtOut₁ OStmtOut₂)
    (h_Oₛᵢ : HEq Oₛᵢ₁ Oₛᵢ₂)
    -- 5. Relation HEqs (Must be HEq because OStmt types change)
    (h_relIn : HEq relIn₁ relIn₂)
    (h_relOut : HEq relOut₁ relOut₂)
    (hPC : R.perfectCompleteness init impl relIn₁ relOut₁) :
    -- 6. Result using destination instance Oₛᵢ₂
    OracleReduction.perfectCompleteness (ι := ι) (oSpec := oSpec) (StmtIn := StmtIn₂)
      (ιₛᵢ := ιₛᵢ₂) (OStmtIn := OStmtIn₂) (WitIn := WitIn₂) (StmtOut := StmtOut₂) (ιₛₒ := ιₛₒ₂)
      (OStmtOut := OStmtOut₂) (WitOut := WitOut₂) (n := n) (pSpec := pSpec)
      (Oₛᵢ := Oₛᵢ₂) (init := init) (impl := impl) (relIn := relIn₂) (relOut := relOut₂)
      (R.castInOut h_stmtIn h_stmtOut h_witIn h_witOut h_idxIn h_idxOut h_ostmtIn
        h_ostmtOut h_Oₛᵢ) := by
  subst_vars
  exact hPC

@[simp]
theorem castInOut_completeness
    {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    -- 1. Generalized Inputs
    {StmtIn₁ StmtIn₂ : Type}
    {ιₛᵢ₁ ιₛᵢ₂ : Type} {OStmtIn₁ : ιₛᵢ₁ → Type} {OStmtIn₂ : ιₛᵢ₂ → Type}
    [Oₛᵢ₁ : ∀ i, OracleInterface (OStmtIn₁ i)]
    [Oₛᵢ₂ : ∀ i, OracleInterface (OStmtIn₂ i)]
    {WitIn₁ WitIn₂ : Type}
    -- 2. Generalized Outputs
    {StmtOut₁ StmtOut₂ : Type}
    {ιₛₒ₁ ιₛₒ₂ : Type} {OStmtOut₁ : ιₛₒ₁ → Type} {OStmtOut₂ : ιₛₒ₂ → Type}
    {WitOut₁ WitOut₂ : Type}
    -- 3. Context
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn₁ : Set ((StmtIn₁ × ∀ i, OStmtIn₁ i) × WitIn₁)}
    {relIn₂ : Set ((StmtIn₂ × ∀ i, OStmtIn₂ i) × WitIn₂)}
    {relOut₁ : Set ((StmtOut₁ × ∀ i, OStmtOut₁ i) × WitOut₁)}
    {relOut₂ : Set ((StmtOut₂ × ∀ i, OStmtOut₂ i) × WitOut₂)}
    (R : OracleReduction oSpec StmtIn₁ OStmtIn₁ WitIn₁ StmtOut₁ OStmtOut₁ WitOut₁ pSpec)
    -- 4. Equalities
    (h_stmtIn : StmtIn₁ = StmtIn₂)
    (h_stmtOut : StmtOut₁ = StmtOut₂)
    (h_witIn : WitIn₁ = WitIn₂)
    (h_witOut : WitOut₁ = WitOut₂)
    (h_idxIn : ιₛᵢ₁ = ιₛᵢ₂)
    (h_idxOut : ιₛₒ₁ = ιₛₒ₂)
    (h_ostmtIn : HEq OStmtIn₁ OStmtIn₂)
    (h_ostmtOut : HEq OStmtOut₁ OStmtOut₂)
    (h_Oₛᵢ : HEq Oₛᵢ₁ Oₛᵢ₂)
    (ε : ℝ≥0)
    (h_relIn : HEq relIn₁ relIn₂)
    (h_relOut : HEq relOut₁ relOut₂)
    (hC : R.completeness init impl relIn₁ relOut₁ ε) :
    OracleReduction.completeness (ι := ι) (oSpec := oSpec) (StmtIn := StmtIn₂) (ιₛᵢ := ιₛᵢ₂)
      (OStmtIn := OStmtIn₂) (WitIn := WitIn₂) (StmtOut := StmtOut₂) (ιₛₒ := ιₛₒ₂)
      (OStmtOut := OStmtOut₂) (WitOut := WitOut₂) (n := n) (pSpec := pSpec) (Oₛᵢ := Oₛᵢ₂)
      (init := init) (impl := impl) (relIn := relIn₂) (relOut := relOut₂) (completenessError := ε)
      (R.castInOut h_stmtIn h_stmtOut h_witIn h_witOut h_idxIn h_idxOut h_ostmtIn
        h_ostmtOut h_Oₛᵢ) := by
  subst_vars
  exact hC

end OracleReduction

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

/-- Fully generalized cast for OracleVerifier.
    Allows changing Input/Output Statements, Indices, and Instances.
    Uses `HEq` (Heterogeneous Equality) to handle dependencies on the changing indices. -/
def castInOut
    -- 1. Input Types & Instances
    {StmtIn₁ StmtIn₂ : Type}
    {ιₛᵢ₁ ιₛᵢ₂ : Type}
    {OStmtIn₁ : ιₛᵢ₁ → Type} {OStmtIn₂ : ιₛᵢ₂ → Type}
    [Oₛᵢ₁ : ∀ i, OracleInterface (OStmtIn₁ i)]
    [Oₛᵢ₂ : ∀ i, OracleInterface (OStmtIn₂ i)]
    -- 2. Output Types
    {StmtOut₁ StmtOut₂ : Type}
    {ιₛₒ₁ ιₛₒ₂ : Type}
    {OStmtOut₁ : ιₛₒ₁ → Type} {OStmtOut₂ : ιₛₒ₂ → Type}
    -- 3. The Verifier (using source types 1)
    (V : OracleVerifier oSpec StmtIn₁ OStmtIn₁ StmtOut₁ OStmtOut₁ pSpec)
    -- 4. Equalities
    (h_stmtIn : StmtIn₁ = StmtIn₂)
    (h_stmtOut : StmtOut₁ = StmtOut₂)
    (h_idxIn : ιₛᵢ₁ = ιₛᵢ₂)           -- Index equality
    (h_idxOut : ιₛₒ₁ = ιₛₒ₂)         -- Index equality
    (h_ostmtIn : HEq OStmtIn₁ OStmtIn₂)   -- HEq required due to type change
    (h_ostmtOut : HEq OStmtOut₁ OStmtOut₂) -- HEq required due to type change
    -- 5. Instance Compatibility
    (h_Oₛᵢ : HEq Oₛᵢ₁ Oₛᵢ₂) :             -- HEq required due to type change
    -- Return type uses destination types 2
    @OracleVerifier ι oSpec StmtIn₂ ιₛᵢ₂ OStmtIn₂ StmtOut₂ ιₛₒ₂ OStmtOut₂ n pSpec
      (by exact Oₛᵢ₂) -- Use destination instance
      Oₘ := by
  -- 1. Unify Index Types
  subst h_idxIn h_idxOut
  -- 2. Convert HEq to Eq (now that types are unified)
  simp only [heq_iff_eq] at h_ostmtIn h_ostmtOut
  -- 3. Unify Statements
  subst h_stmtIn h_stmtOut h_ostmtIn h_ostmtOut
  simp only [heq_iff_eq] at h_Oₛᵢ
  -- 4. Unify Instances
  -- h_Oₛᵢ is now `Oₛᵢ₁ = Oₛᵢ₂`
  have h_inst : Oₛᵢ₂ = Oₛᵢ₁ := h_Oₛᵢ.symm
  subst h_inst
  exact V

@[simp]
theorem castInOut_id
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    V.castInOut rfl rfl rfl rfl (HEq.rfl) (HEq.rfl) (HEq.rfl) = V := rfl

theorem castInOut_rbrKnowledgeSoundness
    {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    -- 1. Generalized Inputs
    {StmtIn₁ StmtIn₂ : Type}
    {ιₛᵢ₁ ιₛᵢ₂ : Type} {OStmtIn₁ : ιₛᵢ₁ → Type} {OStmtIn₂ : ιₛᵢ₂ → Type}
    [Oₛᵢ₁ : ∀ i, OracleInterface (OStmtIn₁ i)]
    [Oₛᵢ₂ : ∀ i, OracleInterface (OStmtIn₂ i)]
    {WitIn₁ WitIn₂ : Type}
    -- 2. Generalized Outputs
    {StmtOut₁ StmtOut₂ : Type}
    {ιₛₒ₁ ιₛₒ₂ : Type} {OStmtOut₁ : ιₛₒ₁ → Type} {OStmtOut₂ : ιₛₒ₂ → Type}
    {WitOut₁ WitOut₂ : Type}
    -- 3. Context
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn₁ : Set ((StmtIn₁ × ∀ i, OStmtIn₁ i) × WitIn₁)}
    {relIn₂ : Set ((StmtIn₂ × ∀ i, OStmtIn₂ i) × WitIn₂)}
    {relOut₁ : Set ((StmtOut₁ × ∀ i, OStmtOut₁ i) × WitOut₁)}
    {relOut₂ : Set ((StmtOut₂ × ∀ i, OStmtOut₂ i) × WitOut₂)}
    (V : OracleVerifier oSpec StmtIn₁ OStmtIn₁ StmtOut₁ OStmtOut₁ pSpec)
    -- 4. Equalities
    (h_stmtIn : StmtIn₁ = StmtIn₂)
    (h_stmtOut : StmtOut₁ = StmtOut₂)
    (h_idxIn : ιₛᵢ₁ = ιₛᵢ₂)
    (h_idxOut : ιₛₒ₁ = ιₛₒ₂)
    (h_ostmtIn : HEq OStmtIn₁ OStmtIn₂)
    (h_ostmtOut : HEq OStmtOut₁ OStmtOut₂)
    (h_witIn : WitIn₁ = WitIn₂)
    (h_witOut : WitOut₁ = WitOut₂)
    (h_Oₛᵢ : HEq Oₛᵢ₁ Oₛᵢ₂)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    -- 5. Relation HEqs (Must be HEq because OStmt types change)
    (h_relIn : HEq relIn₁ relIn₂)
    (h_relOut : HEq relOut₁ relOut₂)
    (hRbrKs : V.rbrKnowledgeSoundness init impl relIn₁ relOut₁ ε) :
    -- 6. Result using destination instance Oₛᵢ₂
    OracleVerifier.rbrKnowledgeSoundness (ι := ι) (oSpec := oSpec) (StmtIn := StmtIn₂)
      (ιₛᵢ := ιₛᵢ₂) (OStmtIn := OStmtIn₂) (StmtOut := StmtOut₂) (ιₛₒ := ιₛₒ₂)
      (OStmtOut := OStmtOut₂) (n := n) (pSpec := pSpec) (WitIn := WitIn₂) (WitOut := WitOut₂)
      (Oₛᵢ := Oₛᵢ₂) (init := init) (impl := impl) (relIn := relIn₂) (relOut := relOut₂)
      (rbrKnowledgeError := ε)
      (V.castInOut h_stmtIn h_stmtOut h_idxIn h_idxOut h_ostmtIn h_ostmtOut h_Oₛᵢ) := by
  subst_vars
  exact hRbrKs

/-- Cast only the output types of an OracleVerifier. -/
def castOutSimple
    {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    {StmtOut₁ StmtOut₂ : Type}
    {ιₛₒ : Type} {OStmtOut₁ OStmtOut₂ : ιₛₒ → Type}
    [∀ i, OracleInterface (OStmtOut₁ i)] [∀ i, OracleInterface (OStmtOut₂ i)]
    [∀ i, OracleInterface (pSpec.Message i)]
    (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut₁ OStmtOut₁ pSpec)
    (h_stmt : StmtOut₁ = StmtOut₂)
    (h_ostmt : OStmtOut₁ = OStmtOut₂) :
    OracleVerifier oSpec StmtIn OStmtIn StmtOut₂ OStmtOut₂ pSpec := by
  subst h_stmt h_ostmt
  exact V

@[simp]
theorem castOutSimple_id
    {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
    [∀ i, OracleInterface (pSpec.Message i)]
    (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    V.castOutSimple rfl rfl = V := rfl

theorem castOutSimple_rbrKnowledgeSoundness
    {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    {WitIn : Type}
    {StmtOut₁ StmtOut₂ : Type}
    {ιₛₒ : Type} {OStmtOut₁ OStmtOut₂ : ιₛₒ → Type}
    [∀ i, OracleInterface (OStmtOut₁ i)] [∀ i, OracleInterface (OStmtOut₂ i)]
    {WitOut₁ WitOut₂ : Type}
    [∀ i, OracleInterface (pSpec.Message i)]
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
    {relOut₁ : Set ((StmtOut₁ × ∀ i, OStmtOut₁ i) × WitOut₁)}
    {relOut₂ : Set ((StmtOut₂ × ∀ i, OStmtOut₂ i) × WitOut₂)}
    (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut₁ OStmtOut₁ pSpec)
    (h_stmt : StmtOut₁ = StmtOut₂)
    (h_ostmt : OStmtOut₁ = OStmtOut₂)
    (h_wit : WitOut₁ = WitOut₂)
    (ε : pSpec.ChallengeIdx → ℝ≥0)
    (h_rel : relOut₁ = cast (by subst_vars; rfl) relOut₂)
    (hRbrKs : V.rbrKnowledgeSoundness init impl relIn relOut₁ ε) :
    (V.castOutSimple h_stmt h_ostmt).rbrKnowledgeSoundness init impl relIn relOut₂ ε := by
  subst_vars
  exact hRbrKs

end OracleVerifier

#print axioms OracleReduction.castInOut_perfectCompleteness
#print axioms OracleReduction.castInOut_completeness
#print axioms OracleReduction.castOutSimple_perfectCompleteness
#print axioms OracleReduction.castOutSimple_completeness
#print axioms OracleVerifier.castInOut_rbrKnowledgeSoundness
#print axioms OracleVerifier.castOutSimple_rbrKnowledgeSoundness
