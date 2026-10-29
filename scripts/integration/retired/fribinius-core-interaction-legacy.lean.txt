/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase
import ArkLib.ProofSystem.Binius.BinaryBasefold.ExtractMLPCorrectness
import ArkLib.ProofSystem.Binius.BinaryBasefold.FinalRelation
import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ArkLib.ProofSystem.Binius.FRIBinius.Prelude
import ArkLib.OracleReduction.LiftContext.Coherence

/-!
# Core Interaction Phase of FRI-Binius IOPCS
This module implements the Core Interaction Phase of the FRI-Binius IOPCS.

This phase combines sumcheck and FRI folding using shared challenges r'ᵢ:

6. `P` and `V` both abbreviate `f^(0) := f`, and execute the following loop:
   for `i ∈ {0, ..., ℓ' - 1}` do
     `P` sends `V` the polynomial
        `h_i(X) := Σ_{w ∈ {0,1}^{ℓ'-i-1}} h(r_0', ..., r_{i-1}', X, w_0, ..., w_{ℓ'-i-2})`.
     `V` requires `s_i ?= h_i(0) + h_i(1)`. `V` samples `r_i' ← T_τ`, sets `s_{i+1} := h_i(r_i')`,
     and sends `P` `r_i'`.
     `P` defines `f^(i+1): S^(i+1) → T_τ` as the function `fold(f^(i), r_i')` of Definition 4.6.
     if `i + 1 = ℓ'` then `P` sends `c := f^(ℓ')(0, ..., 0)` to `V`.
     else if `ϑ | i + 1` then `P` submits `(submit, ℓ' + R - i - 1, f^(i+1))` to the oracle.
7. `P` sends `c := f^(ℓ')(0, ..., 0)` to `V`.
  `V` sets `e := eqTilde(φ_0(r_κ), ..., φ_0(r_{ℓ-1}), φ_1(r'_0), ..., φ_1(r'_{ℓ'-1}))`
    and decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`.
  `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eqTilde(u_0, ..., u_{κ-1},`
                                  `r''_0, ..., r''_{κ-1}) * e_u) * c`.

## Oracle reduction composition

Inside this file, `coreInteractionOracleReduction` is exactly the composition of:
1. `LiftContext(sumcheckFoldOracleReduction)` (the lifted Binary
  Basefold sumcheck-fold reduction), then
2. `finalSumcheckOracleReduction`.

`LiftContext` here is only the bridge from batching-output shape to Binary Basefold sumcheck-fold
input shape. Concretely, it maps
`SumcheckWitness (t', H)` to `BinaryBasefold.Witness (t, H, f₀)`, where
`f₀ := getMidCodewords t challenges`, and keeps the output witness unchanged (`toFunB` is
identity on `innerWitOut`).
-/

set_option linter.style.longFile 1700

set_option backward.isDefEq.respectTransparency false

namespace Binius.FRIBinius.CoreInteractionPhase
noncomputable section

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial TensorProduct Module Binius.BinaryBasefold RingSwitching
open scoped NNReal

-- Future work: how to make params cleaner while can explicitly reuse across sections?
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

section SumcheckFold

/-- Statement lens that projects SumcheckStmt to BinaryBasefold.Statement and lifts back -/
def sumcheckFoldStmtLens : OracleStatement.Lens
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ')) where
  -- Stmt and OStmt are same as in outer context, only witness changes
  toFunA := fun ⟨outerStmtIn, outerOStmtIn⟩ => ⟨outerStmtIn, outerOStmtIn⟩
  toFunB := fun ⟨_, _⟩ ⟨innerStmtOut, innerOStmtOut⟩ => ⟨innerStmtOut, innerOStmtOut⟩

/-- Oracle context lens for sumcheck fold lifting -/
def sumcheckFoldCtxLens : OracleContext.Lens
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (OuterWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (InnerWitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') 0)
    (InnerWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ')) where
  wit := {
    toFunA := fun ⟨⟨outerStmtIn, outerOStmtIn⟩, outerWitIn⟩ => by
      let t : L⦃≤ 1⦄[X Fin ℓ'] := outerWitIn.t'
      let H : L⦃≤ 2⦄[X Fin (ℓ' - 0)] := outerWitIn.H
      let f₀ : (sDomain K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        ⟨0, by omega⟩ → L :=
        BinaryBasefold.getMidCodewords K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (0 : Fin (ℓ' + 1))) (t := t) (challenges := outerStmtIn.challenges)
      exact { t := t, H := H, f := f₀ }
    toFunB := fun ⟨⟨outerStmtIn, outerOStmtIn⟩, outerWitIn⟩
      ⟨⟨innerStmtOut, innerOStmtOut⟩, innerWitOut⟩ => innerWitOut
  }
  stmt := sumcheckFoldStmtLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

/-- Extractor lens for sumcheck fold lifting -/
def sumcheckFoldExtractorLens : Extractor.Lens
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0 ×
      (∀ j, OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j))
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ')
      ×(∀ j, OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0 ×
      (∀ j, OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j))
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ')
      × (∀ j, OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j))
    (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (OuterWitOut := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ℓ:=ℓ') (Fin.last ℓ'))
    (InnerWitIn := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') 0)
    (InnerWitOut := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ')) where
  stmt := sumcheckFoldStmtLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  wit := {
    toFunA := fun ⟨⟨outerStmtIn, outerOStmtIn⟩, outerWitOut⟩ => outerWitOut
    toFunB := fun ⟨⟨outerStmtIn, outerOStmtIn⟩, outerWitOut⟩ innerWitIn => by
      let outerWitIn : SumcheckWitness L ℓ' 0 := {
        t' := innerWitIn.t
        H := innerWitIn.H
      }
      exact outerWitIn
  }

/-- Identity statement and query routing, preserving the inner output-oracle embedding. -/
def sumcheckFoldOracleLens : OracleStatement.OracleLens []ₒ
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec := BinaryBasefold.pSpecSumcheckFold K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  toLens := sumcheckFoldStmtLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate
  projStmt := id
  liftStmt := fun _ s => s
  simOStmt := fun q => ReaderT.mk fun _ =>
    OracleComp.lift (OracleSpec.query q)
  embedOStmt := (BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier K β (ϑ := ϑ)
    (mp := RingSwitching_SumcheckMultParam κ L K (ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
    (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).embed
  hEqOStmt := (BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier K β (ϑ := ϑ)
    (mp := RingSwitching_SumcheckMultParam κ L K (ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
    (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).hEq

/-- The identity router agrees with the value-level context lens. -/
instance sumcheckFoldOracleLens_coherent :
    OracleVerifier.LiftContextCoherent
      (sumcheckFoldOracleLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
      (BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier K β (ϑ := ϑ)
        (mp := RingSwitching_SumcheckMultParam κ L K
          (ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
        (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  apply OracleVerifier.LiftContext.liftContextCoherent_of
  · intros; rfl
  · intro os oos tr q
    change simulateQ _ (OracleComp.lift (OracleSpec.query (Sum.inr (Sum.inl q)))) = _
    simp [sumcheckFoldOracleLens, sumcheckFoldStmtLens, OracleComp.lift,
      OracleInterface.simOracle2, QueryImpl.addLift, QueryImpl.add]
  · intros; rfl

/-- The reduction carries its own output embedding through context lifting. -/
def sumcheckFoldReductionOracleLens :=
  { sumcheckFoldOracleLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑) with
    embedOStmt := (BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction K β (ϑ := ϑ)
      (mp := RingSwitching_SumcheckMultParam κ L K (ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
      (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).verifier.embed
    hEqOStmt := (BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction K β (ϑ := ϑ)
      (mp := RingSwitching_SumcheckMultParam κ L K (ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
      (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).verifier.hEq }

instance sumcheckFoldReductionOracleLens_coherent :
    OracleVerifier.LiftContextCoherent
      (sumcheckFoldReductionOracleLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
      (BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction K β (ϑ := ϑ)
        (mp := RingSwitching_SumcheckMultParam κ L K
          (ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
        (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).verifier := by
  apply OracleVerifier.LiftContext.liftContextCoherent_of
  · intros; rfl
  · intro os oos tr q
    change simulateQ _ (OracleComp.lift (OracleSpec.query (Sum.inr (Sum.inl q)))) = _
    simp [sumcheckFoldReductionOracleLens, sumcheckFoldOracleLens, sumcheckFoldStmtLens,
      OracleComp.lift, OracleInterface.simOracle2, QueryImpl.addLift, QueryImpl.add]
  · intros; rfl

-- The lifted oracle verifier
def sumcheckFoldOracleVerifier :=
  (BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier K β (ϑ:=ϑ)
    (mp := RingSwitching_SumcheckMultParam κ L K (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
    (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).liftContext
      (lens := sumcheckFoldOracleLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))

-- The lifted oracle reduction
def sumcheckFoldOracleReduction :=
  (BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction K β (ϑ:=ϑ)
    (mp := RingSwitching_SumcheckMultParam κ L K (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).liftContext
      (lens := sumcheckFoldCtxLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
      (stmtLens := sumcheckFoldReductionOracleLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))

/-- Context lifting preserves the inner output-oracle interface coherence. -/
instance sumcheckFoldVerifier_appendCoherent :
    OracleVerifier.Append.AppendCoherent (sumcheckFoldOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)) := by
  let base := BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier K β (ϑ := ϑ)
    (mp := RingSwitching_SumcheckMultParam κ L K (ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
    (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let coh : OracleVerifier.Append.AppendCoherent (base) := inferInstance
  exact ⟨coh.hCohInl, coh.hCohInr⟩

/-- Context lifting preserves the inner output-oracle interface coherence. -/
instance sumcheckFoldReduction_appendCoherent :
    OracleVerifier.Append.AppendCoherent ((sumcheckFoldOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)).verifier) := by
  let base := BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction K β (ϑ := ϑ)
    (mp := RingSwitching_SumcheckMultParam κ L K (ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
    (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let coh : OracleVerifier.Append.AppendCoherent (base.verifier) := inferInstance
  exact ⟨coh.hCohInl, coh.hCohInr⟩

/-- The completeness input relation requires exact initial oracle agreement, in addition to
sumcheck consistency and the ring-switching witness invariant. -/
def strictSumcheckInputRelation :
    Set ((Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0 ×
      (∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j)) × RingSwitching.SumcheckWitness L ℓ' 0) :=
  { x | BinaryBasefold.sumcheckConsistencyProp (𝓑 := 𝓑) x.1.1.sumcheck_target x.2.H ∧
    RingSwitching.witnessStructuralInvariant κ L K (ringSwitchingProfile κ L K β)
      ℓ ℓ' h_l x.1.1 x.2 ∧
    BinaryBasefold.strictOracleFoldingConsistencyProp K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t := x.2.t') (i := 0) (challenges := Fin.elim0) (oStmt := x.1.2) }

-- Security properties for the lifted oracle reduction

section Security

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

-- Completeness instance for the context lens
instance sumcheckFoldCtxLens_complete :
  (sumcheckFoldCtxLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    h_l).toContext.IsComplete
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0 ×
      (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 i))
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ') ×
      (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ') i))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0 ×
      (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 i))
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ') ×
      (∀ i, BinaryBasefold.OracleStatement K (⇑β) ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ') i))
    (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (OuterWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (InnerWitIn := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') 0)
    (InnerWitOut := Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (outerRelIn := strictSumcheckInputRelation κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    (outerRelOut :=
      BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ')
    )
    (innerRelIn :=
      BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0
    )
    (innerRelOut :=
      BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ')
    )
    (compat :=
      let originalReduction := (CoreInteraction.sumcheckFoldOracleReduction K β (ϑ:=ϑ)
        (mp := RingSwitching_SumcheckMultParam κ L K (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).toReduction
      Reduction.compatContext (oSpec := []ₒ) (pSpec :=
        pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (sumcheckFoldCtxLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l).toContext originalReduction
    ) where
  proj_complete := fun stmtIn oStmtIn hRelIn => by
    rcases stmtIn with ⟨stmtIn, oStmtIn'⟩
    rcases oStmtIn with ⟨t', H⟩
    rcases hRelIn with ⟨h_local, h_struct, h_strict_compat⟩
    refine ⟨?_, ?_⟩
    · dsimp [sumcheckFoldStmtLens] at h_local ⊢
      exact h_local
    · refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · dsimp [sumcheckFoldStmtLens, RingSwitching.witnessStructuralInvariant,
            BinaryBasefold.witnessStructuralInvariant] at h_struct ⊢
          exact h_struct
        · rfl
      · dsimp [sumcheckFoldCtxLens, sumcheckFoldStmtLens]
        convert h_strict_compat using 1 <;> congr 1
        funext i
        exact Fin.elim0 i
  lift_complete := fun outerStmtIn outerWitIn innerStmtOut innerWitOut compat => by
    intro _ hRelOut
    dsimp [sumcheckFoldStmtLens] at hRelOut ⊢
    exact hRelOut

-- Perfect completeness for the lifted oracle reduction
theorem sumcheckFoldOracleReduction_perfectCompleteness (hInit : NeverFail init)
    (hBinaryBasefoldSumcheckFoldPerfectCompleteness :
      OracleReduction.perfectCompleteness
        (pSpec := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (relIn := BinaryBasefold.strictRoundRelation
          (mp := RingSwitching_SumcheckMultParam κ L K
            (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
        (relOut := BinaryBasefold.strictRoundRelation
          (mp := RingSwitching_SumcheckMultParam κ L K
            (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ'))
        (oracleReduction := BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction K β
          (ϑ:=ϑ) (mp := RingSwitching_SumcheckMultParam κ L K
            (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑))
        (init := init)
        (impl := impl)) :
    OracleReduction.perfectCompleteness
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
    (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (WitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (pSpec := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relIn := strictSumcheckInputRelation κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    (relOut :=
      BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ')
    )
    (oracleReduction := sumcheckFoldOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑 := 𝓑))
    (init := init)
    (impl := impl) :=
  OracleReduction.liftContext_perfectCompleteness
    (oSpec := []ₒ)
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (OuterWitIn := RingSwitching.SumcheckWitness L ℓ' 0)
    (OuterWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (InnerWitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') 0)
    (InnerWitOut := BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (outerRelIn := strictSumcheckInputRelation κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    (outerRelOut := BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
      (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ'))
    (innerRelIn := BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
      (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
    (innerRelOut := BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
      (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ'))
    (lens := sumcheckFoldCtxLens κ L K β ℓ ℓ' 𝓡 ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
    (stmtLens := sumcheckFoldReductionOracleLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    (hStmt := rfl)
    (lensComplete := sumcheckFoldCtxLens_complete κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
    (init := init)
    (impl := impl)
    (h := BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction_perfectCompleteness
      (hInit:=hInit) K β (ϑ := ϑ)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (hSumcheckFoldPerfectCompleteness := hBinaryBasefoldSumcheckFoldPerfectCompleteness))

/-- The current BinaryBasefold input relation does not imply the ring-switching input
relation: its unfinished-block bad-event branch is already true at round zero. In particular,
the zero witness with a claimed sum of one is admitted by the former and rejected by the latter.
This refutes the previously attempted unconditional extractor-lens bridge. -/
theorem sumcheckFold_input_bridge_counterexample :
    ∃ (stmt : Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
      (oStmt : ∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j)
      (wit : BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') 0),
      BinaryBasefold.roundRelation
        (mp := RingSwitching_SumcheckMultParam κ L K (ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
        K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0 ((stmt, oStmt), wit) ∧
      ¬ RingSwitching.sumcheckRoundRelation κ L K (ringSwitchingProfile κ L K β) ℓ ℓ' h_l
        (BinaryBasefoldAbstractOStmtIn (β := β) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0
        ((stmt, oStmt), { t' := wit.t, H := wit.H }) := by
  let stmt : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0 := {
    ctx := { t_eval_point := 0, original_claim := 0, s_hat := 0, r_batching := 0 }
    sumcheck_target := 1
    challenges := Fin.elim0 }
  let oStmt : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j := fun _ _ => 0
  let wit : BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') 0 := {
    t := 0, H := 0, f := fun _ => 0 }
  refine ⟨stmt, oStmt, wit, ?_, ?_⟩
  · apply Or.inl
    exact BinaryBasefold.badEventExistsProp_of_lt K β 0 0 oStmt _
      (by simpa using Nat.pos_of_neZero ℓ') rfl
  · intro h
    have hsum := h.2.1
    change (1 : L) = ∑ x ∈ (boolDomain L ℓ').cube,
      MvPolynomial.eval x (0 : MvPolynomial (Fin ℓ') L) at hsum
    have hzero : ∑ x ∈ (boolDomain L ℓ').cube,
        MvPolynomial.eval x (0 : MvPolynomial (Fin ℓ') L) = (0 : L) := by
      apply Finset.sum_eq_zero
      intro x _
      exact map_zero (MvPolynomial.eval₂Hom (RingHom.id L) x)
    exact one_ne_zero (hsum.trans hzero)

end Security
end SumcheckFold

section FinalSumcheckStep
/-!
## Final Sumcheck Step
-/

/-! ## Pure Logic Functions (ReductionLogicStep Infrastructure) -/

/-- Pure verifier check for FRI final sumcheck step. -/
@[reducible]
def finalSumcheckVerifierCheck
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (c : L) : Prop :=
  let eq_tilde_eval : L := RingSwitching.compute_final_eq_value κ L K
    (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l
    stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
  stmtIn.sumcheck_target = eq_tilde_eval * c

/-- Pure verifier output for FRI final sumcheck step. -/
@[reducible]
def finalSumcheckVerifierStmtOut
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (c : L) : BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ') := {
      ctx := {
        t_eval_point := getEvaluationPointSuffix κ L ℓ ℓ' h_l stmtIn.ctx.t_eval_point
        original_claim := stmtIn.ctx.original_claim
      }
      sumcheck_target := stmtIn.sumcheck_target
      challenges := stmtIn.challenges
      final_constant := c
    }

/-- Pure prover message computation for FRI final sumcheck step. -/
@[reducible]
def finalSumcheckProverComputeMsg
    (witIn : BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ')) : L :=
  witIn.f ⟨0, by simp only [zero_mem]⟩

/-- Pure prover output witness for FRI final sumcheck step. -/
@[reducible]
def finalSumcheckProverWitOut : Unit := ()

/-! ## ReductionLogicStep Instance -/

/-- The logic instance for the FRI final sumcheck step. -/
def finalSumcheckStepLogic :
    Binius.BinaryBasefold.CoreInteraction.ReductionLogicStep
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
      (BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
      (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
      Unit
      (BinaryBasefold.pSpecFinalSumcheckStep (L := L)) where
  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ BinaryBasefold.strictRoundRelation
      (mp := RingSwitching_SumcheckMultParam κ L K
      (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l) K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (Fin.last ℓ')
  completeness_relOut := fun ((stmtOut, oStmtOut), witOut) =>
    ((stmtOut, oStmtOut), witOut) ∈ BinaryBasefold.strictFinalSumcheckRelOut K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  verifierCheck := fun stmtIn transcript =>
    finalSumcheckVerifierCheck κ L K β ℓ ℓ' h_l stmtIn (transcript.messages ⟨0, rfl⟩)
  verifierOut := fun stmtIn transcript =>
    finalSumcheckVerifierStmtOut κ L K β ℓ ℓ' h_l stmtIn (transcript.messages ⟨0, rfl⟩)
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl
  honestProverTranscript := fun _stmtIn witIn _oStmtIn _chal =>
    let c : L := finalSumcheckProverComputeMsg (κ := κ) (L := L) (K := K) (β := β)
      (ℓ' := ℓ') (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn
    FullTranscript.mk1 c
  proverOut := fun stmtIn _witIn oStmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    let stmtOut := finalSumcheckVerifierStmtOut κ L K β ℓ ℓ' h_l stmtIn c
    ((stmtOut, oStmtIn), ())

/-- The prover for the final sumcheck step -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (OStmtIn := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitOut := Unit)
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L)) where
  PrvState := fun
    | 0 => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ')
      × (∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
      × BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ')
    | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ') ×
      (∀ j, BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
      × BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ') × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)
  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    let c : L := finalSumcheckProverComputeMsg (κ := κ) (L := L) (K := K) (β := β)
      (ℓ' := ℓ') (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn
    pure ⟨c, (stmtIn, oStmtIn, witIn, c)⟩
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step
  output := fun ⟨stmtIn, oStmtIn, witIn, s'⟩ => do
    let logic := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
    let t := FullTranscript.mk1 (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L := L)) s'
    pure (logic.proverOut stmtIn witIn oStmtIn t)

/-- The verifier for the final sumcheck step -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (OStmtIn := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L)) where
  verify := fun stmtIn _ => do
    let s' : L ← liftM (OracleSpec.query (spec := [(BinaryBasefold.pSpecFinalSumcheckStep
      (L:=L)).Message]ₒ) ⟨⟨0, by rfl⟩, (by exact ())⟩)
    let t := FullTranscript.mk1 (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L := L)) s'
    let logic := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
    have : Decidable (logic.verifierCheck stmtIn t) := Classical.propDecidable _
    guard (logic.verifierCheck stmtIn t)
    pure (logic.verifierOut stmtIn t)
  embed := (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
    (𝓑 := 𝓑)).embed
  hEq := (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
    (𝓑 := 𝓑)).hEq

/-- The final step preserves every input oracle interface. -/
instance finalSumcheckVerifier_appendCoherent :
    OracleVerifier.Append.AppendCoherent
      (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)) where
  hCohInl a k h := by
    have hak : a = k := by
      simpa only [finalSumcheckVerifier, finalSumcheckStepLogic,
        Function.Embedding.coeFn_mk, Sum.inl.injEq] using h
    subst k
    rfl
  hCohInr a k h := by
    simp only [finalSumcheckVerifier, finalSumcheckStepLogic,
      Function.Embedding.coeFn_mk, reduceCtorEq] at h

/-- The oracle reduction for the final sumcheck step -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (OStmtIn := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (StmtOut := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (WitOut := Unit)
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L)) where
  prover := finalSumcheckProver κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
  verifier := finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)

/-- The reduction inherits the final verifier's output-oracle coherence. -/
instance finalSumcheckOracleReduction_appendCoherent :
    OracleVerifier.Append.AppendCoherent
      (finalSumcheckOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)).verifier :=
  finalSumcheckVerifier_appendCoherent κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l

omit [Fintype L] [DecidableEq L] [CharP L 2] [SampleableType L] [NeZero ℓ'] in
/-- At `Fin.last ℓ'`, sumcheck consistency simplifies to a single evaluation. -/
lemma sumcheckConsistency_at_last_simplifies
    (target : L) (H : L⦃≤ 2⦄[X Fin (ℓ' - Fin.last ℓ')])
    (h_cons : BinaryBasefold.sumcheckConsistencyProp (𝓑 := 𝓑) target H) :
    target = H.val.eval (fun _ => (0 : L)) := by
  simp only [Fin.val_last] at H h_cons ⊢
  simp only [BinaryBasefold.sumcheckConsistencyProp] at h_cons
  haveI : IsEmpty (Fin 0) := Fin.isEmpty
  rw [Finset.sum_eq_single (a := fun _ => 0)
    (h₀ := fun b _ hb_ne => by
      exfalso
      apply hb_ne
      funext i
      simp only [tsub_self] at i
      exact i.elim0)
    (h₁ := fun h_not_mem => by
      exfalso
      apply h_not_mem
      simp only [Fintype.mem_piFinset]
      intro i
      simp only [tsub_self] at i
      exact i.elim0)] at h_cons
  exact h_cons

/-- With no variables remaining, the projected sumcheck polynomial is constant. -/
private lemma projectToMidSumcheckPoly_at_last_eq
    (t m : MultilinearPoly L ℓ') (challenges : Fin (Fin.last ℓ') → L) :
    (Sumcheck.Structured.projectToMidSumcheckPoly ℓ' t m (Fin.last ℓ') challenges).val =
      MvPolynomial.C (m.val.eval challenges * t.val.eval challenges) := by
  haveI : IsEmpty (Fin (ℓ' - (Fin.last ℓ').val)) := ⟨by intro i; have := i.isLt; simp at this⟩
  have h := Sumcheck.Structured.projectToMidSumcheckPoly_at_last_eval ℓ' t m challenges
  have hp := MvPolynomial.eq_C_of_isEmpty
    (Sumcheck.Structured.projectToMidSumcheckPoly ℓ' t m (Fin.last ℓ') challenges).val
  rw [hp] at h ⊢
  simpa only [MvPolynomial.eval_C] using congrArg MvPolynomial.C h

omit [NeZero ℓ] in
/-- The final codeword value at `0` equals `t(challenges)`. -/
lemma finalCodeword_zero_eq_t_eval
    (stmtIn : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (witIn : BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (h_wit_struct : BinaryBasefold.witnessStructuralInvariant K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
      (stmt := stmtIn) (wit := witIn)) :
    witIn.f ⟨0, by simp only [zero_mem]⟩ = witIn.t.val.eval stmtIn.challenges := by
  rw [h_wit_struct.2]
  exact BinaryBasefold.getMidCodewords_last_zero_eq_eval K β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn.t stmtIn.challenges

omit [NeZero ℓ] in
/-- Strict helper: folding the last oracle block in the final sumcheck step yields
the constant function equal to the prover message `witIn.f(0)`. -/
lemma iterated_fold_to_const_strict
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (witIn : BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (oStmtIn : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
    (h_strictOracleWitConsistency_In : BinaryBasefold.strictOracleWitnessConsistency K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Context := RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β))
      (mp := RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
      (stmtIdx := Fin.last ℓ')
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ'))
      (stmt := stmtIn) (wit := witIn) (oStmt := oStmtIn)) :
    let c : L := witIn.f ⟨0, by simp only [zero_mem]⟩
    let lastDomainIdx := getLastOracleDomainIndex ℓ' ϑ (Fin.last ℓ')
    let k := lastDomainIdx.val
    have h_k : k = ℓ' - ϑ := by
      dsimp only [k, lastDomainIdx]
      rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
        Nat.div_mul_cancel (hdiv.out)]
    let curDomainIdx : Fin (2 ^ κ) := ⟨k, by
      rw [h_k]
      omega
    ⟩
    have h_destIdx_eq : curDomainIdx.val = lastDomainIdx.val := rfl
    let f_k : OracleFunction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) curDomainIdx :=
      getLastOracle (h_destIdx := h_destIdx_eq) (oracleFrontierIdx := Fin.last ℓ')
        K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn)
    let finalChallenges : Fin ϑ → L := fun cId => foldOrderChallenges stmtIn.challenges ⟨k + cId, by
      rw [h_k]
      have h_le : ϑ ≤ ℓ' := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ') (hdiv.out)
      have h_cId : cId.val < ϑ := cId.isLt
      have h_last : (Fin.last ℓ').val = ℓ' := rfl
      omega
    ⟩
    let destDomainIdx : Fin (2 ^ κ) := ⟨k + ϑ, by
      rw [h_k]
      have h_le : ϑ ≤ ℓ' := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ') (hdiv.out)
      omega
    ⟩
    let folded := iterated_fold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := curDomainIdx) (steps := ϑ) (destIdx := destDomainIdx) (h_destIdx := by rfl)
      (h_destIdx_le := by
        dsimp only [destDomainIdx, k, lastDomainIdx]
        rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul,
          Nat.div_mul_cancel (hdiv.out)]
        rw [Nat.sub_add_cancel (by
          exact Nat.le_of_dvd (h := by exact Nat.pos_of_neZero ℓ') (hdiv.out))]
      ) (f := f_k)
      (r_challenges := finalChallenges)
    ∀ y, folded y = c := by
  intro c lastDomainIdx k h_k curDomainIdx h_destIdx_eq f_k finalChallenges destDomainIdx folded y
  have hϑℓ : ϑ ≤ ℓ' := Nat.le_of_dvd (Nat.pos_of_neZero ℓ') hdiv.out
  have h_oracle : BinaryBasefold.strictOracleFoldingConsistencyProp K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := witIn.t) (i := Fin.last ℓ')
      (challenges := stmtIn.challenges) (oStmt := oStmtIn) := by
    simpa [strictOracleWitnessConsistency, olderStmtChallenges_self] using
      h_strictOracleWitConsistency_In.2
  have h_final := BinaryBasefold.getLastOracle_finalFold_eq_eval' K β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (t := witIn.t)
    (challenges := stmtIn.challenges) (oStmt := oStmtIn) h_oracle
    (curIdx := curDomainIdx) (destIdx := destDomainIdx)
    (hcur := h_k) (hdest := rfl)
    (hdest_le := by dsimp only [destDomainIdx]; omega)
    (h_destIdx_oracle := h_destIdx_eq) (hpos := by omega)
    (rchal := finalChallenges) (hrchal := rfl) (y := y)
  exact h_final.trans (finalCodeword_zero_eq_t_eval κ L K β ℓ ℓ' 𝓡
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l stmtIn witIn
    h_strictOracleWitConsistency_In.1).symm

omit [CharP L 2] [SampleableType L] [DecidableEq K] h_β₀_eq_1 [NeZero ℓ] in
/-- Honest prover message in final sumcheck equals `witIn.f(0)`. -/
lemma finalSumcheck_honest_message_eq_f_zero
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (witIn : BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (oStmtIn : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
    (challenges : (BinaryBasefold.pSpecFinalSumcheckStep (L := L)).Challenges) :
    let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    transcript.messages ⟨0, rfl⟩ = witIn.f ⟨0, by simp only [zero_mem]⟩ := by
  simp only [finalSumcheckStepLogic, finalSumcheckProverComputeMsg]

/-- Verifier check passes in the FRI final sumcheck logic step. -/
lemma finalSumcheckStep_verifierCheck_passed
    (stmtIn : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (witIn : BinaryBasefold.Witness K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
    (oStmtIn : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
    (challenges : (BinaryBasefold.pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_sumcheck_cons : BinaryBasefold.sumcheckConsistencyProp
      (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H)
    (h_wit_struct : BinaryBasefold.witnessStructuralInvariant K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
      (stmt := stmtIn) (wit := witIn)) :
    let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
    let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
    step.verifierCheck stmtIn transcript := by
  intro step transcript
  have h_target_eq_H_eval :
      stmtIn.sumcheck_target = witIn.H.val.eval (fun _ => (0 : L)) :=
    sumcheckConsistency_at_last_simplifies (L := L) (ℓ' := ℓ') (𝓑 := 𝓑)
      stmtIn.sumcheck_target witIn.H h_sumcheck_cons
  have h_proj_eval :
      (BinaryBasefold.projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witIn.t)
        (m := (RingSwitching_SumcheckMultParam κ L K
          (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx)
        (i := Fin.last ℓ') (challenges := stmtIn.challenges)).val.eval (fun _ => (0 : L)) =
      ((RingSwitching_SumcheckMultParam κ L K
          (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval
        stmtIn.challenges * witIn.t.val.eval stmtIn.challenges := by
    apply Sumcheck.Structured.projectToMidSumcheckPoly_at_last_eval
  have h_mult_eq_eq_value :
      ((RingSwitching_SumcheckMultParam κ L K
          (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval
        stmtIn.challenges =
      RingSwitching.compute_final_eq_value κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l
        stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching :=
    RingSwitching.A_MLE_eval_eq_compute_final_eq_value
      (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l
      stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
  have h_c_eq : witIn.f ⟨0, by simp only [zero_mem]⟩ = witIn.t.val.eval stmtIn.challenges := by
    exact finalCodeword_zero_eq_t_eval (κ := κ) (L := L) (K := K) (β := β)
      (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
      stmtIn witIn h_wit_struct
  let cmsg : L := transcript.messages ⟨0, rfl⟩
  have h_msg_eq : cmsg = witIn.f ⟨0, by simp only [zero_mem]⟩ :=
    finalSumcheck_honest_message_eq_f_zero (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
      (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
      (𝓑 := 𝓑) stmtIn witIn oStmtIn challenges
  have h_eq : stmtIn.sumcheck_target = RingSwitching.compute_final_eq_value κ L K
      (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l
      stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
      cmsg := by
    calc
      stmtIn.sumcheck_target
          = witIn.H.val.eval (fun _ => (0 : L)) := h_target_eq_H_eval
      _ = (BinaryBasefold.projectToMidSumcheckPoly (L := L) (ℓ := ℓ') (t := witIn.t)
            (m := (RingSwitching_SumcheckMultParam κ L K
              (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx)
            (i := Fin.last ℓ') (challenges := stmtIn.challenges)).val.eval (fun _ => (0 : L)) := by
            rw [h_wit_struct.1]
      _ = ((RingSwitching_SumcheckMultParam κ L K
            (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val.eval
            stmtIn.challenges * witIn.t.val.eval stmtIn.challenges := h_proj_eval
      _ = RingSwitching.compute_final_eq_value κ L K
            (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l
            stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
            witIn.t.val.eval stmtIn.challenges := by
            rw [h_mult_eq_eq_value]
      _ = RingSwitching.compute_final_eq_value κ L K
            (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l
            stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
            witIn.f ⟨0, by simp only [zero_mem]⟩ := by
            rw [h_c_eq]
      _ = RingSwitching.compute_final_eq_value κ L K
            (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l
            stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
            cmsg := by
            rw [←h_msg_eq]
  dsimp [step, finalSumcheckStepLogic, finalSumcheckVerifierCheck, cmsg] at h_eq ⊢
  exact h_eq

/-- Strong completeness of the FRI final sumcheck logic step. -/
lemma finalSumcheckStep_is_logic_complete :
    (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
  let transcript := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  simp only [finalSumcheckStepLogic, BinaryBasefold.strictRoundRelation,
    BinaryBasefold.strictRoundRelationProp, Set.mem_setOf_eq] at h_relIn
  obtain ⟨h_sumcheck_cons, h_strictOracleWitConsistency⟩ := h_relIn
  have h_wit_struct := h_strictOracleWitConsistency.1
  let h_VCheck_passed : step.verifierCheck stmtIn transcript :=
    finalSumcheckStep_verifierCheck_passed (κ := κ) (L := L) (K := K) (β := β)
      (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_l := h_l) (𝓑 := 𝓑) stmtIn witIn oStmtIn challenges h_sumcheck_cons h_wit_struct
  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, finalSumcheckStepLogic, finalSumcheckVerifierStmtOut]
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by rfl
  have hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    simp only [step, finalSumcheckStepLogic]
    refine ⟨witIn.t, ?_⟩
    unfold BinaryBasefold.strictfinalSumcheckStepFoldingStateProp
    dsimp only [finalSumcheckVerifierStmtOut]
    constructor
    · simpa [strictOracleWitnessConsistency, olderStmtChallenges_self,
        verifierStmtOut, verifierOStmtOut, transcript, step, finalSumcheckStepLogic,
        finalSumcheckVerifierStmtOut] using h_strictOracleWitConsistency.2
    · funext y
      have h_const := iterated_fold_to_const_strict (κ := κ) (L := L) (K := K) (β := β)
        (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (h_l := h_l) (stmtIn := stmtIn) (witIn := witIn) (oStmtIn := oStmtIn)
        (h_strictOracleWitConsistency_In := h_strictOracleWitConsistency) y
      have h_msg_eq : transcript.messages ⟨0, rfl⟩ = witIn.f ⟨0, by simp only [zero_mem]⟩ :=
        finalSumcheck_honest_message_eq_f_zero (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l)
          (𝓑 := 𝓑) stmtIn witIn oStmtIn challenges
      dsimp [verifierStmtOut, verifierOStmtOut, transcript, step, finalSumcheckStepLogic,
        finalSumcheckVerifierStmtOut] at h_const ⊢
      dsimp [transcript, step, finalSumcheckStepLogic] at h_msg_eq
      rw [h_msg_eq]
      exact h_const
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

/-- Perfect completeness for the final sumcheck step -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
    (init : ProbComp σ) (hInit : NeverFail init)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleReduction.perfectCompleteness
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L))
    (relIn := BinaryBasefold.strictRoundRelation (mp := RingSwitching_SumcheckMultParam κ L K
      (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ'))
    (relOut := BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleReduction := finalSumcheckOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ (𝓑 := 𝓑)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
    (init := init) (impl := impl) := by
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_P_to_V (hInit := hInit)
    (hDir0 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  -- Step 2: Convert probability 1 to universal quantification over support
  rw [probEvent_eq_one_iff]
  -- Step 3: Unfold protocol definitions
  dsimp only [finalSumcheckOracleReduction, finalSumcheckProver, finalSumcheckVerifier,
    OracleVerifier.toVerifier, FullTranscript.mk1]
  let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
  let strongly_complete : step.IsStronglyComplete := finalSumcheckStep_is_logic_complete
    (κ := κ) (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_l := h_l) (𝓑 := 𝓑)
  -- Step 4: Split into safety and correctness goals
  refine ⟨?_, ?_⟩
  -- GOAL 1: SAFETY - Prove the verifier never crashes ([⊥|...] = 0)
  · -- Peel off monadic layers to reach the core verifier logic
    simp only [probFailure_bind_eq_zero_iff]
    conv_lhs =>
      simp only [liftComp_eq_liftM, liftM_pure, probFailure_eq_zero]
    rw [true_and]
    intro inputState hInputState_mem_support
    simp only [Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one, ChallengeIdx,
      Challenge, liftComp_eq_liftM, liftM_pure, support_pure,
      Set.mem_singleton_iff] at hInputState_mem_support
    subst inputState
    conv_lhs =>
      simp only [liftM, monadLift, MonadLift.monadLift]
      simp only [ChallengeIdx, Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
        liftComp_eq_liftM, OptionT.probFailure_lift, HasEvalPMF.probFailure_eq_zero]
    rw [true_and]
    -- ⊢ ∀ x ∈ .. support, ... ∧ ... ∧ ...
    intro h_prover_final_output h_prover_final_output_support
    conv =>
      simp only [guard_eq] -- simplify the `guard`
      enter [2];
      simp only [bind_pure_comp, NeverFail.probFailure_eq_zero, implies_true]
    rw [and_true]
    -- Pr[⊥ | (...) : OracleComp ... (Option ...)] = 0
    rw [OptionT.probFailure_liftComp_of_OracleComp_Option] -- split into two summands
    conv_lhs =>
      enter [1]
      simp only [MessageIdx, Fin.isValue, Message, Matrix.cons_val_zero, Fin.succ_zero_eq_one,
        id_eq, bind_pure_comp, OptionT.run_map, HasEvalPMF.probFailure_eq_zero]
    rw [zero_add]
    simp only [probOutput_eq_zero_iff]
    rw [OptionT.support_run_eq]
    simp only [←probOutput_eq_zero_iff]
    change Pr[= none | OptionT.run (m := (OracleComp []ₒ)) (x := (OptionT.bind _ _)) ] = 0
    rw [OptionT.probOutput_none_bind_eq_zero_iff]
    conv =>
      enter [x]
      rw [OptionT.support_run]
    intro vStmtOut h_vStmtOut_mem_support
    conv at h_vStmtOut_mem_support =>
      erw [simulateQ_bind]
      -- turn the simulated oracle query into OracleInterface.answer form
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2] -- V queries P's message
      change vStmtOut ∈ _root_.support (Bind.bind (m := (OracleComp []ₒ)) _ _)
      erw [_root_.bind_pure_simulateQ_comp]
      simp only [Matrix.cons_val_zero, guard_eq]
      -- simp  [bind_pure_comp,
      -- OptionT.simulateQ_map, OptionT.simulateQ_ite, OptionT.simulateQ_pure,
      -- OptionT.support_map_run, OptionT.support_ite_run, support_pure,
      -- OptionT.support_failure_run, Set.mem_image, Set.mem_ite_empty_right,
      -- Set.mem_singleton_iff, and_true, exists_const, Prod.mk.injEq, existsAndEq]
      rw [bind_pure_comp]
      dsimp only [Functor.map]
      rw [OptionT.simulateQ_bind]
      erw [support_bind]
      rw [simulateQ_ite]
      simp only [Fin.isValue, Message, Matrix.cons_val_zero, id_eq, MessageIdx, support_ite,
        toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure, Set.mem_iUnion,
        exists_prop]
      simp only [OptionT.simulateQ_failure]
      erw [_root_.simulateQ_pure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk1 (msg0 := _)) with h_V_check_def
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFinalSumcheckStep (L := L)).dir 0 ≠ Direction.V_to_P := by
            dsimp only [pSpecFinalSumcheckStep, Fin.isValue, Matrix.cons_val_zero]
            simp only [ne_eq, reduceCtorEq, not_false_eq_true]
          exfalso
          exact hj_ne hj
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, support_pure, Set.mem_singleton_iff, Fin.isValue,
      Fin.val_last, exists_eq_left, OptionT.support_OptionT_pure_run] at h_vStmtOut_mem_support
    rw [h_vStmtOut_mem_support]
    simp only [Fin.isValue, Fin.val_last, OptionT.run_pure, probOutput_eq_zero_iff, support_pure,
      Set.mem_singleton_iff, reduceCtorEq, not_false_eq_true]
  · -- GOAL 2: CORRECTNESS - Prove all outputs in support satisfy the relation
    intro x hx_mem_support
    rcases x with ⟨⟨prvStmtOut, prvOStmtOut⟩, ⟨verStmtOut, verOStmtOut⟩, witOut⟩
    simp only
    -- Step 2a: Simplify the support membership to extract the challenge
    simp only [
      support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, Prod.exists
    ] at hx_mem_support
    conv at hx_mem_support =>
      erw [OptionT.support_mk, support_pure]
      simp only [
        Set.mem_singleton_iff, Option.some.injEq, Set.setOf_eq_eq_singleton, Prod.mk.injEq,
        OptionT.mem_support_iff,
        OptionT.run_monadLift, support_map, Set.mem_image, exists_eq_right, Fin.succ_one_eq_two,
        id_eq, guard_eq, bind_pure_comp,
        toPFunctor_add, toPFunctor_emptySpec, OptionT.support_run, ↓existsAndEq, and_true, true_and,
        exists_eq_right_right', liftM_pure, support_pure, exists_eq_left]
      dsimp only [monadLift, MonadLift.monadLift]
    simp only [Fin.isValue, Challenge, ChallengeIdx,
      liftComp_eq_liftM, liftM_pure, liftComp_pure, support_pure, Set.mem_singleton_iff,
      Fin.reduceLast, MessageIdx, Message] at hx_mem_support
    -- Step 2b: Extract the challenge r1 and the trace equations
    rcases hx_mem_support with ⟨prvWitOut, h_prvOut_mem_support, h_verOut_mem_support⟩
    conv at h_prvOut_mem_support =>
      dsimp only [finalSumcheckStepLogic]
      simp only [Fin.val_last, Fin.isValue, Prod.mk.injEq, and_true]
    -- Step 2c: Simplify the verifier computation
    conv at h_verOut_mem_support =>
      erw [simulateQ_bind]
      simp only [Set.mem_singleton_iff]
      change some (verStmtOut, verOStmtOut) ∈ _root_.support (liftComp _ _)
      rw [_root_.support_liftComp]
      dsimp only [Functor.map]
      erw [support_bind]
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      simp only [Fin.isValue, Fin.val_last, pure_bind,
        OptionT.simulateQ_bind, toPFunctor_emptySpec, Function.comp_apply, OptionT.simulateQ_pure,
        Set.mem_iUnion, exists_prop]
      rw [simulateQ_ite]; erw [simulateQ_pure]
      simp only [OptionT.simulateQ_failure]
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk1
        (msg0 := _))with h_V_check_def
    -- Step 2e: Apply the logic completeness lemma
    obtain ⟨h_V_check, h_rel, h_agree⟩ := strongly_complete (stmtIn := stmtIn)
      (witIn := witIn) (h_relIn := h_relIn) (challenges :=
      fun ⟨j, hj⟩ => by
        match j with
        | 0 =>
          have hj_ne : (pSpecFinalSumcheckStep (L := L)).dir 0 ≠ Direction.V_to_P := by
            dsimp only [pSpecFinalSumcheckStep, Fin.isValue, Matrix.cons_val_zero]
            simp only [ne_eq, reduceCtorEq, not_false_eq_true]
          exfalso
          exact hj_ne hj
      )
    have h_V_check_is_true : V_check := h_V_check
    simp only [h_V_check_is_true, ↓reduceIte, Fin.isValue] at h_verOut_mem_support
    erw [support_bind, support_pure] at h_verOut_mem_support
    simp only [Set.mem_singleton_iff, Fin.isValue, Set.iUnion_iUnion_eq_left,
      OptionT.support_OptionT_pure_run, exists_eq_left, Option.some.injEq,
      Prod.mk.injEq] at h_verOut_mem_support
    rcases h_verOut_mem_support with ⟨verStmtOut_eq, verOStmtOut_eq⟩
    obtain ⟨prvStmtOut_eq, prvOStmtOut_eq⟩ := h_prvOut_mem_support
    constructor
    · rw [verStmtOut_eq, verOStmtOut_eq];
      exact h_rel
    · constructor
      · rw [verStmtOut_eq, prvStmtOut_eq]; rfl
      · rw [verOStmtOut_eq, prvOStmtOut_eq];
        exact h_agree.2

/-- RBR knowledge error for the final sumcheck step -/
def finalSumcheckKnowledgeError (m : pSpecFinalSumcheckStep (L := L).ChallengeIdx) :
  ℝ≥0 :=
  match m with
  | ⟨0, h0⟩ => nomatch h0

def FinalSumcheckWit := fun (m : Fin (1 + 1)) =>
 match m with
 | ⟨0, _⟩ => BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ')
 | ⟨1, _⟩ => Unit

/-- The round-by-round extractor for the final sumcheck step -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β))
      (Fin.last ℓ')) × (∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ  (Fin.last ℓ') j))
    (WitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (WitOut := Unit)
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L))
    (WitMid := FinalSumcheckWit κ (L := L) K β ℓ' 𝓡 (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  eqIn := rfl
  extractMid := fun m ⟨stmtMid, oStmtMid⟩ trSucc witMidSucc => by
    have hm : m = 0 := by omega
    subst hm
    have _ : witMidSucc = () := by rfl
    -- Decode t from the first oracle f^(0)
    let f0 := getFirstOracle K β oStmtMid
    let polyOpt := extractMLP K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨0, by exact Nat.pos_of_neZero ℓ'⟩) (f := f0)
    let H_constant : L⦃≤ 2⦄[X Fin (ℓ' - ↑(Fin.last ℓ'))] := ⟨MvPolynomial.C stmtMid.sumcheck_target,
      by
        rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
        intro i
        simp only [MvPolynomial.degreeOf_C, Nat.zero_le]⟩
    match polyOpt with
    | none =>
      exact {
        t := ⟨0, by apply zero_mem⟩,
        H := H_constant,
        f := fun _ => 0
      }
    | some tpoly =>
      exact {
        t := revIndexMLP tpoly,
        H := H_constant,
        f := getMidCodewords K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (revIndexMLP tpoly) stmtMid.challenges
      }
  extractOut := fun ⟨stmtIn, oStmtIn⟩ tr witOut => ()


def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheckStep (L := L)))
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (witMid : FinalSumcheckWit κ (L := L) K β ℓ' 𝓡 (h_ℓ_add_R_rate := h_ℓ_add_R_rate) m)
    (oStmt : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    BinaryBasefold.roundRelationProp K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (mp := RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l)
      (𝓑 := 𝓑) (Fin.last ℓ') ((stmt, oStmt), witMid)
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let tr_so_far := (pSpecFinalSumcheckStep (L := L)).take 1 (by omega)
    let i_msg0 : tr_so_far.MessageIdx := ⟨⟨0, by omega⟩, rfl⟩
    let s' : L := (ProtocolSpec.Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecFinalSumcheckStep (L := L)) tr).1 i_msg0
    let stmtOut : BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ') := {
      -- **Dummy UNUSED values**
      ctx := {
        t_eval_point := 0,
        original_claim := 0
      },
      sumcheck_target := 0,
      -- **ONLY the last two fields are used in finalSumcheckStepFoldingStateProp**
      challenges := stmt.challenges,
      final_constant := s'
    }
    let sumcheckFinalCheck : Prop := stmt.sumcheck_target = compute_final_eq_value κ L K
      (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l
      stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching * s'
    let finalFoldingProp := finalSumcheckStepFoldingStateProp K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_le := by
        apply Nat.le_of_dvd;
        · exact Nat.pos_of_neZero ℓ'
        · exact hdiv.out) (input := ⟨stmtOut, oStmt⟩)
    sumcheckFinalCheck ∧ finalFoldingProp -- local checks ∧ (oracleConsitency ∨ badEventExists)

/-- The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).KnowledgeStateFunction init impl
    (relIn := roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l) (Fin.last ℓ'))
    (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (extractor := finalSumcheckRbrExtractor κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
  where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    finalSumcheckKStateProp κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun stmt witMid => by
    rfl
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.castSucc_zero]
    -- In the single-message final sumcheck step, the new message `msg` *is* the final constant.
    -- We use it directly rather than reconstructing a truncated transcript.
    let s' : L := msg
    let stmtOut : BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ') := {
      ctx := {
        t_eval_point := 0,
        original_claim := 0
      },
      sumcheck_target := 0,
      challenges := stmtIn.challenges,
      final_constant := s'
    }
    intro h_kState_round1
    unfold finalSumcheckKStateProp BinaryBasefold.finalSumcheckStepFoldingStateProp
      BinaryBasefold.roundRelationProp BinaryBasefold.masterKStateCore at h_kState_round1 ⊢
    simp only [olderStmtChallenges_self]
    simp only [Fin.isValue] at h_kState_round1
    obtain ⟨h_sumcheckFinalCheck, h_core⟩ := h_kState_round1
    -- The input relation uses the terminal block bad event or witness consistency.
    cases h_core with
    | inl hConsistent =>
      have ⟨tpoly, h_extractMLP⟩ :=
        BinaryBasefold.CoreInteraction.extractMLP_some_of_oracleFoldingConsistency K β
          (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtOut oStmtIn hConsistent
      refine Or.inr ?_
      apply and_left_comm.mpr
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- local sumcheck consistency at m=0
        unfold finalSumcheckRbrExtractor sumcheckConsistencyProp
        simp only [Fin.val_last, Fin.mk_zero', Fin.coe_ofNat_eq_mod]
        simp only [h_extractMLP]
        change stmtIn.sumcheck_target =
          ∑ x ∈ Fintype.piFinset (fun _ : Fin (ℓ' - ℓ') => Finset.map 𝓑 univ),
            (MvPolynomial.eval x) (MvPolynomial.C stmtIn.sumcheck_target)
        haveI : IsEmpty (Fin (ℓ' - ℓ')) := by simp only [Nat.sub_self]; infer_instance
        simp only [Nat.sub_self, MvPolynomial.eval_C, sum_const, Fintype.card_piFinset,
          Finset.univ_eq_empty, Finset.prod_empty, Fintype.prod_empty, one_smul]
      · -- witnessStructuralInvariant for extracted witness
        unfold finalSumcheckRbrExtractor BinaryBasefold.witnessStructuralInvariant
        simp only [Fin.val_last, Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, and_true]
        refine SetLike.coe_eq_coe.mp ?_
        rw [projectToMidSumcheckPoly_at_last_eq]
        have h_s'_eq : s' = (revIndexMLP tpoly).val.eval stmtIn.challenges := by
          exact BinaryBasefold.CoreInteraction.extracted_t_poly_eval_eq_final_constant K β
            (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmtOut := oStmtIn) (stmtOut := stmtOut)
            (tpoly := tpoly) (h_extractMLP := h_extractMLP)
            (h_finalSumcheckStepOracleConsistency := hConsistent)
        have h_mult_eq : (MvPolynomial.eval stmtIn.challenges
          ((RingSwitching_SumcheckMultParam κ L K
            (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val) =
          compute_final_eq_value κ L K (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l
            stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching :=
          RingSwitching.A_MLE_eval_eq_compute_final_eq_value (P := ringSwitchingProfile κ L K β)
            ℓ ℓ' h_l stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
        have h_sumcheck_target_eq : stmtIn.sumcheck_target =
          (MvPolynomial.eval stmtIn.challenges
            ((RingSwitching_SumcheckMultParam κ L K
              (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val) *
            (MvPolynomial.eval stmtIn.challenges (revIndexMLP tpoly).val) := by
          calc
            stmtIn.sumcheck_target
                = compute_final_eq_value κ L K (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l
                    stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching * s' :=
                  h_sumcheckFinalCheck
            _ = compute_final_eq_value κ L K (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l
                  stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching *
                  (MvPolynomial.eval stmtIn.challenges (revIndexMLP tpoly).val) := by
                    rw [h_s'_eq]
            _ = (MvPolynomial.eval stmtIn.challenges
                  ((RingSwitching_SumcheckMultParam κ L K
                    (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val) *
                  (MvPolynomial.eval stmtIn.challenges (revIndexMLP tpoly).val) := by
                    rw [h_mult_eq]
        exact congrArg MvPolynomial.C h_sumcheck_target_eq
      · -- initial compatibility via first-oracle consistency
        dsimp only [finalSumcheckRbrExtractor, BinaryBasefold.firstOracleWitnessConsistencyProp]
        simp only [Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, Fin.val_last,
          OracleFrontierIndex.val_mkFromStmtIdx]
        have h_close_first :=
          BinaryBasefold.CoreInteraction.firstOracle_UDRClose_of_finalSumcheckStepOracleConsistency K β
            (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (stmtOut := stmtOut) (oStmt := oStmtIn) hConsistent
        have hUDR : 2 * Code.distFromCode (u := getFirstOracle K β oStmtIn)
            (C := BBF_Code K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin (2 ^ κ))) <
          (BBF_CodeDistance K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (0 : Fin (2 ^ κ)) : ℕ∞) := by
          simpa [UDRClose] using h_close_first
        exact firstOracleWitnessConsistency_revIndexMLP_of_extractMLP_eq_some K β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (f := getFirstOracle K β oStmtIn) (tpoly := tpoly) hUDR h_extractMLP
      · simpa only [olderStmtChallenges_self] using hConsistent.1
    | inr hBad =>
      exact Or.inl hBad
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut probEvent_relOut_gt_0 => by
  -- Same pattern as relay: verifier output (stmtOut, oStmtOut) + h_relOut ⇒ commitKStateProp 1
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at probEvent_relOut_gt_0
    rcases probEvent_relOut_gt_0 with ⟨stmtOut, oStmtOut, h_output_mem_V_run_support, h_relOut⟩
    have h_output_mem_V_run_support' :
        some (stmtOut, oStmtOut) ∈
          support (do
            let s ← init
            Prod.fst <$>
              (simulateQ impl
                (Verifier.run (stmtIn, oStmtIn) tr
                  (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
                    (𝓑 := 𝓑)).toVerifier)).run s) := by
      exact (OptionT.mem_support_iff
        (mx := OptionT.mk (do
          let s ← init
          Prod.fst <$>
            (simulateQ impl
              (Verifier.run (stmtIn, oStmtIn) tr
                (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
                  (𝓑 := 𝓑)).toVerifier)).run s))
        (x := (stmtOut, oStmtOut))).1 h_output_mem_V_run_support
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h_output_mem_V_run_support'
    rcases h_output_mem_V_run_support' with ⟨s, hs_init, h_output_mem_V_run_support⟩
    conv at h_output_mem_V_run_support => -- same as fold step
      simp only [Verifier.run, OracleVerifier.toVerifier]
      -- Now unfold the foldOracleVerifier's `verify()` method
      simp only [finalSumcheckVerifier]
      -- dsimp only [StateT.run]
      -- simp only [simulateQ_bind, simulateQ_query, simulateQ_pure]
      -- oracle query unfolding
      simp only [support_bind, Set.mem_iUnion]
      dsimp only [StateT.run]
      -- enter [1, i_1, 2, 1, x]
      simp only [simulateQ_bind]
      ---------------------------------------
      -- Now simplify the `guard` and `ite` of StateT.map generated from it
      simp only [MessageIdx, Fin.isValue, Matrix.cons_val_zero, simulateQ_pure, Message, guard_eq,
        pure_bind, Function.comp_apply, simulateQ_map, simulateQ_ite,
        OptionT.simulateQ_failure, bind_map_left]
      simp only [MessageIdx, Message, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        bind_pure_comp, simulateQ_map, simulateQ_ite, simulateQ_pure, OptionT.simulateQ_failure,
        bind_map_left, Function.comp_apply]
      simp only [support_ite]
      simp only [Fin.isValue, Set.mem_ite_empty_right, Set.mem_singleton_iff, Prod.mk.injEq,
        exists_and_left, exists_eq', exists_eq_right, exists_and_right]
      simp only [Fin.isValue, id_eq, FullTranscript.mk1_eq_snoc, support_map, Set.mem_image,
        Prod.exists, exists_and_right, exists_eq_right]
      erw [simulateQ_bind]
      enter [1, x, 1, 1, 1, 2];
      erw [simulateQ_bind]
      erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
      simp only [Fin.isValue, FullTranscript.mk1_eq_snoc, pure_bind, OptionT.simulateQ_map]
    conv at h_output_mem_V_run_support =>
      simp only [Fin.isValue, FullTranscript.mk1_eq_snoc, Function.comp_apply]
    erw [support_bind] at h_output_mem_V_run_support
    let step := (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    set V_check := step.verifierCheck stmtIn
      (FullTranscript.mk1 (msg0 := _)) with h_V_check_def
    by_cases h_V_check : V_check
    · simp only [Fin.isValue, h_V_check, ↓reduceIte, OptionT.run_pure, simulateQ_pure,
        Set.mem_iUnion, exists_prop, Prod.exists] at h_output_mem_V_run_support
      erw [simulateQ_bind] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, ↓existsAndEq, and_true, exists_eq_left,
        simulateQ_pure] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Fin.isValue, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq,
        exists_eq_right] at h_output_mem_V_run_support
      rcases h_output_mem_V_run_support with ⟨h_stmtOut_eq, h_oStmtOut_eq⟩
      simp only [Fin.reduceLast, Fin.isValue]
      -- h_relOut : ((stmtOut, oStmtOut), witOut) ∈ roundRelation 𝔽q β i.succ
      simp only [finalSumcheckRelOut, finalSumcheckRelOutProp, Set.mem_setOf_eq] at h_relOut
      -- Goal: commitKStateProp 1 stmtIn oStmtIn tr witOut
      unfold finalSumcheckKStateProp
      -- Unfold the sendMessage, receiveChallenge, output logic of prover
      dsimp only
      -- stmtOut = stmtIn; need oStmtOut = snoc_oracle oStmtIn witOut.f so goal matches h_relOut
      simp only [h_stmtOut_eq] at h_relOut ⊢
      have h_oStmtOut_eq_oStmtIn : oStmtOut = oStmtIn := by rw [h_oStmtOut_eq]; rfl
      -- c equals tr.messages ⟨0, rfl⟩
      constructor
      · -- First conjunct: sumcheck_target = eqTilde r challenges * c
        exact h_V_check
      · -- Second conjunct: finalSumcheckStepFoldingStateProp
          -- ({ toStatement := stmtIn, final_constant := c }, oStmtIn)
        rw [h_oStmtOut_eq_oStmtIn] at h_relOut
        rw [finalNonDoomedFoldingProp_eq_finalSumcheckStepFoldingStateProp K β] at h_relOut
        exact h_relOut
    · simp only [Fin.isValue, h_V_check, ↓reduceIte, OptionT.run_failure,
        OptionT.simulateQ_failure, _root_.simulateQ_pure,
        Set.mem_iUnion, exists_prop, Prod.exists] at h_output_mem_V_run_support
      erw [simulateQ_bind] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, ↓existsAndEq, and_true, exists_eq_left,
        simulateQ_pure] at h_output_mem_V_run_support
      erw [support_pure] at h_output_mem_V_run_support
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and,
        exists_false] at h_output_mem_V_run_support -- False

/-- Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness [Fintype L] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (relIn := roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (mp := RingSwitching_SumcheckMultParam κ L K
          (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l) (Fin.last ℓ'))
      (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := finalSumcheckKnowledgeError L) := by
  use FinalSumcheckWit κ (L := L) K β ℓ' 𝓡 (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  use finalSumcheckRbrExtractor κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate
  use finalSumcheckKnowledgeStateFunction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l init impl
  intro stmtIn witIn prover j
  rcases j with ⟨j, hj⟩
  cases j using Fin.cases with
  | zero =>
    simp only [pSpecFinalSumcheckStep, ne_eq, reduceCtorEq, not_false_eq_true, Fin.isValue,
      Matrix.cons_val_fin_one, Direction.not_P_to_V_eq_V_to_P] at hj
  | succ j' =>
    exact Fin.elim0 j'

end FinalSumcheckStep

section CoreInteractionPhaseReduction

/-- The final oracle verifier that composes sumcheckFold with finalSumcheckStep -/
@[reducible]
def coreInteractionOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (Stmt₁ := Statement (L := L) (ℓ:=ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
    (Stmt₂ := Statement (L := L) (ℓ:=ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (Stmt₃ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (OStmt₁ := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec₁ := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecFinalSumcheckStep (L:=L))
    (V₁ := sumcheckFoldOracleVerifier κ (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l)
      (𝓑 := 𝓑) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (V₂ := finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))

/-- The final oracle reduction that composes sumcheckFold with finalSumcheckStep -/
@[reducible]
def coreInteractionOracleReduction :=
  OracleReduction.append (oSpec:=[]ₒ)
    (Stmt₁ := Statement (L := L) (ℓ:=ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
    (Stmt₂ := Statement (L := L) (ℓ:=ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (Stmt₃ := BinaryBasefold.FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ'))
    (Wit₁ := RingSwitching.SumcheckWitness L ℓ' 0)
    (Wit₂ := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (Wit₃ := Unit)
    (OStmt₁ := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (OStmt₃ := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (pSpec₁ := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := BinaryBasefold.pSpecFinalSumcheckStep (L:=L))
    (R₁ := sumcheckFoldOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑 := 𝓑))
    (R₂ := finalSumcheckOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))

/-- Sequential composition preserves the core verifier's oracle interfaces. -/
instance coreInteractionOracleVerifier_appendCoherent :
    OracleVerifier.Append.AppendCoherent
      (coreInteractionOracleVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)) := by
  unfold coreInteractionOracleVerifier
  infer_instance

/-- The core reduction inherits coherence from its component reductions. -/
instance coreInteractionOracleReduction_appendCoherent :
    OracleVerifier.Append.AppendCoherent
      (coreInteractionOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)).verifier := by
  unfold coreInteractionOracleReduction
  infer_instance

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for the core interaction oracle reduction -/
theorem coreInteractionOracleReduction_perfectCompleteness (hInit : NeverFail init)
    (hAppendPerfectCompleteness :
      OracleReduction.perfectCompleteness
        (oSpec := []ₒ)
        (pSpec := BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
        (OStmtOut := BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
        (relIn := strictSumcheckInputRelation κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
        (relOut := BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (oracleReduction := coreInteractionOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑 := 𝓑))
        (init := init)
        (impl := impl)) :
    OracleReduction.perfectCompleteness
      (oSpec := []ₒ)
      (pSpec := BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (relIn := strictSumcheckInputRelation κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
      (relOut := BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleReduction := coreInteractionOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l (𝓑 := 𝓑))
      (init := init)
      (impl := impl) :=
  hAppendPerfectCompleteness

def coreInteractionOracleRbrKnowledgeError (j : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 :=
    Sum.elim
      (f := fun i => BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError
        K β (ϑ := ϑ) i)
      (g := fun i => finalSumcheckKnowledgeError (L := L) i)
      (ChallengeIdx.sumEquiv.symm j)

/-- Round-by-round knowledge soundness for the core interaction oracle verifier -/
theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness
    (hAppendRbrKnowledgeSoundness :
      (coreInteractionOracleVerifier κ (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
        (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
        (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
        (OStmtOut := BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
        (pSpec := BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (relIn := RingSwitching.sumcheckRoundRelation κ L K (ringSwitchingProfile κ L K β)
          ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn
            (κ := κ) (L := L) (K := K) (β := β)
            (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
        (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (rbrKnowledgeError := coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate))) :
    (coreInteractionOracleVerifier κ (L := L) (K := K) (β := β) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (𝓡 := 𝓡) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
      (OStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (pSpec := BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := RingSwitching.sumcheckRoundRelation κ L K (ringSwitchingProfile κ L K β)
        ℓ ℓ' h_l (aOStmtIn := BinaryBasefoldAbstractOStmtIn
          (κ := κ) (L := L) (K := K) (β := β)
          (ℓ' := ℓ') (𝓡 := 𝓡) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) 0)
      (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  hAppendRbrKnowledgeSoundness

end CoreInteractionPhaseReduction

/-- Sum of the per-round RBR knowledge error over core interaction challenges is **at most**
`2 * ℓ' / |L| + 2^(ℓ' + 𝓡) / |L|`
(see `BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError_le`). -/
theorem coreInteractionOracleRbrKnowledgeError_le :
    (∑ i : (BinaryBasefold.pSpecCoreInteraction K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
      coreInteractionOracleRbrKnowledgeError κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate i)
    ≤ 2 * (ℓ' : ℝ≥0) / (Fintype.card L : ℝ≥0)
      + (2 ^ (ℓ' + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
  classical
  unfold coreInteractionOracleRbrKnowledgeError
  have hsum := Equiv.sum_comp
    (ChallengeIdx.sumEquiv (pSpec₁ := BinaryBasefold.pSpecSumcheckFold K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (pSpec₂ := BinaryBasefold.pSpecFinalSumcheckStep (L := L))).symm
    (Sum.elim (BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) (finalSumcheckKnowledgeError (L := L)))
  erw [hsum]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hb : (∑ i : (BinaryBasefold.pSpecFinalSumcheckStep (L := L)).ChallengeIdx,
      finalSumcheckKnowledgeError (L := L) i) = 0 := by
    simpa using BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError_sum_eq_zero (L := L)
  rw [hb, add_zero]
  exact BinaryBasefold.CoreInteraction.sumcheckFoldKnowledgeError_le (𝔽q := K) (L := L) (β := β)
    (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ')

end
end Binius.FRIBinius.CoreInteractionPhase
