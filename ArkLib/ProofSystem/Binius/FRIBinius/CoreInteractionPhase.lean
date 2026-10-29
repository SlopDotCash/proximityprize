/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.CoreInteractionPhase
import ArkLib.ProofSystem.Binius.BinaryBasefold.ExtractMLPCorrectness
import ArkLib.ProofSystem.Binius.BinaryBasefold.FinalRelation
import ProximityPrize.Extensions.ProofSystem.Binius.BinaryBasefold.ReductionLogic
import ProximityPrize.Extensions.ProofSystem.Binius.FRIBinius.Prelude
import ArkLib.OracleReduction.LiftContext.Coherence
import ArkLib.OracleReduction.LiftContext.OracleStatementPreserving

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

def sumcheckFoldExecutableLens (h_l : ℓ = ℓ' + κ) : OracleStatement.ExecutableLens
    (OuterStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
    (OuterStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (InnerStmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
    (InnerStmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (OuterOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OuterOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
    (InnerOStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (InnerOStmtOut := BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ')) :=
  ProximityPrize.Compatibility.identityExecutableLens

/-- The existing witness transport with the canonical identity statement/oracle lens. -/
def sumcheckFoldExecutableCtxLens : OracleContext.ExecutableLens
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
  stmt := sumcheckFoldExecutableLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
  wit := (sumcheckFoldCtxLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l).wit

/-- Preserve the authoritative native verifier, including its virtual output oracles. -/
def sumcheckFoldOracleVerifier :=
  let V := BinaryBasefold.CoreInteraction.sumcheckFoldOracleVerifier K β (ϑ := ϑ)
    (multpoly := (RingSwitching_SumcheckMultParam κ L K (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly)
    (𝓑 := 𝓑) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  V.liftContext
    (sumcheckFoldExecutableLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l)
    (ProximityPrize.Compatibility.identityLiftContextOutput V)

/-- Transport the witness while preserving the native verifier's output representation. -/
def sumcheckFoldOracleReduction :=
  let R := BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction K β (ϑ := ϑ)
    (multpoly := (RingSwitching_SumcheckMultParam κ L K (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  R.liftContext
    (sumcheckFoldExecutableCtxLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l)
    (ProximityPrize.Compatibility.identityLiftContextOutput R.verifier)

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

/-- Strict input for the canonical chronological folding convention. The historical
`strictSumcheckInputRelation` above uses the explicitly retained newest-first encoding. -/
def nativeStrictSumcheckInputRelation :
    Set ((Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0 ×
      (∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j)) × RingSwitching.SumcheckWitness L ℓ' 0) :=
  { x | BinaryBasefold.sumcheckConsistencyProp (𝓑 := 𝓑) x.1.1.sumcheck_target x.2.H ∧
    RingSwitching.witnessStructuralInvariant κ L K (ringSwitchingProfile κ L K β)
      ℓ ℓ' h_l x.1.1 x.2 ∧
    BinaryBasefold.StrictOracleFoldingConsistent K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (t := x.2.t') (i := 0) (challenges := Fin.elim0) (oStmt := x.1.2) }

-- Security properties for the lifted oracle reduction

section Security

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

-- Completeness instance for the context lens
instance nativeSumcheckFoldCtxLens_complete :
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
    (outerRelIn := nativeStrictSumcheckInputRelation κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    (outerRelOut :=
      BinaryBasefold.strictRoundRelation (multpoly := (RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ')
    )
    (innerRelIn :=
      BinaryBasefold.strictRoundRelation (multpoly := (RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0
    )
    (innerRelOut :=
      BinaryBasefold.strictRoundRelation (multpoly := (RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly) K β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ')
    )
    (compat :=
      let originalReduction := (CoreInteraction.sumcheckFoldOracleReduction K β (ϑ:=ϑ)
        (multpoly := (RingSwitching_SumcheckMultParam κ L K (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly)
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
        simpa only [Fin.take_zero] using h_strict_compat
  lift_complete := fun outerStmtIn outerWitIn innerStmtOut innerWitOut compat => by
    intro _ hRelOut
    dsimp [sumcheckFoldStmtLens] at hRelOut ⊢
    exact hRelOut

-- Perfect completeness for the lifted oracle reduction
theorem sumcheckFoldOracleReduction_perfectCompleteness_native (hInit : NeverFail init)
    (hBinaryBasefoldSumcheckFoldPerfectCompleteness :
      OracleReduction.perfectCompleteness
        (pSpec := BinaryBasefold.pSpecSumcheckFold K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (relIn := BinaryBasefold.strictRoundRelation
          (multpoly := (RingSwitching_SumcheckMultParam κ L K
            (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly) K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
        (relOut := BinaryBasefold.strictRoundRelation
          (multpoly := (RingSwitching_SumcheckMultParam κ L K
            (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly) K β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ'))
        (oracleReduction := BinaryBasefold.CoreInteraction.sumcheckFoldOracleReduction K β
          (ϑ:=ϑ) (multpoly := (RingSwitching_SumcheckMultParam κ L K
            (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly)
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
    (relIn := nativeStrictSumcheckInputRelation κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    (relOut :=
      BinaryBasefold.strictRoundRelation (multpoly := (RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly) K β (ϑ:=ϑ)
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
    (outerRelIn := nativeStrictSumcheckInputRelation κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    (outerRelOut := BinaryBasefold.strictRoundRelation (multpoly := (RingSwitching_SumcheckMultParam κ L K
      (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ'))
    (innerRelIn := BinaryBasefold.strictRoundRelation (multpoly := (RingSwitching_SumcheckMultParam κ L K
      (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
    (innerRelOut := BinaryBasefold.strictRoundRelation (multpoly := (RingSwitching_SumcheckMultParam κ L K
      (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly) K β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ'))
    (lens := sumcheckFoldExecutableCtxLens κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l)
    (output := ProximityPrize.Compatibility.identityLiftContextOutput _)
    (lensComplete := nativeSumcheckFoldCtxLens_complete κ L K β ℓ ℓ' 𝓡 ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_l)
    (init := init)
    (impl := impl)
    (h := hBinaryBasefoldSumcheckFoldPerfectCompleteness)

/-- The retained historical BinaryBasefold input relation does not imply the ring-switching input
relation: its old unfinished-block bad-event branch is already true at round zero. In particular,
the zero witness with a claimed sum of one is admitted by the former and rejected by the latter.
This refutes the old unconditional extractor-lens bridge. The canonical chronological
`HasIncrementalBadEvent` is a different predicate; this theorem makes no claim about it. -/
theorem sumcheckFold_legacy_input_bridge_counterexample :
    ∃ (stmt : Statement (L := L) (ℓ := ℓ')
        (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) 0)
      (oStmt : ∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j)
      (wit : BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') 0),
      BinaryBasefold.roundRelationProp
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
      finalConstant := c
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
    OracleReduction.DeterministicLogicStep []ₒ
      (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
      (BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ') (Fin.last ℓ'))
      (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
      (BinaryBasefold.FinalSumcheckStatementOut (L := L) (ℓ := ℓ'))
      Unit
      (BinaryBasefold.pSpecFinalSumcheckStep (L := L)) where
  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ BinaryBasefold.strictRoundRelation
      (multpoly := (RingSwitching_SumcheckMultParam κ L K
      (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly) K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (Fin.last ℓ')
  completeness_relOut := fun ((stmtOut, oStmtOut), witOut) =>
    ((stmtOut, oStmtOut), witOut) ∈ BinaryBasefold.strictFinalSumcheckRelOut K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  verifierCheck := fun stmtIn transcript =>
    finalSumcheckVerifierCheck κ L K β ℓ ℓ' h_l stmtIn (transcript.messages ⟨0, rfl⟩)
  verifierOut := fun stmtIn transcript =>
    finalSumcheckVerifierStmtOut κ L K β ℓ ℓ' h_l stmtIn (transcript.messages ⟨0, rfl⟩)
  outputInterfaces := inferInstance
  outputOracle := .inl {
    embed := Function.Embedding.inl
    hEq := fun _ => rfl
    outputInterface_heq := fun _ => HEq.rfl }
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
  outputOracle := (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
    (𝓑 := 𝓑)).outputOracle

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

omit [Fintype L] [DecidableEq L] [CharP L 2] [SampleableType L] [NeZero ℓ'] in
/-- At `Fin.last ℓ'`, sumcheck consistency simplifies to a single evaluation. -/
lemma sumcheckConsistency_at_last_simplifies
    (target : L) (H : L⦃≤ 2⦄[X Fin (ℓ' - Fin.last ℓ')])
    (h_cons : BinaryBasefold.sumcheckConsistencyProp (𝓑 := 𝓑) target H) :
    target = H.val.eval (fun _ => (0 : L)) := by
  simp only [Fin.val_last] at H h_cons ⊢
  simp only [_root_.Binius.BinaryBasefold.sumcheckConsistencyProp] at h_cons
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
  exact BinaryBasefold.Compatibility.newestFirstCodeword_last_apply_eq_eval K β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn.t stmtIn.challenges ⟨0, by simp only [zero_mem]⟩

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

/-- The current final verifier executes one deterministic message guard and forwards its oracles. -/
def finalSumcheckVerifierGuardedForm :
    (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).toVerifier.GuardedForm :=
  Verifier.GuardedForm.ofQueryGuard _ ⟨⟨0, rfl⟩, ()⟩
    (fun s a _ => (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).verifierCheck s (FullTranscript.mk1 a))
    (hcheck := fun _ _ _ => Classical.propDecidable _)
    (fun s a _ => (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).verifierOut s (FullTranscript.mk1 a))
    (fun _ _ => rfl)

open Classical in
/-- The native guard checks exactly the RingSwitching final equation on the sent constant. -/
@[simp] theorem finalSumcheckVerifierGuardedForm_check_native
    (s : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ') ×
      ∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j)
    (tr : (pSpecFinalSumcheckStep (L := L)).FullTranscript) :
    (finalSumcheckVerifierGuardedForm κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).check s tr =
      decide (s.1.sumcheck_target = compute_final_eq_value κ L K
        (ringSwitchingProfile κ L K β) ℓ ℓ' h_l s.1.ctx.t_eval_point
        s.1.challenges s.1.ctx.r_batching * (show L from tr.messages ⟨0, rfl⟩)) :=
  decide_eq_decide.mpr Iff.rfl

/-- Closing the canonical chronological relation is strongly complete. -/
lemma finalSumcheckStep_is_logic_complete_native :
    (finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges hIn
  let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
  let tr := step.honestProverTranscript stmtIn witIn oStmtIn challenges
  change BinaryBasefold.StrictRoundRelated K β (multpoly :=
    (RingSwitching_SumcheckMultParam κ L K (ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly)
    (𝓑 := 𝓑) (Fin.last ℓ') ((stmtIn, oStmtIn), witIn) at hIn
  obtain ⟨hSum, hWitness, hOracles⟩ := hIn
  have hTarget : stmtIn.sumcheck_target = witIn.H.val.eval (fun _ => 0) := by
    dsimp only [Sumcheck.Structured.sumcheckConsistencyProp] at hSum
    simp only [Fin.val_last] at hSum
    rw [Finset.sum_eq_single_of_mem (a := fun _ => 0)
      (by simp only [SumcheckDomain.mem_cube]; intro i; have hi := i.isLt; omega)
      (fun b _ hb => (hb (by funext i; have hi := i.isLt; omega)).elim)] at hSum
    exact hSum
  have hFinal : witIn.f ⟨0, by simp only [zero_mem]⟩ =
      witIn.t.val.eval stmtIn.challenges := by
    rw [hWitness.2]
    exact BinaryBasefold.getMidCodewords_last_zero_eq_eval K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) witIn.t stmtIn.challenges
  have hCheck : step.verifierCheck stmtIn tr := by
    change stmtIn.sumcheck_target = compute_final_eq_value κ L K
      (ringSwitchingProfile κ L K β) ℓ ℓ' h_l stmtIn.ctx.t_eval_point
      stmtIn.challenges stmtIn.ctx.r_batching * witIn.f ⟨0, by simp only [zero_mem]⟩
    rw [hTarget, hWitness.1, Sumcheck.Structured.eval_fixPrefix_initial_last, hFinal]
    congr 1
    exact RingSwitching.A_MLE_eval_eq_compute_final_eq_value
      (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l
      stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching
  refine ⟨hCheck, ?_, rfl, rfl⟩
  change ∃ t, BinaryBasefold.StrictFinalSumcheckFoldingState K β t
    (finalSumcheckVerifierStmtOut κ L K β ℓ ℓ' h_l stmtIn
      (witIn.f ⟨0, by simp only [zero_mem]⟩), oStmtIn)
  refine ⟨witIn.t, ?_, ?_⟩
  · simpa only [BinaryBasefold.StrictOracleWitnessConsistent, Fin.val_last,
      OracleFrontierIndex.mkFromStmtIdx, finalSumcheckVerifierStmtOut, Fin.take_eq_self]
      using hOracles
  · funext y
    have h := BinaryBasefold.iteratedFold_lastOracle_eq_finalConstant K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn)
      (witIn := witIn) (oStmtIn := oStmtIn) (h_witness := hWitness.2)
      (h_oracles := by simpa only [Fin.val_last, OracleFrontierIndex.mkFromStmtIdx,
        Fin.take_eq_self] using hOracles)
    dsimp only [BinaryBasefold.lastBlockStart,
      BinaryBasefold.lastBlockEnd,
      BinaryBasefold.lastBlockChallenges, getLastOracleDomainIndex] at h
    exact h y

/-- Perfect completeness for the canonical chronological final sumcheck step. The legacy
support-interpreter proof is archived; the native proof uses the shared deterministic engine. -/
theorem finalSumcheckOracleReduction_perfectCompleteness_native {σ : Type}
    (init : ProbComp σ) (hInit : NeverFail init)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).perfectCompleteness init impl
      (BinaryBasefold.strictRoundRelation K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
        (multpoly := (RingSwitching_SumcheckMultParam κ L K
          (ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly) (Fin.last ℓ'))
      (BinaryBasefold.strictFinalSumcheckRelOut K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  classical
  let step := finalSumcheckStepLogic κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
  apply step.perfectCompleteness_of_isStronglyComplete
    (finalSumcheckOracleReduction κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    (finalSumcheckVerifierGuardedForm κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
    (finalSumcheckStep_is_logic_complete_native κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l)
  · intro stmt wit oracles q hq
    let c : L := wit.f ⟨0, by simp only [zero_mem]⟩
    have hp : (finalSumcheckProver κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
        (𝓑 := 𝓑)).run (stmt, oracles) wit =
        pure (((default : (pSpecFinalSumcheckStep (L := L)).Transcript 0).concat (m := 0) c),
          step.proverOut stmt wit oracles (FullTranscript.mk1 c)) := rfl
    dsimp only [finalSumcheckOracleReduction] at hq
    rw [hp] at hq
    replace hq := OracleComp.eq_of_mem_support_pure _ hq
    refine ⟨isEmptyElim, hq.trans ?_⟩
    apply Prod.ext
    · exact (FullTranscript.mk1_eq_snoc (pSpec := pSpecFinalSumcheckStep (L := L)) c).symm
    · rfl
  · intro stmt oracles tr
    exact decide_eq_decide.mpr Iff.rfl
  · intro stmt oracles tr
    rfl

-- Native strong completeness and perfect completeness above use the canonical
-- exact-encoding relation. Historical support-interpreter proofs are archived in
-- scripts/integration/retired/fribinius-core-interaction-legacy.lean.txt.

def finalSumcheckKnowledgeError (m : pSpecFinalSumcheckStep (L := L).ChallengeIdx) :
  ℝ≥0 :=
  match m with
  | ⟨0, h0⟩ => nomatch h0

def FinalSumcheckWit := fun (m : Fin (1 + 1)) =>
 match m with
 | ⟨0, _⟩ => BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ')
 | ⟨1, _⟩ => Unit

/-- The round-by-round extractor for the final sumcheck step -/
noncomputable def finalSumcheckRbrExtractor_native :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β))
      (Fin.last ℓ')) × (∀ j, BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ  (Fin.last ℓ') j))
    (WitIn := BinaryBasefold.Witness K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ') (Fin.last ℓ'))
    (WitOut := Unit)
    (pSpec := BinaryBasefold.pSpecFinalSumcheckStep (L:=L))
    (WitMid := FinalSumcheckWit κ (L := L) K β ℓ' 𝓡 (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  extractIn := fun _ w => w
  extractMid := fun m ⟨stmtMid, oStmtMid⟩ trSucc witMidSucc => by
    have hm : m = 0 := by omega
    subst hm
    have _ : witMidSucc = () := by rfl
    -- Decode t from the first oracle f^(0)
    let f0 := getFirstOracle K β oStmtMid
    let polyOpt := extractMlp K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
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
        t := tpoly,
        H := H_constant,
        f := getMidCodewords K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          tpoly stmtMid.challenges
      }
  extractOut := fun ⟨stmtIn, oStmtIn⟩ tr witOut => ()


def finalSumcheckKStateProp_native {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheckStep (L := L)))
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ (ringSwitchingProfile κ L K β)) (Fin.last ℓ'))
    (witMid : FinalSumcheckWit κ (L := L) K β ℓ' 𝓡 (h_ℓ_add_R_rate := h_ℓ_add_R_rate) m)
    (oStmt : ∀ j, BinaryBasefold.OracleStatement K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ') j) : Prop :=
  match m with
  | ⟨0, _⟩ =>
    BinaryBasefold.KnowledgeInvariant K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (multpoly := (RingSwitching_SumcheckMultParam κ L K
        (ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly)
      (stmtIdx := Fin.last ℓ') (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ'))
      stmt witMid oStmt
      (localChecks := Sumcheck.Structured.sumcheckConsistencyProp
        (SumcheckDomain.uniform 𝓑 _) stmt.sumcheck_target witMid.H)
  | ⟨1, _⟩ =>
    let c : L := tr.messages ⟨0, rfl⟩
    let stmtOut := finalSumcheckVerifierStmtOut κ L K β ℓ ℓ' h_l stmt c
    (stmt.sumcheck_target = compute_final_eq_value κ L K
      (ringSwitchingProfile κ L K β) ℓ ℓ' h_l
      stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching * c) ∧
      BinaryBasefold.FinalSumcheckFoldingState K β (input := (stmtOut, oStmt))

/-- The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction_native {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).KnowledgeStateFunction init impl
    (relIn := roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (multpoly := (RingSwitching_SumcheckMultParam κ L K
        (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly) (Fin.last ℓ'))
    (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (extractor := finalSumcheckRbrExtractor_native κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
  where
  toFun := fun m ⟨stmtIn, oStmtIn⟩ tr witMid =>
    finalSumcheckKStateProp_native κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑)
      (tr := tr) (stmt := stmtIn) (witMid := witMid) (oStmt := oStmtIn)
  toFun_empty := fun ⟨stmtIn, oStmtIn⟩ witMid h => h
  toFun_next := fun m hDir (stmtIn, oStmtIn) tr msg witMid => by
    have h_m_eq_0 : m = 0 := by
      cases m using Fin.cases with
      | zero => rfl
      | succ m' => omega
    subst h_m_eq_0
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.castSucc_zero]
    -- For the final sumcheck step, there is a single P→V message carrying the final constant,
    -- so we can read it directly from `msg` without reconstructing a truncated transcript.
    let c : L := msg
    let stmtOut := finalSumcheckVerifierStmtOut κ L K β ℓ ℓ' h_l stmtIn c

    intro h_kState_round1
    unfold finalSumcheckKStateProp_native FinalSumcheckFoldingState
      KnowledgeInvariant at h_kState_round1 ⊢
    simp only [Fin.isValue, Nat.reduceAdd, Fin.mk_one,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod] at h_kState_round1
    -- At m=1 we have local final-check and (oracle-consistency ∨ block-bad-event).
    -- At m=0 the target is `KnowledgeInvariant`:
    -- incremental-bad-event ∨ (local ∧ structural ∧ initial ∧ oracleFoldingConsistency).
    obtain ⟨h_V_check, h_core⟩ := h_kState_round1
    -- Case split on the m=1 final-folding state: consistency or block bad-event.
    cases h_core with
    | inl hConsistent =>
      -- When we have FinalSumcheckOracleConsistent, extractMlp must succeed.
      have ⟨tpoly, h_extractMLP⟩ :=
          BinaryBasefold.CoreInteraction.exists_extractMlp_eq_some_of_finalSumcheckOracleConsistent K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmtIn) (h_oracle_consistency := hConsistent)
      refine Or.inr ?_
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- local check at m=0
        unfold finalSumcheckRbrExtractor_native Sumcheck.Structured.sumcheckConsistencyProp
        simp only [Fin.val_last, Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod]
        symm
        calc ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ' - ℓ'), (MvPolynomial.eval x)
                (MvPolynomial.C stmtIn.sumcheck_target)
            = ∑ _x ∈ (univ.map 𝓑) ^ᶠ (ℓ' - ℓ'), stmtIn.sumcheck_target :=
              Finset.sum_congr rfl (fun x _ => MvPolynomial.eval_C (f := x) stmtIn.sumcheck_target)
          _ = stmtIn.sumcheck_target := by
              simp only [Finset.sum_const, Fintype.card_piFinset, Finset.card_map,
                Finset.card_univ, Fintype.card_fin, Finset.prod_const, tsub_self, pow_zero,
                one_smul]
      · -- WitnessStructuralInvariant
        unfold finalSumcheckRbrExtractor_native WitnessStructuralInvariant
        simp only [Fin.val_last, Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, and_true]
        refine SetLike.coe_eq_coe.mp ?_
        rw [Sumcheck.Structured.coe_fixPrefix_initial_last ℓ' tpoly
          ((RingSwitching_SumcheckMultParam κ L K (ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx) stmtIn.challenges]
        have h_sumcheck_target_eq : stmtIn.sumcheck_target =
          (MvPolynomial.eval stmtIn.challenges
            ((RingSwitching_SumcheckMultParam κ L K (ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val) *
            (MvPolynomial.eval stmtIn.challenges tpoly.val) := by
          rw [h_V_check]
          rw [show (MvPolynomial.eval stmtIn.challenges) ((RingSwitching_SumcheckMultParam κ L K (ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly stmtIn.ctx).val =
            compute_final_eq_value κ L K (ringSwitchingProfile κ L K β) ℓ ℓ' h_l
              stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching from
            RingSwitching.A_MLE_eval_eq_compute_final_eq_value
              (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l
              stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching]
          congr 1
          change c = tpoly.val.eval stmtIn.challenges
          exact BinaryBasefold.CoreInteraction.eval_eq_final_constant_of_extractMlp_eq_some K β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmtOut := oStmtIn) (stmtOut := stmtOut)
            (tpoly := tpoly)
            (h_extractMLP := h_extractMLP) (h_finalSumcheckStepOracleConsistency := hConsistent)
        simp only
          [h_sumcheck_target_eq, Fin.val_last, Fin.coe_ofNat_eq_mod, MvPolynomial.C_mul]
      · -- FirstOracleWitnessConsistent
        dsimp only [finalSumcheckRbrExtractor_native, FirstOracleWitnessConsistent]
        simp only [Fin.mk_zero', h_extractMLP, Fin.coe_ofNat_eq_mod, Fin.val_last,
          OracleFrontierIndex.val_mkFromStmtIdx]
        exact (extractMlp_eq_some_iff_pairUniqueDecodingClose K β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (f := getFirstOracle K β oStmtIn) (tpoly := tpoly)).mp h_extractMLP
      · exact hConsistent.1
    | inr hBad =>
      -- A block bad event at the last round is an incremental bad event there.
      exact Or.inl (
        (blockBadEventExists_iff_incrementalBadEventExists_last K β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
          (oStmt := oStmtIn) (challenges := stmtIn.challenges)).1 hBad
      )
  toFun_full := fun s tr witOut h => by
    change FullTranscript (pSpecFinalSumcheckStep (L := L)) at tr
    obtain ⟨hcheck, hrel⟩ := (finalSumcheckVerifierGuardedForm κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).check_and_of_prEvent_pos h
    rw [finalSumcheckVerifierGuardedForm_check_native κ L K β ℓ ℓ' 𝓡 ϑ
      h_ℓ_add_R_rate h_l s tr] at hcheck

    exact ⟨of_decide_eq_true hcheck, hrel⟩
/-- Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness_native {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l
      (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (relIn := roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) (multpoly := (RingSwitching_SumcheckMultParam κ L K
          (P := ringSwitchingProfile κ L K β) ℓ ℓ' h_l).multpoly) (Fin.last ℓ'))
      (relOut := BinaryBasefold.finalSumcheckRelOut K β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (rbrKnowledgeError := finalSumcheckKnowledgeError L) := by
  classical
  have hWith := Verifier.rbrKnowledgeSoundnessWorstCaseWith_of_isEmpty_challengeIdx
    (rbrKnowledgeError := finalSumcheckKnowledgeError L)
    (finalSumcheckRbrExtractor_native κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate)
    (finalSumcheckKnowledgeStateFunction_native κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑) init impl)
  exact Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    ((Verifier.rbrKnowledgeSoundnessWorstCase_iff_exists_with init impl _ _ _ _).mpr
      ⟨_, _, _, hWith⟩)

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

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for the core interaction oracle reduction -/
theorem coreInteractionOracleReduction_perfectCompleteness_native (hInit : NeverFail init)
    (hAppendPerfectCompleteness :
      OracleReduction.perfectCompleteness
        (oSpec := []ₒ)
        (pSpec := BinaryBasefold.pSpecCoreInteraction K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        (OStmtIn := BinaryBasefold.OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
        (OStmtOut := BinaryBasefold.OracleStatement K β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ'))
        (relIn := nativeStrictSumcheckInputRelation κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
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
      (relIn := nativeStrictSumcheckInputRelation κ L K β ℓ ℓ' 𝓡 ϑ h_ℓ_add_R_rate h_l (𝓑 := 𝓑))
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

-- Axiom audit: the native and separately retained historical results require no admissions.
#print axioms Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction_perfectCompleteness_native
#print axioms Binius.FRIBinius.CoreInteractionPhase.sumcheckFold_legacy_input_bridge_counterexample
#print axioms Binius.FRIBinius.CoreInteractionPhase.finalCodeword_zero_eq_t_eval
#print axioms Binius.FRIBinius.CoreInteractionPhase.iterated_fold_to_const_strict
#print axioms Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStep_verifierCheck_passed
#print axioms Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStep_is_logic_complete_native
#print axioms Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness_native
#print axioms Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction_native
#print axioms Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness_native
#print axioms Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness_native
#print axioms Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness
#print axioms Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError_le
