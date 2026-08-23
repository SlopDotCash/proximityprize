/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.OracleZeroKnowledge
import ArkLib.ToMathlib.ZKTransferBricks

/-!
  # Oracle-reduction HVZK transfer bricks for #112

  This module lifts the reusable Reduction-level transfer lemmas from
  `ArkLib.ToMathlib.ZKTransferBricks` to the `OracleReduction` HVZK API boundary.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (OStmtIn i)] [∀ i, OracleInterface (pSpec.Message i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

/-- **OracleReduction perfect HVZK transfers along an equal honest distribution.** -/
theorem perfectHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : perfectHVZK init impl rel R₁ sim)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) =
        evalDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)) :
    perfectHVZK init impl rel R₂ sim :=
  Reduction.perfectHVZK.congr_honestDist h hdist

/-- **OracleReduction statistical HVZK transfers along an equal honest distribution.** -/
theorem statisticalHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) =
        evalDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)) :
    statisticalHVZK init impl rel R₂ sim ε :=
  Reduction.statisticalHVZK.congr_honestDist h hdist

/-- **OracleReduction perfect HVZK honest-distribution congruence with opposite-order equality.** -/
theorem perfectHVZK.congr_honestDist_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : perfectHVZK init impl rel R₁ sim)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn) =
        evalDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn)) :
    perfectHVZK init impl rel R₂ sim :=
  Reduction.perfectHVZK.congr_honestDist_symm h hdist

/-- **OracleReduction statistical HVZK honest-distribution congruence with opposite-order
equality.** -/
theorem statisticalHVZK.congr_honestDist_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn) =
        evalDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn)) :
    statisticalHVZK init impl rel R₂ sim ε :=
  Reduction.statisticalHVZK.congr_honestDist_symm h hdist

/-- **OracleReduction perfect HVZK is preserved under an equal simulator distribution.** -/
theorem perfectHVZK.simulator_congr
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : perfectHVZK init impl rel R sim)
    (hsim : ∀ stmtIn, evalDist (sim stmtIn) = evalDist (sim' stmtIn)) :
    perfectHVZK init impl rel R sim' :=
  Reduction.perfectHVZK.simulator_congr h hsim

/-- **OracleReduction statistical HVZK is preserved under an equal simulator distribution.** -/
theorem statisticalHVZK.simulator_congr
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R sim ε)
    (hsim : ∀ stmtIn, evalDist (sim stmtIn) = evalDist (sim' stmtIn)) :
    statisticalHVZK init impl rel R sim' ε :=
  Reduction.statisticalHVZK.simulator_congr h hsim

/-- **OracleReduction perfect HVZK simulator congruence with opposite-order equality.** -/
theorem perfectHVZK.simulator_congr_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : perfectHVZK init impl rel R sim)
    (hsim : ∀ stmtIn, evalDist (sim' stmtIn) = evalDist (sim stmtIn)) :
    perfectHVZK init impl rel R sim' :=
  h.simulator_congr fun stmtIn => (hsim stmtIn).symm

/-- **OracleReduction statistical HVZK simulator congruence with opposite-order equality.** -/
theorem statisticalHVZK.simulator_congr_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R sim ε)
    (hsim : ∀ stmtIn, evalDist (sim' stmtIn) = evalDist (sim stmtIn)) :
    statisticalHVZK init impl rel R sim' ε :=
  h.simulator_congr fun stmtIn => (hsim stmtIn).symm

/-- **A concrete OracleReduction perfect-HVZK simulator witnesses existential HVZK.** -/
theorem perfectHVZK.isHVZK
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : perfectHVZK init impl rel R sim) :
    _root_.OracleReduction.isHVZK init impl rel R :=
  ⟨sim, h⟩

/-- **A concrete OracleReduction statistical-HVZK simulator witnesses existential statistical
HVZK.** -/
theorem statisticalHVZK.isStatHVZK
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R sim ε) :
    _root_.OracleReduction.isStatHVZK init impl rel R ε :=
  ⟨sim, h⟩

/-- **Package an OracleReduction perfect-HVZK proof after normalizing the simulator
distribution.** -/
theorem perfectHVZK.isHVZK_of_simulator_congr
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : perfectHVZK init impl rel R sim)
    (hsim : ∀ stmtIn, evalDist (sim stmtIn) = evalDist (sim' stmtIn)) :
    _root_.OracleReduction.isHVZK init impl rel R :=
  ⟨sim', h.simulator_congr hsim⟩

/-- **Package an OracleReduction statistical-HVZK proof after normalizing the simulator
distribution.** -/
theorem statisticalHVZK.isStatHVZK_of_simulator_congr
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R sim ε)
    (hsim : ∀ stmtIn, evalDist (sim stmtIn) = evalDist (sim' stmtIn)) :
    _root_.OracleReduction.isStatHVZK init impl rel R ε :=
  ⟨sim', h.simulator_congr hsim⟩

/-- **Package an OracleReduction perfect-HVZK proof after simulator normalization in the opposite
direction.** -/
theorem perfectHVZK.isHVZK_of_simulator_congr_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : perfectHVZK init impl rel R sim)
    (hsim : ∀ stmtIn, evalDist (sim' stmtIn) = evalDist (sim stmtIn)) :
    _root_.OracleReduction.isHVZK init impl rel R :=
  ⟨sim', h.simulator_congr_symm hsim⟩

/-- **Package an OracleReduction statistical-HVZK proof after simulator normalization in the
opposite direction.** -/
theorem statisticalHVZK.isStatHVZK_of_simulator_congr_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R sim ε)
    (hsim : ∀ stmtIn, evalDist (sim' stmtIn) = evalDist (sim stmtIn)) :
    _root_.OracleReduction.isStatHVZK init impl rel R ε :=
  ⟨sim', h.simulator_congr_symm hsim⟩

/-- **Triangle composition of statistical HVZK at the OracleReduction API boundary.** -/
theorem statisticalHVZK.simulator_triangle
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim₁ sim₂ : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (h₁ : statisticalHVZK init impl rel R sim₁ ε₁)
    (h₂ : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn)
        (sim₂ stmtIn) ≤ (ε₂ : ℝ)) :
    ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (sim₁ stmtIn) (sim₂ stmtIn) ≤ ((ε₁ + ε₂ : ℝ≥0) : ℝ) :=
  Reduction.statisticalHVZK.simulator_triangle h₁ h₂

/-- **Approximate honest-distribution transfer at the OracleReduction API boundary.** -/
theorem statisticalHVZK.triangle_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn) ≤ (ε₂ : ℝ)) :
    statisticalHVZK init impl rel R₂ sim (ε₁ + ε₂) :=
  Reduction.statisticalHVZK.triangle_honestDist h hdist

/-- **Symmetric-facing approximate honest-distribution transfer at the OracleReduction API
boundary.** -/
theorem statisticalHVZK.triangle_honestDist_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) ≤ (ε₂ : ℝ)) :
    statisticalHVZK init impl rel R₂ sim (ε₁ + ε₂) :=
  Reduction.statisticalHVZK.triangle_honestDist_symm h hdist

/-- **Zero-error approximate honest-distribution transfer for statistical HVZK at the
OracleReduction API boundary.** -/
theorem statisticalHVZK.triangle_honestDist_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn) ≤ (0 : ℝ)) :
    statisticalHVZK init impl rel R₂ sim ε :=
  Reduction.statisticalHVZK.triangle_honestDist_zero h hdist

/-- Symmetric-facing zero-error approximate honest-distribution transfer for statistical HVZK at
the OracleReduction API boundary. -/
theorem statisticalHVZK.triangle_honestDist_symm_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) ≤ (0 : ℝ)) :
    statisticalHVZK init impl rel R₂ sim ε :=
  Reduction.statisticalHVZK.triangle_honestDist_symm_zero h hdist

/-- **Zero-error approximate honest-distribution transfer for perfect HVZK at the
OracleReduction API boundary.** -/
theorem perfectHVZK.triangle_honestDist_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : perfectHVZK init impl rel R₁ sim)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn) ≤ (0 : ℝ)) :
    perfectHVZK init impl rel R₂ sim :=
  Reduction.perfectHVZK.triangle_honestDist_zero h hdist

/-- Symmetric-facing zero-error approximate honest-distribution transfer for perfect HVZK at the
OracleReduction API boundary. -/
theorem perfectHVZK.triangle_honestDist_symm_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : perfectHVZK init impl rel R₁ sim)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) ≤ (0 : ℝ)) :
    perfectHVZK init impl rel R₂ sim :=
  Reduction.perfectHVZK.triangle_honestDist_symm_zero h hdist

/-- **OracleReduction constant-simulator criterion for perfect HVZK.** -/
theorem perfectHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn) =
        evalDist d) :
    perfectHVZK init impl rel R (fun _ => d) :=
  Reduction.perfectHVZK_of_honestDist_eq_const d hdist

/-- **OracleReduction constant-simulator criterion for statistical HVZK.** -/
theorem statisticalHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn) =
        evalDist d)
    (ε : ℝ≥0) :
    statisticalHVZK init impl rel R (fun _ => d) ε :=
  Reduction.statisticalHVZK_of_honestDist_eq_const d hdist ε

/-- **Symmetric-facing OracleReduction constant-simulator criterion for perfect HVZK.** -/
theorem perfectHVZK_of_const_eq_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist d =
        evalDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn)) :
    perfectHVZK init impl rel R (fun _ => d) := by
  intro stmtIn witIn hMem
  exact hdist stmtIn witIn hMem

/-- **Symmetric-facing OracleReduction constant-simulator criterion for statistical HVZK.** -/
theorem statisticalHVZK_of_const_eq_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist d =
        evalDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn))
    (ε : ℝ≥0) :
    statisticalHVZK init impl rel R (fun _ => d) ε :=
  (perfectHVZK_of_const_eq_honestDist d hdist).statisticalHVZK ε

/-- **OracleReduction `isHVZK` from the constant-simulator criterion.** -/
theorem isHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn) =
        evalDist d) :
    isHVZK init impl rel R :=
  ⟨fun _ => d, perfectHVZK_of_honestDist_eq_const d hdist⟩

/-- **OracleReduction `isStatHVZK` from the constant-simulator criterion.** -/
theorem isStatHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn) =
        evalDist d)
    (ε : ℝ≥0) :
    isStatHVZK init impl rel R ε :=
  ⟨fun _ => d, statisticalHVZK_of_honestDist_eq_const d hdist ε⟩

/-- **OracleReduction `isHVZK` from the symmetric-facing constant-simulator criterion.** -/
theorem isHVZK_of_const_eq_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist d =
        evalDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn)) :
    isHVZK init impl rel R :=
  ⟨fun _ => d, perfectHVZK_of_const_eq_honestDist d hdist⟩

/-- **OracleReduction `isStatHVZK` from the symmetric-facing constant-simulator criterion.** -/
theorem isStatHVZK_of_const_eq_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist d =
        evalDist (Reduction.honestTranscriptDist init impl R.toReduction stmtIn witIn))
    (ε : ℝ≥0) :
    isStatHVZK init impl rel R ε :=
  ⟨fun _ => d, statisticalHVZK_of_const_eq_honestDist d hdist ε⟩

/-- **OracleReduction `isHVZK` transfers along an equal honest distribution.** -/
theorem isHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (h : isHVZK init impl rel R₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) =
        evalDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)) :
    isHVZK init impl rel R₂ :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.congr_honestDist hdist⟩

/-- **OracleReduction `isStatHVZK` transfers along an equal honest distribution.** -/
theorem isStatHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {ε : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) =
        evalDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)) :
    isStatHVZK init impl rel R₂ ε :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.congr_honestDist hdist⟩

/-- **OracleReduction `isHVZK` honest-distribution congruence with opposite-order equality.** -/
theorem isHVZK.congr_honestDist_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (h : isHVZK init impl rel R₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn) =
        evalDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn)) :
    isHVZK init impl rel R₂ :=
  h.congr_honestDist fun stmtIn witIn hMem => (hdist stmtIn witIn hMem).symm

/-- **OracleReduction `isStatHVZK` honest-distribution congruence with opposite-order equality.** -/
theorem isStatHVZK.congr_honestDist_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {ε : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn) =
        evalDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn)) :
    isStatHVZK init impl rel R₂ ε :=
  h.congr_honestDist fun stmtIn witIn hMem => (hdist stmtIn witIn hMem).symm

/-- **Existential approximate honest-distribution transfer at the OracleReduction API boundary.** -/
theorem isStatHVZK.triangle_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {ε₁ ε₂ : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn) ≤ (ε₂ : ℝ)) :
    isStatHVZK init impl rel R₂ (ε₁ + ε₂) :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.triangle_honestDist hdist⟩

/-- **Existential symmetric-facing approximate honest-distribution transfer at the
OracleReduction API boundary.** -/
theorem isStatHVZK.triangle_honestDist_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {ε₁ ε₂ : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) ≤ (ε₂ : ℝ)) :
    isStatHVZK init impl rel R₂ (ε₁ + ε₂) :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.triangle_honestDist_symm hdist⟩

/-- **Existential zero-error approximate honest-distribution transfer for statistical HVZK at the
OracleReduction API boundary.** -/
theorem isStatHVZK.triangle_honestDist_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {ε : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn) ≤ (0 : ℝ)) :
    isStatHVZK init impl rel R₂ ε :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.triangle_honestDist_zero hdist⟩

/-- **Existential symmetric-facing zero-error approximate honest-distribution transfer for
statistical HVZK at the OracleReduction API boundary.** -/
theorem isStatHVZK.triangle_honestDist_symm_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {ε : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) ≤ (0 : ℝ)) :
    isStatHVZK init impl rel R₂ ε :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.triangle_honestDist_symm_zero hdist⟩

/-- **Existential zero-error approximate honest-distribution transfer for exact HVZK at the
OracleReduction API boundary.** -/
theorem isHVZK.triangle_honestDist_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (h : isHVZK init impl rel R₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn) ≤ (0 : ℝ)) :
    isHVZK init impl rel R₂ :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.triangle_honestDist_zero hdist⟩

/-- **Existential symmetric-facing zero-error approximate honest-distribution transfer for exact
HVZK at the OracleReduction API boundary.** -/
theorem isHVZK.triangle_honestDist_symm_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {R₁ R₂ : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (h : isHVZK init impl rel R₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (Reduction.honestTranscriptDist init impl R₂.toReduction stmtIn witIn)
        (Reduction.honestTranscriptDist init impl R₁.toReduction stmtIn witIn) ≤ (0 : ℝ)) :
    isHVZK init impl rel R₂ :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.triangle_honestDist_symm_zero hdist⟩

#print axioms perfectHVZK.congr_honestDist
#print axioms statisticalHVZK.congr_honestDist
#print axioms perfectHVZK.congr_honestDist_symm
#print axioms statisticalHVZK.congr_honestDist_symm
#print axioms perfectHVZK.simulator_congr
#print axioms statisticalHVZK.simulator_congr
#print axioms perfectHVZK.simulator_congr_symm
#print axioms statisticalHVZK.simulator_congr_symm
#print axioms perfectHVZK.isHVZK
#print axioms statisticalHVZK.isStatHVZK
#print axioms perfectHVZK.isHVZK_of_simulator_congr
#print axioms statisticalHVZK.isStatHVZK_of_simulator_congr
#print axioms perfectHVZK.isHVZK_of_simulator_congr_symm
#print axioms statisticalHVZK.isStatHVZK_of_simulator_congr_symm
#print axioms statisticalHVZK.simulator_triangle
#print axioms statisticalHVZK.triangle_honestDist
#print axioms statisticalHVZK.triangle_honestDist_symm
#print axioms statisticalHVZK.triangle_honestDist_zero
#print axioms statisticalHVZK.triangle_honestDist_symm_zero
#print axioms perfectHVZK.triangle_honestDist_zero
#print axioms perfectHVZK.triangle_honestDist_symm_zero
#print axioms perfectHVZK_of_honestDist_eq_const
#print axioms statisticalHVZK_of_honestDist_eq_const
#print axioms perfectHVZK_of_const_eq_honestDist
#print axioms statisticalHVZK_of_const_eq_honestDist
#print axioms isHVZK_of_honestDist_eq_const
#print axioms isStatHVZK_of_honestDist_eq_const
#print axioms isHVZK_of_const_eq_honestDist
#print axioms isStatHVZK_of_const_eq_honestDist
#print axioms isHVZK.congr_honestDist
#print axioms isStatHVZK.congr_honestDist
#print axioms isHVZK.congr_honestDist_symm
#print axioms isStatHVZK.congr_honestDist_symm
#print axioms isStatHVZK.triangle_honestDist
#print axioms isStatHVZK.triangle_honestDist_symm
#print axioms isStatHVZK.triangle_honestDist_zero
#print axioms isStatHVZK.triangle_honestDist_symm_zero
#print axioms isHVZK.triangle_honestDist_zero
#print axioms isHVZK.triangle_honestDist_symm_zero

end OracleReduction
