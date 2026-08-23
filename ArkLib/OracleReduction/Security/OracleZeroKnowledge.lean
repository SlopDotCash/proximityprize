/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
  # Honest-Verifier Zero-Knowledge for Oracle Reductions

  This module exposes the transcript-level HVZK predicates from
  `ArkLib.OracleReduction.Security.ZeroKnowledge` at the `OracleReduction` API boundary. As with
  completeness and soundness, the oracle-reduction predicate delegates to the associated
  non-oracle `Reduction` obtained by `OracleReduction.toReduction`.
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

section Definitions

/-- Transcript simulators for oracle reductions are simulators for the associated non-oracle
  reduction, whose input statement packages the public statement together with the input oracle
  statements. -/
abbrev TranscriptSimulator
    (oSpec : OracleSpec ι) (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    {n : ℕ} (pSpec : ProtocolSpec n) :=
  Reduction.TranscriptSimulator oSpec (StmtIn × (∀ i, OStmtIn i)) pSpec

/-- Perfect HVZK for an oracle reduction, delegated through `OracleReduction.toReduction`. -/
def perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec) : Prop :=
  Reduction.perfectHVZK init impl rel oracleReduction.toReduction sim

/-- Statistical HVZK for an oracle reduction, delegated through `OracleReduction.toReduction`. -/
def statisticalHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec) (ε : ℝ≥0) : Prop :=
  Reduction.statisticalHVZK init impl rel oracleReduction.toReduction sim ε

/-- Existential perfect HVZK for an oracle reduction. -/
def isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) : Prop :=
  ∃ sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec,
    perfectHVZK init impl rel oracleReduction sim

/-- Existential statistical HVZK for an oracle reduction. -/
def isStatHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (ε : ℝ≥0) : Prop :=
  ∃ sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec,
    statisticalHVZK init impl rel oracleReduction sim ε

end Definitions

section BasicLemmas

/-- Perfect HVZK for oracle reductions is exactly statistical HVZK with error `0`. -/
theorem perfectHVZK_iff_statisticalHVZK_zero
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec) :
    perfectHVZK init impl rel oracleReduction sim ↔
      statisticalHVZK init impl rel oracleReduction sim 0 :=
  Reduction.perfectHVZK_iff_statisticalHVZK_zero init impl rel oracleReduction.toReduction sim

/-- Perfect HVZK for oracle reductions implies statistical HVZK with any error bound. -/
theorem perfectHVZK.statisticalHVZK
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : perfectHVZK init impl rel oracleReduction sim) (ε : ℝ≥0) :
    statisticalHVZK init impl rel oracleReduction sim ε :=
  Reduction.perfectHVZK.statisticalHVZK h ε

/-- Perfect HVZK for oracle reductions is antitone in the relation. -/
theorem perfectHVZK.mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : perfectHVZK init impl rel oracleReduction sim) (hsub : rel' ⊆ rel) :
    perfectHVZK init impl rel' oracleReduction sim :=
  Reduction.perfectHVZK.mono_relation h hsub

/-- `isHVZK` for oracle reductions is antitone in the relation. -/
theorem isHVZK.mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (h : isHVZK init impl rel oracleReduction) (hsub : rel' ⊆ rel) :
    isHVZK init impl rel' oracleReduction :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.mono_relation hsub⟩

/-- Statistical HVZK for oracle reductions is antitone in the relation. -/
theorem statisticalHVZK.mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel oracleReduction sim ε) (hsub : rel' ⊆ rel) :
    statisticalHVZK init impl rel' oracleReduction sim ε :=
  Reduction.statisticalHVZK.mono_relation h hsub

/-- Statistical HVZK for oracle reductions is monotone in the error bound. -/
theorem statisticalHVZK.mono_error
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (h : statisticalHVZK init impl rel oracleReduction sim ε₁) (hle : ε₁ ≤ ε₂) :
    statisticalHVZK init impl rel oracleReduction sim ε₂ :=
  Reduction.statisticalHVZK.mono_error h hle

/-- Perfect HVZK existence for oracle reductions implies statistical HVZK existence. -/
theorem isHVZK.isStatHVZK
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (h : isHVZK init impl rel oracleReduction) (ε : ℝ≥0) :
    isStatHVZK init impl rel oracleReduction ε :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.statisticalHVZK ε⟩

/-- Zero-error statistical HVZK existence for oracle reductions recovers perfect HVZK existence. -/
theorem isStatHVZK_zero.isHVZK
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (h : isStatHVZK init impl rel oracleReduction 0) :
    isHVZK init impl rel oracleReduction :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, (perfectHVZK_iff_statisticalHVZK_zero init impl rel oracleReduction sim).2 hsim⟩

/-- Perfect HVZK existence for oracle reductions is equivalent to zero-error statistical HVZK
  existence. -/
theorem isHVZK_iff_isStatHVZK_zero
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
    (oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
    isHVZK init impl rel oracleReduction ↔ isStatHVZK init impl rel oracleReduction 0 := by
  constructor
  · intro h
    exact h.isStatHVZK 0
  · intro h
    exact isStatHVZK_zero.isHVZK h

/-- `isStatHVZK` for oracle reductions is antitone in the relation. -/
theorem isStatHVZK.mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec} {ε : ℝ≥0}
    (h : isStatHVZK init impl rel oracleReduction ε) (hsub : rel' ⊆ rel) :
    isStatHVZK init impl rel' oracleReduction ε :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.mono_relation hsub⟩

/-- `isStatHVZK` for oracle reductions is monotone in the error bound. -/
theorem isStatHVZK.mono_error
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {ε₁ ε₂ : ℝ≥0}
    (h : isStatHVZK init impl rel oracleReduction ε₁) (hle : ε₁ ≤ ε₂) :
    isStatHVZK init impl rel oracleReduction ε₂ :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.mono_error hle⟩

/-- Statistical HVZK for oracle reductions transports across both relation restriction and error
  relaxation. -/
theorem statisticalHVZK.mono_relation_error
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (h : statisticalHVZK init impl rel oracleReduction sim ε₁)
    (hsub : rel' ⊆ rel) (hle : ε₁ ≤ ε₂) :
    statisticalHVZK init impl rel' oracleReduction sim ε₂ :=
  Reduction.statisticalHVZK.mono_relation_error h hsub hle

/-- Perfect HVZK for oracle reductions transports to statistical HVZK on a subrelation at any
  error. The same simulator is reused after restricting the relation. -/
theorem perfectHVZK.statisticalHVZK_mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec} {ε : ℝ≥0}
    (h : perfectHVZK init impl rel oracleReduction sim) (hsub : rel' ⊆ rel) :
    OracleReduction.statisticalHVZK init impl rel' oracleReduction sim ε :=
  OracleReduction.perfectHVZK.statisticalHVZK (h.mono_relation hsub) ε

/-- Zero-error statistical HVZK for oracle reductions converts back to perfect HVZK for the
  same simulator. -/
theorem statisticalHVZK_zero.perfectHVZK
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : statisticalHVZK init impl rel oracleReduction sim 0) :
    OracleReduction.perfectHVZK init impl rel oracleReduction sim :=
  (perfectHVZK_iff_statisticalHVZK_zero init impl rel oracleReduction sim).2 h

/-- Zero-error statistical HVZK for oracle reductions transports back to perfect HVZK on a
  subrelation. The same simulator is reused after restricting the relation. -/
theorem statisticalHVZK_zero.perfectHVZK_mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn OStmtIn pSpec}
    (h : statisticalHVZK init impl rel oracleReduction sim 0) (hsub : rel' ⊆ rel) :
    OracleReduction.perfectHVZK init impl rel' oracleReduction sim :=
  (perfectHVZK_iff_statisticalHVZK_zero init impl rel' oracleReduction sim).2
    (h.mono_relation hsub)

/-- Existential statistical HVZK for oracle reductions transports across both relation restriction
  and error relaxation. -/
theorem isStatHVZK.mono_relation_error
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {ε₁ ε₂ : ℝ≥0}
    (h : isStatHVZK init impl rel oracleReduction ε₁)
    (hsub : rel' ⊆ rel) (hle : ε₁ ≤ ε₂) :
    isStatHVZK init impl rel' oracleReduction ε₂ :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.mono_relation_error hsub hle⟩

/-- Perfect HVZK existence for oracle reductions transports to statistical HVZK on a restricted
  relation at any relaxed error. -/
theorem isHVZK.isStatHVZK_mono_relation_error
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {ε : ℝ≥0}
    (h : isHVZK init impl rel oracleReduction) (hsub : rel' ⊆ rel) :
    OracleReduction.isStatHVZK init impl rel' oracleReduction ε :=
  (h.mono_relation hsub).isStatHVZK ε

/-- Zero-error statistical HVZK existence for oracle reductions transports back to perfect HVZK
  existence on a subrelation. -/
theorem isStatHVZK_zero.isHVZK_mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)}
    {oracleReduction :
      OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    (h : isStatHVZK init impl rel oracleReduction 0) (hsub : rel' ⊆ rel) :
    OracleReduction.isHVZK init impl rel' oracleReduction :=
  (OracleReduction.isStatHVZK_zero.isHVZK h).mono_relation hsub

end BasicLemmas

section Identity

variable {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type} {Witness : Type}
  [∀ i, OracleInterface (OStatement i)]

/-- The zero-round identity oracle reduction is perfect HVZK for any oracle-input relation. -/
theorem id_perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((Statement × (∀ i, OStatement i)) × Witness)) :
    perfectHVZK init impl rel
      (OracleReduction.id :
        OracleReduction oSpec Statement OStatement Witness Statement OStatement Witness !p[])
      Reduction.idTranscriptSimulator := by
  unfold perfectHVZK
  simpa [OracleReduction.id_toReduction] using
    (Reduction.id_perfectHVZK (oSpec := oSpec) (StmtIn := Statement × (∀ i, OStatement i))
      (WitIn := Witness) (σ := σ) init impl rel)

/-- The zero-round identity oracle reduction is statistical HVZK for any oracle-input relation and
  any error bound. -/
theorem id_statisticalHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((Statement × (∀ i, OStatement i)) × Witness)) (ε : ℝ≥0) :
    statisticalHVZK init impl rel
      (OracleReduction.id :
        OracleReduction oSpec Statement OStatement Witness Statement OStatement Witness !p[])
      Reduction.idTranscriptSimulator ε := by
  unfold statisticalHVZK
  simpa [OracleReduction.id_toReduction] using
    (Reduction.id_statisticalHVZK (oSpec := oSpec)
      (StmtIn := Statement × (∀ i, OStatement i)) (WitIn := Witness) (σ := σ)
      init impl rel ε)

/-- The zero-round identity oracle reduction is HVZK for any oracle-input relation. -/
theorem id_isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((Statement × (∀ i, OStatement i)) × Witness)) :
    isHVZK init impl rel
      (OracleReduction.id :
        OracleReduction oSpec Statement OStatement Witness Statement OStatement Witness !p[]) := by
  exact ⟨Reduction.idTranscriptSimulator, id_perfectHVZK init impl rel⟩

/-- The zero-round identity oracle reduction is statistical HVZK for any oracle-input relation and
  any error bound. -/
theorem id_isStatHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set ((Statement × (∀ i, OStatement i)) × Witness)) (ε : ℝ≥0) :
    isStatHVZK init impl rel
      (OracleReduction.id :
        OracleReduction oSpec Statement OStatement Witness Statement OStatement Witness !p[])
      ε := by
  exact ⟨Reduction.idTranscriptSimulator, id_statisticalHVZK init impl rel ε⟩

end Identity

#print axioms TranscriptSimulator
#print axioms perfectHVZK
#print axioms statisticalHVZK
#print axioms isHVZK
#print axioms isStatHVZK
#print axioms perfectHVZK_iff_statisticalHVZK_zero
#print axioms perfectHVZK.statisticalHVZK
#print axioms perfectHVZK.mono_relation
#print axioms isHVZK.mono_relation
#print axioms statisticalHVZK.mono_relation
#print axioms statisticalHVZK.mono_error
#print axioms isHVZK.isStatHVZK
#print axioms isStatHVZK_zero.isHVZK
#print axioms isHVZK_iff_isStatHVZK_zero
#print axioms isStatHVZK.mono_relation
#print axioms isStatHVZK.mono_error
#print axioms statisticalHVZK.mono_relation_error
#print axioms perfectHVZK.statisticalHVZK_mono_relation
#print axioms statisticalHVZK_zero.perfectHVZK
#print axioms statisticalHVZK_zero.perfectHVZK_mono_relation
#print axioms isStatHVZK.mono_relation_error
#print axioms isHVZK.isStatHVZK_mono_relation_error
#print axioms isStatHVZK_zero.isHVZK_mono_relation
#print axioms id_perfectHVZK
#print axioms id_statisticalHVZK
#print axioms id_isHVZK
#print axioms id_isStatHVZK

end OracleReduction
