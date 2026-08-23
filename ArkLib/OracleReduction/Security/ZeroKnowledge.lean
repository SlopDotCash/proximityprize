/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Honest-Verifier Zero-Knowledge for Reductions

  This file defines transcript-level honest-verifier zero-knowledge for `Reduction`s, stated against
  the existing `Reduction.run` execution semantics and the existing probability vocabulary
  (`evalDist`, `tvDist`, `probEvent`).

  The honest interaction produces, for a given `(stmtIn, witIn)`, a full transcript
  `FullTranscript pSpec` together with prover and verifier outputs. We interpret that computation
  into `ProbComp` by `simulateQ`-ing the shared-oracle implementation `impl` together with the
  honest challenge sampler `challengeQueryImpl`, then project onto the transcript.

  A `TranscriptSimulator` produces a transcript distribution from the input statement alone. The
  predicates below compare that simulator distribution with the honest transcript distribution:

  - `perfectHVZK`: equality of `evalDist`s for every related statement-witness pair.
  - `statisticalHVZK`: total-variation distance at most `ε`.

  The file also records the zero-round identity reduction as the first concrete perfect-HVZK
  instance.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

section Definitions

/-- The honest transcript distribution of a reduction on input `(stmtIn, witIn)`: run the reduction
  with honest verifier challenges and the shared-oracle implementation `impl`, then project onto the
  full transcript. The computation lives in `OptionT ProbComp` because the reduction execution may
  fail. -/
def honestTranscriptDist
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    OptionT ProbComp (FullTranscript pSpec) :=
  OptionT.mk do
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    (simulateQ pImpl
      ((fun result => result.1.1) <$> (reduction.run stmtIn witIn)).run).run' (← init)

/-- A transcript simulator produces, from the input statement alone, a distribution over full
  transcripts. This is the post-interpretation transcript-level form of `Reduction.Simulator`. -/
def TranscriptSimulator (_oSpec : OracleSpec ι) (StmtIn : Type) {n : ℕ}
    (pSpec : ProtocolSpec n) :=
  StmtIn → OptionT ProbComp (FullTranscript pSpec)

/-- A reduction satisfies perfect honest-verifier zero-knowledge with respect to a simulator and
  relation `rel` if the simulator's transcript distribution agrees with the honest transcript
  distribution for every related statement-witness pair. -/
def perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sim : TranscriptSimulator oSpec StmtIn pSpec) : Prop :=
  ∀ stmtIn : StmtIn, ∀ witIn : WitIn, (stmtIn, witIn) ∈ rel →
    evalDist (sim stmtIn) = evalDist (honestTranscriptDist init impl reduction stmtIn witIn)

/-- A reduction satisfies statistical honest-verifier zero-knowledge with error `ε` if the
  simulator's transcript distribution is within total-variation distance `ε` of the honest
  transcript distribution for every related statement-witness pair. -/
def statisticalHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sim : TranscriptSimulator oSpec StmtIn pSpec) (ε : ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn, ∀ witIn : WitIn, (stmtIn, witIn) ∈ rel →
    tvDist (sim stmtIn) (honestTranscriptDist init impl reduction stmtIn witIn) ≤ (ε : ℝ)

/-- A reduction is honest-verifier zero-knowledge for relation `rel` if some simulator achieves
  perfect HVZK. -/
def isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  ∃ sim : TranscriptSimulator oSpec StmtIn pSpec, perfectHVZK init impl rel reduction sim

/-- A reduction is *statistically* honest-verifier zero-knowledge with error `ε` if some
  simulator achieves statistical HVZK within error `ε`. The statistical analogue of `isHVZK`. -/
def isStatHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (ε : ℝ≥0) : Prop :=
  ∃ sim : TranscriptSimulator oSpec StmtIn pSpec, statisticalHVZK init impl rel reduction sim ε

end Definitions

section BasicLemmas

/-- Perfect HVZK is exactly statistical HVZK with error `0`. -/
theorem perfectHVZK_iff_statisticalHVZK_zero
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sim : TranscriptSimulator oSpec StmtIn pSpec) :
    perfectHVZK init impl rel reduction sim ↔
      statisticalHVZK init impl rel reduction sim 0 := by
  unfold perfectHVZK statisticalHVZK
  constructor
  · intro h stmtIn witIn hMem
    have heq := h stmtIn witIn hMem
    simp only [NNReal.coe_zero]
    rw [show (0 : ℝ) = tvDist (honestTranscriptDist init impl reduction stmtIn witIn)
        (honestTranscriptDist init impl reduction stmtIn witIn) from (tvDist_self _).symm]
    rw [tvDist, tvDist, heq]
  · intro h stmtIn witIn hMem
    have := h stmtIn witIn hMem
    simp only [NNReal.coe_zero] at this
    have hle : tvDist (sim stmtIn) (honestTranscriptDist init impl reduction stmtIn witIn) ≤ 0 :=
      this
    have hge : 0 ≤ tvDist (sim stmtIn) (honestTranscriptDist init impl reduction stmtIn witIn) :=
      tvDist_nonneg _ _
    have hzero : tvDist (sim stmtIn) (honestTranscriptDist init impl reduction stmtIn witIn) = 0 :=
      le_antisymm hle hge
    rw [tvDist_eq_zero_iff] at hzero
    exact hzero

/-- Perfect HVZK implies statistical HVZK with any error `ε`. -/
theorem perfectHVZK.statisticalHVZK
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel reduction sim) (ε : ℝ≥0) :
    statisticalHVZK init impl rel reduction sim ε := by
  intro stmtIn witIn hMem
  have heq := h stmtIn witIn hMem
  have hzero :
      tvDist (sim stmtIn) (honestTranscriptDist init impl reduction stmtIn witIn) = 0 := by
    rw [tvDist_eq_zero_iff]
    exact heq
  rw [hzero]
  positivity

/-- **Perfect HVZK is antitone in the relation.** A simulator that matches the honest transcript
distribution on every pair of a relation `rel` also matches it on every pair of a sub-relation
`rel' ⊆ rel`. (One proves ZK on the full language relation and restricts as needed.) -/
theorem perfectHVZK.mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel reduction sim) (hsub : rel' ⊆ rel) :
    perfectHVZK init impl rel' reduction sim :=
  fun stmtIn witIn hMem => h stmtIn witIn (hsub hMem)

/-- **`isHVZK` is antitone in the relation.** HVZK for `rel` implies HVZK for any `rel' ⊆ rel`
(the same simulator works). -/
theorem isHVZK.mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (h : isHVZK init impl rel reduction) (hsub : rel' ⊆ rel) :
    isHVZK init impl rel' reduction :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.mono_relation hsub⟩

/-- **Statistical HVZK is antitone in the relation.** -/
theorem statisticalHVZK.mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel reduction sim ε) (hsub : rel' ⊆ rel) :
    statisticalHVZK init impl rel' reduction sim ε :=
  fun stmtIn witIn hMem => h stmtIn witIn (hsub hMem)

/-- **Statistical HVZK is monotone in the error.** A simulator within total-variation distance
`ε₁` is also within any larger error `ε₂ ≥ ε₁`. -/
theorem statisticalHVZK.mono_error
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (h : statisticalHVZK init impl rel reduction sim ε₁) (hle : ε₁ ≤ ε₂) :
    statisticalHVZK init impl rel reduction sim ε₂ :=
  fun stmtIn witIn hMem => le_trans (h stmtIn witIn hMem) (by exact_mod_cast hle)

/-- **Perfect HVZK implies statistical HVZK existence** at any error. -/
theorem isHVZK.isStatHVZK
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (h : isHVZK init impl rel reduction) (ε : ℝ≥0) :
    isStatHVZK init impl rel reduction ε :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.statisticalHVZK ε⟩

/-- **Zero-error statistical HVZK existence is perfect HVZK existence.** -/
theorem isStatHVZK_zero.isHVZK
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (h : isStatHVZK init impl rel reduction 0) :
    isHVZK init impl rel reduction :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, (perfectHVZK_iff_statisticalHVZK_zero init impl rel reduction sim).2 hsim⟩

/-- **Perfect HVZK existence is equivalent to zero-error statistical HVZK existence.** -/
theorem isHVZK_iff_isStatHVZK_zero
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    isHVZK init impl rel reduction ↔ isStatHVZK init impl rel reduction 0 := by
  constructor
  · intro h
    exact h.isStatHVZK 0
  · intro h
    exact isStatHVZK_zero.isHVZK h

/-- **`isStatHVZK` is antitone in the relation.** -/
theorem isStatHVZK.mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} {ε : ℝ≥0}
    (h : isStatHVZK init impl rel reduction ε) (hsub : rel' ⊆ rel) :
    isStatHVZK init impl rel' reduction ε :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.mono_relation hsub⟩

/-- **`isStatHVZK` is monotone in the error.** -/
theorem isStatHVZK.mono_error
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} {ε₁ ε₂ : ℝ≥0}
    (h : isStatHVZK init impl rel reduction ε₁) (hle : ε₁ ≤ ε₂) :
    isStatHVZK init impl rel reduction ε₂ :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.mono_error hle⟩

/-- **Statistical HVZK transports across both relation restriction and error relaxation.** -/
theorem statisticalHVZK.mono_relation_error
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (h : statisticalHVZK init impl rel reduction sim ε₁)
    (hsub : rel' ⊆ rel) (hle : ε₁ ≤ ε₂) :
    statisticalHVZK init impl rel' reduction sim ε₂ :=
  (h.mono_relation hsub).mono_error hle

/-- **Perfect HVZK transports to statistical HVZK on a subrelation at any error.** The same
simulator is reused after restricting the relation. -/
theorem perfectHVZK.statisticalHVZK_mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec} {ε : ℝ≥0}
    (h : perfectHVZK init impl rel reduction sim) (hsub : rel' ⊆ rel) :
    Reduction.statisticalHVZK init impl rel' reduction sim ε :=
  Reduction.perfectHVZK.statisticalHVZK (h.mono_relation hsub) ε

/-- **Zero-error statistical HVZK converts back to perfect HVZK for the same simulator.** -/
theorem statisticalHVZK_zero.perfectHVZK
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec}
    (h : statisticalHVZK init impl rel reduction sim 0) :
    Reduction.perfectHVZK init impl rel reduction sim :=
  (perfectHVZK_iff_statisticalHVZK_zero init impl rel reduction sim).2 h

/-- **Zero-error statistical HVZK transports back to perfect HVZK on a subrelation.** The same
simulator is reused after restricting the relation. -/
theorem statisticalHVZK_zero.perfectHVZK_mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec}
    (h : statisticalHVZK init impl rel reduction sim 0) (hsub : rel' ⊆ rel) :
    Reduction.perfectHVZK init impl rel' reduction sim :=
  (perfectHVZK_iff_statisticalHVZK_zero init impl rel' reduction sim).2
    (h.mono_relation hsub)

/-- **Existential statistical HVZK transports across both relation restriction and error
relaxation.** The same simulator witnesses the transported statement. -/
theorem isStatHVZK.mono_relation_error
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} {ε₁ ε₂ : ℝ≥0}
    (h : isStatHVZK init impl rel reduction ε₁)
    (hsub : rel' ⊆ rel) (hle : ε₁ ≤ ε₂) :
    isStatHVZK init impl rel' reduction ε₂ :=
  (h.mono_relation hsub).mono_error hle

/-- **Perfect HVZK existence gives statistical HVZK on any subrelation and relaxed error.** -/
theorem isHVZK.isStatHVZK_mono_relation_error
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} (ε : ℝ≥0)
    (h : isHVZK init impl rel reduction) (hsub : rel' ⊆ rel) :
    Reduction.isStatHVZK init impl rel' reduction ε :=
  (h.mono_relation hsub).isStatHVZK ε

/-- **Zero-error statistical HVZK existence transports back to perfect HVZK existence on a
subrelation.** -/
theorem isStatHVZK_zero.isHVZK_mono_relation
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel rel' : Set (StmtIn × WitIn)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (h : isStatHVZK init impl rel reduction 0) (hsub : rel' ⊆ rel) :
    Reduction.isHVZK init impl rel' reduction :=
  (Reduction.isStatHVZK_zero.isHVZK h).mono_relation hsub

end BasicLemmas

section Identity

variable {StmtIn WitIn : Type}

/-- The simulator for the zero-round identity reduction: ignore the statement and emit the unique
  empty transcript. -/
def idTranscriptSimulator :
    TranscriptSimulator oSpec StmtIn (!p[] : ProtocolSpec 0) :=
  fun _ => pure default

/-- The honest transcript distribution of the zero-round identity reduction is distributionally
  equal to `pure default`. The computation still samples and discards the ambient initialization
  state, so this is intentionally an `evalDist` equality rather than a raw term equality. -/
theorem honestTranscriptDist_id_evalDist
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmtIn : StmtIn) (witIn : WitIn) :
    evalDist (honestTranscriptDist init impl
        (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[]) stmtIn witIn) =
      evalDist (pure default : OptionT ProbComp (FullTranscript !p[])) := by
  apply evalDist_ext
  intro transcript
  classical
  unfold honestTranscriptDist
  simp only [Reduction.id_run, map_pure, OptionT.run_pure, simulateQ_pure, StateT.run'_eq,
    StateT.run_pure, bind_pure_comp]
  rw [OptionT.probOutput_eq, OptionT.probOutput_eq]
  simp [probOutput_map_const, HasEvalPMF.probFailure_eq_zero]

/-- The zero-round identity reduction satisfies perfect honest-verifier zero-knowledge for any
  input relation. -/
theorem id_perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn)) :
    perfectHVZK init impl rel
      (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[])
      idTranscriptSimulator := by
  intro stmtIn witIn _
  exact (honestTranscriptDist_id_evalDist init impl stmtIn witIn).symm

/-- The zero-round identity reduction satisfies statistical honest-verifier zero-knowledge for any
  relation and error bound. -/
theorem id_statisticalHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn)) (ε : ℝ≥0) :
    statisticalHVZK init impl rel
      (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[])
      idTranscriptSimulator ε :=
  (id_perfectHVZK init impl rel).statisticalHVZK ε

/-- The zero-round identity reduction is honest-verifier zero-knowledge for any relation. -/
theorem id_isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn)) :
    isHVZK init impl rel
      (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[]) :=
  ⟨idTranscriptSimulator, id_perfectHVZK init impl rel⟩

/-- The zero-round identity reduction is statistically honest-verifier zero-knowledge for any
  relation and error bound. -/
theorem id_isStatHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn)) (ε : ℝ≥0) :
    isStatHVZK init impl rel
      (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[]) ε :=
  (id_isHVZK init impl rel).isStatHVZK ε

end Identity

#print axioms honestTranscriptDist
#print axioms TranscriptSimulator
#print axioms perfectHVZK_iff_statisticalHVZK_zero
#print axioms perfectHVZK.statisticalHVZK
#print axioms honestTranscriptDist_id_evalDist
#print axioms id_perfectHVZK
#print axioms id_statisticalHVZK
#print axioms id_isHVZK
#print axioms id_isStatHVZK
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

end Reduction
