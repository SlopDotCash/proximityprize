/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
  # Scratch: HVZK transfer / composability bricks for #112

  Reusable lemmas that downstream simulator-composition and Fiat-Shamir HVZK transfer steps need:

  - `perfectHVZK.congr_honestDist`: perfect HVZK transfers to any reduction with the same honest
    transcript distribution (the simulator is reused unchanged).
  - `perfectHVZK.simulator_congr`: perfect HVZK is preserved when swapping in an
    `evalDist`-equal simulator.
  - `statisticalHVZK.simulator_congr`: statistical HVZK is preserved under the same simulator
    distribution congruence, with the error budget unchanged.
  - `perfectHVZK.simulator_congr_symm` / `statisticalHVZK.simulator_congr_symm`: the same
    simulator-congruence transfer when the `evalDist` equality is stated in the opposite order.
  - `perfectHVZK.isHVZK` / `statisticalHVZK.isStatHVZK`: package a concrete simulator proof into
    the corresponding existential zero-knowledge property.
  - `perfectHVZK.isHVZK_of_simulator_congr` / `statisticalHVZK.isStatHVZK_of_simulator_congr`:
    package an `evalDist`-equal normalized simulator into the existential API.
  - `statisticalHVZK.simulator_triangle`: two statistical-HVZK bounds compose by the triangle
    inequality, giving a combined error budget. This is the shape used when transferring a
    simulator across an `evalDist`-equal intermediate honest distribution.
  - `statisticalHVZK.triangle_honestDist`: statistical HVZK transfers across an approximate
    honest-transcript distribution bridge, adding the bridge error to the simulator error.
  - `statisticalHVZK.triangle_honestDist_symm`: the same transfer when the TV-distance bridge is
    stated in the opposite order.
  - `statisticalHVZK.triangle_honestDist_zero`: the budget-preserving specialization of the
    approximate transfer when the honest-distribution bridge has TV distance at most `0`.
  - `perfectHVZK.triangle_honestDist_zero`: zero-error approximate honest-distribution transfer
    for exact HVZK, via the statistical/perfect bridge at error `0`.
  - `perfectHVZK_of_honestDist_eq_const`: a constant simulator achieves perfect HVZK whenever the
    honest transcript distribution is `evalDist`-equal to a fixed distribution, generalizing the
    zero-round identity instance.
  - `statisticalHVZK_of_honestDist_eq_const`: the statistical counterpart of that constant
    simulator criterion, for any error budget.
  - `perfectHVZK_of_const_eq_honestDist` / `statisticalHVZK_of_const_eq_honestDist`: the same
    constant-simulator criteria when the distribution equality is stated in the opposite order.

  Everything is stated over the promoted `Reduction.perfectHVZK` / `statisticalHVZK` vocabulary in
  `ArkLib.OracleReduction.Security.ZeroKnowledge`.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

/-- **Perfect HVZK transfers along an `evalDist`-equal honest distribution.** If two reductions have
the same honest transcript distribution on every related pair, a simulator that is perfect-HVZK for
one is perfect-HVZK for the other. -/
theorem perfectHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel R₁ sim)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R₁ stmtIn witIn) =
        evalDist (honestTranscriptDist init impl R₂ stmtIn witIn)) :
    perfectHVZK init impl rel R₂ sim := by
  intro stmtIn witIn hMem
  rw [← hdist stmtIn witIn hMem]
  exact h stmtIn witIn hMem

/-- **Statistical HVZK transfers along an `evalDist`-equal honest distribution.** The same
simulator and error budget apply to any reduction with the same honest transcript distribution. -/
theorem statisticalHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R₁ stmtIn witIn) =
        evalDist (honestTranscriptDist init impl R₂ stmtIn witIn)) :
    statisticalHVZK init impl rel R₂ sim ε := by
  intro stmtIn witIn hMem
  unfold tvDist
  rw [← hdist stmtIn witIn hMem]
  exact h stmtIn witIn hMem

/-- **Perfect HVZK honest-distribution congruence with opposite-order equality.** -/
theorem perfectHVZK.congr_honestDist_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel R₁ sim)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R₂ stmtIn witIn) =
        evalDist (honestTranscriptDist init impl R₁ stmtIn witIn)) :
    perfectHVZK init impl rel R₂ sim :=
  h.congr_honestDist fun stmtIn witIn hMem => (hdist stmtIn witIn hMem).symm

/-- **Statistical HVZK honest-distribution congruence with opposite-order equality.** -/
theorem statisticalHVZK.congr_honestDist_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R₂ stmtIn witIn) =
        evalDist (honestTranscriptDist init impl R₁ stmtIn witIn)) :
    statisticalHVZK init impl rel R₂ sim ε :=
  h.congr_honestDist fun stmtIn witIn hMem => (hdist stmtIn witIn hMem).symm

/-- **Perfect HVZK is preserved under an `evalDist`-equal simulator.** Swapping in a simulator that
produces the same transcript distribution everywhere preserves perfect HVZK. -/
theorem perfectHVZK.simulator_congr
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel R sim)
    (hsim : ∀ stmtIn, evalDist (sim stmtIn) = evalDist (sim' stmtIn)) :
    perfectHVZK init impl rel R sim' := by
  intro stmtIn witIn hMem
  rw [← hsim stmtIn]
  exact h stmtIn witIn hMem

/-- **Statistical HVZK is preserved under an `evalDist`-equal simulator.** Swapping in a
simulator that produces the same transcript distribution everywhere preserves the same statistical
error budget. -/
theorem statisticalHVZK.simulator_congr
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R sim ε)
    (hsim : ∀ stmtIn, evalDist (sim stmtIn) = evalDist (sim' stmtIn)) :
    statisticalHVZK init impl rel R sim' ε := by
  intro stmtIn witIn hMem
  unfold tvDist
  rw [← hsim stmtIn]
  exact h stmtIn witIn hMem

/-- **Perfect HVZK simulator congruence with opposite-order equality.** -/
theorem perfectHVZK.simulator_congr_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel R sim)
    (hsim : ∀ stmtIn, evalDist (sim' stmtIn) = evalDist (sim stmtIn)) :
    perfectHVZK init impl rel R sim' :=
  h.simulator_congr fun stmtIn => (hsim stmtIn).symm

/-- **Statistical HVZK simulator congruence with opposite-order equality.** -/
theorem statisticalHVZK.simulator_congr_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R sim ε)
    (hsim : ∀ stmtIn, evalDist (sim' stmtIn) = evalDist (sim stmtIn)) :
    statisticalHVZK init impl rel R sim' ε :=
  h.simulator_congr fun stmtIn => (hsim stmtIn).symm

/-- **A concrete perfect-HVZK simulator witnesses existential HVZK.** -/
theorem perfectHVZK.isHVZK
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel R sim) :
    _root_.Reduction.isHVZK init impl rel R :=
  ⟨sim, h⟩

/-- **A concrete statistical-HVZK simulator witnesses existential statistical HVZK.** -/
theorem statisticalHVZK.isStatHVZK
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R sim ε) :
    _root_.Reduction.isStatHVZK init impl rel R ε :=
  ⟨sim, h⟩

/-- **Package a perfect-HVZK proof after normalizing the simulator distribution.** -/
theorem perfectHVZK.isHVZK_of_simulator_congr
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel R sim)
    (hsim : ∀ stmtIn, evalDist (sim stmtIn) = evalDist (sim' stmtIn)) :
    _root_.Reduction.isHVZK init impl rel R :=
  ⟨sim', h.simulator_congr hsim⟩

/-- **Package a statistical-HVZK proof after normalizing the simulator distribution.** -/
theorem statisticalHVZK.isStatHVZK_of_simulator_congr
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R sim ε)
    (hsim : ∀ stmtIn, evalDist (sim stmtIn) = evalDist (sim' stmtIn)) :
    _root_.Reduction.isStatHVZK init impl rel R ε :=
  ⟨sim', h.simulator_congr hsim⟩

/-- **Package a perfect-HVZK proof after simulator normalization in the opposite direction.** -/
theorem perfectHVZK.isHVZK_of_simulator_congr_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel R sim)
    (hsim : ∀ stmtIn, evalDist (sim' stmtIn) = evalDist (sim stmtIn)) :
    _root_.Reduction.isHVZK init impl rel R :=
  ⟨sim', h.simulator_congr_symm hsim⟩

/-- **Package a statistical-HVZK proof after simulator normalization in the opposite direction.** -/
theorem statisticalHVZK.isStatHVZK_of_simulator_congr_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim sim' : TranscriptSimulator oSpec StmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R sim ε)
    (hsim : ∀ stmtIn, evalDist (sim' stmtIn) = evalDist (sim stmtIn)) :
    _root_.Reduction.isStatHVZK init impl rel R ε :=
  ⟨sim', h.simulator_congr_symm hsim⟩

/-- **Triangle composition of statistical HVZK.** If `sim₁` is within `ε₁` of the honest
distribution and the honest distribution is within `ε₂` of `sim₂`'s, then `sim₁` is within
`ε₁ + ε₂` of `sim₂`. Used when transferring a simulator through an intermediate distribution. -/
theorem statisticalHVZK.simulator_triangle
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim₁ sim₂ : TranscriptSimulator oSpec StmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (h₁ : statisticalHVZK init impl rel R sim₁ ε₁)
    (h₂ : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R stmtIn witIn) (sim₂ stmtIn) ≤ (ε₂ : ℝ)) :
    ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (sim₁ stmtIn) (sim₂ stmtIn) ≤ ((ε₁ + ε₂ : ℝ≥0) : ℝ) := by
  intro stmtIn witIn hMem
  have hstep₁ := h₁ stmtIn witIn hMem
  have hstep₂ := h₂ stmtIn witIn hMem
  have htri := tvDist_triangle (sim₁ stmtIn)
    (honestTranscriptDist init impl R stmtIn witIn) (sim₂ stmtIn)
  calc tvDist (sim₁ stmtIn) (sim₂ stmtIn)
      ≤ tvDist (sim₁ stmtIn) (honestTranscriptDist init impl R stmtIn witIn)
          + tvDist (honestTranscriptDist init impl R stmtIn witIn) (sim₂ stmtIn) := htri
    _ ≤ (ε₁ : ℝ) + (ε₂ : ℝ) := add_le_add hstep₁ hstep₂
    _ = ((ε₁ + ε₂ : ℝ≥0) : ℝ) := by push_cast; ring

/-- **Approximate honest-distribution transfer for statistical HVZK.** If a simulator is
statistical-HVZK for `R₁` with error `ε₁`, and the honest transcript distribution of `R₁` is within
TV distance `ε₂` of the honest transcript distribution of `R₂` on the relation, then the same
simulator is statistical-HVZK for `R₂` with error `ε₁ + ε₂`. -/
theorem statisticalHVZK.triangle_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R₁ stmtIn witIn)
        (honestTranscriptDist init impl R₂ stmtIn witIn) ≤ (ε₂ : ℝ)) :
    statisticalHVZK init impl rel R₂ sim (ε₁ + ε₂) := by
  intro stmtIn witIn hMem
  have hstep₁ := h stmtIn witIn hMem
  have hstep₂ := hdist stmtIn witIn hMem
  have htri := tvDist_triangle (sim stmtIn)
    (honestTranscriptDist init impl R₁ stmtIn witIn)
    (honestTranscriptDist init impl R₂ stmtIn witIn)
  calc tvDist (sim stmtIn) (honestTranscriptDist init impl R₂ stmtIn witIn)
      ≤ tvDist (sim stmtIn) (honestTranscriptDist init impl R₁ stmtIn witIn)
          + tvDist (honestTranscriptDist init impl R₁ stmtIn witIn)
            (honestTranscriptDist init impl R₂ stmtIn witIn) := htri
    _ ≤ (ε₁ : ℝ) + (ε₂ : ℝ) := add_le_add hstep₁ hstep₂
    _ = ((ε₁ + ε₂ : ℝ≥0) : ℝ) := by push_cast; ring

/-- **Symmetric-facing approximate honest-distribution transfer.** This is the same result as
`statisticalHVZK.triangle_honestDist`, but accepts the honest-distribution TV-distance bridge in
the opposite order, which is often how relational simulation lemmas are stated. -/
theorem statisticalHVZK.triangle_honestDist_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R₂ stmtIn witIn)
        (honestTranscriptDist init impl R₁ stmtIn witIn) ≤ (ε₂ : ℝ)) :
    statisticalHVZK init impl rel R₂ sim (ε₁ + ε₂) :=
  h.triangle_honestDist fun stmtIn witIn hMem => by
    rw [tvDist_comm]
    exact hdist stmtIn witIn hMem

/-- **Zero-error approximate honest-distribution transfer for statistical HVZK.** If the honest
transcript distributions are at TV distance at most `0`, the same simulator keeps the same
statistical error budget. -/
theorem statisticalHVZK.triangle_honestDist_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R₁ stmtIn witIn)
        (honestTranscriptDist init impl R₂ stmtIn witIn) ≤ (0 : ℝ)) :
    statisticalHVZK init impl rel R₂ sim ε := by
  have hstat :
      statisticalHVZK init impl rel R₂ sim (ε + 0) :=
    h.triangle_honestDist hdist
  simpa using hstat

/-- Symmetric-facing zero-error approximate honest-distribution transfer for statistical HVZK. -/
theorem statisticalHVZK.triangle_honestDist_symm_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec} {ε : ℝ≥0}
    (h : statisticalHVZK init impl rel R₁ sim ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R₂ stmtIn witIn)
        (honestTranscriptDist init impl R₁ stmtIn witIn) ≤ (0 : ℝ)) :
    statisticalHVZK init impl rel R₂ sim ε :=
  h.triangle_honestDist_zero fun stmtIn witIn hMem => by
    rw [tvDist_comm]
    exact hdist stmtIn witIn hMem

/-- **Zero-error approximate honest-distribution transfer for perfect HVZK.** If the
honest-transcript bridge is stated as total-variation distance at most `0`, exact HVZK transfers by
viewing perfect HVZK as statistical HVZK at error `0`, applying the triangle transfer, and returning
through the zero-error statistical/perfect equivalence. -/
theorem perfectHVZK.triangle_honestDist_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel R₁ sim)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R₁ stmtIn witIn)
        (honestTranscriptDist init impl R₂ stmtIn witIn) ≤ (0 : ℝ)) :
    perfectHVZK init impl rel R₂ sim := by
  have hstat₁ :
      Reduction.statisticalHVZK init impl rel R₁ sim 0 :=
    Reduction.perfectHVZK.statisticalHVZK h 0
  have hstat :
      Reduction.statisticalHVZK init impl rel R₂ sim (0 + 0) :=
    Reduction.statisticalHVZK.triangle_honestDist hstat₁ hdist
  exact (perfectHVZK_iff_statisticalHVZK_zero init impl rel R₂ sim).2 (by
    simpa using hstat)

/-- Symmetric-facing zero-error approximate honest-distribution transfer for perfect HVZK. -/
theorem perfectHVZK.triangle_honestDist_symm_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {sim : TranscriptSimulator oSpec StmtIn pSpec}
    (h : perfectHVZK init impl rel R₁ sim)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R₂ stmtIn witIn)
        (honestTranscriptDist init impl R₁ stmtIn witIn) ≤ (0 : ℝ)) :
    perfectHVZK init impl rel R₂ sim :=
  h.triangle_honestDist_zero fun stmtIn witIn hMem => by
    rw [tvDist_comm]
    exact hdist stmtIn witIn hMem

/-- **Constant-simulator criterion for perfect HVZK.** If the honest transcript distribution is
`evalDist`-equal to a fixed distribution `d` on every related pair, then the constant simulator
returning `d` achieves perfect HVZK. This generalizes the zero-round identity instance, where
`d = pure default`. -/
theorem perfectHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R stmtIn witIn) = evalDist d) :
    perfectHVZK init impl rel R (fun _ => d) := by
  intro stmtIn witIn hMem
  exact (hdist stmtIn witIn hMem).symm

/-- **Statistical constant-simulator criterion.** If the honest transcript distribution is
`evalDist`-equal to a fixed distribution `d` on every related pair, then the constant simulator
returning `d` achieves statistical HVZK for any error budget. -/
theorem statisticalHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R stmtIn witIn) = evalDist d)
    (ε : ℝ≥0) :
    statisticalHVZK init impl rel R (fun _ => d) ε :=
  (perfectHVZK_of_honestDist_eq_const d hdist).statisticalHVZK ε

/-- **Symmetric-facing constant-simulator criterion for perfect HVZK.** -/
theorem perfectHVZK_of_const_eq_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist d =
        evalDist (honestTranscriptDist init impl R stmtIn witIn)) :
    perfectHVZK init impl rel R (fun _ => d) := by
  intro stmtIn witIn hMem
  exact hdist stmtIn witIn hMem

/-- **Symmetric-facing constant-simulator criterion for statistical HVZK.** -/
theorem statisticalHVZK_of_const_eq_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist d =
        evalDist (honestTranscriptDist init impl R stmtIn witIn))
    (ε : ℝ≥0) :
    statisticalHVZK init impl rel R (fun _ => d) ε :=
  (perfectHVZK_of_const_eq_honestDist d hdist).statisticalHVZK ε

/-- **`isHVZK` from the constant-simulator criterion.** -/
theorem isHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R stmtIn witIn) = evalDist d) :
    isHVZK init impl rel R :=
  ⟨fun _ => d, perfectHVZK_of_honestDist_eq_const d hdist⟩

/-- **`isStatHVZK` from the constant-simulator criterion.** -/
theorem isStatHVZK_of_honestDist_eq_const
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R stmtIn witIn) = evalDist d)
    (ε : ℝ≥0) :
    isStatHVZK init impl rel R ε :=
  ⟨fun _ => d, statisticalHVZK_of_honestDist_eq_const d hdist ε⟩

/-- **`isHVZK` from the symmetric-facing constant-simulator criterion.** -/
theorem isHVZK_of_const_eq_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist d =
        evalDist (honestTranscriptDist init impl R stmtIn witIn)) :
    isHVZK init impl rel R :=
  ⟨fun _ => d, perfectHVZK_of_const_eq_honestDist d hdist⟩

/-- **`isStatHVZK` from the symmetric-facing constant-simulator criterion.** -/
theorem isStatHVZK_of_const_eq_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (d : OptionT ProbComp (FullTranscript pSpec))
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist d =
        evalDist (honestTranscriptDist init impl R stmtIn witIn))
    (ε : ℝ≥0) :
    isStatHVZK init impl rel R ε :=
  ⟨fun _ => d, statisticalHVZK_of_const_eq_honestDist d hdist ε⟩

/-- **`isHVZK` transfers along an `evalDist`-equal honest distribution.** -/
theorem isHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (h : isHVZK init impl rel R₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R₁ stmtIn witIn) =
        evalDist (honestTranscriptDist init impl R₂ stmtIn witIn)) :
    isHVZK init impl rel R₂ :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.congr_honestDist hdist⟩

/-- **`isStatHVZK` transfers along an `evalDist`-equal honest distribution.** -/
theorem isStatHVZK.congr_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} {ε : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R₁ stmtIn witIn) =
        evalDist (honestTranscriptDist init impl R₂ stmtIn witIn)) :
    isStatHVZK init impl rel R₂ ε :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.congr_honestDist hdist⟩

/-- **`isHVZK` honest-distribution congruence with opposite-order equality.** -/
theorem isHVZK.congr_honestDist_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (h : isHVZK init impl rel R₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R₂ stmtIn witIn) =
        evalDist (honestTranscriptDist init impl R₁ stmtIn witIn)) :
    isHVZK init impl rel R₂ :=
  h.congr_honestDist fun stmtIn witIn hMem => (hdist stmtIn witIn hMem).symm

/-- **`isStatHVZK` honest-distribution congruence with opposite-order equality.** -/
theorem isStatHVZK.congr_honestDist_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} {ε : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      evalDist (honestTranscriptDist init impl R₂ stmtIn witIn) =
        evalDist (honestTranscriptDist init impl R₁ stmtIn witIn)) :
    isStatHVZK init impl rel R₂ ε :=
  h.congr_honestDist fun stmtIn witIn hMem => (hdist stmtIn witIn hMem).symm

/-- **Existential approximate honest-distribution transfer for statistical HVZK.** -/
theorem isStatHVZK.triangle_honestDist
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} {ε₁ ε₂ : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R₁ stmtIn witIn)
        (honestTranscriptDist init impl R₂ stmtIn witIn) ≤ (ε₂ : ℝ)) :
    isStatHVZK init impl rel R₂ (ε₁ + ε₂) :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.triangle_honestDist hdist⟩

/-- **Existential symmetric-facing approximate honest-distribution transfer.** -/
theorem isStatHVZK.triangle_honestDist_symm
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} {ε₁ ε₂ : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R₂ stmtIn witIn)
        (honestTranscriptDist init impl R₁ stmtIn witIn) ≤ (ε₂ : ℝ)) :
    isStatHVZK init impl rel R₂ (ε₁ + ε₂) :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.triangle_honestDist_symm hdist⟩

/-- **Existential zero-error approximate honest-distribution transfer for statistical HVZK.** -/
theorem isStatHVZK.triangle_honestDist_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} {ε : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R₁ stmtIn witIn)
        (honestTranscriptDist init impl R₂ stmtIn witIn) ≤ (0 : ℝ)) :
    isStatHVZK init impl rel R₂ ε :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.triangle_honestDist_zero hdist⟩

/-- **Existential symmetric-facing zero-error approximate honest-distribution transfer for
statistical HVZK.** -/
theorem isStatHVZK.triangle_honestDist_symm_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} {ε : ℝ≥0}
    (h : isStatHVZK init impl rel R₁ ε)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R₂ stmtIn witIn)
        (honestTranscriptDist init impl R₁ stmtIn witIn) ≤ (0 : ℝ)) :
    isStatHVZK init impl rel R₂ ε :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.triangle_honestDist_symm_zero hdist⟩

/-- **Existential zero-error approximate honest-distribution transfer for exact HVZK.** -/
theorem isHVZK.triangle_honestDist_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (h : isHVZK init impl rel R₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R₁ stmtIn witIn)
        (honestTranscriptDist init impl R₂ stmtIn witIn) ≤ (0 : ℝ)) :
    isHVZK init impl rel R₂ :=
  let ⟨sim, hsim⟩ := h
  ⟨sim, hsim.triangle_honestDist_zero hdist⟩

/-- **Existential symmetric-facing zero-error approximate honest-distribution transfer for exact
HVZK.** -/
theorem isHVZK.triangle_honestDist_symm_zero
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel : Set (StmtIn × WitIn)}
    {R₁ R₂ : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    (h : isHVZK init impl rel R₁)
    (hdist : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel →
      tvDist (honestTranscriptDist init impl R₂ stmtIn witIn)
        (honestTranscriptDist init impl R₁ stmtIn witIn) ≤ (0 : ℝ)) :
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

end Reduction
