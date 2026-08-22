/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Generalized-Paley spectrum-nature / weak-Waring metadata gate

Podesta--Videla's 2026 generalized-Paley spectrum paper gives valuable structural metadata:
real spectrum is characterized by undirectedness, integral spectra have arithmetic construction
criteria, directed periods are classified, and weak Waring numbers are reduced to classical Waring
numbers / graph diameters.

For #464 this metadata is not yet a worst-eigenvalue estimate.  The prize consumer needs a bound on
the non-principal spectral radius

`lambda_2 = max_{b ≠ 0} |sum_{x in mu_n} e_p(bx)|`.

This file proves the small arithmetic guardrail: even perfect knowledge of "real spectrum",
"integral spectrum", and a bounded weak-Waring/diameter datum does not imply a Ramanujan-scale
radius bound.  A separate analytic radius inequality is the missing input.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.GeneralizedPaleyNatureWaringGate

/-- Abstract payload of the spectrum-nature / weak-Waring side of a generalized-Paley graph.

`degree` is the graph degree, `nonprincipalRadius` is the worst non-principal eigenvalue
magnitude, and `weakWaringNumber` is the diameter-like coverage datum.  The two spectrum-nature
fields are kept as propositions because the gate is about logical strength, not about constructing
the graph. -/
structure NatureWaringMetadata where
  degree : ℝ
  nonprincipalRadius : ℝ
  weakWaringNumber : ℕ
  realSpectrum : Prop
  integralSpectrum : Prop

/-- The structural facts supplied by the spectrum-nature / weak-Waring route, abstracted to the
parts relevant for this gate. -/
def HasNatureWaringData (m : NatureWaringMetadata) : Prop :=
  m.weakWaringNumber ≤ 2 ∧ m.realSpectrum ∧ m.integralSpectrum

/-- Ramanujan-scale bound on the non-principal spectral radius. -/
def RamanujanScaleBound (C : ℝ) (m : NatureWaringMetadata) : Prop :=
  m.nonprincipalRadius ≤ C * Real.sqrt m.degree

/-- A graph-theoretic nature/weak-Waring certificate alone does not imply a Ramanujan-scale
radius bound.  For every constant `C ≥ 0` there is abstract metadata with bounded weak-Waring
number, real and integral spectrum, and positive degree, but with
`lambda_2 = degree > C * sqrt(degree)`.

The point is not that this metadata is an actual GP graph.  The point is logical: the metadata
fields do not contain the missing analytic inequality.  Any #464 route using the 2026
generalized-Paley spectrum-nature theorem must add a separate spectral-radius theorem. -/
theorem natureWaringData_not_sufficient_for_ramanujanScale
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ m : NatureWaringMetadata,
      HasNatureWaringData m ∧
        0 < m.degree ∧
          m.nonprincipalRadius = m.degree ∧
            ¬ RamanujanScaleBound C m := by
  let D : ℝ := (C + 1) ^ 2
  have hC1pos : 0 < C + 1 := by linarith
  have hC1nonneg : 0 ≤ C + 1 := hC1pos.le
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  refine
    ⟨{ degree := D
       nonprincipalRadius := D
       weakWaringNumber := 2
       realSpectrum := True
       integralSpectrum := True }, ?_⟩
  refine ⟨?_, hDpos, rfl, ?_⟩
  · exact ⟨by norm_num, trivial, trivial⟩
  · intro hbound
    unfold RamanujanScaleBound at hbound
    have hsqrt : Real.sqrt D = C + 1 := by
      dsimp [D]
      rw [Real.sqrt_sq hC1nonneg]
    have hle : D ≤ C * (C + 1) := by
      simpa [hsqrt] using hbound
    have hlt : C * (C + 1) < D := by
      dsimp [D]
      nlinarith
    exact (not_lt_of_ge hle) hlt

/-- Packaged verdict: spectrum-nature and weak-Waring/diameter data are useful classification
metadata, but they are logically orthogonal to the #464 spectral-radius inequality. -/
theorem generalizedPaley_nature_waring_gate (C : ℝ) (hC : 0 ≤ C) :
    ∃ m : NatureWaringMetadata,
      HasNatureWaringData m ∧ ¬ RamanujanScaleBound C m :=
  let ⟨m, hdata, _hdeg, _hradius, hmiss⟩ :=
    natureWaringData_not_sufficient_for_ramanujanScale C hC
  ⟨m, hdata, hmiss⟩

#print axioms natureWaringData_not_sufficient_for_ramanujanScale
#print axioms generalizedPaley_nature_waring_gate

end ArkLib.ProximityGap.Frontier.GeneralizedPaleyNatureWaringGate
