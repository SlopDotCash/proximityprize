/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R19ExplicitCharacterRung
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R24FullRungAssembly

/-!
# LANE B2 (#466 round 152): octic full-family gate obstructions

R151 exposes octic/Stepanov consumers for the explicit `chiFamily χ` and its thinned
subfamilies.  The usable route is the thinned-family gate.  This file specializes R24's
constant-accounting audit to the octic constant `4 + Cmax`, recording that the normalized
full-family exact-rung gate is impossible for any nontrivial `χ` once `4 + Cmax ≥ 1`.
-/

namespace ArkLib.ProximityGap.Frontier.R152OcticFullFamilyGateObstructions

open ArkLib.ProximityGap.Frontier.R19ExplicitCharacterRung
open ArkLib.ProximityGap.Frontier.R19ChiDecomposition
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The full `chiFamily χ` normalized exact-rung gate cannot fire for the octic constant
`4 + Cmax`, as soon as `4 + Cmax ≥ 1`.  This is exactly the `chiFamily` specialization of
R24's full-family audit theorem. -/
theorem not_octic_chiFamily_constant_gate
    (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) {Cmax : ℝ}
    (hCw : 1 ≤ 4 + Cmax) :
    ¬ 32 * ((4 + Cmax) * ((chiFamily χ).card : ℝ) ^ 4 + 1)
        / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1 := by
  rw [chiFamily_card]
  exact fullFamily_gate_impossible (orderOf χ) hm hCw

/-- Nonnegative octic constants are automatically in the impossible full-family regime. -/
theorem not_octic_chiFamily_constant_gate_of_Cmax_nonneg
    (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) {Cmax : ℝ}
    (hCmax0 : 0 ≤ Cmax) :
    ¬ 32 * ((4 + Cmax) * ((chiFamily χ).card : ℝ) ^ 4 + 1)
        / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1 := by
  exact not_octic_chiFamily_constant_gate χ hm (by linarith)

/-- In particular, the R151 `Cmax ≤ 2` sharp-octic window does not make the full
`chiFamily` exact-rung gate available; the obstruction is independent of that upper bound. -/
theorem not_octic_chiFamily_constant_gate_of_Cmax_nonneg_le_two
    (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) {Cmax : ℝ}
    (hCmax0 : 0 ≤ Cmax) (_hCmax2 : Cmax ≤ 2) :
    ¬ 32 * ((4 + Cmax) * ((chiFamily χ).card : ℝ) ^ 4 + 1)
        / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1 :=
  not_octic_chiFamily_constant_gate_of_Cmax_nonneg χ hm hCmax0

/-- Existential form: there is no nonnegative octic constant for which the full
`chiFamily χ` normalized exact-rung gate can fire. -/
theorem not_exists_octic_chiFamily_constant_gate_of_Cmax_nonneg
    (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) :
    ¬ ∃ Cmax : ℝ, 0 ≤ Cmax ∧
      32 * ((4 + Cmax) * ((chiFamily χ).card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1 := by
  rintro ⟨Cmax, hCmax0, hgate⟩
  exact not_octic_chiFamily_constant_gate_of_Cmax_nonneg χ hm hCmax0 hgate

/-- Existential sharp-window form: even adding the R151-style upper bound `Cmax ≤ 2` cannot
make the full `chiFamily χ` gate fire. -/
theorem not_exists_octic_chiFamily_constant_gate_of_Cmax_nonneg_le_two
    (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) :
    ¬ ∃ Cmax : ℝ, 0 ≤ Cmax ∧ Cmax ≤ 2 ∧
      32 * ((4 + Cmax) * ((chiFamily χ).card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1 := by
  rintro ⟨Cmax, hCmax0, hCmax2, hgate⟩
  exact not_octic_chiFamily_constant_gate_of_Cmax_nonneg_le_two χ hm hCmax0 hCmax2 hgate

/-- The full-family octic pipeline's own coefficient bounds force `Cmax ≥ 0`; hence they
already make the full `chiFamily χ` normalized exact-rung gate impossible. -/
theorem not_octic_chiFamily_constant_gate_of_pipeline_bounds
    (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ)
    (Cd : MulChar F ℂ → ℝ) {Cmax : ℝ}
    (hCd0 : ∀ χ' ∈ chiFamily χ, 0 ≤ Cd χ')
    (hCdmax : ∀ χ' ∈ chiFamily χ, Cd χ' ≤ Cmax) :
    ¬ 32 * ((4 + Cmax) * ((chiFamily χ).card : ℝ) ^ 4 + 1)
        / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1 := by
  obtain ⟨χ', hχ'⟩ := chiFamily_nonempty_of_two_le_order χ hm
  have hCmax0 : 0 ≤ Cmax := le_trans (hCd0 χ' hχ') (hCdmax χ' hχ')
  exact not_octic_chiFamily_constant_gate_of_Cmax_nonneg χ hm hCmax0

/-- Existential form for the exact R151 full-family pipeline bounds: no choice of `Cd` and
`Cmax` can satisfy nonnegative per-character constants, a uniform upper bound, and the full
`chiFamily χ` normalized exact-rung gate simultaneously. -/
theorem not_exists_octic_chiFamily_constant_gate_of_pipeline_bounds
    (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) :
    ¬ ∃ (Cd : MulChar F ℂ → ℝ) (Cmax : ℝ),
      (∀ χ' ∈ chiFamily χ, 0 ≤ Cd χ') ∧
      (∀ χ' ∈ chiFamily χ, Cd χ' ≤ Cmax) ∧
      32 * ((4 + Cmax) * ((chiFamily χ).card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1 := by
  rintro ⟨Cd, Cmax, hCd0, hCdmax, hgate⟩
  exact not_octic_chiFamily_constant_gate_of_pipeline_bounds χ hm Cd hCd0 hCdmax hgate

end ArkLib.ProximityGap.Frontier.R152OcticFullFamilyGateObstructions

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R152OcticFullFamilyGateObstructions in
#print axioms
  not_octic_chiFamily_constant_gate
open ArkLib.ProximityGap.Frontier.R152OcticFullFamilyGateObstructions in
#print axioms
  not_octic_chiFamily_constant_gate_of_Cmax_nonneg
open ArkLib.ProximityGap.Frontier.R152OcticFullFamilyGateObstructions in
#print axioms
  not_octic_chiFamily_constant_gate_of_Cmax_nonneg_le_two
open ArkLib.ProximityGap.Frontier.R152OcticFullFamilyGateObstructions in
#print axioms
  not_exists_octic_chiFamily_constant_gate_of_Cmax_nonneg
open ArkLib.ProximityGap.Frontier.R152OcticFullFamilyGateObstructions in
#print axioms
  not_exists_octic_chiFamily_constant_gate_of_Cmax_nonneg_le_two
open ArkLib.ProximityGap.Frontier.R152OcticFullFamilyGateObstructions in
#print axioms
  not_octic_chiFamily_constant_gate_of_pipeline_bounds
open ArkLib.ProximityGap.Frontier.R152OcticFullFamilyGateObstructions in
#print axioms
  not_exists_octic_chiFamily_constant_gate_of_pipeline_bounds
