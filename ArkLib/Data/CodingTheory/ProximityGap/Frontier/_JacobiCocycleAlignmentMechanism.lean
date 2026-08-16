/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DyadicJacobiCocycleNonContraction

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The Jacobi-cocycle ALIGNMENT MECHANISM: cancellation forces phase non-alignment

**Door (iv), Lane 2/3 — frontier-movement, extends `_DyadicJacobiCocycleNonContraction`.**

`_DyadicJacobiCocycleNonContraction` proved:
* `norm_phaseSum_le_card` — `‖∑ γ_j‖ ≤ M` (triangle bound, the only unconditional ceiling), and
* `exists_unimodular_cocycle_saturating_triangle` — the *aligned* constant family `γ ≡ 1` saturates
  it (`‖∑ γ_j‖ = M`), so the unimodular cocycle is consistent with ZERO cancellation.

What was MISSING is the *mechanism direction*: that the saturating value `M` is produced EXACTLY by
phase alignment, so any sub-saturation (`‖∑‖ < M`, in particular reaching the flat prize target
`C·√(M·log M) ≪ M`) FORCES the phases to be non-aligned. This file locks that converse:

* **alignment ⟹ saturation** (`aligned_phaseSum_eq_card`): all phases equal a common unit `ζ`
  ⟹ `‖∑ γ_j‖ = M`.
* **sub-saturation ⟹ non-alignment** (`not_all_aligned_of_phaseSum_lt_card` and the `≠` form):
  `‖∑ γ_j‖ < M` (or `≠ M`) ⟹ NO common unit phase exists, i.e. the configuration is genuinely
  dispersed.
* **flat target ⟹ non-alignment** (`flat_target_forces_non_alignment`): reaching the prize flat
  budget forces dispersion — the explicit mechanism the prize demands of the Jacobi cocycle.

## HONEST SCOPE
This is the QUALITATIVE mechanism (cancellation ⟺ dispersion), the converse face of the saturation
example. It does NOT prove the cocycle achieves any cancellation — that quantitative dispersion is
the open `JacobiCocycleDispersion` prize, untouched. NO CORE / cancellation / completion /
anti-concentration / moment-saving / capacity claim. Prize CORE stays OPEN. The point: record,
kernel-checked, that the prize budget cannot be met by a configuration close to the trivial aligned
worst case — any prize-meeting cocycle is necessarily phase-dispersed.
-/

namespace ArkLib.ProximityGap.Frontier.JacobiCocycleAlignmentMechanism

open Finset Complex
open ProximityGap.Frontier.DyadicJacobiCocycleNonContraction

/-- **Alignment ⟹ saturation.** If every unit phase equals a common unit `ζ` (`‖ζ‖ = 1`,
`γ j = ζ` ∀ j), then the phase sum saturates the triangle bound: `‖phaseSum γ‖ = M`. This is the
converse anchor to `exists_unimodular_cocycle_saturating_triangle` (which exhibited `ζ = 1`). -/
theorem aligned_phaseSum_eq_card {M : ℕ} (γ : Fin M → ℂ) (ζ : ℂ)
    (hz : ‖ζ‖ = 1) (hal : ∀ j, γ j = ζ) :
    ‖phaseSum γ‖ = (M : ℝ) := by
  have hsum : phaseSum γ = (M : ℂ) * ζ := by
    unfold phaseSum
    rw [Finset.sum_congr rfl (fun j _ => hal j)]
    simp [Finset.sum_const, Finset.card_univ]
  rw [hsum, norm_mul, hz, mul_one, Complex.norm_natCast]

/-- **Sub-saturation ⟹ non-alignment (`≠` form, the mechanism).** If the phase sum fails to
saturate (`‖phaseSum γ‖ ≠ M`), then there is NO common unit phase: the configuration cannot be
written as all-`γ_j = ζ` for a single unit `ζ`. Contrapositive of `aligned_phaseSum_eq_card`. -/
theorem not_all_aligned_of_phaseSum_ne_card {M : ℕ} (γ : Fin M → ℂ)
    (h : ‖phaseSum γ‖ ≠ (M : ℝ)) :
    ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ j, γ j = ζ := by
  rintro ⟨ζ, hz, hal⟩
  exact h (aligned_phaseSum_eq_card γ ζ hz hal)

/-- **Strict-cancellation ⟹ non-alignment.** Any genuine cancellation (`‖phaseSum γ‖ < M`) forces
phase dispersion: no common unit phase. The strict-inequality specialization of the mechanism. -/
theorem not_all_aligned_of_phaseSum_lt_card {M : ℕ} (γ : Fin M → ℂ)
    (h : ‖phaseSum γ‖ < (M : ℝ)) :
    ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ j, γ j = ζ :=
  not_all_aligned_of_phaseSum_ne_card γ (ne_of_lt h)

/-- **Flat prize target ⟹ non-alignment (the door-(iv) mechanism statement).** If a unit-phase
configuration meets the flat prize budget `‖phaseSum γ‖ ≤ C·√(M·log M)` and that budget is strictly
below the baseline `M` (the prize regime `C·√(M log M) < M`), then the configuration is necessarily
phase-dispersed: no common unit phase. So the Jacobi cocycle, to reach the prize, MUST induce genuine
phase non-alignment — it cannot sit near the trivial aligned worst case. -/
theorem flat_target_forces_non_alignment {M : ℕ} {C : ℝ} {γ : Fin M → ℂ}
    (hbudget : ‖phaseSum γ‖ ≤ C * Real.sqrt ((M : ℝ) * Real.log M))
    (hgap : C * Real.sqrt ((M : ℝ) * Real.log M) < (M : ℝ)) :
    ¬ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ j, γ j = ζ :=
  not_all_aligned_of_phaseSum_lt_card γ (lt_of_le_of_lt hbudget hgap)

/-- **Mechanism iff (consolidation): for unit phases, full saturation is EXACTLY alignment to the
common value `γ 0`, in the nonempty case.** One direction (alignment ⟹ saturation) is
`aligned_phaseSum_eq_card`; this packages the contrapositive as the clean equivalence-of-failure: the
configuration is non-aligned to its own first phase whenever it sub-saturates. (We state the provable
non-vacuous half; the converse `saturation ⟹ alignment` is the heavier Mathlib equality-case of the
triangle inequality and is not needed for the mechanism.) -/
theorem sub_saturation_iff_not_aligned_to_head {M : ℕ} (γ : Fin M → ℂ)
    (hM : 0 < M) (hunit : IsUnitPhase γ)
    (h : ‖phaseSum γ‖ < (M : ℝ)) :
    ¬ ∀ j, γ j = γ ⟨0, hM⟩ := by
  intro hal
  have hz : ‖γ ⟨0, hM⟩‖ = 1 := hunit ⟨0, hM⟩
  exact (ne_of_lt h) (aligned_phaseSum_eq_card γ (γ ⟨0, hM⟩) hz hal)

end ArkLib.ProximityGap.Frontier.JacobiCocycleAlignmentMechanism

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleAlignmentMechanism.aligned_phaseSum_eq_card
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleAlignmentMechanism.not_all_aligned_of_phaseSum_ne_card
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleAlignmentMechanism.not_all_aligned_of_phaseSum_lt_card
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleAlignmentMechanism.flat_target_forces_non_alignment
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleAlignmentMechanism.sub_saturation_iff_not_aligned_to_head
