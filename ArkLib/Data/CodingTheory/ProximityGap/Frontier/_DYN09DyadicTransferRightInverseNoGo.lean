/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# DYN09: the dyadic sibling transfer has a norm-preserving right inverse

This file tests the most literal Ruelle/renormalization operator suggested by the dyadic subgroup
tower.  A fine state has two children above every coarse state.  The normalized transfer averages
the siblings, and its fine-to-fine version is conditional expectation onto the coarse sigma-algebra.

The exact obstruction is stronger than a numerical failure of a candidate constant:

* the unweighted sibling average has `coarseLift` as a right inverse;
* its fine-to-fine conditional expectation is idempotent;
* a nonzero mean-zero coarse mode is fixed with full `L∞` amplitude, so no strict contraction on
  the whole centered space is possible;
* adding arbitrary nonzero branch weights does not fix this on the unrestricted function space:
  the weights can be compensated branchwise, again giving a right inverse;
* for unit-modulus weights this compensated right inverse preserves every pointwise norm.

Thus a useful arithmetic transfer theorem must restrict the input to the *actual coupled
Gauss-period state* and prove that it avoids this norm-preserving range.  That restriction is the
missing phase-correlation input; it is not supplied by the abstract dyadic dynamics.  This is a
no-go for a generic Ruelle spectral-gap argument, not a Paley/proximity-gap closure.
-/

noncomputable section

namespace ArkLib.ProximityGap.Frontier.DYN09DyadicTransferRightInverseNoGo

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Average the two fine children above a coarse state. -/
def siblingAverage (f : ι × Bool → ℂ) (i : ι) : ℂ :=
  (f (i, false) + f (i, true)) / 2

/-- Lift a coarse observable by making it constant on each sibling pair. -/
def coarseLift (g : ι → ℂ) (x : ι × Bool) : ℂ :=
  g x.1

/-- The sibling average is split-surjective: coarse lifting is an exact right inverse. -/
@[simp] theorem siblingAverage_coarseLift (g : ι → ℂ) :
    siblingAverage (coarseLift g) = g := by
  funext i
  simp [siblingAverage, coarseLift]

/-- Fine-to-fine conditional expectation onto the sibling-constant range. -/
def haarProjection (f : ι × Bool → ℂ) : ι × Bool → ℂ :=
  coarseLift (siblingAverage f)

/-- Every coarse lift is fixed by the Haar projection. -/
@[simp] theorem haarProjection_coarseLift (g : ι → ℂ) :
    haarProjection (coarseLift g) = coarseLift g := by
  simp [haarProjection]

/-- The fine-level transfer is a projection, not a strictly contracting semigroup. -/
theorem haarProjection_idempotent (f : ι × Bool → ℂ) :
    haarProjection (haarProjection f) = haarProjection f := by
  simp [haarProjection]

/-- Mean-zero predicate for a finite observable. -/
def Centered {α : Type*} [Fintype α] (f : α → ℂ) : Prop :=
  ∑ x, f x = 0

/-- Coarse lifting preserves centering (the fine sum is twice the coarse sum). -/
theorem centered_coarseLift {g : ι → ℂ} (hg : Centered g) :
    Centered (coarseLift g) := by
  classical
  unfold Centered at *
  rw [Fintype.sum_prod_type]
  simp only [coarseLift, Fintype.sum_bool]
  rw [Finset.sum_add_distrib, hg, zero_add]

/-- The smallest explicit nonzero centered coarse mode. -/
def signMode (i : Fin 2) : ℂ :=
  if i = 0 then 1 else -1

theorem centered_signMode : Centered signMode := by
  unfold Centered
  rw [Fin.sum_univ_two]
  simp [signMode]

theorem norm_coarseLift_signMode_le_one (x : Fin 2 × Bool) :
    ‖coarseLift signMode x‖ ≤ 1 := by
  rcases x with ⟨i, b⟩
  fin_cases i <;> simp [coarseLift, signMode]

/-- A proposed uniform strict `L∞` contraction on all centered fine observables. -/
def StrictMeanZeroContraction (c : ℝ) : Prop :=
  ∀ f : Fin 2 × Bool → ℂ,
    Centered f →
    (∀ x, ‖f x‖ ≤ 1) →
    ∀ x, ‖haarProjection f x‖ ≤ c

/-- **Unweighted no-gap theorem.** No constant `c < 1` contracts every centered observable:
the sibling-constant lift of `signMode` is centered, pointwise bounded by one, and fixed with norm
one. -/
theorem not_strictMeanZeroContraction {c : ℝ} (hc : c < 1) :
    ¬ StrictMeanZeroContraction c := by
  intro h
  let f : Fin 2 × Bool → ℂ := coarseLift signMode
  have hfcenter : Centered f := centered_coarseLift centered_signMode
  have hfbound : ∀ x, ‖f x‖ ≤ 1 := by
    intro x
    exact norm_coarseLift_signMode_le_one x
  have hx := h f hfcenter hfbound ((0 : Fin 2), false)
  have hone : (1 : ℝ) ≤ c := by
    simpa [f, haarProjection, coarseLift, signMode] using hx
  exact (not_le_of_gt hc) hone

/-! ## Phase-weighted transfer -/

/-- A normalized sibling transfer with arbitrary complex branch weights. -/
def weightedSiblingTransfer (w f : ι × Bool → ℂ) (i : ι) : ℂ :=
  (w (i, false) * f (i, false) + w (i, true) * f (i, true)) / 2

/-- Compensate a nonzero branch weight before lifting a coarse observable. -/
def phaseCompensatedLift (w : ι × Bool → ℂ) (g : ι → ℂ) (x : ι × Bool) : ℂ :=
  (w x)⁻¹ * g x.1

/-- Every nonvanishing weighted sibling transfer is still split-surjective. -/
theorem weightedTransfer_phaseCompensatedLift (w : ι × Bool → ℂ) (g : ι → ℂ)
    (hw : ∀ x, w x ≠ 0) :
    weightedSiblingTransfer w (phaseCompensatedLift w g) = g := by
  funext i
  simp [weightedSiblingTransfer, phaseCompensatedLift, hw]

/-- Unit weights make the compensating right inverse pointwise isometric. -/
theorem norm_phaseCompensatedLift (w : ι × Bool → ℂ) (g : ι → ℂ)
    (hw : ∀ x, ‖w x‖ = 1) (x : ι × Bool) :
    ‖phaseCompensatedLift w g x‖ = ‖g x.1‖ := by
  rw [phaseCompensatedLift, norm_mul, norm_inv, hw x, inv_one, one_mul]

/-- Fine-to-fine weighted projection obtained from the transfer and its compensated lift. -/
def weightedHaarProjection (w f : ι × Bool → ℂ) : ι × Bool → ℂ :=
  phaseCompensatedLift w (weightedSiblingTransfer w f)

/-- The weighted projection fixes the entire compensated coarse range. -/
theorem weightedHaarProjection_phaseCompensatedLift (w : ι × Bool → ℂ) (g : ι → ℂ)
    (hw : ∀ x, w x ≠ 0) :
    weightedHaarProjection w (phaseCompensatedLift w g) = phaseCompensatedLift w g := by
  unfold weightedHaarProjection
  rw [weightedTransfer_phaseCompensatedLift w g hw]

/-- The weighted fine-level operator is idempotent whenever all branch weights are nonzero. -/
theorem weightedHaarProjection_idempotent (w f : ι × Bool → ℂ)
    (hw : ∀ x, w x ≠ 0) :
    weightedHaarProjection w (weightedHaarProjection w f) = weightedHaarProjection w f := by
  unfold weightedHaarProjection
  rw [weightedTransfer_phaseCompensatedLift w (weightedSiblingTransfer w f) hw]

/-- **Weighted no-gap package.** Unit-modulus weights admit an exact right inverse that preserves
pointwise norms.  A contraction can therefore only come from an additional arithmetic restriction
on the admissible state, not from the abstract weighted transfer operator. -/
theorem weightedTransfer_normPreserving_rightInverse (w : ι × Bool → ℂ) (g : ι → ℂ)
    (hw : ∀ x, ‖w x‖ = 1) :
    weightedSiblingTransfer w (phaseCompensatedLift w g) = g ∧
      ∀ x, ‖phaseCompensatedLift w g x‖ = ‖g x.1‖ := by
  have hw0 : ∀ x, w x ≠ 0 := fun x => by
    intro hx
    have := hw x
    simp [hx] at this
  exact ⟨weightedTransfer_phaseCompensatedLift w g hw0,
    norm_phaseCompensatedLift w g hw⟩

end ArkLib.ProximityGap.Frontier.DYN09DyadicTransferRightInverseNoGo

#print axioms ArkLib.ProximityGap.Frontier.DYN09DyadicTransferRightInverseNoGo.siblingAverage_coarseLift
#print axioms ArkLib.ProximityGap.Frontier.DYN09DyadicTransferRightInverseNoGo.haarProjection_idempotent
#print axioms ArkLib.ProximityGap.Frontier.DYN09DyadicTransferRightInverseNoGo.centered_coarseLift
#print axioms ArkLib.ProximityGap.Frontier.DYN09DyadicTransferRightInverseNoGo.not_strictMeanZeroContraction
#print axioms ArkLib.ProximityGap.Frontier.DYN09DyadicTransferRightInverseNoGo.weightedTransfer_phaseCompensatedLift
#print axioms ArkLib.ProximityGap.Frontier.DYN09DyadicTransferRightInverseNoGo.weightedHaarProjection_idempotent
#print axioms ArkLib.ProximityGap.Frontier.DYN09DyadicTransferRightInverseNoGo.weightedTransfer_normPreserving_rightInverse
