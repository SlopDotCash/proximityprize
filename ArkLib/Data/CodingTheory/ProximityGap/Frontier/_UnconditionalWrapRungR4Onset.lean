/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._UnconditionalWrapRungR3

/-!
# The first explicit wraparound witness at the next rung (#444, Angle 1)

`_UnconditionalWrapRungR3` proves that, for the concrete embedding used there
`ζ ↦ 43 ∈ F₁₉₃` of the `8`th roots of unity, the wrap-excess witness set is empty at
`r = 3` (budget `2r = 6`).  The file docstring records the probe-side sharpness witness
`(-5, 2, 1, 0)`, whose `ℓ¹`-norm is `8` and whose evaluation is

`-5 + 2·43 + 112 = 193 ≡ 0 (mod 193)`.

This file formalizes that explicit onset witness: the same wrap-excess set is nonempty at
`r = 4` (budget `8`).  It is a small exact lattice/incidence calibration brick only.  It does
not prove exact shortest-vector optimality at `ℓ¹ = 8`, does not close CORE, and makes no
capacity or growth-law claim.
-/

set_option linter.style.longLine false

open ArkLib.ProximityGap.CyclotomicLatticeWrapOnset

namespace ArkLib.ProximityGap.Frontier.UnconditionalWrapRungR4Onset

open ArkLib.ProximityGap.Frontier.UnconditionalWrapRungR3 (gvec)

/-- The explicit first-wrap vector from the probe: `-5 + 2ζ + ζ²`. -/
def firstWrapVec : Fin 4 → ℤ := ![-5, 2, 1, 0]

/-- The vector evaluates to `193`, hence lies in the ideal above `193` for `ζ ↦ 43`. -/
theorem firstWrapVec_mem_ideal : InIdeal 193 gvec firstWrapVec := by
  unfold InIdeal firstWrapVec gvec
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  norm_num

/-- The first-wrap vector uses exactly the `r=4` budget: `|-5|+|2|+|1|+|0| = 8`. -/
theorem firstWrapVec_l1Norm : l1Norm firstWrapVec = 8 := by
  unfold l1Norm firstWrapVec
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  norm_num

/-- The first-wrap vector is genuinely nonzero as an integer coefficient vector. -/
theorem firstWrapVec_ne_zero : firstWrapVec ≠ 0 := by
  intro h
  have h0 := congr_fun h (0 : Fin 4)
  norm_num [firstWrapVec] at h0

/-- **The wrap-excess witness set is nonempty at `r = 4`.**
Together with `_UnconditionalWrapRungR3.wrapExcess_zero_at_r3`, this pins the concrete onset
transition for the `(n,p)=(8,193)` embedding: budget `6` has no nonzero ideal vector, while
budget `8` already has the explicit vector `(-5,2,1,0)`. -/
theorem wrapExcess_nonempty_at_r4 :
    ({c : Fin 4 → ℤ | InIdeal 193 gvec c ∧ l1Norm c ≤ 2 * 4 ∧ c ≠ 0} : Set (Fin 4 → ℤ)).Nonempty := by
  refine ⟨firstWrapVec, ?_⟩
  exact ⟨firstWrapVec_mem_ideal, by simp [firstWrapVec_l1Norm], firstWrapVec_ne_zero⟩

end ArkLib.ProximityGap.Frontier.UnconditionalWrapRungR4Onset

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.UnconditionalWrapRungR4Onset.firstWrapVec_mem_ideal
#print axioms ArkLib.ProximityGap.Frontier.UnconditionalWrapRungR4Onset.firstWrapVec_l1Norm
#print axioms ArkLib.ProximityGap.Frontier.UnconditionalWrapRungR4Onset.wrapExcess_nonempty_at_r4
