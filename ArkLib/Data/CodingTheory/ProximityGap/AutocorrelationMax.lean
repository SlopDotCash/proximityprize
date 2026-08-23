/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Autocorrelation is maximised at the origin (#389 cyclotomic-lattice core)

The structural backbone of the cyclotomic-lattice reformulation of the δ* open core
(`docs/kb/deltastar-cyclotomic-lattice-collision-core-2026-06-13.md`): the representation
function `R_r(z) = #{(x,y) : Σx − Σy = z}` of a subgroup is the autocorrelation
`R_r = r_r ⋆ r_r` of the `r`-fold sumset count `r_r`, hence is maximised at `z = 0`:

    `R_r(z) ≤ R_r(0)   for all z.`

This says the **spurious** (`z ≠ 0`, `𝔭 | z`) representation mass per lattice point never
exceeds the **diagonal** mass `R_r(0)` — the elementary half of the halo bound. (The open part
is that the *number* of contributing sublattice points times this cap stays small; that is the
genuine analytic-NT residual and is NOT addressed here.)

Here we prove the field-independent analytic heart: for any `f : A → ℝ` with `0 ≤ f`,
`∑_w f(w)·f(w − z) ≤ ∑_w f(w)^2`, via Cauchy–Schwarz and translation-invariance of the sum.
Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace ArkLib.ProximityGap.AutocorrelationMax

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- Translation invariance of a full sum over a finite abelian group:
`∑_w g(w − z) = ∑_w g(w)`. -/
theorem sum_comp_sub_right (g : A → ℝ) (z : A) :
    ∑ w, g (w - z) = ∑ w, g w := by
  refine Fintype.sum_equiv (Equiv.subRight z) _ _ ?_
  intro w; rfl

/-- **Autocorrelation is maximised at the origin.** For a nonnegative weight `f : A → ℝ`, the
cross-correlation at any shift `z` is bounded by the value at `0`:
`∑_w f(w)·f(w − z) ≤ ∑_w f(w)^2`.  This is the structural cap `R_r(z) ≤ R_r(0)`. -/
theorem autocorr_le_autocorr_zero (f : A → ℝ) (hf : ∀ w, 0 ≤ f w) (z : A) :
    ∑ w, f w * f (w - z) ≤ ∑ w, f w ^ 2 := by
  -- Cauchy–Schwarz: (∑ a·b)² ≤ (∑ a²)(∑ b²), with a = f w, b = f (w - z).
  have hcs : (∑ w, f w * f (w - z)) ^ 2
      ≤ (∑ w, f w ^ 2) * (∑ w, f (w - z) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq univ (fun w => f w) (fun w => f (w - z))
  -- the two L² masses are equal by translation invariance
  have hshift : ∑ w, f (w - z) ^ 2 = ∑ w, f w ^ 2 :=
    sum_comp_sub_right (fun w => f w ^ 2) z
  rw [hshift] at hcs
  -- so (∑ cross)² ≤ (∑ f²)², and ∑ f² ≥ 0, ∑ cross ≥ 0 ⟹ ∑ cross ≤ ∑ f²
  have hsq_nonneg : 0 ≤ ∑ w, f w ^ 2 := Finset.sum_nonneg (fun w _ => sq_nonneg _)
  have hcross_nonneg : 0 ≤ ∑ w, f w * f (w - z) :=
    Finset.sum_nonneg (fun w _ => mul_nonneg (hf w) (hf _))
  nlinarith [hcs, hsq_nonneg, hcross_nonneg,
    sq_nonneg ((∑ w, f w ^ 2) - (∑ w, f w * f (w - z)))]

end ArkLib.ProximityGap.AutocorrelationMax

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AutocorrelationMax.autocorr_le_autocorr_zero
