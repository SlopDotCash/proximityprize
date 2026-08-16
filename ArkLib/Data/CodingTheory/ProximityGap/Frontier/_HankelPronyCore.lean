/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
Scratch: the genuinely-provable Prony/Hankel CORE for ESCAPE B1 hankel-rank angle.
A t-term exponential sum on mu_n that vanishes at t consecutive sampling points (an AP) and
is sampled by DISTINCT ratios is identically zero on that AP -- the Vandermonde nonsingularity.
This is the OFF-BGK provable lever; the AP-core extraction (vanishing-sums) is the open part.
-/
open Matrix Finset

namespace ProximityGap.Frontier.HankelPronyCore

variable {F : Type*} [Field F]

/-- The provable Vandermonde core: distinct ratios `r : Fin t → F` give an invertible
Vandermonde, so a `t`-term exponential sum vanishing at `t` consecutive AP points whose
ratio-powers form that Vandermonde forces all coefficients to be 0 (= identically zero on
the AP). This is the cyclic-Prony / generalized-Descartes nonsingularity. -/
theorem expSum_vanish_t_consecutive_forces_zero
    {t : ℕ} (r : Fin t → F) (hr : Function.Injective r) (u : Fin t → F)
    (hvanish : ∀ m : Fin t, ∑ j, u j * (r j) ^ (m : ℕ) = 0) :
    ∀ j, u j = 0 := by
  -- The vanishing conditions say (vandermonde r)ᵀ ⬝ u = 0; vandermonde r invertible ⟹ u = 0.
  have hdet : (Matrix.vandermonde r).det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]; exact hr
  -- vandermonde r has (i,j) entry r i ^ j. The system: for each m, ∑_j u j * r j ^ m = 0.
  -- That is (Vᵀ) m j = r j ^ m, so ∑_j (Vᵀ) m j * u j = 0, i.e. Vᵀ.mulVec u = 0.
  have hMV : (Matrix.vandermonde r)ᵀ.mulVec u = 0 := by
    funext m
    simp only [Matrix.mulVec, Matrix.transpose_apply, Matrix.vandermonde_apply,
      dotProduct, Pi.zero_apply]
    rw [← hvanish m]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hinj := Matrix.mulVec_injective_iff_isUnit (A := (Matrix.vandermonde r)ᵀ)
  have hunit : IsUnit ((Matrix.vandermonde r)ᵀ) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 hdet
  have : (Matrix.vandermonde r)ᵀ.mulVec u = (Matrix.vandermonde r)ᵀ.mulVec 0 := by
    rw [hMV, Matrix.mulVec_zero]
  have := (hinj.2 hunit) this
  intro j; rw [this]; rfl

end ProximityGap.Frontier.HankelPronyCore

#print axioms ProximityGap.Frontier.HankelPronyCore.expSum_vanish_t_consecutive_forces_zero
