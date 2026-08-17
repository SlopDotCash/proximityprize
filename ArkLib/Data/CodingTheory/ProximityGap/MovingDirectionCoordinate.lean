/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepStratumMovingDirection
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandCoherence

/-!
# The surviving moving-direction coordinate is core-independent (#389, route-2 deep stratum)

At a deep overlap (`k+1 ≤ |T∩T'|`) with a point `p ∈ T'∖T`, the moving interpolant has a nonzero
coefficient in the band `k+1, …, k+m` (`exists_surviving_band_coord`), while the core interpolant of
the vanishing polynomial `Z_T` is identically zero (`interp_T_vanishPoly_eq_zero`) so *all* its band
coefficients vanish.  This packages the two into a single witness: a band coordinate where the moving
direction survives and the core does not — the coordinate that drives the `m+1` rank gain.
-/

set_option linter.unusedSectionVars false


open Finset Polynomial

namespace ProximityGap.DeepStratumMoving

open ProximityGap.Ownership

variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}

/-- **The surviving moving-direction coordinate is core-independent.** -/
theorem moving_direction_surviving_coordinate_independent (dom : Fin n ↪ F) {k m : ℕ}
    (T T' : Finset (Fin n)) (hT' : T'.card = k + m + 1) (hdeep : k + 1 ≤ (T ∩ T').card)
    {p : Fin n} (hpT' : p ∈ T') (hpT : p ∉ T) :
    ∃ d : Fin m, (movingInterp dom T T').coeff (k + 1 + (d : ℕ)) ≠ 0 ∧
      (coreInterp dom T (vanishPoly dom T)).coeff (k + 1 + (d : ℕ)) = 0 := by
  obtain ⟨d, hd⟩ := exists_surviving_band_coord dom T T' hT' hdeep hpT' hpT
  refine ⟨d, hd, ?_⟩
  have hzero : coreInterp dom T (vanishPoly dom T) = 0 := interp_T_vanishPoly_eq_zero dom T
  rw [hzero, Polynomial.coeff_zero]

end ProximityGap.DeepStratumMoving
