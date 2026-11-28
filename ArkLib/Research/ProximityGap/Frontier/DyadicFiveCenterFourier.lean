/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Roots

/-! # Five-center separation for the two Fourier frequencies on a dyadic grid -/

namespace ProximityGap.DyadicFiveCenterFourier

open Polynomial

variable {K : Type*} [Field K]

/-- Clearing the two negative powers of a two-frequency Fourier expression gives a quartic.
Five distinct zeros force both its top Fourier coefficients to vanish. The four coefficients
may be independent, which includes the conjugate-symmetric specialization. -/
theorem five_center_separation (sites : Finset K) (a b c d h : K)
    (five : 5 ≤ sites.card)
    (zeros : ∀ z ∈ sites, b * z ^ 4 + a * z ^ 3 + h * z ^ 2 + c * z + d = 0) :
    b = 0 ∧ a = 0 := by
  classical
  let f : K[X] := C b * X ^ 4 + C a * X ^ 3 + C h * X ^ 2 + C c * X ^ 1 + C d
  have deg : f.natDegree ≤ 4 := by
    have bound := natDegree_add_le_of_le (natDegree_add_le_of_le (natDegree_add_le_of_le
      (natDegree_add_le_of_le (natDegree_C_mul_X_pow_le b 4) (natDegree_C_mul_X_pow_le a 3))
      (natDegree_C_mul_X_pow_le h 2)) (natDegree_C_mul_X_pow_le c 1))
      (show (C d).natDegree ≤ 0 by simp)
    simpa [f] using bound
  have zero : f = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' f sites
    (fun z hz => by simpa [f] using zeros z hz) (by omega)
  constructor
  · simpa [f, coeff_C_mul_X_pow, coeff_C] using congrArg (fun g : K[X] => g.coeff 4) zero
  · simpa [f, coeff_C_mul_X_pow, coeff_C] using congrArg (fun g : K[X] => g.coeff 3) zero

#print axioms five_center_separation

end ProximityGap.DyadicFiveCenterFourier
