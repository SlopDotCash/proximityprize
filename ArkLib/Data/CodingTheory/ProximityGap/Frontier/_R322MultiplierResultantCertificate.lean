/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R322MultiplierResultantCertificate

open Polynomial

/-! Exact certificate for the R320 multiplier at the first relevant dyadic scale. -/
theorem x16_add_one_resultant_x4_sub_one :
    resultant (X ^ 16 + 1 : Polynomial ℤ) (X ^ 4 - 1) = 16 := by
  let f : Polynomial ℤ := C 2
  let g : Polynomial ℤ := X ^ 4 - 1
  let p : Polynomial ℤ := X ^ 12 + X ^ 8 + X ^ 4 + 1
  have hpoly : X ^ 16 + 1 = f + g * p := by
    simp only [f, g, p]
    norm_num
    ring
  rw [show (X ^ 16 + 1 : Polynomial ℤ).natDegree = 16 by compute_degree!]
  rw [show (X ^ 4 - 1 : Polynomial ℤ).natDegree = 4 by compute_degree!]
  change resultant (X ^ 16 + 1 : Polynomial ℤ) g 16 4 = 16
  rw [hpoly, resultant_add_mul_left (f := f) (p := p)]
  · norm_num [f, g, coeff_one]
  · dsimp only [p]
    have hp : (X ^ 12 + X ^ 8 + X ^ 4 + 1 : Polynomial ℤ).natDegree = 12 := by
      compute_degree!
    omega
  · dsimp only [g]
    have hg : (X ^ 4 - 1 : Polynomial ℤ).natDegree = 4 := by
      compute_degree!
    omega

end ArkLib.ProximityGap.Frontier.R322MultiplierResultantCertificate

#print axioms
  ArkLib.ProximityGap.Frontier.R322MultiplierResultantCertificate.x16_add_one_resultant_x4_sub_one
