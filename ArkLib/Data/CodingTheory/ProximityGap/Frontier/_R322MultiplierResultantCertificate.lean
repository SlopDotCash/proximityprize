import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R322MultiplierResultantCertificate

open Polynomial

/-! Exact certificate for the R320 multiplier at the first relevant dyadic scale. -/
theorem x16_add_one_resultant_x4_sub_one :
    resultant (X ^ 16 + 1 : Polynomial ℤ) (X ^ 4 - 1) = 16 := by
  norm_num [resultant, sylvester]

end ArkLib.ProximityGap.Frontier.R322MultiplierResultantCertificate

#print axioms
  ArkLib.ProximityGap.Frontier.R322MultiplierResultantCertificate.x16_add_one_resultant_x4_sub_one
