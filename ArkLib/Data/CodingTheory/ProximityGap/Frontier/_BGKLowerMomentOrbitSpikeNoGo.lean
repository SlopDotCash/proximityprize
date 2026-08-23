/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Production orbit-moment spike: moments through six do not control depth seven

This file audits a tempting truncated-moment route to the repaired BGK depth-seven target.  Put
`s_b = |eta_b|^2` on the nonzero frequencies.  Multiplicative invariance makes `s_b` constant on
each orbit of the subgroup, and every orbit has size `n`.  At the production parameters

* `n = 2^30`,
* `m = 2^128 + 192` nonzero-frequency orbits,
* `q = n*m + 1`,

the exact Parseval mass is `sum_(b != 0) s_b = n*(q-n)`.  The desired repaired depth-seven bound is

`sum_(b != 0) s_b^7 <= q * 2^18 * n^7`.

The characteristic-zero dyadic census has Wick ceilings
`sum s_b^r <= q*(2r-1)!!*n^r`.  Those ceilings are NOT known unconditionally at the production
prime for `r = 2,...,6`; their characteristic-`p` transfer is part of the open wall.  The no-go
below is stronger: even granting every one of those six ceilings, together with exact mass, orbit
multiplicity, and the trivial pointwise cap `s_b <= n^2`, does not imply the seventh target.

The witness has one orbit at `T = 2^53 = 2^23*n`, `2^23-1` zero orbits, one orbit at `1`, and all
remaining orbits at `n`.  Replacing `2^23` baseline `n`-orbits by one `T`-orbit and zero orbits
preserves the exact first moment.  The sixth-moment Wick allowance still has more than three bits
of room for this spike, while its seventh moment violates the target by a factor strictly between
`2^15` and `2^16`.

Thus a truncated moment argument through `sum s_b^6` necessarily loses an orbit-count factor of
order `m^(1/6)`.  A closing argument needs genuinely seventh-order arithmetic/phase information;
the already-landed characteristic-zero/no-wrap facts at lower depth cannot be interpolated upward.
This is a negative guardrail, not a BGK closure.  Issue #466.
-/

set_option autoImplicit false
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192

namespace ArkLib.ProximityGap.Frontier.BGKLowerMomentOrbitSpikeNoGo

/-- Production subgroup size. -/
def productionN : Nat := 2 ^ 30

/-- Number of multiplicative orbits on the nonzero frequencies. -/
def productionM : Nat := 2 ^ 128 + 192

/-- Production field cardinality. -/
def productionQ : Nat := productionN * productionM + 1

/-- The single exceptional squared-amplitude orbit in the countermodel. -/
def productionSpike : Nat := 2 ^ 53

/-- Number of zero orbits used to preserve the exact first moment. -/
def productionZeroOrbits : Nat := 2 ^ 23 - 1

/-- Number of ordinary orbits, each of squared amplitude `n`. -/
def productionBulkOrbits : Nat := productionM - 2 ^ 23 - 1

/-- Orbit-level power sum of the explicit profile.  Multiplying by `productionN` gives the
corresponding sum over all nonzero frequencies, since every orbit has size `productionN`. -/
def orbitPowerMoment (r : Nat) : Nat :=
  productionSpike ^ r + 1 + productionBulkOrbits * productionN ^ r

/-- Full nonzero-frequency power sum represented by the explicit orbit profile. -/
def fullPowerMoment (r : Nat) : Nat := productionN * orbitPowerMoment r

/-- The repaired public depth-seven target. -/
def productionSeventhTarget : Nat :=
  productionQ * 2 ^ 18 * productionN ^ 7

/-- The profile really has exactly `m` orbits: one spike, one unit orbit, the stated zero orbits,
and the remaining bulk orbits. -/
theorem profile_orbit_count :
    1 + 1 + productionZeroOrbits + productionBulkOrbits = productionM := by
  norm_num [productionZeroOrbits, productionBulkOrbits, productionM]

/-- The spike respects the elementary Gauss-sum cap `s_b = |eta_b|^2 <= n^2`. -/
theorem productionSpike_le_trivialCap : productionSpike <= productionN ^ 2 := by
  norm_num [productionSpike, productionN]

/-- Exact Parseval mass: the explicit orbit profile has
`n * sum_orbits s = n*(q-n)`. -/
theorem fullPowerMoment_one_exact :
    fullPowerMoment 1 = productionN * (productionQ - productionN) := by
  norm_num [fullPowerMoment, orbitPowerMoment, productionSpike, productionBulkOrbits,
    productionQ, productionM, productionN]

/-- The first through sixth Wick coefficients. -/
def wickCoefficient (r : Nat) : Nat := Nat.doubleFactorial (2 * r - 1)

/-- Even after granting the characteristic-zero Wick ceiling at depth two, the profile is
feasible. -/
theorem fullPowerMoment_two_le_wick :
    fullPowerMoment 2 <= productionQ * wickCoefficient 2 * productionN ^ 2 := by
  norm_num [fullPowerMoment, orbitPowerMoment, productionSpike, productionBulkOrbits,
    productionQ, productionM, productionN, wickCoefficient, Nat.doubleFactorial]

/-- Even after granting the characteristic-zero Wick ceiling at depth three, the profile is
feasible. -/
theorem fullPowerMoment_three_le_wick :
    fullPowerMoment 3 <= productionQ * wickCoefficient 3 * productionN ^ 3 := by
  norm_num [fullPowerMoment, orbitPowerMoment, productionSpike, productionBulkOrbits,
    productionQ, productionM, productionN, wickCoefficient, Nat.doubleFactorial]

/-- Even after granting the characteristic-zero Wick ceiling at depth four, the profile is
feasible. -/
theorem fullPowerMoment_four_le_wick :
    fullPowerMoment 4 <= productionQ * wickCoefficient 4 * productionN ^ 4 := by
  norm_num [fullPowerMoment, orbitPowerMoment, productionSpike, productionBulkOrbits,
    productionQ, productionM, productionN, wickCoefficient, Nat.doubleFactorial]

/-- Even after granting the characteristic-zero Wick ceiling at depth five, the profile is
feasible. -/
theorem fullPowerMoment_five_le_wick :
    fullPowerMoment 5 <= productionQ * wickCoefficient 5 * productionN ^ 5 := by
  norm_num [fullPowerMoment, orbitPowerMoment, productionSpike, productionBulkOrbits,
    productionQ, productionM, productionN, wickCoefficient, Nat.doubleFactorial]

/-- Even after granting the characteristic-zero Wick ceiling at depth six, the profile is
feasible.  This is the load-bearing strongest lower-moment constraint. -/
theorem fullPowerMoment_six_le_wick :
    fullPowerMoment 6 <= productionQ * wickCoefficient 6 * productionN ^ 6 := by
  norm_num [fullPowerMoment, orbitPowerMoment, productionSpike, productionBulkOrbits,
    productionQ, productionM, productionN, wickCoefficient, Nat.doubleFactorial]

/-- Package of every granted lower-moment ceiling `r = 2,...,6`. -/
theorem all_lower_moment_wick_ceils :
    fullPowerMoment 2 <= productionQ * wickCoefficient 2 * productionN ^ 2 /\
    fullPowerMoment 3 <= productionQ * wickCoefficient 3 * productionN ^ 3 /\
    fullPowerMoment 4 <= productionQ * wickCoefficient 4 * productionN ^ 4 /\
    fullPowerMoment 5 <= productionQ * wickCoefficient 5 * productionN ^ 5 /\
    fullPowerMoment 6 <= productionQ * wickCoefficient 6 * productionN ^ 6 := by
  exact And.intro fullPowerMoment_two_le_wick
    (And.intro fullPowerMoment_three_le_wick
      (And.intro fullPowerMoment_four_le_wick
        (And.intro fullPowerMoment_five_le_wick fullPowerMoment_six_le_wick)))

/-- The explicit profile exceeds the repaired seventh-moment target by more than fifteen bits. -/
theorem fifteen_bit_target_failure :
    2 ^ 15 * productionSeventhTarget < fullPowerMoment 7 := by
  norm_num [productionSeventhTarget, fullPowerMoment, orbitPowerMoment, productionSpike,
    productionBulkOrbits, productionQ, productionM, productionN]

/-- The exact gap is below sixteen bits, locating the countermodel ratio in `[2^15,2^16)`. -/
theorem target_failure_lt_sixteen_bits :
    fullPowerMoment 7 < 2 ^ 16 * productionSeventhTarget := by
  norm_num [productionSeventhTarget, fullPowerMoment, orbitPowerMoment, productionSpike,
    productionBulkOrbits, productionQ, productionM, productionN]

/-- Consolidated no-go: exact mass, orbit count, the elementary amplitude cap, and every Wick
ceiling through depth six coexist with a greater-than-`2^15` failure of the depth-seven target. -/
theorem lower_moments_through_six_do_not_force_target :
    1 + 1 + productionZeroOrbits + productionBulkOrbits = productionM /\
    productionSpike <= productionN ^ 2 /\
    fullPowerMoment 1 = productionN * (productionQ - productionN) /\
    (fullPowerMoment 2 <= productionQ * wickCoefficient 2 * productionN ^ 2 /\
      fullPowerMoment 3 <= productionQ * wickCoefficient 3 * productionN ^ 3 /\
      fullPowerMoment 4 <= productionQ * wickCoefficient 4 * productionN ^ 4 /\
      fullPowerMoment 5 <= productionQ * wickCoefficient 5 * productionN ^ 5 /\
      fullPowerMoment 6 <= productionQ * wickCoefficient 6 * productionN ^ 6) /\
    2 ^ 15 * productionSeventhTarget < fullPowerMoment 7 /\
    fullPowerMoment 7 < 2 ^ 16 * productionSeventhTarget := by
  exact And.intro profile_orbit_count
    (And.intro productionSpike_le_trivialCap
      (And.intro fullPowerMoment_one_exact
        (And.intro all_lower_moment_wick_ceils
          (And.intro fifteen_bit_target_failure target_failure_lt_sixteen_bits))))

end ArkLib.ProximityGap.Frontier.BGKLowerMomentOrbitSpikeNoGo

/-! ## Axiom audit (expected: no axioms) -/
#print axioms
  ArkLib.ProximityGap.Frontier.BGKLowerMomentOrbitSpikeNoGo.lower_moments_through_six_do_not_force_target
