/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Data.Nat.Basic

/-! # Degree and fiber-size requirements for improving the half-rate tetrahedron

A one-fresh witness before the named six-edge construction needs all six edge
cores to have at least 686001720 sites. The hypotheses express the incidence
and direction bounds of the geometry on an arbitrary rational quotient.
-/

namespace ProximityGap.RationalTetrahedronLimits

/-- Degree at most one eighth, or at least one quarter, cannot improve the
named step. The arguments count owned ordinary sites and all six core sizes. -/
theorem degree_window {r d o l : ℕ}
    (hd : r+d+2 ≤ 536870912) (hbudget : 2147483648 < l)
    (hlabels : l+3*o+6*r ≤ 6*1073741824)
    (hfibers : 6*686001720 ≤ 6*r+o+8*d)
    (hthree : 6*686001720 ≤ 3*1073741824+3*r) :
    134217728 < d ∧ d < 268435456 := by omega

/-- The three edges incident with the smallest fiber have at most one joint
owner away from that vertex and the common roots. -/
theorem minimum_fiber {r d f : ℕ} (hd : r+d+2 ≤ 536870912)
    (hstar : 3*686001720 ≤ 2*r+1073741824+2*f) :
    (201326592 ≤ d → 134217728 < f) ∧ (234881024 ≤ d → 167772160 < f) := by omega

/-- With at most two full quintic fibers on the 32-node quotient, delete the
edge between the two largest vertex fibers. The other five cores cannot
all reach the required size. -/
theorem quintic_needs_three_full {r o l : ℕ}
    (hd : r+167772160+2 ≤ 536870912) (hbudget : 2147483648 < l)
    (hlabels : l+3*o+6*r ≤ 6*1073741824) :
    5*r+o+26*33554432 < 5*686001720 := by omega

/-- If all four sextic fibers have at most five quotient elements, counting
all six edge cores excludes a better allocation. -/
theorem sextic_needs_full {r o : ℕ}
    (hd : r+201326592+2 ≤ 536870912) (hslots : o+r ≤ 1073741824) :
    6*r+o+40*33554432 < 6*686001720 := by omega

#print axioms degree_window
#print axioms minimum_fiber
#print axioms quintic_needs_three_full
#print axioms sextic_needs_full
end ProximityGap.RationalTetrahedronLimits
