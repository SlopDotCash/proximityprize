/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import Mathlib.Data.Fin.VecNotation

/-! # Four septics for the first-prime ceiling of 313174699 errors

The sixteenth-root evaluations and production slot counts are certified here. The
witness construction is in `docs/research/proximity-gap/rate-half-seven-twenty-fourths.md`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace ProximityGap.RateHalfSevenTwentyFourths

open ArkLib.ProximityGap.PrizeShapePrimeP30 (P g)
open ArkLib.ProximityGap.BinaryPower (binaryPow_eq_pow)

private abbrev F := ZMod P
private instance : Fact P.Prime := ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

def omega : F := g ^ (2 ^ 26 : ℕ)
private abbrev omegaValue : F := 357111556877444407914257742635116754287240874648

theorem omega_eq : omega = omegaValue := by
  unfold omega
  rw [← binaryPow_eq_pow]
  decide

/-- The degree-six even-factor locator times the degree-one correction. -/
def head (z : F) (i : Fin 4) (y : F) : F :=
  let a := z ^ (4 * i.val)
  (y^6 + a*y^4 + a^2*y^2 + a^3) * ((a + z^2*a^2)*y + z^5 + z^3*a^3)

def classID (j : Fin 16) : Fin 4 → ℕ :=
  ![![0,1,1,1], ![0,1,1,1], ![0,1,0,0], ![0,1,2,1],
    ![0,0,2,0], ![0,1,0,0], ![0,0,0,3], ![0,1,2,3],
    ![0,1,1,1], ![0,0,2,0], ![0,1,0,0], ![0,1,0,3],
    ![0,0,2,0], ![0,0,0,3], ![0,0,0,3], ![0,1,1,0]] j

/-- Every equality and inequality on all sixteen fibers at the actual prime. -/
theorem equality_class_table : ∀ (j : Fin 16) (i k : Fin 4),
    head omega i (omega ^ j.val) = head omega k (omega ^ j.val) ↔
    classID j i = classID j k := by
  rw [omega_eq]
  decide

/-- The allocation has `s-2` locator roots and enough distinct witness labels. -/
theorem allocation (s t : ℕ) (hs : s = 6*t+4) (ht : 1 ≤ t) :
    (4*t+3)+(t-1)+t = s-2 ∧ 16*s-(s-2)+3*(2*t+1) = 16*s+1 ∧
    9*s+(s-2)+(s-t)+s/2 = 68*t+44 ∧
    16*s-(68*t+44)-1 = 28*t+19 ∧ 24*(28*t+19) = 7*(16*s)+8 := by omega

/-- The degree, security budget, label count, and absolute error endpoint. -/
theorem production : let n := 2^30; let s := 2^26; let t := 11184810
    s = 6*t+4 ∧ 16*s = n ∧ 7*s+(s-2)+1 < n/2 ∧ 68*t+44 = 760567124 ∧
    n-(68*t+44)-1 = 313174699 ∧ P/2^128 = n ∧ 4*(n+1)+1 < P := by decide

#print axioms omega_eq
#print axioms equality_class_table
#print axioms allocation
#print axioms production

end ProximityGap.RateHalfSevenTwentyFourths
