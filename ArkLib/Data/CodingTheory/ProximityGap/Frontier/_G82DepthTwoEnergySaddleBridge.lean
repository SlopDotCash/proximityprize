/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G82: a square-root energy saving absorbs the full primitive depth-two sector

The corrected factorial-padding route reduces a primitive depth-two sector to the arithmetic
condition `J * r^2 <= n^2`, where `J` is the count of primitive orbit representatives supplied
by the cancellation encoding. This file records a useful square-root form of that condition.

If

```text
J^2 <= C^2 * n^3                    (J <= C * n^(3/2))
C^2 * r^4 <= n,
```

then `J * r^2 <= n^2`. At the nominal
production point `(n,r)=(2^30,110)`, the arithmetic has enough room for the explicit constant
`C=2`.

This permits `J` of order `n^(3/2)` and isolates a classical additive-energy-sized input rather
than a Paley/sup-norm input. The file does not assert that the actual primitive orbit count
satisfies this estimate. It intentionally does not consume G79S's refuted raw padding envelope;
the intended consumer is G81's factorial-corrected full-Wick envelope. Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge

/-- A square-root saving in the primitive orbit count implies the exact depth-two saddle
condition.  The cleared hypothesis allows an explicit constant `C`. -/
theorem orbit_budget_of_sq_le
    {n r J C : ℕ}
    (hJ : J ^ 2 ≤ C ^ 2 * n ^ 3)
    (hsmall : C ^ 2 * r ^ 4 ≤ n) :
    J * r ^ 2 ≤ n ^ 2 := by
  apply (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp
  calc
    (J * r ^ 2) ^ 2 = J ^ 2 * r ^ 4 := by ring
    _ ≤ (C ^ 2 * n ^ 3) * r ^ 4 := by gcongr
    _ = n ^ 3 * (C ^ 2 * r ^ 4) := by ring
    _ ≤ n ^ 3 * n := by gcongr
    _ = (n ^ 2) ^ 2 := by ring

/-- Convert a standard additive-energy-shaped estimate into the orbit-count hypothesis above.
If every primitive orbit has at least `n` realizations (`n*J <= E`) and the total energy has
the square-root-saving bound `E^2 <= C^2*n^5`, then `J^2 <= C^2*n^3`.

The statement deliberately separates the combinatorial orbit-to-energy injection from the
numeric cancellation, so the former can be supplied by G80's canonical encoding. -/
theorem sq_orbit_bound_of_energy
    {n J E C : ℕ}
    (hn : 0 < n)
    (hJE : n * J ≤ E)
    (hE : E ^ 2 ≤ C ^ 2 * n ^ 5) :
    J ^ 2 ≤ C ^ 2 * n ^ 3 := by
  have hsq : (n * J) ^ 2 ≤ E ^ 2 := Nat.pow_le_pow_left hJE 2
  have hmul : n ^ 2 * J ^ 2 ≤ n ^ 2 * (C ^ 2 * n ^ 3) := by
    calc
      n ^ 2 * J ^ 2 = (n * J) ^ 2 := by ring
      _ ≤ E ^ 2 := hsq
      _ ≤ C ^ 2 * n ^ 5 := hE
      _ = n ^ 2 * (C ^ 2 * n ^ 3) := by ring
  exact Nat.le_of_mul_le_mul_left hmul (by positivity)

/-- At `(n,r)=(2^30,110)`, the `C=2` energy-sized orbit hypothesis implies the exact
depth-two saddle budget required by the corrected padding consumer. -/
theorem production_depth_two_orbit_budget
    {J : ℕ}
    (hJ : J ^ 2 ≤ 2 ^ 2 * (2 ^ 30) ^ 3) :
    J * 110 ^ 2 ≤ (2 ^ 30) ^ 2 := by
  apply orbit_budget_of_sq_le hJ
  norm_num

end ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.orbit_budget_of_sq_le
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.sq_orbit_bound_of_energy
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.production_depth_two_orbit_budget
