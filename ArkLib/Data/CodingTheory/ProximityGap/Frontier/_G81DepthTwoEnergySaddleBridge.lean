/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G79SPrimitivePaddingSaddleLocalization

/-!
# G81: a square-root energy saving absorbs the full primitive depth-two sector

G79S reduces a primitive depth-`s` sector to the arithmetic condition `J * r^s <= n^s`,
where `J` is the count of primitive orbit representatives supplied by the cancellation encoding.
For `s = 2`, this file records the quantitatively useful square-root form of that condition.

If

```text
J^2 <= C^2 * n^3                    (J <= C * n^(3/2))
C^2 * r^4 <= n,
```

then `J * r^2 <= n^2`, so G79S absorbs the whole padded depth-two sector.  At the nominal
production point `(n,r)=(2^30,110)`, the arithmetic has enough room for the explicit constant
`C=2`.

This is a genuine weakening of the linear-orbit hypothesis used by G79S's first concrete
corollary: it permits `J` of order `n^(3/2)`.  It isolates a classical additive-energy-sized
input, rather than a Paley/sup-norm input.  The file does not assert that the actual primitive
orbit count satisfies this estimate; connecting the canonical G80 cancellation encoding to a
subgroup additive-energy theorem is the remaining depth-two task.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G81DepthTwoEnergySaddleBridge

open G79PrimitivePaddingSaddleLocalization

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

/-- **Depth-two energy-to-Wick consumer.**  A padded primitive depth-two sector is absorbed
whenever its orbit count has a `C*n^(3/2)` square bound and the saddle has
`C^2*r^4 <= n`. -/
theorem paddedDepthTwo_le_oddTailWick_of_sq_orbit_bound
    {n r J W C : ℕ}
    (hrs : 4 ≤ r + 1)
    (hr : 2 ≤ r)
    (hW : W ≤ padEnvelope n r J 2)
    (hJ : J ^ 2 ≤ C ^ 2 * n ^ 3)
    (hsmall : C ^ 2 * r ^ 4 ≤ n) :
    W ≤ oddWickTail r 2 * n ^ r := by
  apply paddedSector_le_oddTailWick hrs hr hW
  exact orbit_budget_of_sq_le hJ hsmall

/-- End-to-end numeric consumer from an additive-energy-shaped estimate. -/
theorem paddedDepthTwo_le_oddTailWick_of_energy
    {n r J E W C : ℕ}
    (hn : 0 < n)
    (hrs : 4 ≤ r + 1)
    (hr : 2 ≤ r)
    (hW : W ≤ padEnvelope n r J 2)
    (hJE : n * J ≤ E)
    (hE : E ^ 2 ≤ C ^ 2 * n ^ 5)
    (hsmall : C ^ 2 * r ^ 4 ≤ n) :
    W ≤ oddWickTail r 2 * n ^ r := by
  apply paddedDepthTwo_le_oddTailWick_of_sq_orbit_bound hrs hr hW
  · exact sq_orbit_bound_of_energy hn hJE hE
  · exact hsmall

/-- At `(n,r)=(2^30,110)`, even a `2*n^(3/2)` primitive orbit budget is absorbed. -/
theorem production_depth_two_energy_absorbed
    {J W : ℕ}
    (hW : W ≤ padEnvelope (2 ^ 30) 110 J 2)
    (hJ : J ^ 2 ≤ 2 ^ 2 * (2 ^ 30) ^ 3) :
    W ≤ oddWickTail 110 2 * (2 ^ 30) ^ 110 := by
  apply paddedDepthTwo_le_oddTailWick_of_sq_orbit_bound
      (n := 2 ^ 30) (r := 110) (J := J) (W := W) (C := 2)
  · norm_num
  · norm_num
  · exact hW
  · exact hJ
  · norm_num

end ArkLib.ProximityGap.Frontier.G81DepthTwoEnergySaddleBridge

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G81DepthTwoEnergySaddleBridge.orbit_budget_of_sq_le
#print axioms
  ArkLib.ProximityGap.Frontier.G81DepthTwoEnergySaddleBridge.sq_orbit_bound_of_energy
#print axioms
  ArkLib.ProximityGap.Frontier.G81DepthTwoEnergySaddleBridge.paddedDepthTwo_le_oddTailWick_of_sq_orbit_bound
#print axioms
  ArkLib.ProximityGap.Frontier.G81DepthTwoEnergySaddleBridge.paddedDepthTwo_le_oddTailWick_of_energy
#print axioms
  ArkLib.ProximityGap.Frontier.G81DepthTwoEnergySaddleBridge.production_depth_two_energy_absorbed
