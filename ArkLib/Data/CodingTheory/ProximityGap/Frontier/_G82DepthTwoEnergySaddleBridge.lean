/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G81FactorialPaddingWickAbsorption

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

open G81FactorialPaddingWickAbsorption
open G79PrimitivePaddingSaddleLocalization

/-- The deliberately unrestricted type of ordered depth-two core pairs has cardinality `n^4`.
No equal-sum, disjointness, primitivity, or orbit quotient is used. -/
theorem card_orderedDepthTwoCorePairs (A : Type*) [Fintype A] :
    Fintype.card ((Fin 2 → A) × (Fin 2 → A)) = (Fintype.card A) ^ 4 := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  ring

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

/-- **Corrected depth-two energy-to-Wick consumer.** G81 pays the independently ordered
padding factorial from the unused Wick head. G82 supplies its remaining orbit budget from a
`C*n^(3/2)` square estimate. -/
theorem correctedPaddedDepthTwo_le_fullWick_of_sq_orbit_bound
    {n r J W C : ℕ}
    (hrs : 4 ≤ r + 1)
    (hr : 2 ≤ r)
    (hW : W ≤ correctedPadEnvelope n r J 2)
    (hJ : J ^ 2 ≤ C ^ 2 * n ^ 3)
    (hsmall : C ^ 2 * r ^ 4 ≤ n) :
    W ≤ Nat.doubleFactorial (2 * r - 1) * n ^ r := by
  apply correctedPaddedSector_le_fullWick hrs hr hW
  exact orbit_budget_of_sq_le hJ hsmall

/-- End-to-end corrected consumer from an additive-energy-shaped estimate. -/
theorem correctedPaddedDepthTwo_le_fullWick_of_energy
    {n r J E W C : ℕ}
    (hn : 0 < n)
    (hrs : 4 ≤ r + 1)
    (hr : 2 ≤ r)
    (hW : W ≤ correctedPadEnvelope n r J 2)
    (hJE : n * J ≤ E)
    (hE : E ^ 2 ≤ C ^ 2 * n ^ 5)
    (hsmall : C ^ 2 * r ^ 4 ≤ n) :
    W ≤ Nat.doubleFactorial (2 * r - 1) * n ^ r := by
  apply correctedPaddedDepthTwo_le_fullWick_of_sq_orbit_bound hrs hr hW
  · exact sq_orbit_bound_of_energy hn hJE hE
  · exact hsmall

/-- **Exact depth-two budget.** Keeping the true two insertion factors and the true final two
odd Wick factors avoids the factor-four loss in `r^4` versus `r^2`. -/
theorem correctedPaddedDepthTwo_le_fullWick_of_exact_budget
    {n r J W : ℕ}
    (hr : 2 ≤ r)
    (hW : W ≤ correctedPadEnvelope n r J 2)
    (hJ : J * (r.descFactorial 2) ^ 2 ≤ oddWickTail r 2 * n ^ 2) :
    W ≤ Nat.doubleFactorial (2 * r - 1) * n ^ r := by
  have hfac := factorial_le_oddDoubleFactorial (r - 2)
  calc
    W ≤ correctedPadEnvelope n r J 2 := hW
    _ = (J * (r.descFactorial 2) ^ 2) * (r - 2).factorial * n ^ (r - 2) := by
      simp only [correctedPadEnvelope]
    _ ≤ (oddWickTail r 2 * n ^ 2) *
        Nat.doubleFactorial (2 * (r - 2) - 1) * n ^ (r - 2) := by gcongr
    _ = (oddWickTail r 2 * Nat.doubleFactorial (2 * (r - 2) - 1)) *
        (n ^ 2 * n ^ (r - 2)) := by ring
    _ = Nat.doubleFactorial (2 * r - 1) * n ^ r := by
      rw [← oddDoubleFactorial_split hr, ← pow_add, Nat.add_sub_of_le hr]

/-- A square-root orbit estimate supplies the exact depth-two budget without rounding the
insertion and Wick factors separately. -/
theorem exact_budget_of_sq_orbit_bound
    {n r J C : ℕ}
    (hJ : J ^ 2 ≤ C ^ 2 * n ^ 3)
    (hsmall : C ^ 2 * (r.descFactorial 2) ^ 4 ≤
      (oddWickTail r 2) ^ 2 * n) :
    J * (r.descFactorial 2) ^ 2 ≤ oddWickTail r 2 * n ^ 2 := by
  apply (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp
  calc
    (J * (r.descFactorial 2) ^ 2) ^ 2 =
        J ^ 2 * (r.descFactorial 2) ^ 4 := by ring
    _ ≤ (C ^ 2 * n ^ 3) * (r.descFactorial 2) ^ 4 := by gcongr
    _ = n ^ 3 * (C ^ 2 * (r.descFactorial 2) ^ 4) := by ring
    _ ≤ n ^ 3 * ((oddWickTail r 2) ^ 2 * n) := by gcongr
    _ = (oddWickTail r 2 * n ^ 2) ^ 2 := by ring

/-- Corrected full-Wick absorption from the exact-factor square-root orbit estimate. -/
theorem correctedPaddedDepthTwo_le_fullWick_of_exact_sq_orbit_bound
    {n r J W C : ℕ}
    (hr : 2 ≤ r)
    (hW : W ≤ correctedPadEnvelope n r J 2)
    (hJ : J ^ 2 ≤ C ^ 2 * n ^ 3)
    (hsmall : C ^ 2 * (r.descFactorial 2) ^ 4 ≤
      (oddWickTail r 2) ^ 2 * n) :
    W ≤ Nat.doubleFactorial (2 * r - 1) * n ^ r := by
  apply correctedPaddedDepthTwo_le_fullWick_of_exact_budget hr hW
  exact exact_budget_of_sq_orbit_bound hJ hsmall

/-- At `(n,r)=(2^30,110)`, the `C=2` energy-sized orbit hypothesis implies the exact
depth-two saddle budget required by the corrected padding consumer. -/
theorem production_depth_two_orbit_budget
    {J : ℕ}
    (hJ : J ^ 2 ≤ 2 ^ 2 * (2 ^ 30) ^ 3) :
    J * 110 ^ 2 ≤ (2 ^ 30) ^ 2 := by
  apply orbit_budget_of_sq_le hJ
  norm_num

/-- Production-scale corrected sector consumer with explicit energy constant `C=2`. -/
theorem production_corrected_depth_two_energy_absorbed
    {J E W : ℕ}
    (hW : W ≤ correctedPadEnvelope (2 ^ 30) 110 J 2)
    (hJE : (2 ^ 30) * J ≤ E)
    (hE : E ^ 2 ≤ 2 ^ 2 * (2 ^ 30) ^ 5) :
    W ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  apply correctedPaddedDepthTwo_le_fullWick_of_energy
      (n := 2 ^ 30) (r := 110) (J := J) (E := E) (W := W) (C := 2)
  · norm_num
  · norm_num
  · norm_num
  · exact hW
  · exact hJE
  · exact hE
  · norm_num

/-- **Sharp production calibration.** Keeping exact insertion/Wick factors raises the accepted
energy constant from `C=2` to `C=10`. -/
theorem production_corrected_depth_two_energy_absorbed_sharp
    {J E W : ℕ}
    (hW : W ≤ correctedPadEnvelope (2 ^ 30) 110 J 2)
    (hJE : (2 ^ 30) * J ≤ E)
    (hE : E ^ 2 ≤ 10 ^ 2 * (2 ^ 30) ^ 5) :
    W ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  apply correctedPaddedDepthTwo_le_fullWick_of_exact_sq_orbit_bound
      (n := 2 ^ 30) (r := 110) (J := J) (W := W) (C := 10)
  · norm_num
  · exact hW
  · exact sq_orbit_bound_of_energy (by norm_num) hJE hE
  · norm_num [oddWickTail]

/-- **All-core-pairs production calibration.** There are at most `n^4` ordered pairs of
depth-two words before imposing disjointness, equal sums, primitivity, or quotienting by
rotation. Even assigning one full factorial-corrected padding envelope to every such pair fits
inside the production Wick budget. This bypasses additive energy entirely at depth two. -/
theorem production_all_depth_two_core_pairs_le_fullWick :
    (2 ^ 30) ^ 4 * correctedPadEnvelope (2 ^ 30) 110 1 2 ≤
      Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  norm_num [correctedPadEnvelope, Nat.doubleFactorial]

/-- Any actual depth-two sector bounded by the deliberately overcounted universe of all
ordered core pairs is absorbed at production scale. -/
theorem production_all_depth_two_sector_absorbed
    {W : ℕ}
    (hW : W ≤ (2 ^ 30) ^ 4 * correctedPadEnvelope (2 ^ 30) 110 1 2) :
    W ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 :=
  hW.trans production_all_depth_two_core_pairs_le_fullWick

/-- **Sharp cutoff of the unrestricted-core method.** Repeating the same deliberately crude
overcount at primitive depth three exceeds the full production Wick budget. This does not refute
the actual depth-three sector, which is much smaller than the unrestricted `n^6` core universe;
it proves that depth three needs genuine equal-sum/energy structure. -/
theorem production_all_depth_three_core_pairs_exceed_fullWick :
    Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 <
      (2 ^ 30) ^ 6 * correctedPadEnvelope (2 ^ 30) 110 1 3 := by
  norm_num [correctedPadEnvelope, Nat.doubleFactorial]

end ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.card_orderedDepthTwoCorePairs
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.orbit_budget_of_sq_le
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.sq_orbit_bound_of_energy
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.correctedPaddedDepthTwo_le_fullWick_of_sq_orbit_bound
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.correctedPaddedDepthTwo_le_fullWick_of_energy
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.correctedPaddedDepthTwo_le_fullWick_of_exact_budget
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.exact_budget_of_sq_orbit_bound
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.correctedPaddedDepthTwo_le_fullWick_of_exact_sq_orbit_bound
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.production_depth_two_orbit_budget
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.production_corrected_depth_two_energy_absorbed
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.production_corrected_depth_two_energy_absorbed_sharp
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.production_all_depth_two_core_pairs_le_fullWick
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.production_all_depth_two_sector_absorbed
#print axioms
  ArkLib.ProximityGap.Frontier.G82DepthTwoEnergySaddleBridge.production_all_depth_three_core_pairs_exceed_fullWick
