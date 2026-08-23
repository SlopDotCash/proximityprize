/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G81FactorialPaddingWickAbsorption

/-!
# G91: unordered primitive cores plus fixed-depth HBK energy absorb depth five

G83 shows that the elementary ordered-core universe first misses the production Wick budget at
primitive depth five.  The miss is only a constant at the fixed production saddle, while the
current decoder counts two independent orderings of each primitive core.

For a full-support depth-five core, replacing each ordered core by its multiset removes exactly
`(5!)² = 14400` labels; the free subgroup action removes a further factor `n`.  The remaining
analytic input is fixed-depth, not logarithmic-depth: the standard convolution inequality
`E₅(G) ≤ n⁶ E₂(G)` and the Heath-Brown--Konyagin estimate `E₂(G)² ≤ C n⁵` give
`E₅(G)² ≤ C n¹⁷`.  This file proves the production arithmetic consumer with a very generous
`C ≤ 2²⁰`.

The two hypotheses are left explicit:

* `14400*n*J ≤ E₅` is the unordered-core/free-orbit encoding. Repeated-coordinate strata must be
  assigned to their lower-support sectors rather than divided by `5!`.
* `E₅² ≤ C*n¹⁷` is the fixed-depth energy transport from the cited HBK input.

Thus this is not a prize closure. It identifies a new binding inequality which changes G83's
negative depth-five arithmetic: once internal endpoint order is not double-counted, a classical
fixed-depth energy theorem has more than ten bits of constant headroom and the whole depth-five
sector fits. The deep growing-depth primitive-core union remains open. Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G91DepthFiveUnorderedHBKBridge

open G81FactorialPaddingWickAbsorption

/-- The two independent orderings of full-support depth-five cores contribute `(5!)²`. -/
theorem depthFive_internal_order_factor : ((5 : ℕ).factorial : ℕ) ^ 2 = 14400 := by
  norm_num

/-- The elementary fixed-depth transport used by the consumer.  Fixing the three extra
coordinates on each side gives `E₅ ≤ n⁶ E₂`; squaring and inserting HBK's
`E₂² ≤ C n⁵` gives `E₅² ≤ C n¹⁷`. -/
theorem fifthEnergy_sq_le_of_secondEnergy
    {n E₂ E₅ C : ℕ}
    (hfive : E₅ ≤ n ^ 6 * E₂)
    (hsecond : E₂ ^ 2 ≤ C * n ^ 5) :
    E₅ ^ 2 ≤ C * n ^ 17 := by
  calc
    E₅ ^ 2 ≤ (n ^ 6 * E₂) ^ 2 := Nat.pow_le_pow_left hfive 2
    _ = n ^ 12 * E₂ ^ 2 := by ring
    _ ≤ n ^ 12 * (C * n ^ 5) := Nat.mul_le_mul_left _ hsecond
    _ = C * n ^ 17 := by ring

/-- **Production depth-five consumer.**  The factorial-corrected padding sector is absorbed once
its primitive core classes inject into fifth energy after removing the free scaling orbit and the
two redundant internal core orders, and the fixed fifth energy obeys the HBK-transport scale.

`C ≤ 2²⁰` means the unsquared fifth-energy constant may be as large as `2¹⁰`; this is deliberately
far looser than published fixed-depth subgroup-energy constants. -/
theorem production_depth_five_unordered_hbk_absorbed
    {J E₅ W C : ℕ}
    (hW : W ≤ correctedPadEnvelope (2 ^ 30) 110 J 5)
    (hencode : 14400 * (2 ^ 30) * J ≤ E₅)
    (henergy : E₅ ^ 2 ≤ C * (2 ^ 30) ^ 17)
    (hC : C ≤ 2 ^ 20) :
    W ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  let A : ℕ := correctedPadEnvelope (2 ^ 30) 110 1 5
  let T : ℕ := Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110
  have hencode_sq : (14400 * (2 ^ 30) * J) ^ 2 ≤ E₅ ^ 2 :=
    Nat.pow_le_pow_left hencode 2
  have hnumeric :
      (2 ^ 20) * (2 ^ 30) ^ 17 * A ^ 2 ≤ (14400 * (2 ^ 30) * T) ^ 2 := by
    norm_num [A, T, correctedPadEnvelope, Nat.doubleFactorial, Nat.descFactorial]
  have hscaled_sq : (14400 * (2 ^ 30) * (J * A)) ^ 2 ≤
      (14400 * (2 ^ 30) * T) ^ 2 := by
    calc
      (14400 * (2 ^ 30) * (J * A)) ^ 2 =
          (14400 * (2 ^ 30) * J) ^ 2 * A ^ 2 := by ring
      _ ≤ E₅ ^ 2 * A ^ 2 := Nat.mul_le_mul_right _ hencode_sq
      _ ≤ (C * (2 ^ 30) ^ 17) * A ^ 2 := Nat.mul_le_mul_right _ henergy
      _ ≤ ((2 ^ 20) * (2 ^ 30) ^ 17) * A ^ 2 := by gcongr
      _ ≤ (14400 * (2 ^ 30) * T) ^ 2 := hnumeric
  have hscaled : 14400 * (2 ^ 30) * (J * A) ≤ 14400 * (2 ^ 30) * T :=
    (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hscaled_sq
  have hJA : J * A ≤ T := by
    exact Nat.le_of_mul_le_mul_left hscaled (by positivity)
  calc
    W ≤ correctedPadEnvelope (2 ^ 30) 110 J 5 := hW
    _ = J * A := by
      simp only [correctedPadEnvelope, A]
      ring
    _ ≤ T := hJA
    _ = Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := rfl

/-- End-to-end arithmetic composition from a second-energy HBK estimate and the elementary
fixed-depth transport.  No logarithmic-depth moment hypothesis appears. -/
theorem production_depth_five_unordered_of_secondEnergy
    {J E₂ E₅ W C : ℕ}
    (hW : W ≤ correctedPadEnvelope (2 ^ 30) 110 J 5)
    (hencode : 14400 * (2 ^ 30) * J ≤ E₅)
    (hfive : E₅ ≤ (2 ^ 30) ^ 6 * E₂)
    (hsecond : E₂ ^ 2 ≤ C * (2 ^ 30) ^ 5)
    (hC : C ≤ 2 ^ 20) :
    W ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  apply production_depth_five_unordered_hbk_absorbed hW hencode _ hC
  exact fifthEnergy_sq_le_of_secondEnergy hfive hsecond

end ArkLib.ProximityGap.Frontier.G91DepthFiveUnorderedHBKBridge

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G91DepthFiveUnorderedHBKBridge.depthFive_internal_order_factor
#print axioms
  ArkLib.ProximityGap.Frontier.G91DepthFiveUnorderedHBKBridge.fifthEnergy_sq_le_of_secondEnergy
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.G91DepthFiveUnorderedHBKBridge.production_depth_five_unordered_hbk_absorbed
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.G91DepthFiveUnorderedHBKBridge.production_depth_five_unordered_of_secondEnergy
