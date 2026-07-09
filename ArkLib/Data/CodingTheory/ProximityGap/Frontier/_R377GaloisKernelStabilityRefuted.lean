import Mathlib

/-!
# R377: Galois exponent multipliers do not preserve a fixed shadow kernel

R371--R372 prove that exponent translation preserves a fixed finite-field relation:
it multiplies both sides by the same subgroup element. A tempting strengthening is to
use all odd exponent multipliers and gain a second orbit factor `phi(n)`. This is false.
The multiplier is a Galois automorphism of the characteristic-zero cyclotomic field, but
in characteristic `p` it moves the chosen prime ideal; it need not preserve addition at
the fixed evaluation root.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R377GaloisKernelStabilityRefuted

/-- `2` has order dividing eight in `F_17`; this is the smallest useful smooth cell. -/
theorem two_pow_eight_mod_seventeen : (2 : ZMod 17) ^ 8 = 1 := by decide

/-- A genuine two-sum relation at the fixed order-eight root `g=2`. -/
theorem base_relation :
    (2 : ZMod 17) ^ 1 + 2 ^ 3 = 2 ^ 0 + 2 ^ 7 := by decide

/-- Multiplication of every exponent by the unit `3 mod 8` does not preserve the relation. -/
theorem odd_multiplier_three_breaks_relation :
    (2 : ZMod 17) ^ ((3 * 1) % 8) + 2 ^ ((3 * 3) % 8) ≠
      2 ^ ((3 * 0) % 8) + 2 ^ ((3 * 7) % 8) := by decide

/-- The original vanishing relation and failure of its odd-multiplier image. -/
theorem fixed_kernel_not_galois_stable :
    ((2 : ZMod 17) ^ 1 + 2 ^ 3 - 2 ^ 0 - 2 ^ 7 = 0) ∧
    ((2 : ZMod 17) ^ ((3 * 1) % 8) + 2 ^ ((3 * 3) % 8) -
      2 ^ ((3 * 0) % 8) - 2 ^ ((3 * 7) % 8) ≠ 0) := by
  constructor <;> decide

end ArkLib.ProximityGap.Frontier.R377GaloisKernelStabilityRefuted

#print axioms
  ArkLib.ProximityGap.Frontier.R377GaloisKernelStabilityRefuted.fixed_kernel_not_galois_stable
