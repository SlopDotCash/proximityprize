/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second
import Mathlib.Tactic.FinCases

/-!
# Distinct scalar directions for three affine Reed–Solomon heads

On the second prize field the three cosets with representatives `-1, -2, -3` are
disjoint. At the remaining coordinate the received pair `(8,3)` supplies three
additional directions outside those cosets. Raising a direction to the domain
length tests coset membership. These computations use ordinary kernel reduction.
-/

namespace ArkLib.ProximityGap.Frontier.ThreeCoreSecondPrimeArithmetic

open ArkLib.ProximityGap.PrizeShapePrimeP30Second
open ArkLib.ProximityGap.BinaryPower

local instance : Fact P.Prime := ⟨prime_P⟩

/-- The three ordinary direction cosets have different powers. -/
theorem scale_injective : Function.Injective
    (fun c : Fin 3 => (-((c.val + 1 : ℕ) : ZMod P)) ^ (2 ^ 30 : ℕ)) := by
  simp only [Function.Injective, ← binaryPow_eq_pow]
  decide

private def label (i : Fin 3) : ZMod P :=
  if i.val = 0 then 487167212443634306067894944238761006561283276798
  else if i.val = 1 then 365375409332725729550921208179070754920962457597
  else 730750818665451459101842416358141509841924915197

private theorem ratio_eq_label (i : Fin 3) :
    (((i.val : ZMod P) ^ 2) - 8) / (3 - (i.val : ZMod P)) = label i := by
  have hd : (3 : ZMod P) - (i.val : ZMod P) ≠ 0 := by fin_cases i <;> decide
  apply (div_eq_iff hd).2
  fin_cases i <;> decide

/-- The three exceptional directions at the identity are different. -/
theorem exceptional_injective : Function.Injective
    (fun i : Fin 3 => (((i.val : ZMod P) ^ 2) - 8) / (3 - (i.val : ZMod P))) := by
  simp only [Function.Injective, ratio_eq_label]
  decide

/-- None of the exceptional directions belongs to an ordinary coset. -/
theorem exceptional_separation (c i : Fin 3) :
    (-((c.val + 1 : ℕ) : ZMod P)) ^ (2 ^ 30 : ℕ) ≠
    ((((i.val : ZMod P) ^ 2) - 8) / (3 - (i.val : ZMod P))) ^ (2 ^ 30 : ℕ) := by
  rw [ratio_eq_label]
  simp only [← binaryPow_eq_pow]
  fin_cases c <;> fin_cases i <;> decide

end ArkLib.ProximityGap.Frontier.ThreeCoreSecondPrimeArithmetic

#print axioms ArkLib.ProximityGap.Frontier.ThreeCoreSecondPrimeArithmetic.scale_injective
#print axioms ArkLib.ProximityGap.Frontier.ThreeCoreSecondPrimeArithmetic.exceptional_injective
#print axioms ArkLib.ProximityGap.Frontier.ThreeCoreSecondPrimeArithmetic.exceptional_separation
