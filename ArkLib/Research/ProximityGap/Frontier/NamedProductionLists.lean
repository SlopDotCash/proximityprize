/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoAnchorListWitness
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-! # Actual over-budget lists at all four nominated production rates -/

namespace ProximityGap.NamedProductionLists

open Code ReservedFiberList TwoAnchorListWitness
variable {F : Type} [Field F] [Fintype F]

/-- Canonical closed-list failure count on the full order-2³⁰ cyclic domain. -/
def Fails {r h : ℕ} (g : Fˣ) (hg : orderOf g = h*r) (b e width B : ℕ) : Prop :=
 (B : ℕ∞) < Lambda (interleavedCodeSet (κ := Fin width)
   (ReedSolomon.code (cyclicDomain g hg) (b*h) : Set (Fin r × Fin h → F)))
   ((e : ℝ)/(r*h : ℕ))

/-- Four actual over-budget balls on the same full subgroup, in decreasing rate
order. Coordinates are grouped by their 64 or 128 quotient fibers. -/
def FourFailures (g : Fˣ) (hg : orderOf g = 2^30) (width B : ℕ) : Prop :=
 Fails (r:=64) (h:=16777216) g hg 32 503316481 width B ∧
 Fails (r:=64) (h:=16777216) g hg 16 771751937 width B ∧
 Fails (r:=128) (h:=8388608) g hg 16 922746881 width B ∧
 Fails (r:=128) (h:=8388608) g hg 8 989855745 width B

/-- Every finite field with this subgroup supports the four failures until the
smallest of the four certified list populations is exhausted. -/
theorem four_failures (g : Fˣ) (hg : orderOf g = 2^30) (width : ℕ) (hw : 0 < width)
    (B : ℕ) (hB : B ≤ 128644068888) : FourFailures g hg width B := by
  have count (r b : ℕ) (hh : r * 128644068888 < (r - 2).choose (b+1)) :
      r*B < (r-2).choose (b+1) := (Nat.mul_le_mul_left r hB).trans_lt hh
  exact ⟨cyclic_exceeds (r:=64) (h:=16777216) (b:=32) (by decide) (by decide) (by decide)
      g hg (count _ _ (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide)) width hw,
    cyclic_exceeds (r:=64) (h:=16777216) (b:=16) (by decide) (by decide) (by decide)
      g hg (count _ _ (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide)) width hw,
    cyclic_exceeds (r:=128) (h:=8388608) (b:=16) (by decide) (by decide) (by decide)
      g hg (count _ _ (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide)) width hw,
    cyclic_exceeds (r:=128) (h:=8388608) (b:=8) (by decide) (by decide) (by decide)
      g hg (count _ _ (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide)) width hw⟩

namespace First
open ArkLib.ProximityGap.PrizeShapePrimeP30
local instance : Fact P.Prime := ⟨prime_P⟩
/-- The designated generator presented as a unit of the first prime field. -/
def generator : (ZMod P)ˣ := Units.mk0 g (by decide)
theorem order : orderOf generator = 2^30 := by rw [← orderOf_units]; exact orderOf_g
/-- The first designated field at its actual 128-bit list budget. -/
theorem failures (width : ℕ) (hw : 0 < width) : FourFailures generator order width (P/2^128) :=
  four_failures generator order width hw _ (by decide)
end First

namespace Second
open ArkLib.ProximityGap.PrizeShapePrimeP30Second
local instance : Fact P.Prime := ⟨prime_P⟩
/-- The designated generator presented as a unit of the second prime field. -/
def generator : (ZMod P)ˣ := Units.mk0 g (by decide)
theorem order : orderOf generator = 2^30 := by rw [← orderOf_units]; exact orderOf_g
/-- The second designated field at its actual 128-bit list budget. -/
theorem failures (width : ℕ) (hw : 0 < width) : FourFailures generator order width (P/2^128) :=
  four_failures generator order width hw _ (by decide)
end Second

#print axioms four_failures
#print axioms First.failures
#print axioms Second.failures
end ProximityGap.NamedProductionLists
