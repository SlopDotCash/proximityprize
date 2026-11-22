/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic

/-! # Reflection from two equal symmetric translates -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.DyadicTwoCenterReflection

/-- Equal symmetric translates at two centers force reflection when a multiple
of their difference is an antiperiod. -/
theorem reflection {G : Type*} [AddCommGroup G] (v : G → ℤ) (x y h : G) (k : ℕ)
    (hk : k • (y - x) = h) (hanti : ∀ a, v (a + h) = -v a)
    (hs : ∀ i, v (x + i) + v (x - i) = v (y + i) + v (y - i)) (a : G) :
    v a = v (x + y - a) := by
  let D (j : G) := v j - v (x + y - j)
  have step (j : G) : D (j + (y - x)) = D j := by
    have t := hs (j - x)
    rw [show x + (j - x) = j by abel, show y + (j - x) = j + (y - x) by abel,
      show y - (j - x) = x + y - j by abel,
      show x - (j - x) = x + y - (j + (y - x)) by abel] at t
    dsimp [D]
    omega
  have steps (m : ℕ) : D (a + m • (y - x)) = D a := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [succ_nsmul, ← add_assoc, step, ih]
  have per := steps k
  rw [hk] at per
  have left := hanti a
  have right := hanti (x + y - (a + h))
  rw [show x + y - (a + h) + h = x + y - a by abel] at right
  dsimp [D] at per
  omega

/-- Every nonzero displacement in the order-32 group reaches the antipode. -/
theorem reaches_half : ∀ u : ZMod 32, u ≠ 0 → ∃ k : Fin 32, k.val • u = 16 := by
  decide

#print axioms reflection
#print axioms reaches_half

end ArkLib.ProximityGap.Frontier.DyadicTwoCenterReflection
