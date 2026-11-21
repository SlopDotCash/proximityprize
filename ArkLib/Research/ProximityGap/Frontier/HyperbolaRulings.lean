/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PlanarQuartetMass
import Mathlib.GroupTheory.OrderOfElement

/-! # Six polynomial heads on the sixteen power fibers of a smooth coset -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.HyperbolaRulings
open Polynomial

/-- The owner at each of the nine pair fibers and seven remaining fibers. -/
def owner : Fin 16 → Fin 6 := ![0,1,2,0,1,2,0,1,2,0,0,0,0,0,0,0]
/-- All heads equal to the owner at that fiber. -/
def group : Fin 16 → Finset (Fin 6) :=
  ![{0,3},{1,3},{2,3},{0,4},{1,4},{2,4},{0,5},{1,5},{2,5},{0},{0},{0},{0},{0},{0},{0}]

private def linear (i : Fin 6) (second : Bool) :=
  if second then decide (i.val < 3) else decide (3 ≤ i.val)
private def shift (i : Fin 6) (second : Bool) : ℕ :=
  if second then (![0,15,14,0,3,6] : Fin 6 → ℕ) i else (![0,1,2,0,13,10] : Fin 6 → ℕ) i
private def exponent (i : Fin 6) (r : Fin 16) (second : Bool) : ℕ :=
  (shift i second + if linear i second then r.val else 0) % 16

variable {F : Type} [Field F]

/-- Either coordinate of the hyperbola point at a quotient fiber. -/
def value (w : F) (second : Bool) (i : Fin 6) (r : Fin 16) : F := w ^ exponent i r second

/-- Polynomial realizing a coordinate after scaling by the inverse coset representative. -/
noncomputable def poly (s : ℕ) (w u : F) (second : Bool) (i : Fin 6) : F[X] :=
  C (w ^ shift i second) * (if linear i second then (C u * X)^s else 1)

theorem degree (s : ℕ) (w u : F) (second : Bool) (i : Fin 6) :
    (poly s w u second i).natDegree ≤ s := by
  apply (natDegree_C_mul_le ..).trans
  split
  · simpa using (natDegree_pow_le.trans (Nat.mul_le_mul_left s
      ((natDegree_C_mul_le u (X : F[X])).trans natDegree_X_le)))
  · simp

theorem eval (s : ℕ) {w u x : F} (hw : orderOf w = 16) (second : Bool) (i : Fin 6) (r : Fin 16)
    (hr : (u*x)^s = w^r.val) : (poly s w u second i).eval x = value w second i r := by
  have red (n : ℕ) : w ^ (n % 16) = w ^ n := by simpa only [hw] using pow_mod_orderOf w n
  rw [poly, eval_mul, eval_C, value, exponent, red, pow_add]
  split <;> simp_all

private theorem injective_exponents {w : F} (h : orderOf w = 16) {i j : ℕ}
    (hi : i < 16) (hj : j < 16) (eq : w^i = w^j) : i = j :=
  pow_injOn_Iio_orderOf (h.symm ▸ hi) (h.symm ▸ hj) eq

theorem agrees (w : F) (r : Fin 16) (i : Fin 6) (h : i ∈ group r) :
    value w false i r = value w false (owner r) r ∧
      value w true i r = value w true (owner r) r := by
  have same : ∀ r i, i ∈ group r → ∀ c, exponent i r c = exponent (owner r) r c := by decide
  exact ⟨congrArg (w ^ ·) (same r i h false), congrArg (w ^ ·) (same r i h true)⟩

private theorem distinct {w : F} (hw : orderOf w = 16) {r : Fin 16} {i j : Fin 6}
    (hne : exponent i r true ≠ exponent j r true) : value w true i r ≠ value w true j r := by
  exact fun eq => hne (injective_exponents hw (Nat.mod_lt _ (by decide : 0 < 16))
    (Nat.mod_lt _ (by decide : 0 < 16)) eq)

theorem misses {w : F} (hw : orderOf w = 16) (r : Fin 16) (i : Fin 6) (h : i ∉ group r) :
    value w true i r ≠ value w true (owner r) r := by
  have diff : ∀ r i, i ∉ group r → exponent i r true ≠ exponent (owner r) r true := by decide
  exact distinct hw (diff r i h)

private theorem product {w : F} (hw : orderOf w = 16) (r : Fin 16) (i : Fin 6) :
    value w false i r * value w true i r = w^r.val := by
  have total : ∀ i r, (exponent i r false + exponent i r true) % 16 = r.val := by decide
  rw [value, value, ← pow_add, ← pow_mod_orderOf w (exponent i r false + exponent i r true), hw, total]

/-- Secants from one point of a nonzero hyperbola to two distinct foreign points have
different slopes. This is uniform in the field characteristic. -/
theorem separated {w : F} (hw : orderOf w = 16) (r : Fin 16) (i j : Fin 6)
    (hi : i ∉ group r) (hj : j ∉ group r) (ne : i ≠ j) :
    (value w false (owner r) r - value w false i r) *
        (value w true j r - value w true (owner r) r) ≠
      (value w false (owner r) r - value w false j r) *
        (value w true i r - value w true (owner r) r) := by
  have table : ∀ r i j, i ∉ group r → j ∉ group r → i ≠ j →
      exponent i r true ≠ exponent j r true := by decide
  let x := value w false (owner r) r
  let a := value w true (owner r) r
  let b := value w true i r
  let c := value w true j r
  have pi : (x - value w false i r) * b = x * (b-a) := by
    dsimp [x,a,b]
    linear_combination product hw r (owner r) - product hw r i
  have pj : (x - value w false j r) * c = x * (c-a) := by
    dsimp [x,a,c]
    linear_combination product hw r (owner r) - product hw r j
  have wn : w ≠ 0 := by intro h; subst w; simp at hw
  have xn : x ≠ 0 := pow_ne_zero _ wn
  have bn : b-a ≠ 0 := sub_ne_zero.mpr (misses hw r i hi)
  have cn : c-a ≠ 0 := sub_ne_zero.mpr (misses hw r j hj)
  have cb : c-b ≠ 0 := sub_ne_zero.mpr (distinct hw (table r i j hi hj ne)).symm
  intro equality
  change (x - _) * (c-a) = (x - _) * (b-a) at equality
  have eq : (x - value w false i r) * b * (c - a) * c =
      (x - value w false j r) * c * (b - a) * b := by linear_combination b*c*equality
  rw [pi, pj] at eq
  apply (mul_ne_zero (mul_ne_zero (mul_ne_zero xn bn) cn) cb)
  linear_combination eq

end ArkLib.ProximityGap.Frontier.HyperbolaRulings
