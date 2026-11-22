/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

/-! # Prescribed equal evaluations of different ternary locator selections

Choose one site from each disjoint block consisting of an odd antipodal pair
and an even filler. Normalized evaluations on marked sites take values in a
finite group. Any collision leaves equal numbers of uncancelled numerator and
denominator factors and a nonzero signed imbalance at an odd pair.
-/

namespace ProximityGap.TernaryLocatorCollision

private theorem equal_of_balanced : ∀ a b : Fin 3,
    (if a = 0 then (1:ℤ) else 0) - (if b = 0 then 1 else 0)
    = (if a = 1 then 1 else 0) - (if b = 1 then 1 else 0) → a = b := by decide

/-- A collision of normalized evaluation vectors gives a constant ratio using
only the coordinates that survive cancellation. At some block the signed
indicators distinguish its two antipodal sites. The group may itself be a product. -/
theorem prescribed_collision {G : Type*} [CommGroup G] [Fintype G] (m t : ℕ)
    (U : Fin m → Fin 3 → Option (Fin t) → G) (h : (Fintype.card G)^t < 3^m) :
    ∃ a b : Fin m → Fin 3, ∃ c : G,
      (∃ j, (if a j = 0 then (1:ℤ) else 0) - (if b j = 0 then 1 else 0)
        ≠ (if a j = 1 then 1 else 0) - (if b j = 1 then 1 else 0)) ∧
      ∀ x, (∏ j ∈ Finset.univ.filter (fun j ↦ a j ≠ b j), U j (a j) x / U j (b j) x) = c := by
  classical
  let L (a : Fin m → Fin 3) (x : Option (Fin t)) := ∏ j, U j (a j) x
  let v (a : Fin m → Fin 3) (x : Fin t) := L a (some x) / L a none
  obtain ⟨a,b,hab,he⟩ := Fintype.exists_ne_map_eq_of_card_lt v (by simpa using h)
  refine ⟨a,b,L a none / L b none,?_,?_⟩
  · by_contra! hn
    exact hab (funext fun j ↦ equal_of_balanced (a j) (b j) (hn j))
  · intro x
    have hL : L a x / L b x = L a none / L b none := by
      cases x with
      | none => rfl
      | some x =>
        have hx : L a (some x) / L a none = L b (some x) / L b none := congrFun he x
        apply div_eq_div_iff_mul_eq_mul.mpr
        simpa only [mul_comm] using div_eq_div_iff_mul_eq_mul.mp hx
    rw [← hL, Finset.prod_filter]
    unfold L
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j _
    split_ifs with hj
    · rfl
    · rw [not_ne_iff.mp hj, div_self']

private theorem of_block (q e m b r : ℕ) (he : 0 < e)
    (h : q^b < 3^r) (hw : r*e ≤ m*b) : q^e < 3^m := by
  by_contra! hn
  have heq : (q^e)^b = (q^b)^e := by rw [← pow_mul, ← pow_mul, Nat.mul_comm e b]
  have ht : (3^m)^b < (3^m)^b := calc
    (3^m)^b ≤ (q^e)^b := Nat.pow_le_pow_left hn _
    _ = (q^b)^e := heq
    _ < (3^r)^e := Nat.pow_lt_pow_left h (by omega)
    _ ≤ (3^m)^b := by simpa only [← pow_mul] using Nat.pow_le_pow_right (by decide : 0<3) hw
  exact (lt_irrefl _) ht

/-- First named field, with 2,692,786 prescribed evaluation sites including the base. -/
theorem first_count :
    365375409332725729550921208179070755120141565952^2692785 < 3^268435456 :=
  of_block _ _ _ 214 21333 (by decide) (by decide +kernel) (by decide)

/-- Second named field, with 2,675,850 prescribed evaluation sites including the base. -/
theorem second_count :
    730750818665451459101842416358141509841924915200^2675849 < 3^268435456 :=
  of_block _ _ _ 280 28089 (by decide) (by decide +kernel) (by decide)

/-- Simultaneous collision for both named fields at 1,342,146 prescribed sites. -/
theorem joint_count :
    (365375409332725729550921208179070755120141565952 *
      730750818665451459101842416358141509841924915200)^1342145 < 3^268435456 :=
  of_block _ _ _ 208 41601 (by decide) (by decide +kernel) (by decide)

/-- The named one-field three-site obstruction already occurs on 1,024 roots. -/
theorem small_count : 730750818665451459101842416358141509841924915200^2 < 3^256 := by decide

#print axioms prescribed_collision
#print axioms first_count
#print axioms second_count
#print axioms joint_count
#print axioms small_count

end ProximityGap.TernaryLocatorCollision
