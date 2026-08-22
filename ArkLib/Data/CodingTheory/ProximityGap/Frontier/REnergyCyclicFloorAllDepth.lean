/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharPMomentRecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergyThreeCyclicFloor

/-!
# The cyclic additive-energy floor at every depth (#1)

`REnergyThreeCyclicFloor.rEnergy_three_ge_cyclic_floor` proves

`3 * |G| ^ 3 - 2 * |G| ≤ rEnergy G 3`

by counting the cyclic rotations of a triple. This file lifts that result to every higher depth.
The exact recursion `CharPMomentRecursion.rEnergy_succ` has a nonnegative cross term, so appending
one common coordinate to the two sides gives

`|G| * rEnergy G r ≤ rEnergy G (r + 1)`.

Iterating this inequality supplies a reusable depth-lifting theorem and the closed-form bound

> **`rEnergy_ge_cyclic_floor_all_depth`.**
> `3 * |G| ^ (m + 3) - 2 * |G| ^ (m + 1) ≤ rEnergy G (m + 3)`.

For `|G| ≥ 2`, this is strictly stronger than the all-depth adjacent-swap floor. The proof is
pure finite counting over an arbitrary finite field. It does not assert an upper energy bound,
CORE closure, characteristic transfer, capacity, or a value of delta star.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Appending one common coordinate to both tuples lifts every collision at depth `r`, giving
`|G| * rEnergy G r ≤ rEnergy G (r + 1)`. -/
theorem card_mul_rEnergy_le_succ (G : Finset F) (r : ℕ) :
    G.card * rEnergy G r ≤ rEnergy G (r + 1) := by
  rw [ArkLib.ProximityGap.CharPMomentRecursion.rEnergy_succ]
  exact Nat.le_add_right _ _

/-- Iterated common-coordinate lifting: every depth-`r` collision and every common tail of length
`m` give a collision at depth `r + m`. -/
theorem card_pow_mul_rEnergy_le_add (G : Finset F) (r m : ℕ) :
    G.card ^ m * rEnergy G r ≤ rEnergy G (r + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        G.card ^ (m + 1) * rEnergy G r =
            G.card * (G.card ^ m * rEnergy G r) := by
          rw [pow_succ]
          ring
        _ ≤ G.card * rEnergy G (r + m) := Nat.mul_le_mul_left _ ih
        _ ≤ rEnergy G ((r + m) + 1) := card_mul_rEnergy_le_succ G (r + m)
        _ = rEnergy G (r + (m + 1)) := by rw [Nat.add_assoc]

private theorem mul_swap_floor_eq (n m : ℕ) :
    n ^ m * (2 * n ^ 3 - n ^ 2) = 2 * n ^ (m + 3) - n ^ (m + 2) := by
  rw [Nat.mul_sub_left_distrib]
  simp only [pow_add]
  ring

private theorem mul_cyclic_floor_eq (n m : ℕ) :
    n ^ m * (3 * n ^ 3 - 2 * n) = 3 * n ^ (m + 3) - 2 * n ^ (m + 1) := by
  rw [Nat.mul_sub_left_distrib]
  simp only [pow_add]
  ring

/-- **The universal cyclic floor at every depth at least three.** The depth-three cyclic-orbit
bound lifts through an arbitrary common tail of length `m`. -/
theorem rEnergy_ge_cyclic_floor_all_depth (G : Finset F) (m : ℕ) :
    3 * G.card ^ (m + 3) - 2 * G.card ^ (m + 1) ≤ rEnergy G (m + 3) := by
  calc
    3 * G.card ^ (m + 3) - 2 * G.card ^ (m + 1) =
        G.card ^ m * (3 * G.card ^ 3 - 2 * G.card) :=
      (mul_cyclic_floor_eq G.card m).symm
    _ ≤ G.card ^ m * rEnergy G 3 :=
      Nat.mul_le_mul_left _ (rEnergy_three_ge_cyclic_floor G)
    _ ≤ rEnergy G (3 + m) := card_pow_mul_rEnergy_le_add G 3 m
    _ = rEnergy G (m + 3) := by rw [Nat.add_comm]

/-- The all-depth cyclic floor dominates the adjacent-swap floor. -/
theorem swap_floor_le_cyclic_floor_all_depth (n m : ℕ) :
    2 * n ^ (m + 3) - n ^ (m + 2) ≤ 3 * n ^ (m + 3) - 2 * n ^ (m + 1) := by
  calc
    2 * n ^ (m + 3) - n ^ (m + 2) = n ^ m * (2 * n ^ 3 - n ^ 2) :=
      (mul_swap_floor_eq n m).symm
    _ ≤ n ^ m * (3 * n ^ 3 - 2 * n) :=
      Nat.mul_le_mul_left _ (swap_floor_le_cyclic_floor_three n)
    _ = 3 * n ^ (m + 3) - 2 * n ^ (m + 1) := mul_cyclic_floor_eq n m

/-- For every nontrivial support size, the all-depth cyclic floor is strictly stronger than the
adjacent-swap floor. -/
theorem swap_floor_lt_cyclic_floor_all_depth_of_two_le {n : ℕ} (m : ℕ) (hn : 2 ≤ n) :
    2 * n ^ (m + 3) - n ^ (m + 2) < 3 * n ^ (m + 3) - 2 * n ^ (m + 1) := by
  have hpow : 0 < n ^ m := pow_pos (by omega) m
  calc
    2 * n ^ (m + 3) - n ^ (m + 2) = n ^ m * (2 * n ^ 3 - n ^ 2) :=
      (mul_swap_floor_eq n m).symm
    _ < n ^ m * (3 * n ^ 3 - 2 * n) :=
      Nat.mul_lt_mul_of_pos_left (swap_floor_lt_cyclic_floor_three_of_two_le hn) hpow
    _ = 3 * n ^ (m + 3) - 2 * n ^ (m + 1) := mul_cyclic_floor_eq n m

end ArkLib.ProximityGap.SubgroupGaussSumMoment

-- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.card_mul_rEnergy_le_succ
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.card_pow_mul_rEnergy_le_add
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_ge_cyclic_floor_all_depth
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.swap_floor_le_cyclic_floor_all_depth
#print axioms
  ArkLib.ProximityGap.SubgroupGaussSumMoment.swap_floor_lt_cyclic_floor_all_depth_of_two_le
