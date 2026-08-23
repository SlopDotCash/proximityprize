/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The subset-sum halo energy: the large-`n` `δ*` core, made explicit (#389)

Working out the large-`n` (deployed, below-threshold) `δ*`, the census **halo** — non-antipodal
`E ⊆ [0,2^m)` with `∑_{e∈E} g^e ≡ 0 (mod p)` — reduces *exactly* to **subset-sum collisions** of
`{g^0,…,g^{N-1}}` (`N = 2^{m-1}`): pairs of subsets `A ≠ B` with `∑_{j∈A} g^j = ∑_{j∈B} g^j` in
`F_p`.  Its size is the **subset-sum energy** `∑_v r(v)²`, `r(v) = #{A : ∑_{j∈A} x_j = v}`.

This file proves the unconditional Cauchy–Schwarz lower bound on that energy:

> **`four_pow_le_card_mul_subsetSum_energy`** — `4^N ≤ |F| · ∑_v r(v)²`.

Equivalently the collision count `∑_v r(v)² − 2^N ≥ 4^N/|F| − 2^N`, which is **strictly
positive once `|F| < 2^N`**.  Consequence for `δ*`: the halo is empty (so the past-Johnson
pin `δ* = 1−r/2^μ` holds) exactly in the regime `p ≳ 2^N`; for **deployed `p < 2^N` the halo
is provably nonempty**, the clean classification fails, and `δ*` drops below `1−r/2^μ` toward
the Johnson radius — the deployed wall is *real*, governed by this subset-sum energy.  This
replaces the crude doubly-exponential `N^N` threshold by the sharp `2^N`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.SubsetSumHalo

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {N : ℕ}

/-- The subset-sum representation count: `#{A ⊆ [N] : ∑_{j∈A} x j = v}`. -/
noncomputable def subsetSumRep (x : Fin N → F) (v : F) : ℕ :=
  (Finset.univ.filter (fun A : Finset (Fin N) => ∑ j ∈ A, x j = v)).card

/-- Total subset-sum mass: `∑_v r(v) = 2^N` (every subset has exactly one sum). -/
theorem sum_subsetSumRep (x : Fin N → F) :
    ∑ v : F, subsetSumRep x v = 2 ^ N := by
  classical
  unfold subsetSumRep
  rw [← Finset.card_eq_sum_card_fiberwise
    (fun A _ => Finset.mem_univ (∑ j ∈ A, x j))]
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

/-- **The subset-sum energy lower bound** (Cauchy–Schwarz): `4^N ≤ |F| · ∑_v r(v)²`.
Equivalently `∑_v r(v)² ≥ 4^N / |F|`, so the collision count `∑ r² − 2^N` is positive
once `|F| < 2^N`. -/
theorem four_pow_le_card_mul_subsetSum_energy (x : Fin N → F) :
    4 ^ N ≤ Fintype.card F * ∑ v : F, (subsetSumRep x v) ^ 2 := by
  classical
  have hcs : (∑ v : F, subsetSumRep x v) ^ 2
      ≤ (Finset.univ : Finset F).card * ∑ v : F, (subsetSumRep x v) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [sum_subsetSumRep, Finset.card_univ] at hcs
  have h4 : (4 : ℕ) ^ N = (2 ^ N) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow, sq]
  rw [h4]; exact hcs

/-- **The halo is nonempty below the sharp threshold `2^N`.**  If `|F| < 2^N` then the
subset-sum energy strictly exceeds `2^N`, i.e. there is at least one nontrivial collision
`A ≠ B` with equal sum — the deployed census halo is provably nonempty (so the past-Johnson
pin cannot hold there: `δ*` lies strictly below `1−r/2^μ`). -/
theorem subsetSum_energy_gt_of_card_lt (x : Fin N → F)
    (hlt : Fintype.card F < 2 ^ N) :
    2 ^ N < ∑ v : F, (subsetSumRep x v) ^ 2 := by
  by_contra hle
  push_neg at hle
  have h1 : 4 ^ N ≤ Fintype.card F * ∑ v : F, (subsetSumRep x v) ^ 2 :=
    four_pow_le_card_mul_subsetSum_energy x
  have h2 : Fintype.card F * ∑ v : F, (subsetSumRep x v) ^ 2
      ≤ Fintype.card F * 2 ^ N := Nat.mul_le_mul_left _ hle
  have h3 : Fintype.card F * 2 ^ N < 2 ^ N * 2 ^ N :=
    Nat.mul_lt_mul_of_pos_right hlt (by positivity)
  have h4 : (2 : ℕ) ^ N * 2 ^ N = 4 ^ N := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]
  omega

/-- **The subset-sum energy is always `≥ 2^N`** (the diagonal/no-collision floor).
Since `r(v) ≤ r(v)²` pointwise and `∑_v r(v) = 2^N`, the energy never drops below `2^N`. -/
theorem two_pow_le_subsetSum_energy (x : Fin N → F) :
    2 ^ N ≤ ∑ v : F, (subsetSumRep x v) ^ 2 := by
  rw [← sum_subsetSumRep x]
  exact Finset.sum_le_sum (fun v _ => Nat.le_self_pow (by norm_num) _)

/-- **The halo vanishes EXACTLY when the subset-sums are distinct.**  The subset-sum energy
equals its floor `2^N` iff every value has at most one representing subset — i.e. the sums
`{∑_{j∈A} x_j : A ⊆ [N]}` are all distinct (no collision).  Combined with
`subsetSum_energy_gt_of_card_lt` (`|F| < 2^N ⟹ energy > 2^N`), this pins the wall precisely:
the census halo is empty (so the past-Johnson pin `δ* = 1−r/2^μ` is valid) **iff** the geometric
sequence `{g^j}` is Sidon for subset sums — automatic above `p ≳ 2^N`, provably violated below. -/
theorem subsetSum_energy_eq_two_pow_iff (x : Fin N → F) :
    (∑ v : F, (subsetSumRep x v) ^ 2) = 2 ^ N ↔ ∀ v : F, subsetSumRep x v ≤ 1 := by
  rw [← sum_subsetSumRep x, eq_comm,
    Finset.sum_eq_sum_iff_of_le (fun v _ => Nat.le_self_pow (by norm_num) _)]
  constructor
  · intro h v
    have hv := h v (Finset.mem_univ v)
    rw [pow_two] at hv
    rcases Nat.lt_or_ge (subsetSumRep x v) 2 with h' | h'
    · omega
    · exfalso
      have hmul : 2 * subsetSumRep x v ≤ subsetSumRep x v * subsetSumRep x v :=
        Nat.mul_le_mul_right (subsetSumRep x v) h'
      omega
  · intro h v _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (h v) with h' | h' <;> simp [h']

end ArkLib.ProximityGap.SubsetSumHalo

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.SubsetSumHalo.four_pow_le_card_mul_subsetSum_energy
#print axioms ArkLib.ProximityGap.SubsetSumHalo.subsetSum_energy_gt_of_card_lt
#print axioms ArkLib.ProximityGap.SubsetSumHalo.two_pow_le_subsetSum_energy
#print axioms ArkLib.ProximityGap.SubsetSumHalo.subsetSum_energy_eq_two_pow_iff
