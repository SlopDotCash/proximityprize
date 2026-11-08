/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# The subset-sum halo energy: the large-`n` `δ*` core, made explicit (#389)

Working out the large-`n` (deployed, below-threshold) `δ*`, the census **halo** — non-antipodal
`E ⊆ [0,2^m)` with `∑_{e∈E} g^e ≡ 0 (mod p)` — is related (via `g^{e+N} = −g^e`) to
**subset-sum collisions** of `{g^0,…,g^{N-1}}` (`N = 2^{m-1}`): pairs of subsets `A ≠ B` with
`∑_{j∈A} g^j = ∑_{j∈B} g^j` in `F_p`.  These collisions are counted by the **subset-sum energy**
`∑_v r(v)²`, `r(v) = #{A : ∑_{j∈A} x_j = v}` (ordered subset pairs, not distinct supports).

This file proves the unconditional Cauchy–Schwarz lower bound on that energy:

> **`four_pow_le_card_mul_subsetSum_energy`** — `4^N ≤ |F| · ∑_v r(v)²`.

Equivalently the collision count `∑_v r(v)² − 2^N ≥ 4^N/|F| − 2^N`, which is **strictly
positive once `|F| < 2^N`** (`subsetSum_energy_gt_of_card_lt`), and the energy equals its
diagonal floor `2^N` **iff** the subset-sum map is injective (`subsetSum_energy_eq_two_pow_iff`).

**Scope (what is NOT proved).**
* `|F| < 2^N` is only a pigeonhole *sufficient condition for collisions*; the converse
  "`p > 2^N` ⟹ distinct subset sums" is FALSE.  Kernel-checked counterexample
  (`subsetSum_collision_above_two_pow` below): in `F_337`, `g = 191` has order `16`, its first
  `N = 8` powers are `[1,191,85,59,148,297,111,307]`, and although `337 > 2^8 = 256` the subsets
  `{0,4,5}` and `{1,2,3,6}` both sum to `109`.  No large-`p` sufficiency threshold for an empty
  halo is established; a valid route would need a genuine arithmetic separation / norm condition.
* `∑_v r(v)²` counts ordered pairs of *subsets*, not distinct vanishing supports (overlapping
  pairs can give several representations of one support), so it is not literally the halo size.
* No bridge from a subset-sum collision (or its absence) to an exact value of `δ*` or to any
  fixed-band MCA consequence is proved here; statements such as "the halo is empty, so the
  past-Johnson pin `δ* = 1−r/2^μ` holds" or "`δ*` drops below `1−r/2^μ`" are motivation only.

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

/-- **Pigeonhole collisions below `2^N`.**  If `|F| < 2^N` then the subset-sum energy strictly
exceeds `2^N`, i.e. there is at least one nontrivial collision `A ≠ B` with equal sum.  This is a
sufficient condition for a collision only: collisions can also occur for `|F| > 2^N`
(`subsetSum_collision_above_two_pow`), and no consequence for `δ*` is proved here. -/
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
`subsetSum_energy_gt_of_card_lt`, distinct subset sums are impossible when `|F| < 2^N`; they are
NOT automatic when `|F| > 2^N` (`subsetSum_collision_above_two_pow`).  This is a statement about
subset sums only; no equivalence with an empty census halo or with `δ* = 1−r/2^μ` is proved. -/
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

section Counterexample

/-- `337` is prime (used only for the counterexample below). -/
theorem prime_337 : Nat.Prime 337 := by norm_num

instance fact_prime_337 : Fact (Nat.Prime 337) := ⟨prime_337⟩

/-- The first `8` powers of `191` in `F_337`. -/
def geom191 : Fin 8 → ZMod 337 := fun j => 191 ^ (j : ℕ)

/-- `191` has multiplicative order exactly `16` in `F_337` (so `{191^j}` generates the proper
smooth subgroup `μ_16`, and `191^8 = −1`). -/
theorem orderOf_191_eq_16 : orderOf (191 : ZMod 337) = 16 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 3) (x := (191 : ZMod 337))
    (by decide) (by decide)
  rw [h]
  norm_num

/-- **Refutation of "`p > 2^N` ⟹ distinct subset sums".**  In `F_337` with `N = 8` and
`x_j = 191^j` (`191` of order `16`), the field is larger than `2^N = 256`, yet the value `109`
has at least two subset-sum representations: `{0,4,5}` (`1 + 148 + 297`) and `{1,2,3,6}`
(`191 + 85 + 59 + 111`).  Hence the energy exceeds its floor `2^N` above the pigeonhole
threshold, and `|F| < 2^N` in `subsetSum_energy_gt_of_card_lt` is not a sharp threshold. -/
theorem subsetSum_collision_above_two_pow :
    2 ^ 8 < Fintype.card (ZMod 337) ∧ 1 < subsetSumRep geom191 109 ∧
      ¬ ∀ v : ZMod 337, subsetSumRep geom191 v ≤ 1 := by
  have hrep : 1 < subsetSumRep geom191 109 := by
    unfold subsetSumRep
    refine Finset.one_lt_card.mpr ⟨{0, 4, 5}, ?_, {1, 2, 3, 6}, ?_, by decide⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by decide⟩
  refine ⟨by rw [ZMod.card]; norm_num, hrep, fun h => ?_⟩
  have := h 109
  omega

end Counterexample

end ArkLib.ProximityGap.SubsetSumHalo

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.SubsetSumHalo.four_pow_le_card_mul_subsetSum_energy
#print axioms ArkLib.ProximityGap.SubsetSumHalo.subsetSum_energy_gt_of_card_lt
#print axioms ArkLib.ProximityGap.SubsetSumHalo.two_pow_le_subsetSum_energy
#print axioms ArkLib.ProximityGap.SubsetSumHalo.subsetSum_energy_eq_two_pow_iff
#print axioms ArkLib.ProximityGap.SubsetSumHalo.orderOf_191_eq_16
#print axioms ArkLib.ProximityGap.SubsetSumHalo.subsetSum_collision_above_two_pow
