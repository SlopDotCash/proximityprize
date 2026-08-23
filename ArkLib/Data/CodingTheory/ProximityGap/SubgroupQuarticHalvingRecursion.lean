/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Round 8 (Issue #232, ABF26) — the QUARTIC subgroup-tower step: 4th powers of the order-`4m` smooth
# subgroup ARE the order-`m` subgroup.

`SubgroupSquaresHalvingRecursion` proved the order-2 step — squaring the order-`2m` smooth subgroup
`μ_{2m}` gives exactly the order-`m` subgroup `μ_m` (`image_sq_eq_half`). This file is the order-4
analogue, welding the round-8 **quartic descent** (`SubsetSumQuarticDescent.pow4_injOn_of_omegaFree`,
`psum4_count_eq_subsetSumCount_pow4Set`) to the literal multiplicative subgroup tower:

  `(nthRootsFinset (4m) 1).image (·⁴) = nthRootsFinset m 1`     (`image_pow4_eq_quarter`),

i.e. the 4th powers of the order-`4m` smooth subgroup `μ_{4m}` are **exactly** the order-`m` smooth
subgroup `μ_m` (the unique index-4 subgroup, since `gcd(4, 4m) = 4`). With
`SubsetSumQuarticDescent`, the surviving `∑x⁴` coordinate of the order-4 `⟨ω⟩`-closure is therefore a
subset-sum **over `μ_m`** — a genuine descent down the `2`-power subgroup tower
`μ_{4m} ⊃ μ_m ⊃ …`, one *quartic* step (two halvings).

## Honest scope

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Order-4 analogue of the
landed order-2 `image_sq_eq_half`. Like the descent, this is **structural** — it exhibits the
self-similar subgroup tower; it does **not** pin `δ*` (the prize core stays open research).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial BigOperators Finset

namespace ArkLib.ProximityGap.Round8QuarticSubgroup

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

/-! ## 1. 4th powers map the order-`4m` subgroup into the order-`m` subgroup. -/

omit [DecidableEq R] in
/-- **4th powers land in the quarter-order subgroup.** If `x ∈ μ_{4m}` (so `x^{4m} = 1`), then
`x⁴ ∈ μ_m`, because `(x⁴)^m = x^{4m} = 1`. -/
theorem pow4_mem_quarter {m : ℕ} {x : R} (hx : x ∈ nthRootsFinset (4 * m) (1 : R)) :
    x ^ 4 ∈ nthRootsFinset m (1 : R) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp only [Nat.mul_zero, nthRootsFinset_zero, Finset.notMem_empty] at hx
  · rw [mem_nthRootsFinset (by omega : 0 < 4 * m)] at hx
    rw [mem_nthRootsFinset hm]
    calc (x ^ 4) ^ m = x ^ (4 * m) := by rw [← pow_mul, mul_comm]
      _ = 1 := hx

/-- **The 4th-power image is contained in the quarter-order subgroup.** -/
theorem image_pow4_subset_quarter {m : ℕ} :
    (nthRootsFinset (4 * m) (1 : R)).image (fun x => x ^ 4) ⊆ nthRootsFinset m (1 : R) := by
  classical
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact pow4_mem_quarter hx

/-! ## 2. The headline: the 4th powers of `μ_{4m}` ARE the order-`m` subgroup `μ_m`. -/

/-- **The 4th-power image equals the order-`m` subgroup.** For a primitive `4m`-th root `ζ`
(`m ≥ 1`),

  `(nthRootsFinset (4m) 1).image (·⁴) = nthRootsFinset m 1`.

The 4th powers of the order-`4m` smooth subgroup are **exactly** the order-`m` smooth subgroup (the
index-4 subgroup). The `⊆` direction is `image_pow4_subset_quarter`. For `⊇`: `ζ⁴` is a primitive
`m`-th root (`IsPrimitiveRoot.pow` with `4m = 4·m`), so every `y` with `y^m = 1` is a power
`y = (ζ⁴)^j = (ζ^j)⁴`, and `ζ^j ∈ μ_{4m}`. -/
theorem image_pow4_eq_quarter {ζ : R} {m : ℕ} (hm : 0 < m) (hζ : IsPrimitiveRoot ζ (4 * m)) :
    (nthRootsFinset (4 * m) (1 : R)).image (fun x => x ^ 4) = nthRootsFinset m (1 : R) := by
  classical
  apply Finset.Subset.antisymm image_pow4_subset_quarter
  -- `ζ⁴` is a primitive `m`-th root.
  have hζ4 : IsPrimitiveRoot (ζ ^ 4) m := hζ.pow (by omega : 0 < 4 * m) (by ring)
  haveI : NeZero m := ⟨by omega⟩
  intro y hy
  rw [mem_nthRootsFinset hm] at hy
  -- every `m`-th root `y` is a power of the primitive `m`-th root `ζ⁴`.
  obtain ⟨j, _, hj⟩ := hζ4.eq_pow_of_pow_eq_one hy
  rw [Finset.mem_image]
  refine ⟨ζ ^ j, ?_, ?_⟩
  · -- `ζ^j ∈ μ_{4m}` since `(ζ^j)^{4m} = (ζ^{4m})^j = 1`.
    rw [mem_nthRootsFinset (by omega : 0 < 4 * m), ← pow_mul, mul_comm j (4 * m), pow_mul,
      hζ.pow_eq_one, one_pow]
  · -- `(ζ^j)⁴ = (ζ⁴)^j = y`.
    rw [← pow_mul, mul_comm j 4, pow_mul, hj]

/-! ## 3. Cardinality: the 4th-power map on the order-`4m` subgroup is exactly `4`-to-`1`. -/

/-- **The 4th-power image has cardinality `m = n/4`.** Combining `image_pow4_eq_quarter` with
`card_nthRootsFinset` for the primitive `m`-th root `ζ⁴`. So the 4th-power map on the order-`4m`
smooth subgroup is exactly `4`-to-`1` onto the order-`m` subgroup. -/
theorem image_pow4_card_eq_quarter {ζ : R} {m : ℕ} (hm : 0 < m) (hζ : IsPrimitiveRoot ζ (4 * m)) :
    ((nthRootsFinset (4 * m) (1 : R)).image (fun x => x ^ 4)).card = m := by
  rw [image_pow4_eq_quarter hm hζ]
  have hζ4 : IsPrimitiveRoot (ζ ^ 4) m := hζ.pow (by omega : 0 < 4 * m) (by ring)
  exact hζ4.card_nthRootsFinset

end ArkLib.ProximityGap.Round8QuarticSubgroup

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round8QuarticSubgroup.image_pow4_eq_quarter
#print axioms ArkLib.ProximityGap.Round8QuarticSubgroup.image_pow4_card_eq_quarter
