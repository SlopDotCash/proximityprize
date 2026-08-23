/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Round 8 (Issue #232, ABF26) — the GENERAL `d`-th-power subgroup-tower step.

The order-2 step (`SubgroupSquaresHalvingRecursion.image_sq_eq_half`: `μ_{2m}² = μ_m`) and the
order-4 step (`SubgroupQuarticHalvingRecursion.image_pow4_eq_quarter`: `μ_{4m}⁴ = μ_m`) are both
special cases of a single law: for **any** `d, m ≥ 1` and a primitive `dm`-th root `ζ`,

  `(nthRootsFinset (d·m) 1).image (·^d) = nthRootsFinset m 1`     (`image_pow_eq_quotient`),

i.e. the `d`-th powers of the order-`dm` smooth subgroup `μ_{dm}` are **exactly** the order-`m`
subgroup `μ_m` (the unique index-`d` subgroup, since `gcd(d, dm) = d`), and the `d`-th-power map is
exactly `d`-to-`1` (`image_pow_card_eq_quotient`). This is the general step of the self-similar
descent down the subgroup tower `μ_{dm} ⊃ μ_m ⊃ …` that the round-8 descent files exploit; the
`d = 2` and `d = 4` results are the `image_pow_eq_quotient`-instances at `d = 2, 4`.

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Structural — exhibits the
self-similar tower; does **not** pin `δ*`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial BigOperators Finset

namespace ArkLib.ProximityGap.Round8PowerSubgroup

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

omit [DecidableEq R] in
/-- **`d`-th powers land in the order-`m` subgroup.** If `x ∈ μ_{dm}` (so `x^{dm} = 1`) and
`0 < d`, then `x^d ∈ μ_m`, because `(x^d)^m = x^{dm} = 1`. -/
theorem pow_mem_quotient {d m : ℕ} (hd : 0 < d) {x : R}
    (hx : x ∈ nthRootsFinset (d * m) (1 : R)) :
    x ^ d ∈ nthRootsFinset m (1 : R) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp only [Nat.mul_zero, nthRootsFinset_zero, Finset.notMem_empty] at hx
  · rw [mem_nthRootsFinset (by positivity : 0 < d * m)] at hx
    rw [mem_nthRootsFinset hm]
    calc (x ^ d) ^ m = x ^ (d * m) := by rw [← pow_mul]
      _ = 1 := hx

/-- **The `d`-th-power image is contained in the order-`m` subgroup.** -/
theorem image_pow_subset_quotient {d m : ℕ} (hd : 0 < d) :
    (nthRootsFinset (d * m) (1 : R)).image (fun x => x ^ d) ⊆ nthRootsFinset m (1 : R) := by
  classical
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact pow_mem_quotient hd hx

/-- **The general subgroup-tower step: the `d`-th powers of `μ_{dm}` ARE the order-`m` subgroup.**
For a primitive `dm`-th root `ζ` (`d, m ≥ 1`),

  `(nthRootsFinset (dm) 1).image (·^d) = nthRootsFinset m 1`.

The `⊆` direction is `image_pow_subset_quotient`. For `⊇`: `ζ^d` is a primitive `m`-th root
(`IsPrimitiveRoot.pow` with `dm = d·m`), so every `y` with `y^m = 1` is a power `y = (ζ^d)^j =
(ζ^j)^d`, with `ζ^j ∈ μ_{dm}`. Subsumes the `d = 2` (`image_sq_eq_half`) and `d = 4`
(`image_pow4_eq_quarter`) instances. -/
theorem image_pow_eq_quotient {ζ : R} {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hζ : IsPrimitiveRoot ζ (d * m)) :
    (nthRootsFinset (d * m) (1 : R)).image (fun x => x ^ d) = nthRootsFinset m (1 : R) := by
  classical
  apply Finset.Subset.antisymm (image_pow_subset_quotient hd)
  -- `ζ^d` is a primitive `m`-th root.
  have hζd : IsPrimitiveRoot (ζ ^ d) m := hζ.pow (by positivity : 0 < d * m) rfl
  haveI : NeZero m := ⟨by omega⟩
  intro y hy
  rw [mem_nthRootsFinset hm] at hy
  obtain ⟨j, _, hj⟩ := hζd.eq_pow_of_pow_eq_one hy
  rw [Finset.mem_image]
  refine ⟨ζ ^ j, ?_, ?_⟩
  · -- `ζ^j ∈ μ_{dm}` since `(ζ^j)^{dm} = (ζ^{dm})^j = 1`.
    rw [mem_nthRootsFinset (by positivity : 0 < d * m), ← pow_mul, mul_comm j (d * m), pow_mul,
      hζ.pow_eq_one, one_pow]
  · -- `(ζ^j)^d = (ζ^d)^j = y`.
    rw [← pow_mul, mul_comm j d, pow_mul, hj]

/-- **The `d`-th-power image has cardinality `m = n/d`** (the map is exactly `d`-to-`1`). -/
theorem image_pow_card_eq_quotient {ζ : R} {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hζ : IsPrimitiveRoot ζ (d * m)) :
    ((nthRootsFinset (d * m) (1 : R)).image (fun x => x ^ d)).card = m := by
  rw [image_pow_eq_quotient hd hm hζ]
  exact (hζ.pow (by positivity : 0 < d * m) rfl).card_nthRootsFinset

end ArkLib.ProximityGap.Round8PowerSubgroup

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round8PowerSubgroup.image_pow_eq_quotient
#print axioms ArkLib.ProximityGap.Round8PowerSubgroup.image_pow_card_eq_quotient
