/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# The diagonal of the GV representation count collapses to a single value (#389)

`RepCountStepanovOrderTwo.lean` proves the explicit order-2 Stepanov bound `2·r(c) ≤ n+1` for the
**off-diagonal** cosets `c^n ≠ 1`; its auxiliary `Q(X) = (c−X)^{n+1} + X^{n+1} − c` degenerates
exactly when `c^n = 1` (then `Q(0) = c(c^n−1) = 0`).  This file handles the complementary
**diagonal** case by the multiplicative symmetry of `μ_n`: every diagonal value gives the *same*
representation count.

> **`repCount_eq_of_pow_eq_one`** — for `G = μ_n` and `c` with `c^n = 1` (so `c ∈ G`),
> `r(c) = r(1)`.

The map `y ↦ y·c⁻¹` is a bijection between `{y ∈ G : c − y ∈ G}` and `{w ∈ G : 1 − w ∈ G}`
(it preserves `G`-membership because `(y·c⁻¹)^n = y^n·(c^n)⁻¹ = 1`, and sends `c − y` to
`(c−y)·c⁻¹ = 1 − y·c⁻¹ ∈ G`).  So the entire diagonal `{c : c^n = 1}` of the representation count
is pinned to the single value `r(1) = |G ∩ (1 − G)|`, completing the per-coset picture started
by the off-diagonal order-2 bound.  Unconditional, axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The diagonal representation count is constant.**  For `G = μ_n` and any `c` with `c^n = 1`,
the representation count equals the value at `1`: `r(c) = r(1)`. -/
theorem repCount_eq_of_pow_eq_one {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {c : F} (hc : c ^ n = 1) :
    repCount G c = repCount G 1 := by
  classical
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega : n ≠ 0)] at hc
    exact one_ne_zero hc.symm
  have hcn_inv : (c⁻¹) ^ n = 1 := by
    rw [inv_pow, hc, inv_one]
  refine Finset.card_bij' (fun y _ => y * c⁻¹) (fun w _ => w * c) ?_ ?_ ?_ ?_
  · -- {y∈G : c−y∈G} → {w∈G : 1−w∈G}
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    obtain ⟨hyG, hcyG⟩ := hy
    have hyn : y ^ n = 1 := (hGmem y).mp hyG
    have hcyn : (c - y) ^ n = 1 := (hGmem (c - y)).mp hcyG
    constructor
    · rw [hGmem]; rw [mul_pow, hyn, hcn_inv, mul_one]
    · have h1 : (1 : F) - y * c⁻¹ = (c - y) * c⁻¹ := by field_simp
      rw [h1, hGmem, mul_pow, hcyn, hcn_inv, mul_one]
  · -- {w∈G : 1−w∈G} → {y∈G : c−y∈G}
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    obtain ⟨hwG, hwwG⟩ := hw
    have hwn : w ^ n = 1 := (hGmem w).mp hwG
    have hwwn : (1 - w) ^ n = 1 := (hGmem (1 - w)).mp hwwG
    constructor
    · rw [hGmem]; rw [mul_pow, hwn, hc, mul_one]
    · have h1 : c - w * c = (1 - w) * c := by ring
      rw [h1, hGmem, mul_pow, hwwn, hc, mul_one]
  · intro y hy
    field_simp
  · intro w hw
    field_simp

end ArkLib.ProximityGap.AdditiveEnergyRepBound
