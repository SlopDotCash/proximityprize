/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PairSumRigidityModP

/-!
# The universal seed family: a one-parameter supply of second-layer slanted circuits

Campaign #357, the supply half of the second slanted layer. The corrected census found
the slanted stratum splits as `family n(n−4)²/8` (the two-plus-antipodal chord law) plus
a **second layer** `n(n−4)(n−8)/6`, which probe analysis showed is Galois-generated from
`(n−8)/4` seeds per scale (the recursion `B(n) = n²(n−8)/8 + 2·B(n/2)`). Inspecting the
seeds revealed a **scale-independent shape**: for every `t`, the exponent triple

  `{0, 1}, {t+1, n−(2t+1)}, {2t+1, 2^(m−1)−t}`

is collinear in `Γ_n` — at every smooth scale `n = 2^m`, uniformly (probe: all admissible
`t` at `n = 16 … 256`). This file proves it:

* `seed_collinear_identity` — the underlying **rational identity**: over any field, for
  nonzero `ζ, P`, the three points
  `(1+ζ, ζ), (ζP + (ζP²)⁻¹, P⁻¹), (ζP² − P⁻¹, −ζP)`
  satisfy the pencil collinearity equation. No roots of unity at all — the entire
  12-term cancellation is `field_simp; ring`.
* `shape1_collinear` — **the supply theorem**: instantiating `P = ζ^t` at a primitive
  `2^m`-th root (`ζ^(2^(m−1)) = −1` converts the inverses to the wrapped exponents)
  yields the collinearity of the exponent triple above for every `t < 2^(m−1)` — an
  infinite, scale-uniform family of second-layer circuits; rotations and Galois twists
  generate the rest of the layer's orbits.

## Honest scope

This is the *supply* (existence) half. The census *exactness* — that rotations + Galois
images of the seed shapes exhaust the measured `n(n−4)(n−8)/6` — and the closed-form
orbit accounting remain the named open residual of the slanted classification (along
with the shape-II seeds `Σ ≡ n/2+4`, e.g. `{0,1},{2,−2},{4,15}` at `n = 32`).

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #357 (the census-correction and Galois-recursion comments);
  `TwoPlusAntipodalChordLaw.lean` (the first slanted family);
  `MCADualPencilLaw.dependent_iff_collinear` (the consumer interface).
* Probe: `scripts/probes/probe_slanted_char0_census.py` (orbit decomposition, seed
  shapes, shape-I universality at `n = 16 … 256`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SecondLayerSeedFamily

open ArkLib.ProximityGap.PairSumRigidityModP

variable {L : Type*} [Field L]

/-- **The seed identity** (pure field algebra, no roots of unity): the three points
`(1+ζ, ζ)`, `(ζP + (ζP²)⁻¹, P⁻¹)`, `(ζP² − P⁻¹, −ζP)` are collinear. -/
theorem seed_collinear_identity {ζ P : L} (hζ : ζ ≠ 0) (hP : P ≠ 0) :
    (ζ * P + (ζ * P ^ 2)⁻¹ - (1 + ζ)) * (-(ζ * P) - ζ)
      = (P⁻¹ - ζ) * (ζ * P ^ 2 - P⁻¹ - (1 + ζ)) := by
  field_simp
  ring

/-- **THE UNIVERSAL SEED FAMILY (shape I).** At every smooth scale `n = 2^m` and every
parameter `t < 2^(m−1)`: the exponent triple
`{0, 1}, {t+1, n−(2t+1)}, {2t+1, 2^(m−1)−t}` of `Γ_n` satisfies the pencil collinearity
equation — an infinite, scale-uniform supply of second-layer slanted circuits. -/
theorem shape1_collinear {m : ℕ} (hm : 1 ≤ m) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) {t : ℕ} (ht : t < 2 ^ (m - 1)) :
    (ζ ^ (t + 1) + ζ ^ (2 ^ m - (2 * t + 1)) - (ζ ^ 0 + ζ ^ 1))
        * (ζ ^ (2 * t + 1) * ζ ^ (2 ^ (m - 1) - t) - ζ ^ 0 * ζ ^ 1)
      = (ζ ^ (t + 1) * ζ ^ (2 ^ m - (2 * t + 1)) - ζ ^ 0 * ζ ^ 1)
        * (ζ ^ (2 * t + 1) + ζ ^ (2 ^ (m - 1) - t) - (ζ ^ 0 + ζ ^ 1)) := by
  have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by positivity)
  have hP0 : ζ ^ t ≠ 0 := pow_ne_zero t hζ0
  have hhalf : ζ ^ 2 ^ (m - 1) = -1 := pow_half_eq_neg_one_field hm hζ
  have h2t1 : 2 * t + 1 ≤ 2 ^ m := by omega
  -- the four wrapped powers, as explicit rational expressions in ζ and ζ^t
  have ht1 : ζ ^ (t + 1) = ζ ^ t * ζ := pow_succ ζ t
  have h2t : ζ ^ (2 * t + 1) = (ζ ^ t) ^ 2 * ζ := by
    rw [pow_succ, ← pow_mul, mul_comm 2 t]
  have he2 : ζ ^ (2 ^ m - (2 * t + 1)) = ((ζ ^ t) ^ 2 * ζ)⁻¹ := by
    have hprod : ζ ^ (2 ^ m - (2 * t + 1)) * ((ζ ^ t) ^ 2 * ζ) = 1 := by
      rw [← h2t, ← pow_add, Nat.sub_add_cancel h2t1, hζ.pow_eq_one]
    exact eq_inv_of_mul_eq_one_left hprod
  have he3 : ζ ^ (2 ^ (m - 1) - t) = -(ζ ^ t)⁻¹ := by
    have hprod : ζ ^ (2 ^ (m - 1) - t) * ζ ^ t = -1 := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt ht), hhalf]
    have hx : ζ ^ (2 ^ (m - 1) - t) = -1 / ζ ^ t := by
      rw [eq_div_iff hP0]
      exact hprod
    rw [hx, neg_div, one_div]
  rw [pow_zero, pow_one, ht1, h2t, he2, he3]
  field_simp
  ring

/-- **The shape-II seed identity** (pure field algebra): the three points
`(1+ζ, ζ)`, `(ζ²P + (ζ²P²)⁻¹, P⁻¹)`, `(ζ⁴P² − (ζP)⁻¹, −ζ³P)` are collinear. Together
with `seed_collinear_identity` these are the only two identities of their ansatz class
(probe sweep), and their orbits + doubling **exhaust the second layer exactly** at
`n = 16, 32` (0 missing, 0 extra). -/
theorem seed_collinear_identity_II {ζ P : L} (hζ : ζ ≠ 0) (hP : P ≠ 0) :
    (ζ ^ 2 * P + (ζ ^ 2 * P ^ 2)⁻¹ - (1 + ζ)) * (-(ζ ^ 3 * P) - ζ)
      = (P⁻¹ - ζ) * (ζ ^ 4 * P ^ 2 - (ζ * P)⁻¹ - (1 + ζ)) := by
  field_simp
  ring

/-- **THE UNIVERSAL SEED FAMILY (shape II).** At every smooth scale `n = 2^m`, `m ≥ 2`,
and every `t + 1 < 2^(m−1)`: the exponent triple
`{0, 1}, {t+2, n−(2t+2)}, {2t+4, 2^(m−1)−t−1}` of `Γ_n` satisfies the pencil
collinearity equation. -/
theorem shape2_collinear {m : ℕ} (hm : 1 ≤ m) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) {t : ℕ} (ht : t + 1 < 2 ^ (m - 1)) :
    (ζ ^ (t + 2) + ζ ^ (2 ^ m - (2 * t + 2)) - (ζ ^ 0 + ζ ^ 1))
        * (ζ ^ (2 * t + 4) * ζ ^ (2 ^ (m - 1) - (t + 1)) - ζ ^ 0 * ζ ^ 1)
      = (ζ ^ (t + 2) * ζ ^ (2 ^ m - (2 * t + 2)) - ζ ^ 0 * ζ ^ 1)
        * (ζ ^ (2 * t + 4) + ζ ^ (2 ^ (m - 1) - (t + 1)) - (ζ ^ 0 + ζ ^ 1)) := by
  have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by positivity)
  have hP0 : ζ ^ t ≠ 0 := pow_ne_zero t hζ0
  have hhalf : ζ ^ 2 ^ (m - 1) = -1 := pow_half_eq_neg_one_field hm hζ
  have h2t2 : 2 * t + 2 ≤ 2 ^ m := by omega
  have ht2 : ζ ^ (t + 2) = ζ ^ t * ζ ^ 2 := by rw [pow_add]
  have h2t4 : ζ ^ (2 * t + 4) = (ζ ^ t) ^ 2 * ζ ^ 4 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have he2 : ζ ^ (2 ^ m - (2 * t + 2)) = ((ζ ^ t) ^ 2 * ζ ^ 2)⁻¹ := by
    have hprod : ζ ^ (2 ^ m - (2 * t + 2)) * ((ζ ^ t) ^ 2 * ζ ^ 2) = 1 := by
      rw [← pow_mul, ← pow_add, ← pow_add,
        show 2 ^ m - (2 * t + 2) + (t * 2 + 2) = 2 ^ m from by omega,
        hζ.pow_eq_one]
    exact eq_inv_of_mul_eq_one_left hprod
  have he3 : ζ ^ (2 ^ (m - 1) - (t + 1)) = -(ζ ^ t * ζ)⁻¹ := by
    have hprod : ζ ^ (2 ^ (m - 1) - (t + 1)) * (ζ ^ t * ζ) = -1 := by
      rw [← pow_succ, ← pow_add, Nat.sub_add_cancel (le_of_lt ht), hhalf]
    have hx : ζ ^ (2 ^ (m - 1) - (t + 1)) = -1 / (ζ ^ t * ζ) := by
      rw [eq_div_iff (mul_ne_zero hP0 hζ0)]
      exact hprod
    rw [hx, neg_div, one_div]
  rw [pow_zero, pow_one, ht2, h2t4, he2, he3]
  field_simp
  ring

/-! ## Source audit -/

#print axioms seed_collinear_identity
#print axioms shape1_collinear
#print axioms seed_collinear_identity_II
#print axioms shape2_collinear

end ArkLib.ProximityGap.SecondLayerSeedFamily
