/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyResultant

/-!
# Characteristic-0 vanishing of the BGK prize kernel (#232)

The complement to `AdditiveEnergyFermat` (which enumerates the *positive*-characteristic
obstructions). Here we prove that over `ℂ` the open additive-energy intersection count
`M = bgkCount (2^k)` is identically `0`: there is no `u ∈ μ_{2^k}` with `-(1+u) ∈ μ_{2^k}`.

* `no_common_root_complex` — the algebraic core: if `u^(2^k) = 1` and `(u+1)^(2^k) = 1` over `ℂ`,
  then `False`. Proof: both `u` and `u+1` lie on the unit circle (`‖u‖ = ‖u+1‖ = 1`), so
  `u·conj u = 1` and `(u+1)·conj(u+1) = 1`; subtracting gives `u + conj u = -1`, and substituting
  `conj u = -1 - u` into `u·conj u = 1` gives `u² + u + 1 = 0`. Thus `u` is a primitive cube root of
  unity: `orderOf u ∣ 3`. But `orderOf u ∣ 2^k` as well, and `gcd(3, 2^k) = 1`, so `orderOf u = 1`,
  i.e. `u = 1` — contradicting `u² + u + 1 = 0` (which would give `3 = 0`).
* `bgkCount_complex_eq_zero` — consequently `bgkCount (F := ℂ) (2^k) = 0` for all `k ≥ 1`.

**Interpretation.** Together with [`AdditiveEnergyFermat`] this frames the prize kernel as a *purely
positive-characteristic* phenomenon: in characteristic 0 the additive energy of the smooth subgroup
vanishes and the prize cell survives unconditionally, while in characteristic `p` it can break only
when `p` divides the resultant `Res(X^{2^k}-1, (X+1)^{2^k}-1)` (the `u=1` factor of which is the
Fermat product `∏_{j<k} F_j`). The obstruction is exactly the arithmetic of the smooth subgroup over
`𝔽_p`, i.e. the Bourgain–Glibichuk–Konyagin additive-energy problem. Axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset Polynomial

attribute [local instance] Classical.propDecidable

namespace ArkLib.ProximityGap.AdditiveEnergyKernel

/-- **No `u` with `u` and `u+1` both `2^k`-th roots of unity, over `ℂ`.** If `u^(2^k) = 1` and
`(u+1)^(2^k) = 1` then `‖u‖ = ‖u+1‖ = 1`, which forces `u² + u + 1 = 0` (so `u` is a primitive cube
root of unity); but `orderOf u ∣ 3` and `orderOf u ∣ 2^k` are coprime, so `u = 1`, contradicting
`u² + u + 1 = 0`. (Holds for all `k`, including `k = 0` vacuously.) -/
theorem no_common_root_complex (k : ℕ) (u : ℂ)
    (h1 : u ^ (2 ^ k) = 1) (h2 : (u + 1) ^ (2 ^ k) = 1) : False := by
  have hne0 : (2 ^ k : ℕ) ≠ 0 := (Nat.two_pow_pos k).ne'
  -- unit-circle facts
  have hn1 : ‖u‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 hne0
  have hn2 : ‖u + 1‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h2 hne0
  have hs1 : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hn1]; norm_num
  have hs2 : Complex.normSq (u + 1) = 1 := by rw [Complex.normSq_eq_norm_sq, hn2]; norm_num
  have hc1 : u * (starRingEnd ℂ) u = 1 := by rw [Complex.mul_conj, hs1, Complex.ofReal_one]
  have hc2 : (u + 1) * (starRingEnd ℂ) (u + 1) = 1 := by
    rw [Complex.mul_conj, hs2, Complex.ofReal_one]
  rw [map_add, map_one] at hc2
  -- algebra: u + conj u = -1, hence u² + u + 1 = 0
  have hsum : u + (starRingEnd ℂ) u = -1 := by linear_combination hc2 - hc1
  have huu : u ^ 2 + u + 1 = 0 := by linear_combination (-1 : ℂ) * hc1 + u * hsum
  have hcube : u ^ 3 = 1 := by linear_combination (u - 1) * huu
  have hne1 : u ≠ 1 := by
    intro h; rw [h] at huu; norm_num at huu
  -- order argument
  have ho3 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hcube
  have hon : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have hco : Nat.Coprime 3 (2 ^ k) := (by decide : Nat.Coprime 3 2).pow_right k
  have hord1 : orderOf u = 1 := Nat.dvd_one.mp (hco ▸ Nat.dvd_gcd ho3 hon)
  exact hne1 (orderOf_eq_one_iff.mp hord1)

/-- **Characteristic-0 vanishing of the BGK kernel.** Over `ℂ` the additive-energy intersection
count `M = bgkCount (2^k)` is `0` for every `k ≥ 1`: there is no `u ∈ μ_{2^k}` with
`-(1+u) ∈ μ_{2^k}`. So the BGK obstruction to the proximity prize is a *purely
positive-characteristic* phenomenon — in characteristic 0 the prize cell survives unconditionally. -/
theorem bgkCount_complex_eq_zero (k : ℕ) (hk : 0 < k) :
    bgkCount (F := ℂ) (2 ^ k) = 0 := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  rw [bgkCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u hu hcon
  obtain ⟨hr1, hr2⟩ := (mem_bgk_iff_common_root hpos heven).mp ⟨hu, hcon⟩
  have h1 : u ^ (2 ^ k) = 1 := by
    have h := hr1; rw [IsRoot.def, eval_sub, eval_pow, eval_X, eval_one] at h
    exact sub_eq_zero.mp h
  have h2 : (u + 1) ^ (2 ^ k) = 1 := by
    have h := hr2; rw [IsRoot.def, eval_sub, eval_pow, eval_add, eval_X, eval_one] at h
    exact sub_eq_zero.mp h
  exact no_common_root_complex k u h1 h2

end ArkLib.ProximityGap.AdditiveEnergyKernel

#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.no_common_root_complex
#print axioms ArkLib.ProximityGap.AdditiveEnergyKernel.bgkCount_complex_eq_zero
