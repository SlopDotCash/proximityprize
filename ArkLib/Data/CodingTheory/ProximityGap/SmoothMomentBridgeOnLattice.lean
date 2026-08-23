/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.MomentCollisionTower
import ArkLib.Data.CodingTheory.ProximityGap.CosetExactCount
import ArkLib.Data.CodingTheory.ProximityGap.CosetPowerSumConcentration
import ArkLib.Data.CodingTheory.ProximityGap.SmoothMomentBridge

/-!
# On-lattice exact count of the first open interior cell (#232)

Capstone completing `SmoothMomentBridge`. For the smooth domain `μ_n` with `(t+1) ∣ n`, the
zero-fiber of the depth-`t` power-sum statistic at the first open cell `a = t+1` has EXACT count
`statCount μ_n (t+1) (momentVec t) 0 = n/(t+1)` (`statCount_momentVec_zero_eq_div`). The reverse
direction `esymm = 0 ⟹ momentVec = 0` (which `SmoothMomentBridge` left open) is supplied here
WITHOUT reverse-Newton: rigidity forces such an `S` to be a fiber `{x∈μ_n : x^{t+1}=c} = g·μ_h`,
whose power sums vanish because `∑_{y∈μ_h} y^i = 0` for `1 ≤ i < h` (`coset_powersum_zero` with
`g=1`). Combined with the off-lattice case (`statCount = 0` when `t+1 ∤ n`,
`CosetVanishingDichotomy`), this pins the `N_t(0)` fiber EXACTLY over the power-of-2 lattice:
`N_t(0) = n/(t+1)` if `t+1` is a power of 2, else `0`. Axiom-clean.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.SmoothMomentBridge

open ArkLib.ProximityGap.MomentCollisionTower
open ArkLib.ProximityGap.Rigidity
open ArkLib.ProximityGap.CosetConcentration

variable {F : Type*} [Field F] [DecidableEq F]

/-- `μ_h` enumerated as the powers of a primitive `h`-th root. -/
theorem nthRootsFinset_eq_image {ω : F} {h : ℕ} (hh : 0 < h) (hω : IsPrimitiveRoot ω h) :
    nthRootsFinset h (1 : F) = (range h).image (fun l => ω ^ l) := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [mem_nthRootsFinset hh] at hx
    haveI : NeZero h := ⟨hh.ne'⟩
    obtain ⟨l, hl, rfl⟩ := hω.eq_pow_of_pow_eq_one hx
    exact Finset.mem_image.2 ⟨l, Finset.mem_range.2 hl, rfl⟩
  · rw [hω.card_nthRootsFinset]
    exact Finset.card_image_le.trans (by rw [Finset.card_range])

/-- **The `i`-th power sum over `μ_h` vanishes for `1 ≤ i < h`.** -/
theorem sum_pow_nthRootsFinset_eq_zero {ω : F} {h : ℕ} (hh : 0 < h) (hω : IsPrimitiveRoot ω h)
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i < h) :
    ∑ y ∈ nthRootsFinset h (1 : F), y ^ i = 0 := by
  rw [nthRootsFinset_eq_image hh hω, Finset.sum_image (fun a ha b hb hab =>
    hω.injOn_pow (by simpa using ha) (by simpa using hb) hab)]
  have hωi : ω ^ i ≠ 1 := by
    intro hc
    exact absurd (Nat.le_of_dvd hi1 ((hω.pow_eq_one_iff_dvd i).1 hc)) (Nat.not_le.2 hih)
  have := coset_powersum_zero (F := F) (ζ := ω) (h := h) hω.pow_eq_one hωi 1
  simpa using this

/-- **The fiber `{x ∈ μ_n : x^h = c}` equals the coset `g·μ_h` for a representative `g`.** -/
theorem fiber_eq_image_mul {n h : ℕ} (hn : 0 < n) (hdvd : h ∣ n)
    {g : F} (hgn : g ^ n = 1) :
    fiber n h (g ^ h) = (nthRootsFinset h (1 : F)).image (fun y => g * y) := by
  have hh : 0 < h := Nat.pos_of_ne_zero (by rintro rfl; simp at hdvd; omega)
  have hg0 : g ≠ 0 := by intro h0; rw [h0, zero_pow hn.ne'] at hgn; exact one_ne_zero hgn.symm
  ext x
  rw [mem_fiber hn, Finset.mem_image]
  constructor
  · rintro ⟨hxn, hxh⟩
    refine ⟨x * g⁻¹, ?_, by field_simp⟩
    rw [mem_nthRootsFinset hh, mul_pow, hxh, inv_pow, mul_inv_cancel₀ (pow_ne_zero h hg0)]
  · rintro ⟨y, hy, rfl⟩
    rw [mem_nthRootsFinset hh] at hy
    refine ⟨?_, by rw [mul_pow, hy, mul_one]⟩
    have hyn : y ^ n = 1 := by
      obtain ⟨k, rfl⟩ := hdvd
      rw [pow_mul, hy, one_pow]
    rw [mul_pow, hgn, hyn, mul_one]

/-- **The fiber has vanishing power sums for `1 ≤ i < h`** (it is `g·μ_h`). -/
theorem fiber_powersum_zero {ω : F} {n h : ℕ} (hn : 0 < n) (hdvd : h ∣ n)
    (hω : IsPrimitiveRoot ω h) {g : F} (hgn : g ^ n = 1)
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i < h) :
    ∑ x ∈ fiber n h (g ^ h), x ^ i = 0 := by
  have hh : 0 < h := Nat.pos_of_ne_zero (by rintro rfl; simp at hdvd; omega)
  have hg0 : g ≠ 0 := by intro h0; rw [h0, zero_pow hn.ne'] at hgn; exact one_ne_zero hgn.symm
  rw [fiber_eq_image_mul hn hdvd hgn,
    Finset.sum_image (fun a _ b _ hab => mul_left_cancel₀ hg0 hab)]
  have : ∑ y ∈ nthRootsFinset h (1 : F), (g * y) ^ i
      = g ^ i * ∑ y ∈ nthRootsFinset h (1 : F), y ^ i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun y _ => by rw [mul_pow])
  rw [this, sum_pow_nthRootsFinset_eq_zero hh hω hi1 hih, mul_zero]

/-- **The fiber `{x∈μ_n : x^{t+1}=c}` has `momentVec t = 0`** (every power sum `1..t` vanishes). -/
theorem fiber_momentVec_zero {ω : F} {n t : ℕ} (hn : 0 < n) (hdvd : (t + 1) ∣ n)
    (hω : IsPrimitiveRoot ω (t + 1)) {g : F} (hgn : g ^ n = 1) :
    momentVec t (fiber n (t + 1) (g ^ (t + 1))) = 0 := by
  funext j
  simp only [momentVec, Pi.zero_apply]
  exact fiber_powersum_zero hn hdvd hω hgn (by omega) (by omega)

/-- **On-lattice exact count (the capstone).** For `μ_n` with `(t+1) ∣ n`, the zero-fiber of the
depth-`t` power-sum statistic at the first open cell `a=t+1` has EXACT count `n/(t+1)`. -/
theorem statCount_momentVec_zero_eq_div {n t : ℕ} (hn : 0 < n) (ht : 0 < t)
    (hchar : ∀ i, 0 < i → i ≤ t → (i : F) ≠ 0)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (hdvd : (t + 1) ∣ n) :
    statCount (nthRootsFinset n (1 : F)) (t + 1) (momentVec t) 0 = n / (t + 1) := by
  have hω : IsPrimitiveRoot (ζ ^ (n / (t + 1))) (t + 1) :=
    hζ.pow hn (Nat.div_mul_cancel hdvd).symm
  rw [statCount, ← card_vanishingEsymm_subsets_eq hn (by omega) hdvd hζ]
  congr 1
  ext S
  rw [Finset.mem_filter, Finset.mem_powersetCard, mem_vanishingEsymmSubsets]
  constructor
  · rintro ⟨⟨hSsub, hScard⟩, hmv⟩
    refine ⟨⟨hSsub, hScard⟩, fun j hj1 hj2 => ?_⟩
    exact esymm_zero_of_momentVec_zero hchar hmv j hj1 (by omega)
  · rintro ⟨⟨hSsub, hScard⟩, hesymm⟩
    refine ⟨⟨hSsub, hScard⟩, ?_⟩
    obtain ⟨c, hc⟩ := all_pow_eq_of_esymm_zero (by omega) hScard
      (fun j hj1 hjt => hesymm j hj1 (by omega))
    obtain ⟨x0, hx0⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    have hx0n : x0 ^ n = 1 := (mem_nthRootsFinset hn _).mp (hSsub hx0)
    have hceq : c = x0 ^ (t + 1) := (hc x0 hx0).symm
    have hSfib : S = fiber n (t + 1) (x0 ^ (t + 1)) := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [mem_fiber hn]
        exact ⟨(mem_nthRootsFinset hn _).mp (hSsub hx), by rw [hc x hx, hceq]⟩
      · rw [fiber_card_eq hn hdvd hζ hx0n rfl, hScard]
    rw [hSfib]
    exact fiber_momentVec_zero hn hdvd hω hx0n

end ArkLib.ProximityGap.SmoothMomentBridge

#print axioms ArkLib.ProximityGap.SmoothMomentBridge.statCount_momentVec_zero_eq_div
