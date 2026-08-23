/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SmoothCubicSupplyBound
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumAntiConc

/-!
# The GV-sharpened Gauss-sum anti-concentration (#357/#389): a concrete production bound

`SubgroupGaussSumAntiConc.card_johnson_scale_frequencies_le_min` proved, with NO Weil input,
that the number of frequencies reaching the Johnson scale `‖η_b‖² ≥ q` is
`≤ min(|G|, E(G)/q)` — sharp in the sum-product regime `E(G) < q·|G|`, but stated with the
abstract energy `E(G)`.  This file makes it CONCRETE by feeding the named Garcia–Voloch
energy bound (`GVHBKEnergyReduction`, `E(G)³ ≤ 260·|G|⁸`):

* `additiveEnergy_eq_fourthMoment` — the bridge: the `repCount`-additive energy equals the
  fourth-moment quadruple count `SubgroupGaussSumFourthMoment.addEnergy` (one line, via
  `repCount_eq_sum_pairs`).
* `card_johnson_scale_le_gv` — **the concrete anti-concentration**: under `GVRepBound G M`,
  the Johnson-scale frequency count `N` satisfies `(N·q)³ ≤ 260·|G|⁸`, i.e.
  `N ≤ 260^{1/3}·|G|^{8/3}/q`.

In production (`|G| = n`, `q = 2¹²⁸`): `N < 1` whenever `q > 260^{1/3}·n^{8/3}` — i.e. for all
smooth domains up to `n ≈ 2⁴⁸`, **no Gauss-sum frequency reaches the Johnson scale at all**,
conditional only on the one open subgroup sum-product input.  (Honest scope, unchanged from
the parent: this is the AVERAGE side — it provably beats Johnson but does not pin the
worst-case `δ*` apex; it sharpens the proven average bound with an explicit constant.)
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment (addEnergy)
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- **Bridge**: the `repCount`-additive energy equals the fourth-moment quadruple count. -/
theorem additiveEnergy_eq_fourthMoment (G : Finset F) :
    additiveEnergy G = addEnergy G := by
  classical
  rw [additiveEnergy, addEnergy]
  refine Finset.sum_congr rfl (fun y₁ _ => Finset.sum_congr rfl (fun y₂ _ => ?_))
  rw [repCount_eq_sum_pairs]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  by_cases h : a + b = y₁ + y₂
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

open ArkLib.ProximityGap.SubgroupGaussSumAntiConc in
/-- **The GV-sharpened average-side anti-concentration.**  Under the named Garcia–Voloch
input, the count `N` of frequencies reaching the Johnson scale `‖η_b‖² ≥ q` satisfies
`(N·q)³ ≤ 260·|G|⁸` — so `N ≤ 260^{1/3}·|G|^{8/3}/q`, vanishing for `q ≫ |G|^{5/3}`. -/
theorem card_johnson_scale_le_gv {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hq : 0 < Fintype.card F) {M : ℕ} (h : GVRepBound G M) :
    (((Finset.univ.filter
        (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
        * (Fintype.card F : ℝ)) ^ 3
      ≤ 260 * (G.card : ℝ) ^ 8 := by
  set N : ℝ := ((Finset.univ.filter
      (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ) with hN
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  -- the abstract min-bound, then take the energy branch
  have hmin := card_johnson_scale_frequencies_le_min hψ G hq
  have hNle : N ≤ (addEnergy G : ℝ) / (Fintype.card F : ℝ) := le_trans hmin (min_le_right _ _)
  have hNq : N * (Fintype.card F : ℝ) ≤ (addEnergy G : ℝ) := by
    rw [← additiveEnergy_eq_fourthMoment] at hNle ⊢
    rwa [le_div_iff₀ hqR] at hNle
  have hNqnn : 0 ≤ N * (Fintype.card F : ℝ) :=
    mul_nonneg (by positivity) (le_of_lt hqR)
  have hEcube : (additiveEnergy G : ℝ) ^ 3 ≤ 260 * (G.card : ℝ) ^ 8 := by
    have := additiveEnergy_cube_le_of_gvRepBound G h
    have : ((additiveEnergy G ^ 3 : ℕ) : ℝ) ≤ ((260 * G.card ^ 8 : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at this
    linarith [this]
  calc (N * (Fintype.card F : ℝ)) ^ 3
      ≤ (additiveEnergy G : ℝ) ^ 3 := by
        apply pow_le_pow_left₀ hNqnn
        rw [additiveEnergy_eq_fourthMoment]; exact hNq
    _ ≤ 260 * (G.card : ℝ) ^ 8 := hEcube

end ArkLib.ProximityGap.AdditiveEnergyRepBound
