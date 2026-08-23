/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyBridge
import ArkLib.Data.CodingTheory.ProximityGap.SidonModNegImproved
import ArkLib.Data.CodingTheory.ProximityGap.SidonLiftDevacuated

/-!
# The r = 2 rung of the BGK ladder, discharged unconditionally (#407)

The corrected reduction's open input is `DCEnergyBound G r` (`A_r ≤ Wick`) at `r ≈ ln q`. The base
`r = 1` is unconditional (`DCEnergyBaseCase`). Here the **`r = 2` rung is also unconditional** for the
dyadic roots of unity `μ_{2^m}` (at the Sidon threshold `12^{φ(n)} < p²`):

> **`dcEnergyBound_two_rootsOfUnity`** — `DCEnergyBound μ_{2^m} 2`.

Mechanism: the sharp additive energy `E_2(μ_{2^m}) = 3n²−3n` (`rootsOfUnity_additiveEnergy_eq_improved`,
the Sidon-mod-negation pin) feeds `DCEnergyBound G 2 ⟺ q(3n²−3n)−n⁴ ≤ 3qn² ⟺ −3qn−n⁴ ≤ 0`, true
always. The energy↔moment bridge `rEnergy G 2 = addEnergy G` is read off the two fourth-moment Parseval
identities (`subgroup_gaussSum_moment` at `r=2` and `subgroup_gaussSum_fourthMoment`), and
`addEnergy = additiveEnergy` is `additiveEnergy_eq_addEnergy`.

So the BGK hypothesis is **proven at `r = 1, 2`**; only `r ≥ 3` (specifically `r ≈ ln q`) is open. (`ψ`
is a proof device — a primitive additive character exists on every `ZMod p`.)

Issue #407.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergyBridge

namespace ArkLib.ProximityGap.DCEnergyRungTwo

/-- **The r = 2 BGK rung, unconditional.** For `μ_{2^m}` over `ZMod p` at the Sidon threshold, the
corrected DC-subtracted energy bound holds at `r = 2` with no energy conjecture: `DCEnergyBound μ 2`. -/
theorem dcEnergyBound_two_rootsOfUnity {m : ℕ} (hm : 1 ≤ m) {p : ℕ} [Fact p.Prime]
    [NeZero ((2 ^ m : ℕ) : ZMod p)] (hp : 12 ^ (2 ^ m).totient < p ^ 2)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω (2 ^ m))
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    DCEnergyBound ((Finset.range (2 ^ m)).image (ω ^ ·)) 2 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set G := (Finset.range (2 ^ m)).image (ω ^ ·) with hG
  have hn0 : (2 ^ m : ℕ) ≠ 0 := by positivity
  have hn1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  -- card of G
  have hinj : Set.InjOn (fun k => ω ^ k) (Finset.range (2 ^ m)) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h := (primitiveRoot_pow_eq_iff hn0 hω a b).mp hab
    unfold Nat.ModEq at h; rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  have hcard : G.card = 2 ^ m := by
    rw [hG, Finset.card_image_of_injOn hinj, Finset.card_range]
  -- additive energy pin
  have hAE : additiveEnergy G = 3 * (2 ^ m) ^ 2 - 3 * 2 ^ m :=
    rootsOfUnity_additiveEnergy_eq_improved hm hp hω
  have hbridge : additiveEnergy G = addEnergy G := additiveEnergy_eq_addEnergy G
  -- rEnergy G 2 = addEnergy G via two fourth-moment Parseval identities
  have hP1 := subgroup_gaussSum_moment hψ G 2
  have hP2 := subgroup_gaussSum_fourthMoment hψ G
  have hqR : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum_eq : (Fintype.card (ZMod p) : ℝ) * (rEnergy G 2 : ℝ)
      = (Fintype.card (ZMod p) : ℝ) * (addEnergy G : ℝ) := by rw [← hP1, ← hP2]
  have hRE : (rEnergy G 2 : ℝ) = (addEnergy G : ℝ) :=
    mul_left_cancel₀ (ne_of_gt hqR) hsum_eq
  -- value of (addEnergy G : ℝ)
  have hle : 3 * 2 ^ m ≤ 3 * (2 ^ m) ^ 2 := by nlinarith [hn1, sq_nonneg (2 ^ m : ℕ)]
  have hAEval : (addEnergy G : ℝ) = 3 * ((2 ^ m : ℕ) : ℝ) ^ 2 - 3 * ((2 ^ m : ℕ) : ℝ) := by
    rw [← hbridge, hAE, Nat.cast_sub hle]; push_cast; ring
  -- assemble DCEnergyBound
  unfold DCEnergyBound
  have hdf : (Nat.doubleFactorial (2 * 2 - 1) : ℝ) = 3 := by norm_num [Nat.doubleFactorial]
  rw [hdf, hcard, hRE, hAEval]
  set q := (Fintype.card (ZMod p) : ℝ) with hq
  set N := ((2 ^ m : ℕ) : ℝ) with hN
  have hNnn : (0 : ℝ) ≤ N := by positivity
  have hqnn : (0 : ℝ) ≤ q := le_of_lt hqR
  -- q*(3N²-3N) - N^(2*2) ≤ q*(3*N²)
  have h44 : N ^ (2 * 2) = N ^ 4 := by norm_num
  rw [h44]
  nlinarith [hNnn, hqnn, mul_nonneg hqnn hNnn, pow_nonneg hNnn 4]

end ArkLib.ProximityGap.DCEnergyRungTwo
#print axioms ArkLib.ProximityGap.DCEnergyRungTwo.dcEnergyBound_two_rootsOfUnity
