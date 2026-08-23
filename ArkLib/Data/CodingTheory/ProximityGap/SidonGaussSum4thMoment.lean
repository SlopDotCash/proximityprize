/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonGVClosure
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyBridge
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment

/-!
# THE SUBGROUP GAUSS-SUM FOURTH MOMENT IS PINNED FOR SMALL SUBGROUPS (#389)

The character-sum side of the δ* machinery uses the subgroup Gauss sums `η_b = ∑_{y ∈ μ_n} ψ(b·y)`
and their fourth moment `∑_b ‖η_b‖⁴ = q · E(μ_n)` (`subgroup_gaussSum_fourthMoment`).  Through the
de-vacuated Sidon lifting, the additive energy `E(μ_n)` is pinned to its exact char-0 minimal value
`3n² − 3n` for `p > 4^{φ(n)}` (`= 2^n` when `n = 2^m`).  Composing:

> **`gaussSum_fourthMoment_rootsOfUnity`** — for a primitive additive character `ψ` and `p > 4^{φ(n)}`,
> `∑_b ‖η_b‖⁴ = q · (3n² − 3n)` exactly, unconditionally.

This is the Fourier-side form of the small-subgroup Sidon pin: the fourth moment of the subgroup
Gauss sums is exactly the char-0 minimal value, with no Weil and no Stepanov.  It is the
character-sum kernel that the line-incidence / MCA analysis consumes — pinned exactly in the
regime `n < log₂ p`.  (Past Johnson, and at prize scale `n ~ √p`, the energy excess over `3n² − 3n`
is the open Stepanov/sum-product kernel.)  Issue #389.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

open ArkLib.ProximityGap.AdditiveEnergySidonModNeg ArkLib.ProximityGap.AdditiveEnergyBridge
  ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
  ArkLib.ProximityGap.SubgroupGaussSumSecondMoment in
/-- **The subgroup Gauss-sum fourth moment, pinned for `p > 4^{φ(n)}`.**  For a primitive additive
character `ψ` on `ZMod p` and `n` even with `p > 4^{φ(n)}`, the fourth moment of the subgroup Gauss
sums of `μ_n` is exactly `q · (3n² − 3n)` — the char-0 minimal value, unconditionally. -/
theorem gaussSum_fourthMoment_rootsOfUnity {n : ℕ} (hn2 : 2 ∣ n) (hn0 : n ≠ 0)
    {p : ℕ} [Fact p.Prime] [NeZero (n : ZMod p)] (hp : 4 ^ n.totient < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    ∑ b : ZMod p, ‖eta ψ ((Finset.range n).image (ω ^ ·)) b‖ ^ 4
      = (Fintype.card (ZMod p) : ℝ) * ((3 * n ^ 2 - 3 * n : ℕ) : ℝ) := by
  set G := (Finset.range n).image (ω ^ ·) with hG
  have hp2 : 2 < p := by
    have : (4 : ℕ) ≤ 4 ^ n.totient :=
      Nat.le_self_pow (by have : 1 ≤ n.totient := Nat.totient_pos.mpr (by omega); omega) 4
    omega
  haveI : NeZero p := ⟨by omega⟩
  have hGmem : ∀ z, z ∈ G ↔ z ^ n = 1 := by
    intro z
    rw [hG, image_eq_nthRootsFinset hn0 hω, Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn0)]
  have hcard : G.card = n := by
    rw [hG, image_eq_nthRootsFinset hn0 hω, hω.card_nthRootsFinset]
  have h2 : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, Ne,
      CharP.cast_eq_zero_iff (ZMod p) p]
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  have h0 : (0 : ZMod p) ∉ G := by
    intro hmem; rw [hGmem, zero_pow hn0] at hmem; exact zero_ne_one hmem
  have hev : Even n := even_iff_two_dvd.mpr hn2
  have hneg : ∀ x ∈ G, -x ∈ G := by
    intro x hx
    rw [hGmem] at hx
    rw [hGmem, neg_pow, hx, mul_one]; exact hev.neg_one_pow
  have hS : SidonModNeg G := sidonModNeg_rootsOfUnity hn2 hn0 hp hω
  rw [subgroup_gaussSum_fourthMoment hψ G, addEnergy_eq_of_sidonModNeg h2 h0 hneg hS, hcard]

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.gaussSum_fourthMoment_rootsOfUnity
