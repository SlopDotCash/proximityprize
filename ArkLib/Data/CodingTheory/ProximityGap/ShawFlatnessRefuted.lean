/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodLowerBound
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyBridge
import ArkLib.Data.CodingTheory.ProximityGap.SidonSubgroupClosed

/-!
# The energy floor REFUTES "Shaw Flatness" — a novel, falsifiable, fully-proven theorem (#389/#371)

The Shaw-operator route to the proximity prize reduces the closed-form `δ*` to one inequality,
**"Shaw Flatness"** `B(μ_n) = max_{b≠0}‖η_b‖ ≤ √2·√n`, asserted to be *"pinned sharp by the
`3n²−3n` energy floor."*  This file proves, in closed axiom-clean Lean, that **the opposite is
true**: the energy floor *forces* `max_{b≠0}‖η_b‖ > √2·√n`, so Shaw Flatness with constant `√2`
is FALSE.

The mechanism is the L⁴/L² (Cauchy–Schwarz) worst-period lower bound
(`exists_period_sq_ge`): for the nonzero frequencies,
`max ‖η_b‖² ≥ (∑_{b≠0}‖η_b‖⁴)/(∑_{b≠0}‖η_b‖²) = (q·E − |G|⁴)/(q·|G| − |G|²)`.
The 4th moment `∑‖η_b‖⁴ = q·E` is exactly what the energy floor controls; with `E = 3|G|²−3|G|`
the ratio tends to `E/|G| = 3|G|−3`, which **exceeds** `2|G|` for `|G| ≥ 4`.  Thus the energy floor
controls the *average* `≈√n` AND, through the 4th moment, forces the *max* above `√2·√n` — the
"flatness via energy floor" argument confuses the two moments; the floor disproves the bound.

This is the closed mathematical content behind `probe_shaw_flatness_refute.py` (which measured
`B = Θ(√(n·log(q/n)))`): here the `√2` constant is refuted with a *proof*, in the prize regime.
Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option maxHeartbeats 1000000


open Finset Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.AdditiveEnergyBridge
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

namespace ArkLib.ProximityGap.ShawFlatnessRefuted

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The energy floor refutes Shaw Flatness (general form).** If the additive energy of `G` is at
least the char-0 minimal value `3|G|²−3|G|` (an equality for Sidon-mod-negation `μ_n`) and the field
is large in the prize sense `|G|²·(|G|−2) < q·(|G|−3)`, then some nontrivial frequency has
`‖η_b‖² > 2·|G|` — i.e. `max_{b≠0}‖η_b‖ > √2·√|G|`.  So the Shaw-Flatness bound `B ≤ √2·√|G|` is
FALSE, and it is the energy floor itself that forces the violation, through the L⁴/L² bound
`max ‖η_b‖² ≥ (q·E − |G|⁴)/(q·|G| − |G|²) → E/|G| = 3|G|−3 > 2|G|`. -/
theorem worst_period_sq_gt_two_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hc : 4 ≤ G.card)
    (hE : 3 * (G.card : ℝ) ^ 2 - 3 * G.card ≤ (addEnergy G : ℝ))
    (hq : (G.card : ℝ) ^ 2 * ((G.card : ℝ) - 2) < (Fintype.card F : ℝ) * ((G.card : ℝ) - 3)) :
    ∃ b : F, b ≠ 0 ∧ 2 * (G.card : ℝ) < ‖eta ψ G b‖ ^ 2 := by
  obtain ⟨b, hb0, hbge⟩ := exists_period_sq_ge hψ G
  refine ⟨b, hb0, ?_⟩
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set n : ℝ := (G.card : ℝ) with hndef
  have hn4 : (4 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hc
  have hqgt : n ^ 2 < q := by nlinarith [hq, hn4]
  have hqn : 0 < q * n - n ^ 2 := by nlinarith [hqgt, hn4]
  -- the energy floor (4th moment) beats the average (2nd moment) by the L⁴/L² ratio
  have hkey : 2 * n * (q * n - n ^ 2) < q * (addEnergy G : ℝ) - n ^ 4 := by
    nlinarith [hE, hq, hn4, hqgt]
  have hchain : 2 * n * (q * n - n ^ 2) < ‖eta ψ G b‖ ^ 2 * (q * n - n ^ 2) :=
    lt_of_lt_of_le hkey hbge
  exact lt_of_mul_lt_mul_right hchain (le_of_lt hqn)

/-- **Shaw Flatness is FALSE for the small-subgroup `μ_n` — unconditional, closed.** For `n = 2^m`
(`m ≥ 1`, `n ≥ 4`), a prime `p > 2^n`, a primitive `n`-th root `ω ∈ ZMod p`, a primitive additive
character `ψ`, and the prize-regime field size `n²(n−2) < p(n−3)` (true for `p ≈ n·2^128`), the
`n`-th roots of unity satisfy `∃ b ≠ 0, ‖η_b‖² > 2n` — so `max_{b≠0}‖η_b‖ > √2·√n`, refuting Shaw
Flatness.  Combines the *proven* small-subgroup energy `E(μ_n) = 3n²−3n` (`sidonModNeg_mu_n` ⟹
`addEnergy_eq_of_sidonModNeg`) with the L⁴/L² worst-period bound. -/
theorem shaw_flatness_false_mu_n {p : ℕ} [Fact p.Prime] {n m : ℕ} (hn2 : n = 2 ^ m) (hm : 1 ≤ m)
    (hp : 2 ^ n < p) (hc : 4 ≤ n) {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (hq : (n : ℝ) ^ 2 * ((n : ℝ) - 2) < (p : ℝ) * ((n : ℝ) - 3)) :
    ∃ b : ZMod p, b ≠ 0 ∧ 2 * (n : ℝ) < ‖eta ψ (nthRootsFinset n (1 : ZMod p)) b‖ ^ 2 := by
  set G : Finset (ZMod p) := nthRootsFinset n (1 : ZMod p) with hGdef
  have hn0 : n ≠ 0 := by rw [hn2]; positivity
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have h2n : 2 ≤ 2 ^ n :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hn0))
  have hp2 : 2 < p := by omega
  have hGmem : ∀ z : ZMod p, z ∈ G ↔ z ^ n = 1 := fun z => mem_nthRootsFinset hnpos 1
  have hcard : G.card = n := hω.card_nthRootsFinset
  have h2F : (2 : ZMod p) ≠ 0 := by
    intro hcontra
    have hdvd : (p : ℕ) ∣ 2 := by rw [← ZMod.natCast_eq_zero_iff]; exact_mod_cast hcontra
    have := Nat.le_of_dvd (by norm_num) hdvd; omega
  have h0 : (0 : ZMod p) ∉ G := by rw [hGmem]; simp [zero_pow hn0]
  have hneg : ∀ x ∈ G, -x ∈ G := by
    intro x hx
    rw [hGmem] at hx ⊢
    have he : Even n := by rw [hn2]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
    rw [neg_pow, he.neg_one_pow, one_mul]; exact hx
  have hS := sidonModNeg_mu_n hn2 hm hp hω hGmem
  have hEnat : addEnergy G = 3 * G.card ^ 2 - 3 * G.card :=
    addEnergy_eq_of_sidonModNeg h2F h0 hneg hS
  have hc' : 4 ≤ G.card := by rw [hcard]; exact hc
  have hsub : 3 * G.card ≤ 3 * G.card ^ 2 := by nlinarith [Nat.le_self_pow (two_ne_zero) G.card]
  have hEreal : (addEnergy G : ℝ) = 3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ) := by
    rw [hEnat, Nat.cast_sub hsub]; push_cast; ring
  have hE' : 3 * (G.card : ℝ) ^ 2 - 3 * G.card ≤ (addEnergy G : ℝ) := le_of_eq hEreal.symm
  have hq' : (G.card : ℝ) ^ 2 * ((G.card : ℝ) - 2)
      < (Fintype.card (ZMod p) : ℝ) * ((G.card : ℝ) - 3) := by
    rw [hcard, ZMod.card p]; exact hq
  obtain ⟨b, hb0, hbgt⟩ := worst_period_sq_gt_two_card hψ G hc' hE' hq'
  rw [hcard] at hbgt
  exact ⟨b, hb0, hbgt⟩

end ArkLib.ProximityGap.ShawFlatnessRefuted

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ShawFlatnessRefuted.worst_period_sq_gt_two_card
#print axioms ArkLib.ProximityGap.ShawFlatnessRefuted.shaw_flatness_false_mu_n
