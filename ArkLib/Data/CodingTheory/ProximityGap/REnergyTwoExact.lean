/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyBridge
import ArkLib.Data.CodingTheory.ProximityGap.SidonModNegEnergyEquality

/-!
# `rEnergy G 2 = E(G)` exported, and `rEnergy(μ_n) 2 = 3n² − 3n` proven (#407)

The `r`-fold relation energy `rEnergy G r = #{(v,w) ∈ (Fin r → G)² : Σv = Σw}` (the
`SubgroupGaussSumMoment` nested-`piFinset` form) and the quadruple additive energy
`addEnergy G = #{(a,a',c,c') ∈ G⁴ : a+a' = c+c'}` (the `SubgroupGaussSumFourthMoment` form)
are the SAME `r = 2` fourth-moment census, but their equality `rEnergy G 2 = addEnergy G`
was only ever produced **inline** inside `DCEnergyRungTwo.dcEnergyBound_two_rootsOfUnity`
(as a local `have hRE`), never exported as a reusable theorem.

This file exports it as a standalone identity and pushes the consequence to the thin subgroup:

* `rEnergy_two_eq_addEnergy` — `rEnergy G 2 = addEnergy G` for **any** finite field `F`
  (read off the two fourth-moment Parseval laws `subgroup_gaussSum_moment` at `r = 2` and
  `subgroup_gaussSum_fourthMoment`; `q ≠ 0` cancels). A primitive additive character `ψ` is a
  proof device — one exists on every `ZMod p` — and does not appear in the statement's content.
* `rEnergy_two_eq_additiveEnergy` — `rEnergy G 2 = additiveEnergy G` (the Mathlib
  representation-count energy), composing the above with `additiveEnergy_eq_addEnergy`.
* `mu_n_rEnergy_two_eq` — **the payoff:** `rEnergy (μ_n) 2 = 3n² − 3n` for `n = 2^m` (`m ≥ 1`)
  and `p > 2^n`, by feeding the proven Sidon-mod-negation energy pin
  `EnergyEqualitySidonModNeg.mu_n_additiveEnergy_eq`.

## Why this is a brick, not a moment lever

This is a pure **count identity** between two combinatorial census definitions of the SAME object
(the additive 4-fold zero-sum / energy census), NOT an additive-moment cancellation bound on
`M = max_b ‖η_b‖` (which the §6 meta-theorem proves non-proving). Its value is plumbing:
the hypothesis `rEnergy G 2 = 3|G|² − 3|G|` (`hE2`) is threaded as an *assumption* through the
cross-step rung ladder (`Frontier/CrossStepRungTwo.lean`, three occurrences) and produced only
inline in `DCEnergyRungTwo`; here it becomes a discharged in-tree theorem for `μ_n`.

Scope: this pins the EXACT r = 2 energy of the thin subgroup; the worst-case sup-norm
`M(μ_n) ≤ C·√(n·log(p/n))` (CORE) stays **OPEN** — it is the worst-case single-frequency
deviation above this average L⁴ mass, the BGK/Paley √-cancellation wall.

Issue #407. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergyBridge

namespace ArkLib.ProximityGap.REnergyTwoExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`rEnergy G 2 = addEnergy G`.** The two `r = 2` fourth-moment census definitions agree:
the nested-`piFinset` relation energy equals the quadruple additive energy. Read off the two
Parseval fourth-moment laws (`∑_b ‖η_b‖⁴ = q · rEnergy G 2` and `∑_b ‖η_b‖⁴ = q · addEnergy G`),
cancelling `q = |F| ≠ 0`. The primitive character `ψ` is a proof device (one exists on every
`ZMod p`); it is absent from the statement. -/
theorem rEnergy_two_eq_addEnergy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    rEnergy G 2 = addEnergy G := by
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  -- ∑_b ‖η_b‖^(2*2) = q · rEnergy G 2
  have hP1 := subgroup_gaussSum_moment hψ G 2
  -- ∑_b ‖η_b‖^4 = q · addEnergy G
  have hP2 := subgroup_gaussSum_fourthMoment hψ G
  -- the two left-hand sides are equal (2*2 = 4)
  have hpow : (2 * 2 : ℕ) = 4 := by norm_num
  have hsum_eq : (Fintype.card F : ℝ) * (rEnergy G 2 : ℝ)
      = (Fintype.card F : ℝ) * (addEnergy G : ℝ) := by
    rw [← hP1, ← hP2, hpow]
  have hRE : (rEnergy G 2 : ℝ) = (addEnergy G : ℝ) :=
    mul_left_cancel₀ (ne_of_gt hqR) hsum_eq
  exact_mod_cast hRE

/-- **`rEnergy G 2 = additiveEnergy G`** (Mathlib representation-count energy). Composes
`rEnergy_two_eq_addEnergy` with `additiveEnergy_eq_addEnergy`. -/
theorem rEnergy_two_eq_additiveEnergy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    rEnergy G 2 = additiveEnergy G := by
  rw [rEnergy_two_eq_addEnergy hψ G, ← additiveEnergy_eq_addEnergy G]

end ArkLib.ProximityGap.REnergyTwoExact

namespace ArkLib.ProximityGap.REnergyTwoExact

open ArkLib.ProximityGap.EnergyEqualitySidonModNeg

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

/-- **`rEnergy(μ_n) 2 = 3n² − 3n`** — the exact `r = 2` relation energy of the thin 2-power
subgroup `μ_n ⊂ F_p` for `n = 2^m` (`m ≥ 1`) and `p > 2^n`. Discharges the `hE2` hypothesis
threaded through the cross-step rung ladder: combines this file's `rEnergy_two_eq_additiveEnergy`
bridge with the proven Sidon-mod-negation energy pin `mu_n_additiveEnergy_eq`. A primitive
additive character `ψ` is a proof device (one exists on every `ZMod p`). -/
theorem mu_n_rEnergy_two_eq (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    rEnergy (muN p n) 2 = 3 * n ^ 2 - 3 * n := by
  rw [rEnergy_two_eq_additiveEnergy hψ (muN p n), mu_n_additiveEnergy_eq hn2 hm hp hω]

end ArkLib.ProximityGap.REnergyTwoExact

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.REnergyTwoExact.rEnergy_two_eq_addEnergy
#print axioms ArkLib.ProximityGap.REnergyTwoExact.rEnergy_two_eq_additiveEnergy
#print axioms ArkLib.ProximityGap.REnergyTwoExact.mu_n_rEnergy_two_eq
