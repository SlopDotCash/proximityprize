/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The first-moment / de-Finetti linear constraint on the Gauss periods (#407)

The crack-audit's top closure re-attack (CRACK 7) is to prove the BGK floor `max_{b≠0}‖η_b‖ ≤
√(2n·log(p/n))` as an **extreme-value theorem** for the *exchangeable de-Finetti* period family: the
periods `η_b = Σ_{x∈G} ψ(bx)` over the nonzero frequencies are exchangeable white-noise with bulk
Gaussian (Wick) moments, and the floor is the Gumbel max of `m = (q−1)/n` such variables under the
**linear constraints** of their first two moments. The second-moment constraint is landed
(`GaussPeriodParsevalFloor`: `Σ_{b≠0} ‖η_b‖² = q·n − n²`). This file lands the **first-moment**
constraint, the other half of the de-Finetti data:

> `Σ_{b≠0} η_b = −|G|`  (for any `0 ∉ G`, primitive `ψ`).

Proof: `Σ_{b∈F} η_b = Σ_{y∈G} Σ_b ψ(by) = Σ_{y∈G} 0 = 0` (character orthogonality
`AddChar.sum_mulShift`, since `0 ∉ G ⟹ y ≠ 0`), and `η_0 = |G|` (`eta_zero`); subtract. So the
nonzero periods have mean `−n/(q−1) ≈ 0` and (with Parseval) variance `≈ n` — the exact two-moment
constraint the EVT/Gumbel concentration consumes. Axiom-clean. Issue #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction

namespace ProximityGap.Frontier.GaussPeriodFirstMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The total period sum vanishes** when `0 ∉ G`: `Σ_{b∈F} η_b = 0`. Character orthogonality —
each `y ∈ G` is nonzero, so `Σ_b ψ(by) = 0`. -/
theorem sum_eta_eq_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} (hG : (0 : F) ∉ G) :
    ∑ b : F, eta ψ G b = 0 := by
  simp only [eta]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y hy
  have hy0 : y ≠ 0 := fun h => hG (h ▸ hy)
  have h := AddChar.sum_mulShift y hψ
  rw [if_neg hy0] at h
  simpa using h

/-- **The first-moment / de-Finetti linear constraint:** `Σ_{b≠0} η_b = −|G|` (for `0 ∉ G`,
primitive `ψ`). Together with the Parseval second moment `Σ_{b≠0}‖η_b‖² = q·n − n²` this is the
exact two-moment data the EVT/Gumbel concentration of the exchangeable period family consumes
(CRACK 7 closure route). -/
theorem subgroup_gaussSum_firstMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hG : (0 : F) ∉ G) :
    ∑ b ∈ Finset.univ.erase (0 : F), eta ψ G b = -(G.card : ℂ) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : F)), sum_eta_eq_zero hψ hG, eta_zero]
  ring

end ProximityGap.Frontier.GaussPeriodFirstMoment

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.GaussPeriodFirstMoment.sum_eta_eq_zero
#print axioms ProximityGap.Frontier.GaussPeriodFirstMoment.subgroup_gaussSum_firstMoment
