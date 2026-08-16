/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatedTelescopeBridge

/-!
# Door-(iv) Lane-3: the `XGatedRatio` open hypothesis reduces END-TO-END to the prize `√n` floor (#444)

`_BetaGatedRatioGate` named `XGatedRatio ψ G ζ μ x₀ lnm` as THE corrected open object — the
`x = n/ln m`-gated per-level ratio bound, "the tower phrasing of the sub-Gaussian floor `M ≲ √(n ln m)`"
— and the `_DoorIVXGatedTelescopeBridge` (`5840b2e42`) telescoped its conclusion `LevelRatioBoundNZ … √2`
to the prize scale.  This file CHAINS the two so the reduction is stated directly on the named open
hypothesis:

> **`XGatedRatio ψ G ζ μ x₀ lnm`  ∧  (the `x`-gate holds at every level `k ≤ μ`)
>   ⟹  `M(level μ) ≤ (√2)^μ · M(level 0) = √(2^μ)·M_0`.**

At `2^μ = n` this is `M(μ_n) ≤ √n · M_0`: discharging the single open `XGatedRatio` (the per-level
`√2` ratio in the cancellation regime) yields the prize square-root floor.  This is the citable
end-to-end "what the open door buys" statement on the object `_BetaGatedRatioGate` actually named open.

It does NOT discharge `XGatedRatio` (which is OPEN = the prize), makes NO cancellation / completion /
moment / anti-concentration / capacity claim, and CORE stays OPEN.  Pure forward-chaining:
`XGatedRatio` unfolds to `(gate) → LevelRatioBoundNZ … √2`; feed the gate, then the telescope bridge.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge

namespace ArkLib.ProximityGap.Frontier.DoorIVXGatedPrizeReduction

/-- `(√2)^μ = √(2^μ)`: the geometric factor in the prize reading, by induction via `√` multiplicativity. -/
private theorem sqrt2_pow_eq (μ : ℕ) : (Real.sqrt 2) ^ μ = Real.sqrt ((2 : ℝ) ^ μ) := by
  induction μ with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ih, ← Real.sqrt_mul (by positivity)]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **End-to-end reduction of the named open `XGatedRatio` hypothesis to the prize `√n` scale.**
Given the corrected open hypothesis `XGatedRatio ψ G ζ μ x₀ lnm` and the assumption that its
`x`-gate is met (every tower level `k ≤ μ` sits in the cancellation regime `x₀·lnm ≤ |level k|`), the
level-`μ` worst period obeys the prize-scale geometric bound `M_μ ≤ (√2)^μ · M_0`.

Forward chain: `XGatedRatio` is by definition `(gate) → LevelRatioBoundNZ ψ G ζ μ (√2)`; supplying the
gate yields the corrected `√2` ratio bound, which `levelWorst_le_sqrt2_pow_mul_of_xgate` telescopes to
`M_μ ≤ (√2)^μ · M_0`. -/
theorem levelWorst_le_sqrt2_pow_mul_of_xGatedRatio [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} {μ : ℕ} {x₀ lnm : ℝ}
    (hx : XGatedRatio ψ G ζ μ x₀ lnm)
    (hgate : ∀ k : ℕ, k ≤ μ → x₀ * lnm ≤ ((levelTower ψ G ζ k).card : ℝ)) :
    levelWorst ψ G ζ μ ≤ (Real.sqrt 2) ^ μ * levelWorst ψ G ζ 0 :=
  levelWorst_le_sqrt2_pow_mul_of_xgate μ (hx hgate)

/-- **The reduction reads as the prize floor at `n = 2^μ`.**  Rewriting the geometric factor
`(√2)^μ = √(2^μ)` (nonneg base), the `XGatedRatio` reduction gives `M_μ ≤ √(2^μ) · M_0` — i.e.
`M(μ_n) ≤ √n · M_0` at `n = 2^μ`, the prize square-root scale.  Makes the "buys the prize" reading
explicit. -/
theorem levelWorst_le_sqrt_two_pow_mul_of_xGatedRatio [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} {μ : ℕ} {x₀ lnm : ℝ}
    (hx : XGatedRatio ψ G ζ μ x₀ lnm)
    (hgate : ∀ k : ℕ, k ≤ μ → x₀ * lnm ≤ ((levelTower ψ G ζ k).card : ℝ)) :
    levelWorst ψ G ζ μ ≤ Real.sqrt ((2 : ℝ) ^ μ) * levelWorst ψ G ζ 0 := by
  have hchain := levelWorst_le_sqrt2_pow_mul_of_xGatedRatio hx hgate
  rwa [sqrt2_pow_eq μ] at hchain

end ArkLib.ProximityGap.Frontier.DoorIVXGatedPrizeReduction
