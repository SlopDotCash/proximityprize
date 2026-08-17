/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BetaGatedRatioGate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDilationDescentTelescope

/-!
# Door-(iv) Lane-3: what the open `√2`-gate BUYS — telescoping the per-level ratio to the prize (#444)

`_BetaGatedRatioGate` isolated the corrected open hypothesis `LevelRatioBoundNZ ψ G ζ μ (√2)` (the
`b ≠ 0` per-level sup-norm ratio bound, `≤ √2` at every level of the dyadic tower) and machine-checked
that the *all-`b`* version is FALSE (`not_levelRatioBound_sqrt2`, the `b = 0` carrier doubles).  What it
did NOT record is the **consequence** of the corrected hypothesis: telescoping the per-level `√2` ratio
down the `μ = log₂ n` tower lands exactly on the prize square-root floor.

This file supplies that bridge by feeding `LevelRatioBoundNZ` into the parametric telescope
(`_DoorIVDilationDescentTelescope`, `232650e42`):

> **`LevelRatioBoundNZ ψ G ζ μ (√2)`  ⟹  `M(level μ) ≤ (√2)^μ · M(level 0) = √(2^μ) · M_0`.**

At `2^μ = n` this is `M(μ_n) ≤ √n · M_0` — the **prize square-root scale** (the `√(n·log)` floor is the
`x`-gated refinement; the bare `√n` is the geometric content).  So the corrected `b ≠ 0` gate is exactly
"shave the per-level factor from `2` (trivial, `2^μ = n`) to `√2` (prize, `(√2)^μ = √n`)" — and the
factor-`2` doubling that the dilation probes measured at the worst frequency (`ρ(b*) = 1`,
`_DoorIVTwoDilateNoJointExtreme`) is precisely the obstruction to the `√2` gate.

This is the "what the open door buys" capstone: a clean, certain reduction of the prize-scale descent to
the single open per-level inequality `LevelRatioBoundNZ … √2`.  It does NOT prove that inequality (which
is OPEN = the prize), makes NO cancellation / completion / moment / anti-concentration / capacity claim,
and CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.DoorIVDilationDescentTelescope

namespace ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The level-`k` worst nonzero period as the supremum used by `LevelRatioBoundNZ`:
`M_k = ⨆_{c ≠ 0} ‖eta ψ (levelTower ψ G ζ k) c‖`. -/
noncomputable def levelWorst (ψ : AddChar F ℂ) (G : Finset F) (ζ : F) (k : ℕ) : ℝ :=
  ⨆ c : { c : F // c ≠ 0 }, ‖eta ψ (levelTower ψ G ζ k) (c : F)‖

/-- **`M_k ≥ 0`.**  The level worst period is a supremum of norms over a nonempty subtype (`F` is a
field, hence has a nonzero element), so it is nonnegative. -/
theorem levelWorst_nonneg [Nontrivial F] (ψ : AddChar F ℂ) (G : Finset F) (ζ : F) (k : ℕ) :
    0 ≤ levelWorst ψ G ζ k := by
  unfold levelWorst
  obtain ⟨c, hc⟩ := exists_ne (0 : F)
  refine le_ciSup_of_le ?_ ⟨c, hc⟩ (norm_nonneg _)
  exact Set.Finite.bddAbove (Set.finite_range _)

/-- **The corrected `b ≠ 0` ratio bound is a per-level doubling-or-better step on `M_k`.**  If
`LevelRatioBoundNZ ψ G ζ μ r` holds, then for every level `k < μ` the level worst period satisfies
`M_{k+1} ≤ r · M_k`: each `‖eta (level k+1) b‖` (`b ≠ 0`) is `≤ r · M_k`, so their supremum is too. -/
theorem levelWorst_step_of_levelRatioBoundNZ [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} {μ : ℕ} {r : ℝ}
    (hr : LevelRatioBoundNZ ψ G ζ μ r) {k : ℕ} (hk : k < μ) :
    levelWorst ψ G ζ (k + 1) ≤ r * levelWorst ψ G ζ k := by
  obtain ⟨c₀, hc₀⟩ := exists_ne (0 : F)
  haveI : Nonempty { c : F // c ≠ 0 } := ⟨⟨c₀, hc₀⟩⟩
  unfold levelWorst
  apply ciSup_le
  rintro ⟨b, hb⟩
  exact hr k hk b hb

/-- **★ Telescoping the corrected `√2`-gate to the prize square-root scale.**  If the corrected open
hypothesis `LevelRatioBoundNZ ψ G ζ μ (√2)` holds, then the level-`μ` worst period obeys the
prize-scale bound `M_μ ≤ (√2)^μ · M_0`.  At `2^μ = n` this is `M(μ_n) ≤ √n · M_0` — the geometric
square-root floor the prize asks for.  Pure assembly: the per-level `√2` step (from
`levelWorst_step_of_levelRatioBoundNZ`) fed into `telescope_per_level_factor` with `c = √2 ≥ 1`. -/
theorem levelWorst_le_sqrt2_pow_mul_of_xgate [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} (μ : ℕ)
    (hr : LevelRatioBoundNZ ψ G ζ μ (Real.sqrt 2)) :
    levelWorst ψ G ζ μ ≤ (Real.sqrt 2) ^ μ * levelWorst ψ G ζ 0 := by
  -- extend the per-level step (valid for k < μ) to a total `∀ k` step by capping the index at μ.
  -- telescope only consumes the steps with k < μ along the chain 0 → μ, so a total surrogate works.
  set M : ℕ → ℝ := fun k => levelWorst ψ G ζ (min k μ) with hM
  have hMpos : ∀ k, 0 ≤ M k := fun k => levelWorst_nonneg ψ G ζ (min k μ)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hstep : ∀ k, M (k + 1) ≤ Real.sqrt 2 * M k := by
    intro k
    by_cases hk : k < μ
    · have hmin1 : min (k + 1) μ = min k μ + 1 := by omega
      have hmink : min k μ = k := by omega
      simp only [hM, hmin1, hmink]
      have := levelWorst_step_of_levelRatioBoundNZ hr hk
      simpa [hmink] using this
    · -- past the cap both indices are μ; the step is `M_μ ≤ √2 · M_μ`, true since √2 ≥ 1, M_μ ≥ 0.
      have hmin1 : min (k + 1) μ = μ := by omega
      have hmink : min k μ = μ := by omega
      simp only [hM, hmin1, hmink]
      nlinarith [levelWorst_nonneg ψ G ζ μ, hsqrt1]
  have htel := telescope_per_level_factor M hMpos hsqrt1 hstep μ
  have hMμ : M μ = levelWorst ψ G ζ μ := by simp [hM]
  have hM0 : M 0 = levelWorst ψ G ζ 0 := by simp [hM]
  rwa [hMμ, hM0] at htel

end ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge
