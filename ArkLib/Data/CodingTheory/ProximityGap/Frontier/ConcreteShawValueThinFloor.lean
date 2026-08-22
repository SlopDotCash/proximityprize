/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteShawValueBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.WorstPeriodSqrtNFloor

/-!
# The CLEAN thin-regime Shaw-value floor `1/√(2L) ≤ Sh(M(μ_n))` (#444)

**Lane-2 capstone rung — frontier-movement, wiring an orphaned proven floor into the corridor.**

`ConcreteShawValueBridge` already threads the *raw RMS* Parseval floor
`√(n(q−n)/(q−1)) ≤ M(μ_n)` and the trivial ceiling `M(μ_n) ≤ n` into the Shaw-value normalization,
giving the concrete corridor `√((q−n)/(q−1)·L⁻¹) .. √(n/L)` around `Sh(M(μ_n))`.  But the *clean*
denominator-free thin-regime floor

> `WorstPeriodSqrtNFloor.worstPeriod_ge_sqrt_half_n` :  `√(n/2) ≤ M(μ_n)`   (when `q ≥ 2n`)

was proven and then left **orphaned** — no file imported it, so the clean Plancherel-floor rung the
Shaw-value capstone names (`M ≥ √n` ⟹ normalized floor `1/√L`, independent of `n`) had never been
instantiated on the REAL worst period in the prize regime.  This file closes that gap.

## What this supplies

For the actual Gauss-period worst frequency `M(μ_n) = worstPeriod ψ G hne`, in the thin prize regime
`q ≥ 2n` (automatic at `q = n^β`, `β > 1`):

* `shawValue_worstPeriod_half_n_floor` — the clean **`√(n/2)/scale ≤ Sh(M(μ_n))`** floor, threading
  `worstPeriod_ge_sqrt_half_n` through Shaw normalization.
* `shawValue_worstPeriod_floor_clean` — the closed form: that lower endpoint **equals `1/√(2L)`**,
  *independent of `n`* (the Plancherel floor lands the normalized Shaw value at `1/√(2·log(p/n))`).
* `shawValue_worstPeriod_clean_corridor` — the clean two-sided corridor
  `1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)` on the real character sum.  The open prize is exactly the demand
  to collapse this `√n`-wide corridor (lower `O(1/√L)`, upper `√(n/L)`) to an absolute constant.

## Honesty (scope)

Pure normalization arithmetic + one orphaned proven floor.  The floor is unconditional (Parseval,
thin-regime `q ≥ 2n`); the ceiling is unconditional (triangle inequality).  NO anti-concentration,
NO completion, NO moment, NO cancellation, NO capacity claim.  CORE `M(μ_n) ≤ C·√(n·log(p/n))`
(equivalently `Sh(M(μ_n)) = O(1)`) stays OPEN; it lives strictly inside the proven
`1/√(2L) .. √(n/L)` corridor supplied here.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.Frontier.ShawValueCapstone
open ProximityGap.Frontier.ConcreteMomentAssembly
open ProximityGap.Frontier.ConcreteParsevalLower
open ProximityGap.Frontier.ConcreteShawValueBridge
open ProximityGap.Frontier.WorstPeriodSqrtNFloor

namespace ProximityGap.Frontier.ConcreteShawValueThinFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The clean `√(n/2)/scale` Shaw-value floor on the real worst period (thin regime).**
For `q ≥ 2n` (and `n ≥ 1`), the clean denominator-free floor `√(n/2) ≤ M(μ_n)`
(`worstPeriod_ge_sqrt_half_n`) passes through Shaw normalization:
`√(n/2) / scale ≤ Sh(M(μ_n))`.  This is the clean Plancherel-floor rung the capstone names,
instantiated on the REAL character sum. -/
theorem shawValue_worstPeriod_half_n_floor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty)
    (hn1 : 1 ≤ (G.card : ℝ))
    (hq2n : 2 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) {L : ℝ}
    (hs : 0 < prizeScale (G.card : ℝ) L) :
    Real.sqrt ((G.card : ℝ) / 2) / prizeScale (G.card : ℝ) L
      ≤ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L := by
  unfold shawValue
  exact div_le_div_of_nonneg_right
    (worstPeriod_ge_sqrt_half_n hψ G hne hn1 hq2n) (le_of_lt hs)

/-- **Closed form of the clean lower endpoint: `√(n/2)/scale = 1/√(2L)`.**  The thin-regime
Plancherel floor lands the normalized Shaw value at `1/√(2·log(p/n))`, *independent of `n`*.
Mechanism: `√(n/2)/√(n·L) = √(n/2)/(√n·√L) = (1/√2)/√L = 1/√(2L)`. -/
theorem floor_half_bracket_eq {n L : ℝ} (hn : 0 < n) :
    Real.sqrt (n / 2) / prizeScale n L = 1 / Real.sqrt (2 * L) := by
  unfold prizeScale
  rw [show n / 2 = n * (1 / 2) by ring, Real.sqrt_mul (le_of_lt hn),
    Real.sqrt_mul (le_of_lt hn) L]
  rw [show (2 : ℝ) * L = 2 * L by ring, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) L]
  have hsn : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
  have hs2 : Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div' 1 (by norm_num), Real.sqrt_one]
  rw [hs2]
  field_simp

/-- **The clean thin-regime Shaw-value floor in closed form: `1/√(2L) ≤ Sh(M(μ_n))`.**  Combines
`shawValue_worstPeriod_half_n_floor` with the closed form `floor_half_bracket_eq`.  In the thin prize
regime, the normalized worst period is at least `1/√(2L)`, *independent of `n`* — the cleanest
citable floor rung of the Lane-2 capstone. -/
theorem shawValue_worstPeriod_floor_clean {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty)
    (hn1 : 1 ≤ (G.card : ℝ))
    (hq2n : 2 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) {L : ℝ}
    (hs : 0 < prizeScale (G.card : ℝ) L) :
    1 / Real.sqrt (2 * L) ≤ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L := by
  have hn0 : 0 < (G.card : ℝ) := lt_of_lt_of_le one_pos hn1
  have hfloor := shawValue_worstPeriod_half_n_floor hψ G hne hn1 hq2n hs
  rwa [floor_half_bracket_eq hn0] at hfloor

/-- **The clean two-sided Shaw-value corridor on the real worst period (thin regime).**
`1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)`, both endpoints in closed form.  The lower endpoint is the
`n`-independent Plancherel floor `1/√(2L)` (thin-regime); the upper endpoint is the trivial-ceiling
scale `√(n/L)`.  The prize target `Sh(M(μ_n)) = O(1)` lives strictly inside this proven corridor,
whose multiplicative width is `√(n/2)` — exactly the open gap CORE must collapse. -/
theorem shawValue_worstPeriod_clean_corridor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty)
    (hn1 : 1 ≤ (G.card : ℝ))
    (hq2n : 2 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) {L : ℝ} (hL : 0 < L)
    (hs : 0 < prizeScale (G.card : ℝ) L) :
    1 / Real.sqrt (2 * L) ≤ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L
      ∧ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L
          ≤ Real.sqrt ((G.card : ℝ) / L) := by
  have hn0 : 0 < (G.card : ℝ) := lt_of_lt_of_le one_pos hn1
  refine ⟨shawValue_worstPeriod_floor_clean hψ G hne hn1 hq2n hs, ?_⟩
  have hceil := shawValue_worstPeriod_le_of_card (ψ := ψ) G hne hs
  rwa [ceiling_bracket_eq hn0 hL] at hceil

/-- **The clean normalized Shaw-value corridor is `√(2n)`-wide.**  The proven thin-regime
endpoints in `shawValue_worstPeriod_clean_corridor` are `1/√(2L)` and `√(n/L)`.  Their ratio is
exactly `√(2n)`, so normalization by the prize scale has not hidden the open gap: the unconditional
Lane-2 bracket is still `√n`-wide (up to the harmless `√2`).  Closing this to `O(1)` is exactly the
open door-(iv) CORE bound, not something supplied here. -/
theorem clean_corridor_width_eq {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    Real.sqrt (n / L) / (1 / Real.sqrt (2 * L)) = Real.sqrt (2 * n) := by
  have h2L : 0 < 2 * L := by positivity
  have hs2L : Real.sqrt (2 * L) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h2L)
  field_simp [hs2L]
  rw [Real.sqrt_div (le_of_lt hn) L]
  rw [Real.sqrt_mul (le_of_lt hL) 2]
  rw [Real.sqrt_mul (le_of_lt hn) 2]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hL)]

end ProximityGap.Frontier.ConcreteShawValueThinFloor

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ConcreteShawValueThinFloor.shawValue_worstPeriod_half_n_floor
#print axioms ProximityGap.Frontier.ConcreteShawValueThinFloor.floor_half_bracket_eq
#print axioms ProximityGap.Frontier.ConcreteShawValueThinFloor.shawValue_worstPeriod_floor_clean
#print axioms ProximityGap.Frontier.ConcreteShawValueThinFloor.shawValue_worstPeriod_clean_corridor
#print axioms ProximityGap.Frontier.ConcreteShawValueThinFloor.clean_corridor_width_eq
