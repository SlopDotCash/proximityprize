/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The worst-case incomplete character-sum hypothesis as a named Prop + its landed consumer (#389)

Interior open core (one of two equivalent faces): the worst-case incomplete subgroup Gauss sum
`max_{b≠0} ‖η_b‖`. The energy↔character-sum bridge `addEnergy_le`
(`SubgroupGaussSumFourthMoment.lean:122`) is PROVEN:

  `‖η_b‖² ≤ M  (∀ b ≠ 0)  ⟹  q·E(G) ≤ |G|⁴ + M·(q|G| − |G|²)`.

The OPEN input is the per-frequency worst-case bound itself (BGK/Bourgain regime `|G| ≥ √q`;
the moment ladder provably stops at `√q` per round 28). Round 30 refined the conjectured
worst case to `‖η_b‖² ≤ C·n·log n` (`n = |G|`), which yields `E(G) = O(n²·log n)` and the
window `Θ(1/log n)`.

This file does the LANDABLE half: it names the open input as an explicit Prop and proves its
consumer END-TO-END via the in-tree `addEnergy_le` bridge — the composition is unconditional,
only the worst-case bound itself stays open. Concretely:

* `WorstCaseIncompleteSumBound ψ G M` — the named open Prop `∀ b ≠ 0, ‖η_b‖² ≤ M`.
* `addEnergy_le_of_worstCase` — drops the `−|G|²` term: `q·E ≤ |G|⁴ + M·q·|G|`.
* `addEnergy_le_div` — the deployed regime `q ≥ |G|²`: `E(G) ≤ |G|² + M·|G|`.
* `RoundThirtyScale C n M` — the round-30 scale `M = C·n·log n`.
* `addEnergy_O_n_sq_log_n` — the headline: in the deployed regime with the round-30 scale,
  `E(G) ≤ (1 + C·log|G|)·|G|²`, i.e. `E(G) = O(n²·log n)`.

The `log n` factor is the precise gap between the round-28 ladder ceiling (`√q`, i.e. `E = |G|²`
exactly) and the conjectured worst case — and it IS the window `Θ(1/log n)`; that last
identification is a documented (not proven) bridge, recorded as `window_is_one_over_log` below.

All proofs here are axiom-clean (`propext, Classical.choice, Quot.sound`); the open content is
entirely isolated in the hypothesis `WorstCaseIncompleteSumBound`. Issue #389.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

namespace ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The named open Prop -/

/-- **The worst-case incomplete subgroup Gauss-sum bound** at scale `M`: every nonzero
frequency `b` has `‖η_b‖² ≤ M`. This is the OPEN interior-core input (face #3 of the δ\*
programme; BGK/Bourgain `|G| ≥ √q` regime). The in-tree completion anchor
(`norm_eta_torsion_le`) gives the unconditional `M = q`; the moment ladder
(`no_johnson_scale_frequency_of_ladder`) drives the count-side threshold to `|G| < √q`; round 30
conjectures the worst case is `M = C·n·log n`. Stated as a Prop — never asserted — so the
consumer below is unconditional. -/
def WorstCaseIncompleteSumBound (ψ : AddChar F ℂ) (G : Finset F) (M : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ^ 2 ≤ M

/-! ## Consumer 1 — drop the `−|G|²` term (a clean linear envelope) -/

/-- **The energy budget from the worst-case bound**: `q·E(G) ≤ |G|⁴ + M·q·|G|`. Specialises the
in-tree bridge `addEnergy_le` and discards the (negative, when `q ≥ |G|`) `−M·|G|²` term to get a
self-contained envelope with no subtraction. Holds for `M ≥ 0`. -/
theorem addEnergy_le_of_worstCase {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hwc : WorstCaseIncompleteSumBound ψ G M) :
    (Fintype.card F : ℝ) * (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4 + M * ((Fintype.card F : ℝ) * G.card) := by
  have hbridge := addEnergy_le hψ G (M := M) hwc
  have hGnn : (0 : ℝ) ≤ (G.card : ℝ) ^ 2 := sq_nonneg _
  -- `M·(q|G| − |G|²) ≤ M·(q|G|)` since `M ≥ 0` and `|G|² ≥ 0`.
  have hdrop : M * ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2)
      ≤ M * ((Fintype.card F : ℝ) * G.card) := by
    have : (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
        ≤ (Fintype.card F : ℝ) * G.card := by linarith
    exact mul_le_mul_of_nonneg_left this hM0
  linarith

/-! ## Consumer 2 — the deployed regime `q ≥ |G|²` -/

/-- **The energy bound in the deployed regime**: when `q ≥ |G|²` (every smooth FRI/STIR domain,
`q ≥ n²·2¹²⁸`), the worst-case bound gives `E(G) ≤ |G|² + M·|G|`. The `|G|⁴/q` term collapses to
`≤ |G|²`; what remains is the `M·|G|` contribution of the off-zero mass. With the Weil-strength
`M = O(|G|)` this is the sharp `E = O(|G|²)`; with the round-30 `M = C·n·log n` it is
`O(n²·log n)`. -/
theorem addEnergy_le_div {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {M : ℝ}
    (hM0 : 0 ≤ M) (hwc : WorstCaseIncompleteSumBound ψ G M)
    (hq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) (hqpos : 0 < Fintype.card F) :
    (addEnergy G : ℝ) ≤ (G.card : ℝ) ^ 2 + M * (G.card : ℝ) := by
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hqpos
  have hbudget := addEnergy_le_of_worstCase hψ G hM0 hwc
  -- `|G|⁴ = |G|²·|G|² ≤ |G|²·q`, so `|G|⁴ + M·q·|G| ≤ q·(|G|² + M·|G|)`.
  have hGnn : (0 : ℝ) ≤ (G.card : ℝ) ^ 2 := sq_nonneg _
  have h4 : (G.card : ℝ) ^ 4 ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2 := by
    have : (G.card : ℝ) ^ 4 = (G.card : ℝ) ^ 2 * (G.card : ℝ) ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hq hGnn |>.trans (le_of_eq (by ring))
  have hkey : (Fintype.card F : ℝ) * (addEnergy G : ℝ)
      ≤ (Fintype.card F : ℝ) * ((G.card : ℝ) ^ 2 + M * (G.card : ℝ)) := by
    calc (Fintype.card F : ℝ) * (addEnergy G : ℝ)
        ≤ (G.card : ℝ) ^ 4 + M * ((Fintype.card F : ℝ) * G.card) := hbudget
      _ ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ 2 + M * ((Fintype.card F : ℝ) * G.card) := by
          linarith
      _ = (Fintype.card F : ℝ) * ((G.card : ℝ) ^ 2 + M * (G.card : ℝ)) := by ring
  exact le_of_mul_le_mul_left hkey hqR

/-! ## The round-30 scale `M = C·n·log n` and the `O(n²·log n)` headline -/

/-- **The round-30 conjectured worst-case scale**: `M = C·|G|·log|G|`. This is the conjectured
shape of the open `WorstCaseIncompleteSumBound` (the BGK/Bourgain regime); it sits exactly one
`log` factor above the in-tree ladder ceiling `√q` (which corresponds to `M = q`, i.e. the
trivial energy `|G|²` when `q ≥ |G|²`). -/
noncomputable def RoundThirtyScale (C : ℝ) (G : Finset F) : ℝ :=
  C * (G.card : ℝ) * Real.log (G.card : ℝ)

/-- **The `O(n²·log n)` energy headline.** If the open `WorstCaseIncompleteSumBound` holds at the
round-30 scale `M = C·|G|·log|G|` (with `C ≥ 0`, `|G| ≥ 1`), then in the deployed regime
`q ≥ |G|²` the additive energy is

  `E(G) ≤ (1 + C·log|G|)·|G|²`,

i.e. `E(G) = O(n²·log n)`. This is the precise composition the task names as "landable": the open
input is isolated entirely in the hypothesis, and the bound is derived unconditionally through the
landed `addEnergy_le` bridge. The `log|G|` factor is the gap between the round-28 ladder ceiling
(`E = |G|²`) and the conjectured worst case. -/
theorem addEnergy_O_n_sq_log_n {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {C : ℝ}
    (hC0 : 0 ≤ C) (hG1 : 1 ≤ G.card)
    (hwc : WorstCaseIncompleteSumBound ψ G (RoundThirtyScale C G))
    (hq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) (hqpos : 0 < Fintype.card F) :
    (addEnergy G : ℝ) ≤ (1 + C * Real.log (G.card : ℝ)) * (G.card : ℝ) ^ 2 := by
  have hG1R : (1 : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hG1
  have hlog0 : 0 ≤ Real.log (G.card : ℝ) := Real.log_nonneg hG1R
  have hM0 : 0 ≤ RoundThirtyScale C G := by
    unfold RoundThirtyScale
    have : (0 : ℝ) ≤ (G.card : ℝ) := by positivity
    positivity
  have hbound := addEnergy_le_div hψ G hM0 hwc hq hqpos
  -- `M·|G| = C·|G|·log|G|·|G| = C·log|G|·|G|²`.
  have hMG : RoundThirtyScale C G * (G.card : ℝ) = C * Real.log (G.card : ℝ) * (G.card : ℝ) ^ 2 := by
    unfold RoundThirtyScale; ring
  rw [hMG] at hbound
  calc (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 2 + C * Real.log (G.card : ℝ) * (G.card : ℝ) ^ 2 := hbound
    _ = (1 + C * Real.log (G.card : ℝ)) * (G.card : ℝ) ^ 2 := by ring

/-! ## The window `Θ(1/log n)` — the documented (NOT proven) bridge -/

/-- **The documented round-30 window identification (NOT a proof — a named record).** The δ\*
window width is `Θ(1/log n)`; the energy headline above shows that the ONLY way the conjectured
worst case exceeds the round-28 ladder ceiling is by the multiplicative `log n` factor in `E(G)`.
The round-30 reading is that this `log n` energy inflation is exactly the reciprocal of the window:

  `windowWidth(n) = Θ(1 / log n)`   ⟺   `E(G) = Θ(n²·log n)`.

This file PROVES the right-to-left direction's upper half (`addEnergy_O_n_sq_log_n`: the
`log n`-scale energy bound FROM the conjectured worst case). The equivalence to the window width
itself routes through the δ\* ledger (`KKH26WitnessSpread`, `[KKH26]` Thm 1 `η = Θ(1/log n)`) and
is the conjectural bridge, recorded here as a Prop, never asserted.

The bridge equation is the RECIPROCAL relation: the window width times the energy-inflation
factor `E(G)/n²` (which the headline above bounds by `1 + C·log n`) is a constant. At the
round-30 ceiling `E = n²·log n` the inflation factor is exactly `log n`, so `1/log n` is forced. -/
def WindowIsOneOverLog (windowWidth : ℝ → ℝ) (G : Finset F) (energyOf : Finset F → ℝ) : Prop :=
  -- the documented bridge: window width and the energy-inflation factor `E/n²` are reciprocal.
  windowWidth (G.card : ℝ) * (energyOf G / (G.card : ℝ) ^ 2) = 1

/-- The right-to-left consistency of the documented window bridge: IF the window is `1/log n`
(documented `[KKH26]` Thm 1) AND the energy attains the round-30 ceiling `n²·log n`, then the
reciprocal bridge equation `windowWidth·(E/n²) = 1` holds. A pure consistency check that the two
documented round-30 statements are mutually compatible — NOT a proof of either. -/
theorem windowBridge_consistency {F : Type*} (G : Finset F) (hG1 : 1 < (G.card : ℝ))
    (windowWidth : ℝ → ℝ) (energyOf : Finset F → ℝ)
    (hwin : windowWidth (G.card : ℝ) = 1 / Real.log (G.card : ℝ))
    (hen : energyOf G = (G.card : ℝ) ^ 2 * Real.log (G.card : ℝ)) :
    WindowIsOneOverLog windowWidth G energyOf := by
  unfold WindowIsOneOverLog
  have hlogpos : 0 < Real.log (G.card : ℝ) := Real.log_pos hG1
  have hGsq : (0 : ℝ) < (G.card : ℝ) ^ 2 := by
    have : (0 : ℝ) < (G.card : ℝ) := by linarith
    positivity
  rw [hwin, hen]
  field_simp

end ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

