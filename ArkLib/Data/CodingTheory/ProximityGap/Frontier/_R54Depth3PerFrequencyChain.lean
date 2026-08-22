/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R53Depth3ExcessHeadroom
import ArkLib.Data.CodingTheory.ProximityGap.EnergyBoundImplication
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection

/-!
# LANE B2 (#466 round 54): THE END-TO-END DEPTH-3 CHAIN — headroom atom → per-frequency
  Gauss-period bound, through the in-tree DC-subtracted machinery

Round 53 reduced the depth-3 rung to the one-sided excess bound `E ≤ 45n² − 40n`, giving the
exact `GaussianEnergyBound G 3`.  This brick chains that all the way to the object the prize
actually consumes — the per-frequency bound `‖η_b‖⁶ ≤ q·15·|G|³` for `b ≠ 0` — routing through
the in-tree DC-subtracted energy bound:

  headroom hypothesis  →  `GaussianEnergyBound G 3`   (round 53)
                       →  `DCEnergyBound G 3`         (`dcEnergyBound_of_gaussianEnergyBound`)
                       →  `‖η_b‖⁶ ≤ q·15·|G|³`, `b ≠ 0`  (`eta_pow_le_of_dcEnergyBound`).

**Why route through the DC-subtracted bound.**  The round-52/54 probes found that the RAW
energy `E₃ ≤ 15n³` is violated at *small* primes (`β ≈ 1`): e.g. `E₃/15n³ = 2.03` (`n=8,p=17`),
`16.1` (`n=16,p=17`), `22.6` (`n=32,p=97`).  But the entire excess there is the **DC term**
`|G|⁶/q` (the `b = 0` frequency `η₀ = |G|`): the DC-subtracted ratio `(E₃ − |G|⁶/q)/15n³` is
`0.018, 0.000, 0.042` at the same cells — Wick-bounded even at `β ≈ 1`.  The in-tree
`DCEnergyBound` (`q·E₃ − |G|⁶ ≤ q·Wick`) is the division-cleared prize-correct form, and the
per-frequency consumer needs only THAT (`eta_pow_le_of_dcEnergyBound` is non-vacuous at the
prize, unlike the raw route).

**Honest scope note.**  The DC term `|G|^{2r}/q` overtakes the Wick term `(2r−1)‼·|G|^r` when
`n^{2r}/q ≳ n^r`, i.e. `r ≳ log_n q = β`.  So the DC crossover that makes RAW
`GaussianEnergyBound` fail is a DEEP-`r` phenomenon (`r ≈ β ≈ 129` at prize), NOT `r = 3`:
at `r = 3`, prize scale, the DC term `|G|⁶/q = n⁵/2¹²⁸` is negligible against `45n²`, so the
round-53 raw headroom reduction is correctly shaped and its open target (`excess ≤ 45n²`) is
the genuine remaining content at `r = 3`.  The small-`β` "violations" are DC artifacts of
probing tiny primes, not obstructions at prize scale.  Deep `r` remains the wall.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 54, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R54Depth3PerFrequencyChain

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.EnergyBoundImplication
open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.Frontier.R53Depth3ExcessHeadroom

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The DC-subtracted energy bound from the headroom hypothesis.**  The round-53 excess
headroom yields the prize-correct division-cleared bound `q·E₃ − |G|⁶ ≤ q·15·|G|³`. -/
theorem dcEnergyBound_three_of_excess_headroom {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {E : ℝ} (hexc : Depth3ExcessBounded G E)
    (hhead : E ≤ 45 * (G.card : ℝ) ^ 2 - 40 * (G.card : ℝ)) :
    DCEnergyBound G 3 :=
  dcEnergyBound_of_gaussianEnergyBound
    (gaussianEnergyBound_three_of_excess_headroom hψ G hexc hhead)

/-- **THE END-TO-END DEPTH-3 SPECTRAL BOUND (round-54 main theorem).**  Under the round-53
excess-headroom hypothesis, every nontrivial Gauss period satisfies the sharp Wick per-frequency
bound `‖η_b‖⁶ ≤ q·15·|G|³` — the object the prize's moment method consumes at depth 3. -/
theorem eta_sixth_le_of_excess_headroom {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {E : ℝ} (hexc : Depth3ExcessBounded G E)
    (hhead : E ≤ 45 * (G.card : ℝ) ^ 2 - 40 * (G.card : ℝ))
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 6
      ≤ (Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3) := by
  have hdc : DCEnergyBound G 3 := dcEnergyBound_three_of_excess_headroom hψ G hexc hhead
  have h := eta_pow_le_of_dcEnergyBound hψ hdc hb
  -- rewrite `2*3 = 6` and `(2·3−1)‼ = 15`
  have hpow : (2 * 3 : ℕ) = 6 := by norm_num
  have hdf : (Nat.doubleFactorial (2 * 3 - 1) : ℝ) = 15 := by norm_num [Nat.doubleFactorial]
  rw [hpow] at h
  rw [hdf] at h
  exact h

/-- **Concrete corollary (r52 regime).**  Quadratic excess with `C ≤ 44` and `n ≥ 40` gives the
per-frequency depth-3 spectral bound directly. -/
theorem eta_sixth_le_of_quadraticExcess {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {C : ℝ} (hexc : Depth3ExcessBounded G (C * (G.card : ℝ) ^ 2))
    (hC : C ≤ 44) (hn : 40 ≤ (G.card : ℝ)) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 6 ≤ (Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3) :=
  eta_sixth_le_of_excess_headroom hψ G hexc (quadraticExcess_within_headroom G hC hn) hb

end ArkLib.ProximityGap.Frontier.R54Depth3PerFrequencyChain

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R54Depth3PerFrequencyChain.dcEnergyBound_three_of_excess_headroom
#print axioms
  ArkLib.ProximityGap.Frontier.R54Depth3PerFrequencyChain.eta_sixth_le_of_excess_headroom
#print axioms
  ArkLib.ProximityGap.Frontier.R54Depth3PerFrequencyChain.eta_sixth_le_of_quadraticExcess
