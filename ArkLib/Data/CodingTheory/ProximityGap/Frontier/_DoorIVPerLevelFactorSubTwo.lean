/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVTwoDilateNoJointExtreme
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatePrizeBudget

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Door-(iv) Lane-3: per-level factor bookkeeping for the two-dilate recursion (#444)

The empirical door-(iv) object now lives at the dyadic recursion

`M_n = S(b*) + S(g b*)`,

where `Smax = M_{n/2}` is the thinner-level marginal maximum.  The probe
`probe_dooriv_perlevel_factor_law.py` measured the normalized per-level multiplier

`c_n = M_n / M_{n/2}`

and found it stable near `√2`, strictly below the trivial co-peak ceiling `2`, and not drifting upward
toward the Johnson/trivial doubling wall.  This file does **not** kernel any empirical numeric claim.
It records the real-algebra bookkeeping that makes that probe citable:

* `H ≤ 2 Smax` is exactly `c ≤ 2` once `H = c Smax` and `Smax > 0`.
* a strict two-dilate no-co-peak gap `H < 2 Smax` is exactly `c < 2`.
* the corrected `√2` gate already landed in `_DoorIVXGatePrizeBudget`: once every per-level factor is
  bounded by `√2`, the telescope gives the prize-shaped `C √(n L)` budget.

No CORE upper bound, cancellation, completion, moment, anti-concentration, or capacity claim is made.
The open content remains the arithmetic proof of the `√2` per-level gate.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.DoorIVTwoDilateNoJointExtreme
open ArkLib.ProximityGap.Frontier.DoorIVXGatePrizeBudget
open ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge

/-- **Per-level factor ceiling from the two-dilate envelope.**  If the measured two-dilate maximum is
written as `H = c·Smax` with positive thinner-level maximum `Smax`, then the unconditional envelope
`H ≤ 2·Smax` is exactly the normalized ceiling `c ≤ 2`.  This packages the probe's ratio
`c(n)=M(n)/M(n/2)` in the same units as the no-co-peak theorem. -/
theorem perLevelFactor_le_two_of_dilate_le_two_mul
    {H Smax c : ℝ} (hSmax : 0 < Smax) (hH : H = c * Smax) (hbound : H ≤ 2 * Smax) :
    c ≤ 2 := by
  nlinarith

/-- **Strict no-co-peak gap ⇔ strict sub-doubling per-level factor.**  With `H = c·Smax` and
`Smax > 0`, the strict two-dilate gap `H < 2·Smax` is equivalent to `c < 2`.  Thus the empirical
statement `M(n)/M(n/2) < 2` is not a new analytic assumption: it is the normalized form of the
already-kernelled no-co-peak obstruction. -/
theorem perLevelFactor_lt_two_iff_dilate_lt_two_mul
    {H Smax c : ℝ} (hSmax : 0 < Smax) (hH : H = c * Smax) :
    c < 2 ↔ H < 2 * Smax := by
  constructor
  · intro hc
    nlinarith
  · intro hHlt
    nlinarith

/-- **No-co-peak certificate as a normalized factor bound.**  Applying
`not_both_max_of_lt_two_mul` to a two-dilate frequency with envelope `H = c·Smax`, `c < 2`, says the
normalized sub-doubling factor rules out a perfect joint marginal extreme at that same frequency. -/
theorem no_copeak_of_perLevelFactor_lt_two
    {ι : Type*} {s : ι → ℝ} {σ : ι → ι} {Smax c : ℝ} {b : ι}
    (hc : c < 2) (hSmax : 0 < Smax)
    (hfactor : twoDilate s σ b = c * Smax) :
    s b + s (σ b) < 2 * Smax := by
  exact not_both_max_of_lt_two_mul hc hSmax (le_of_eq hfactor)

/-- **The `√2` factor is a strict sub-doubling factor.**  This is the scalar separation that the
per-level-factor probe localizes: the prize gate `√2` is genuinely below the co-peak ceiling `2`. -/
theorem sqrt_two_lt_two : Real.sqrt 2 < (2 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **Prize budget from the normalized `√2` per-level factor.**  This restates the existing corrected
x-gate capstone in the per-level-factor language: once the single open arithmetic gate supplies
`LevelRatioBoundNZ … √2`, the telescope and base estimate yield `C√(nL)`.  It deliberately contains no
proof of the gate; it is bookkeeping tying the empirical factor target `c≈√2` to the citable prize
budget. -/
theorem prizeBudget_of_sqrtTwo_perLevelFactor
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} {C L n : ℝ} {μ : ℕ}
    (hr : LevelRatioBoundNZ ψ G ζ μ (Real.sqrt 2))
    (h_dim : (Real.sqrt 2) ^ μ ≤ Real.sqrt n)
    (h_base : levelWorst ψ G ζ 0 ≤ C * Real.sqrt L)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hn : 0 ≤ n) :
    levelWorst ψ G ζ μ ≤ C * Real.sqrt (n * L) := by
  exact levelWorst_le_prize_budget_of_xgate hr h_dim h_base hC hL hn

end ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo

#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.perLevelFactor_le_two_of_dilate_le_two_mul
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.perLevelFactor_lt_two_iff_dilate_lt_two_mul
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.no_copeak_of_perLevelFactor_lt_two
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.sqrt_two_lt_two
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPerLevelFactorSubTwo.prizeBudget_of_sqrtTwo_perLevelFactor
