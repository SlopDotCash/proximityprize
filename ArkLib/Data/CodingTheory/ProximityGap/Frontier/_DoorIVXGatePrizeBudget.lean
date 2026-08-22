/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatedTelescopeBridge

/-!
# Door-(iv) Lane-2: the corrected `√2` gate lands exactly on the prize budget (#444)

`_DoorIVXGatedTelescopeBridge` proves the structural reduction

`LevelRatioBoundNZ ψ G ζ μ (√2) ⟹ M_μ ≤ (√2)^μ · M_0`.

This file adds the last bookkeeping rung used in Shaw's reduction chain: if the base level is bounded by
`C·√L` and the tower dimension is `n` with `(√2)^μ ≤ √n`, the same corrected per-level gate gives

`M_μ ≤ C·√(n·L)`.

This is not a proof of the gate.  It is the citable capstone saying precisely what the single open
door-(iv) scalar buys once supplied: the usual prize-scale `√(n log)` budget, with `L` standing for the
logarithmic factor.  No cancellation, completion, moment, capacity, or CORE claim is made here.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge

namespace ArkLib.ProximityGap.Frontier.DoorIVXGatePrizeBudget

/-- **Abstract prize-budget bookkeeping for the corrected `√2` gate.**  If a telescope gives
`Mμ ≤ (√2)^μ M0`, the tower factor satisfies `(√2)^μ ≤ √n`, and the base level satisfies
`M0 ≤ C√L`, then `Mμ ≤ C√(nL)`.  This is pure real algebra: the corrected gate supplies the
square-root dimension factor and the base estimate supplies the logarithmic/base constant. -/
theorem prize_budget_of_sqrt2_telescope
    {Mμ M0 C L n : ℝ} {μ : ℕ}
    (h_tel : Mμ ≤ (Real.sqrt 2) ^ μ * M0)
    (h_dim : (Real.sqrt 2) ^ μ ≤ Real.sqrt n)
    (h_base : M0 ≤ C * Real.sqrt L)
    (hM0 : 0 ≤ M0) (hC : 0 ≤ C) (hL : 0 ≤ L) (hn : 0 ≤ n) :
    Mμ ≤ C * Real.sqrt (n * L) := by
  have hpow_nonneg : 0 ≤ (Real.sqrt 2) ^ μ := pow_nonneg (Real.sqrt_nonneg 2) μ
  have hCroot_nonneg : 0 ≤ C * Real.sqrt L := mul_nonneg hC (Real.sqrt_nonneg L)
  have hmul : (Real.sqrt 2) ^ μ * M0 ≤ Real.sqrt n * (C * Real.sqrt L) := by
    exact mul_le_mul h_dim h_base hM0 (Real.sqrt_nonneg n)
  have hrewrite : Real.sqrt n * (C * Real.sqrt L) = C * Real.sqrt (n * L) := by
    rw [Real.sqrt_mul hn]
    ring
  exact le_trans h_tel (by simpa [hrewrite] using hmul)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]

/-- **Corrected door-(iv) gate ⇒ prize-shaped budget.**  Supplying the single open per-level inequality
`LevelRatioBoundNZ … √2` and a base-level `C√L` bound yields the prize-shaped estimate
`levelWorst μ ≤ C√(nL)`, provided the dyadic tower factor is registered as `(√2)^μ ≤ √n`.

The open content is exactly `LevelRatioBoundNZ`; this theorem only composes the already-proven telescope
with the final real-algebra budget conversion. -/
theorem levelWorst_le_prize_budget_of_xgate
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} {C L n : ℝ} {μ : ℕ}
    (hr : LevelRatioBoundNZ ψ G ζ μ (Real.sqrt 2))
    (h_dim : (Real.sqrt 2) ^ μ ≤ Real.sqrt n)
    (h_base : levelWorst ψ G ζ 0 ≤ C * Real.sqrt L)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hn : 0 ≤ n) :
    levelWorst ψ G ζ μ ≤ C * Real.sqrt (n * L) := by
  exact prize_budget_of_sqrt2_telescope
    (levelWorst_le_sqrt2_pow_mul_of_xgate μ hr) h_dim h_base
    (levelWorst_nonneg ψ G ζ 0) hC hL hn

end ArkLib.ProximityGap.Frontier.DoorIVXGatePrizeBudget

#print axioms ArkLib.ProximityGap.Frontier.DoorIVXGatePrizeBudget.prize_budget_of_sqrt2_telescope
#print axioms ArkLib.ProximityGap.Frontier.DoorIVXGatePrizeBudget.levelWorst_le_prize_budget_of_xgate
