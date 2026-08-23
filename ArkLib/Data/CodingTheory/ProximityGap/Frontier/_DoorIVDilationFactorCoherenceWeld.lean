/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceDeficitQuantitative

/-!
# Door-(iv) weld: the 2-dilation per-level factor is controlled by the coherence deficit

This module **welds** two previously disconnected door-(iv) facts:

* the quantitative **coherence deficit** law
  (`_DoorIVCoherenceDeficitQuantitative.one_sub_coherence_ge_misalign_div_sq`):
  `1 − ρ ≥ (‖x‖·‖y‖ − ⟪x,y⟫_ℝ)/(‖x‖+‖y‖)²`, where `ρ = ‖x+y‖/(‖x‖+‖y‖)`; and
* the **2-dilation telescope** route (`_DoorIVDilationDescentTelescope`), whose whole obstruction is
  that the *per-level dilation factor* is bounded only by the trivial doubling constant `2`.

No file in the repository connected the two before.  The per-level dilation factor of a 2-dilation
union step is `c = ‖x+y‖ / max(‖x‖,‖y‖)` (the union half-mass `‖A+B‖` over the larger single-period
piece).  The telescope shows that *any working descent must beat the per-level factor `2`*.  This
module proves the missing quantitative bridge: **the per-level factor `c` is at most `2·ρ`, hence
drops below `2` by exactly twice the coherence deficit.**

## What this module proves (and what it does NOT)

In a real inner product space `F` (where the coset-half Gauss-period pieces of `Σ_y e_p(b·y^m)` live):

* `dilationFactor_le_two_mul_coherence` :
  `‖x+y‖ / max(‖x‖,‖y‖) ≤ 2 · (‖x+y‖/(‖x‖+‖y‖))`  — the per-level factor is at most `2ρ`.
* `dilationFactor_le_two` :
  the trivial ceiling `c ≤ 2` (recovered, since `ρ ≤ 1`).
* `dilationFactor_le_two_sub_two_misalign_div_sq` :
  `‖x+y‖/max(‖x‖,‖y‖) ≤ 2 − 2·(‖x‖·‖y‖ − ⟪x,y⟫_ℝ)/(‖x‖+‖y‖)²` — the headline weld: the per-level
  factor is at most `2` *minus twice* the coherence-deficit lower bound.  A working descent (factor
  `< √2`, the prize threshold from `_DoorIVTowerGrowthIteration`) therefore demands a *quantified*
  coherence deficit at every level — exactly `1 − ρ ≥ (2−√2)/2` sustained — which is precisely the
  arithmetic anti-concentration input the door-(iv) wall is missing.

It does **NOT** prove that deficit is achievable.  It uses **no** Gauss-period cancellation, **no**
moment, **no** completion, **no** anti-concentration estimate — only Cauchy–Schwarz / triangle
bookkeeping and the `max ≥ average` elementary fact.  This is a Lane-3 **constraint lemma**: it
quantifies the cost the dilation route must pay, it does not pay it.  `M(μ_n) ≤ C·√(n·log(p/n))`
stays exactly as OPEN as before.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVDilationFactorCoherenceWeld

open scoped InnerProductSpace
open ProximityGap.Frontier.DoorIVCoherenceDeficitQuantitative

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The **per-level 2-dilation factor**: the union half-mass `‖x+y‖` over the larger single-period
piece `max(‖x‖,‖y‖)`.  This is the quantity the dilation telescope must push below `√2` per level. -/
noncomputable def dilationFactor (x y : F) : ℝ :=
  ‖x + y‖ / max ‖x‖ ‖y‖

omit [InnerProductSpace ℝ F] in
/-- The larger piece is at least the average: `(‖x‖+‖y‖)/2 ≤ max ‖x‖ ‖y‖`. -/
theorem half_sum_le_max (x y : F) : (‖x‖ + ‖y‖) / 2 ≤ max ‖x‖ ‖y‖ := by
  rcases le_total ‖x‖ ‖y‖ with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

omit [InnerProductSpace ℝ F] in
/-- **The per-level dilation factor is at most `2·ρ`.**  Since the larger piece dominates the average,
`c = ‖x+y‖/max(‖x‖,‖y‖) ≤ ‖x+y‖/((‖x‖+‖y‖)/2) = 2·(‖x+y‖/(‖x‖+‖y‖)) = 2ρ`. -/
theorem dilationFactor_le_two_mul_coherence (x y : F) (hden : 0 < ‖x‖ + ‖y‖) :
    dilationFactor x y ≤ 2 * twoPieceNormCoherence x y := by
  unfold dilationFactor twoPieceNormCoherence
  have hmaxpos : 0 < max ‖x‖ ‖y‖ :=
    lt_of_lt_of_le (by linarith) (half_sum_le_max x y)
  have hnum_nonneg : 0 ≤ ‖x + y‖ := norm_nonneg _
  -- 2 * (s/(a)) = s/(a/2); and a/2 ≤ max, so s/max ≤ s/(a/2).
  have hhalf : (‖x‖ + ‖y‖) / 2 ≤ max ‖x‖ ‖y‖ := half_sum_le_max x y
  have hrw : 2 * (‖x + y‖ / (‖x‖ + ‖y‖)) = ‖x + y‖ / ((‖x‖ + ‖y‖) / 2) := by
    rw [div_div_eq_mul_div]; ring
  rw [hrw]
  apply div_le_div_of_nonneg_left hnum_nonneg _ hhalf
  positivity

omit [InnerProductSpace ℝ F] in
/-- **Trivial ceiling recovered.**  Since `ρ = ‖x+y‖/(‖x‖+‖y‖) ≤ 1` (triangle inequality), the
per-level dilation factor satisfies `c ≤ 2`.  This is the doubling constant the telescope route is
stuck at without coherence input. -/
theorem dilationFactor_le_two (x y : F) (hden : 0 < ‖x‖ + ‖y‖) :
    dilationFactor x y ≤ 2 := by
  have h1 : dilationFactor x y ≤ 2 * twoPieceNormCoherence x y :=
    dilationFactor_le_two_mul_coherence x y hden
  have hrho_le_one : twoPieceNormCoherence x y ≤ 1 := by
    unfold twoPieceNormCoherence
    rw [div_le_one hden]
    exact norm_add_le x y
  nlinarith [h1, hrho_le_one]

/-- **The headline weld.**  The per-level 2-dilation factor is at most `2` *minus twice* the coherence
deficit lower bound:
`‖x+y‖/max(‖x‖,‖y‖) ≤ 2 − 2·(‖x‖·‖y‖ − ⟪x,y⟫_ℝ)/(‖x‖+‖y‖)²`.

This is the quantitative bridge the dilation route was missing: to beat the doubling constant `2`
(and reach the prize per-level threshold `√2`, cf. `_DoorIVTowerGrowthIteration`), a 2-dilation step
must purchase a coherence deficit of size `≥ (2−√2)/2` — an arithmetic anti-concentration of the
two coset-half pieces, which is exactly the open door-(iv) input.  Pure Cauchy–Schwarz/triangle
bookkeeping; no cancellation, moment, completion, or anti-concentration estimate. -/
theorem dilationFactor_le_two_sub_two_misalign_div_sq (x y : F) (hden : 0 < ‖x‖ + ‖y‖) :
    dilationFactor x y ≤ 2 - 2 * ((‖x‖ * ‖y‖ - ⟪x, y⟫_ℝ) / (‖x‖ + ‖y‖) ^ 2) := by
  have h1 : dilationFactor x y ≤ 2 * twoPieceNormCoherence x y :=
    dilationFactor_le_two_mul_coherence x y hden
  -- 1 - ρ ≥ misalign/(‖x‖+‖y‖)², i.e. ρ ≤ 1 - misalign/(‖x‖+‖y‖)²
  have h2 : 1 - twoPieceNormCoherence x y
      ≥ (‖x‖ * ‖y‖ - ⟪x, y⟫_ℝ) / (‖x‖ + ‖y‖) ^ 2 :=
    one_sub_coherence_ge_misalign_div_sq x y hden
  -- so 2ρ ≤ 2(1 - misalign/(...)²) = 2 - 2·misalign/(...)²
  nlinarith [h1, h2]
end ArkLib.ProximityGap.Frontier.DoorIVDilationFactorCoherenceWeld
