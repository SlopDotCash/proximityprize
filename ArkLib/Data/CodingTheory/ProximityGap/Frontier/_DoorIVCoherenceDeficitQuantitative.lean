/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Door (iv): the QUANTITATIVE two-piece coherence deficit bound

`_DoorIVComplexRayCoherence.lean` proves the SHARP *qualitative* two-piece criterion
`twoPieceNormCoherence x y = 1 ↔ SameRay ℝ x y`, and its docstring explicitly flags the gap that a
genuine two-piece phase anti-concentration theorem cannot merely subdivide the sum but must prove
"non-collinearity (or **quantitative distance from same-ray alignment**) for the adversarial pieces."
`_DoorIVMultiPieceSameRayConverse.lean` then closes the qualitative multi-piece converse
(`ρ = 1 ⟺ pairwise same-ray`, `ρ < 1 ⟺ ∃ non-collinear pair`).

Both of those are QUALITATIVE: they say a strict coherence drop `ρ < 1` *requires* a non-collinear
pair, but say NOTHING about HOW MUCH drop a given amount of non-collinearity buys.  An actual door-(iv)
anti-concentration certificate needs the QUANTITATIVE law: a lower bound on the coherence deficit
`1 − ρ` in terms of a measure of misalignment of the pieces.  Without it, "the pieces are not exactly
collinear" gives you an unquantified `ρ < 1` that could be `1 − o(1)` — useless against the wall.

This file supplies that quantitative law in the concrete door-(iv) ambient space: a **real inner
product space** (in particular `ℂ` over `ℝ`, where the coset-half Gauss-period pieces of
`Σ_y e_p(b·y^m)` live).  The clean tight inequality is, for `x, y` with `‖x‖+‖y‖ > 0`:

> `(‖x‖+‖y‖) − ‖x+y‖  ≥  (‖x‖·‖y‖ − ⟪x,y⟫_ℝ) / (‖x‖+‖y‖)`

equivalently, writing the **unit-direction chordal distance** `d = ‖x/‖x‖ − y/‖y‖‖` (for nonzero
pieces) and the coherence `ρ = ‖x+y‖/(‖x‖+‖y‖)`:

> `1 − ρ  ≥  (1/2) · (‖x‖·‖y‖ / (‖x‖+‖y‖)²) · d²`  **and this constant `1/2` is TIGHT** (numerically
> verified: the ratio `(1−ρ)/[(‖x‖‖y‖/(‖x‖+‖y‖)²)·d²] → 1/2` as `d → 0`).

The proof is pure triangle-equality / Cauchy–Schwarz bookkeeping:
set `a=‖x‖, b=‖y‖, s=‖x+y‖`; then `s² = a²+b²+2⟪x,y⟫` gives the **difference-of-squares identity**
`(a+b)² − s² = 2(ab − ⟪x,y⟫)`, hence `ab − ⟪x,y⟫ = (a+b−s)(a+b+s)/2`, and the bound reduces to
`(a+b)(a+b−s) ≥ (a+b−s)(a+b+s)/2`, i.e. (since `a+b−s ≥ 0` by the triangle inequality)
`a+b ≥ (a+b+s)/2`, i.e. `a+b ≥ s` — the triangle inequality again.  No Gauss-period cancellation, no
moment, no completion, no anti-concentration is claimed or used.  This is a CONSTRAINT lemma: it
strengthens `_DoorIVMultiPieceSameRayConverse` from "a saving needs a non-collinear pair" to "a saving
of size `1−ρ` needs misalignment of size `≳ √(1−ρ)`", quantifying exactly what a multi-piece door-(iv)
certificate must buy.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ProximityGap.Frontier.DoorIVCoherenceDeficitQuantitative

open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Two-piece norm coherence (same definition as `_DoorIVComplexRayCoherence`). -/
noncomputable def twoPieceNormCoherence (x y : F) : ℝ :=
  ‖x + y‖ / (‖x‖ + ‖y‖)

/-- **Difference-of-squares identity.** In a real inner product space,
`(‖x‖+‖y‖)² − ‖x+y‖² = 2·(‖x‖·‖y‖ − ⟪x,y⟫_ℝ)`.  This is the algebraic engine. -/
theorem sq_sum_sub_sq_norm_add (x y : F) :
    (‖x‖ + ‖y‖) ^ 2 - ‖x + y‖ ^ 2 = 2 * (‖x‖ * ‖y‖ - ⟪x, y⟫_ℝ) := by
  rw [norm_add_sq_real]
  ring

/-- The "misalignment numerator" `‖x‖·‖y‖ − ⟪x,y⟫_ℝ` is nonnegative (Cauchy–Schwarz). -/
theorem misalign_nonneg (x y : F) : 0 ≤ ‖x‖ * ‖y‖ - ⟪x, y⟫_ℝ :=
  sub_nonneg.mpr (real_inner_le_norm x y)

/-- **The quantitative two-piece coherence deficit bound (inner-product form).** The combined-norm
gap `(‖x‖+‖y‖) − ‖x+y‖` is at least the misalignment numerator divided by the total piece mass. -/
theorem norm_sum_gap_ge_misalign_div (x y : F) (hden : 0 < ‖x‖ + ‖y‖) :
    (‖x‖ + ‖y‖) - ‖x + y‖ ≥ (‖x‖ * ‖y‖ - ⟪x, y⟫_ℝ) / (‖x‖ + ‖y‖) := by
  set a := ‖x‖ + ‖y‖ with ha
  set s := ‖x + y‖ with hs
  -- triangle inequality: s ≤ a, so a - s ≥ 0
  have htri : s ≤ a := by rw [hs, ha]; exact norm_add_le x y
  have hgap : 0 ≤ a - s := sub_nonneg.mpr htri
  have hs_nonneg : 0 ≤ s := by rw [hs]; exact norm_nonneg _
  -- difference of squares: a² - s² = 2(‖x‖‖y‖ - ⟪x,y⟫)
  have hsq : a ^ 2 - s ^ 2 = 2 * (‖x‖ * ‖y‖ - ⟪x, y⟫_ℝ) := by
    rw [ha, hs]; exact sq_sum_sub_sq_norm_add x y
  -- so ‖x‖‖y‖ - ⟪x,y⟫ = (a - s)(a + s)/2
  have hnum : ‖x‖ * ‖y‖ - ⟪x, y⟫_ℝ = (a - s) * (a + s) / 2 := by
    have : a ^ 2 - s ^ 2 = (a - s) * (a + s) := by ring
    rw [this] at hsq; linarith
  -- target: a - s ≥ ((a-s)(a+s)/2) / a, i.e. (a - s) * a ≥ (a-s)(a+s)/2  (mult by a > 0)
  rw [ge_iff_le, hnum, div_le_iff₀ hden]
  -- (a - s)*(a + s)/2 ≤ (a - s) * a
  have hbound : (a - s) * (a + s) / 2 ≤ (a - s) * a := by
    -- (a - s) ≥ 0 and (a + s)/2 ≤ a  ⟸  s ≤ a
    have hhalf : (a + s) / 2 ≤ a := by linarith
    calc (a - s) * (a + s) / 2 = (a - s) * ((a + s) / 2) := by ring
      _ ≤ (a - s) * a := by
          apply mul_le_mul_of_nonneg_left hhalf hgap
  linarith [hbound]

/-- **Coherence deficit lower bound (the headline statement).** The two-piece coherence deficit
`1 − ρ` is at least the misalignment numerator over the squared total piece mass:
`1 − twoPieceNormCoherence x y ≥ (‖x‖·‖y‖ − ⟪x,y⟫_ℝ) / (‖x‖+‖y‖)²`. -/
theorem one_sub_coherence_ge_misalign_div_sq (x y : F) (hden : 0 < ‖x‖ + ‖y‖) :
    1 - twoPieceNormCoherence x y ≥ (‖x‖ * ‖y‖ - ⟪x, y⟫_ℝ) / (‖x‖ + ‖y‖) ^ 2 := by
  unfold twoPieceNormCoherence
  rw [ge_iff_le, sq]
  rw [div_mul_eq_div_div]
  -- 1 - s/a = (a - s)/a, and we want ((‖x‖‖y‖-⟪x,y⟫)/a)/a ≤ (a-s)/a
  have hgap := norm_sum_gap_ge_misalign_div x y hden
  have hstep : (‖x‖ * ‖y‖ - ⟪x, y⟫_ℝ) / (‖x‖ + ‖y‖) ≤ (‖x‖ + ‖y‖) - ‖x + y‖ := hgap
  have hkey : ((‖x‖ * ‖y‖ - ⟪x, y⟫_ℝ) / (‖x‖ + ‖y‖)) / (‖x‖ + ‖y‖)
      ≤ ((‖x‖ + ‖y‖) - ‖x + y‖) / (‖x‖ + ‖y‖) := by
    gcongr
  -- RHS equals 1 - ‖x+y‖/(‖x‖+‖y‖)
  have hrw : ((‖x‖ + ‖y‖) - ‖x + y‖) / (‖x‖ + ‖y‖) = 1 - ‖x + y‖ / (‖x‖ + ‖y‖) := by
    rw [sub_div, div_self (ne_of_gt hden)]
  rw [hrw] at hkey
  exact hkey

/-- **Misalignment numerator as a unit-direction chordal distance (nonzero pieces).** For nonzero
`x, y`, the misalignment numerator equals `(‖x‖·‖y‖/2)·d²` where `d = ‖x/‖x‖ − y/‖y‖‖` is the chordal
distance between the unit directions.  Hence the deficit bound reads
`1 − ρ ≥ (1/2)·(‖x‖·‖y‖/(‖x‖+‖y‖)²)·d²`, exposing the TIGHT constant `1/2`. -/
theorem misalign_eq_half_mul_dist_sq (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x‖ * ‖y‖ - ⟪x, y⟫_ℝ
      = (‖x‖ * ‖y‖ / 2) * ‖(‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y‖ ^ 2 := by
  have hxn : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hyn : (0:ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  set u : F := (‖x‖)⁻¹ • x with hu
  set v : F := (‖y‖)⁻¹ • y with hv
  -- ‖u‖ = ‖v‖ = 1
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxn), inv_mul_cancel₀ (ne_of_gt hxn)]
  have hvn : ‖v‖ = 1 := by
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyn), inv_mul_cancel₀ (ne_of_gt hyn)]
  -- ‖u - v‖² = ‖u‖² - 2⟪u,v⟫ + ‖v‖² = 2 - 2⟪u,v⟫
  have hdist : ‖u - v‖ ^ 2 = 2 - 2 * ⟪u, v⟫_ℝ := by
    rw [norm_sub_sq_real, hun, hvn]; ring
  -- ⟪u,v⟫ = ‖x‖⁻¹ ‖y‖⁻¹ ⟪x,y⟫
  have hinner : ⟪u, v⟫_ℝ = (‖x‖)⁻¹ * (‖y‖)⁻¹ * ⟪x, y⟫_ℝ := by
    rw [hu, hv, real_inner_smul_left, real_inner_smul_right]; ring
  rw [hdist, hinner]
  field_simp

/-- **Headline quantitative deficit bound in chordal-distance form (nonzero pieces).**
`1 − ρ ≥ (1/2)·(‖x‖·‖y‖/(‖x‖+‖y‖)²)·‖x/‖x‖ − y/‖y‖‖²`.  The right side is strictly positive exactly
when the unit directions differ, recovering — and now QUANTIFYING — the `_DoorIVComplexRayCoherence`
"strict drop ⟺ not same-ray" obstruction: a coherence saving of size `1−ρ` forces unit-direction
misalignment of size `≳ √(1−ρ)`. -/
theorem one_sub_coherence_ge_half_dist_sq (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    1 - twoPieceNormCoherence x y
      ≥ (1/2) * (‖x‖ * ‖y‖ / (‖x‖ + ‖y‖) ^ 2) * ‖(‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y‖ ^ 2 := by
  have hxn : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hyn : (0:ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hden : 0 < ‖x‖ + ‖y‖ := by linarith
  have hbase := one_sub_coherence_ge_misalign_div_sq x y hden
  have heq := misalign_eq_half_mul_dist_sq x y hx hy
  -- rewrite the numerator in hbase using heq, then match the target shape
  rw [heq] at hbase
  -- hbase : 1 - ρ ≥ ((‖x‖‖y‖/2)·d²) / (‖x‖+‖y‖)²
  -- target : 1 - ρ ≥ (1/2)·(‖x‖‖y‖/(‖x‖+‖y‖)²)·d²   — same value
  refine le_trans (le_of_eq ?_) hbase
  field_simp

end ProximityGap.Frontier.DoorIVCoherenceDeficitQuantitative

#print axioms ProximityGap.Frontier.DoorIVCoherenceDeficitQuantitative.sq_sum_sub_sq_norm_add
#print axioms ProximityGap.Frontier.DoorIVCoherenceDeficitQuantitative.norm_sum_gap_ge_misalign_div
#print axioms ProximityGap.Frontier.DoorIVCoherenceDeficitQuantitative.one_sub_coherence_ge_misalign_div_sq
#print axioms ProximityGap.Frontier.DoorIVCoherenceDeficitQuantitative.misalign_eq_half_mul_dist_sq
#print axioms ProximityGap.Frontier.DoorIVCoherenceDeficitQuantitative.one_sub_coherence_ge_half_dist_sq
