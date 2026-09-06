/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# Door IV transverse (angular-spread) constraint

The door-(iv) coherence files record a qualitative dichotomy:

* `_DoorIVCommonRayCoherence`: if all pieces lie on one closed complex ray then the
  triangle inequality saturates and `ρ = 1` (no anti-concentration slack).
* `_DoorIVSectorCoherence`: a coherence deficit forces an aggregate *projection deficit*
  `‖z‖ - rayProj u z` in every unit direction `u`.

The projection deficit `‖z‖ - rayProj u z` is **not** the same object as the geometric
angular spread.  A piece can have a large projection deficit purely by pointing *backwards*
along `u` (antipodal), with zero transverse component.  The honest "angular spread is
essential" statement is about the genuine perpendicular component

`rayPerp u z = Im(conj u · z)`,

which vanishes exactly when `z` is collinear with the real axis of the `u`-frame, i.e. on the
common ray (or its antipode).  This file supplies the missing quantitative bridge between the
two views:

* `rayProj_sq_add_rayPerp_sq` — the exact Pythagorean identity
  `(rayProj u z)² + (rayPerp u z)² = ‖z‖²` for a unit direction `u`.
* `rayPerp_sq_le_two_norm_mul_deficit` — the **sharp** one-sided bound
  `(rayPerp u z)² ≤ 2‖z‖·(‖z‖ - rayProj u z)`, converting a projection-deficit certificate
  (what the sector lemmas produce) into a genuine transverse-spread certificate.  It is tight
  as `rayProj → ‖z‖`.
* `rayPerp_eq_zero_of_no_deficit` — zero projection deficit forces zero transverse component
  (a piece at full projection is *exactly* on the ray), the converse direction matching
  `_DoorIVCommonRayCoherence`.
* `rayPerp` additivity (`rayPerp_add`, `rayPerp_list_sum`), so the constraint is stated at the
  same list level as the coherence ratio.

This is a constraint lemma only.  It proves no cancellation, anti-concentration, completion
saving, or CORE bound: it merely makes the geometric content of "angular spread" sharp.
-/

namespace ProximityGap.Frontier.DoorIVTransverseSpread

open Complex

/-- The real projection of `z` onto the unit direction `u` (same convention as the sector file:
`rayProj u z = Re(conj u · z)`, so `z = t·u` with `t ≥ 0` projects to `t`). -/
noncomputable def rayProj (u z : ℂ) : ℝ :=
  (starRingEnd ℂ u * z).re

/-- The transverse (perpendicular) component of `z` in the unit `u`-frame:
`rayPerp u z = Im(conj u · z)`.  It vanishes exactly when `z` is collinear with `u`
(`z` a real multiple of `u`). -/
noncomputable def rayPerp (u z : ℂ) : ℝ :=
  (starRingEnd ℂ u * z).im

/-- Transverse component is additive. -/
theorem rayPerp_add (u z w : ℂ) : rayPerp u (z + w) = rayPerp u z + rayPerp u w := by
  simp [rayPerp, mul_add]

/-- Transverse component is additive over a finite list:
`Σ rayPerp u z_i = rayPerp u (Σ z_i)`. -/
theorem rayPerp_list_sum (u : ℂ) (zs : List ℂ) :
    rayPerp u zs.sum = (zs.map (rayPerp u)).sum := by
  induction zs with
  | nil => simp [rayPerp]
  | cons z zs ih =>
      simp [rayPerp_add, ih]

/-- **Pythagorean identity in the unit `u`-frame.**  For a unit direction `u`, the projection and
the transverse component decompose the squared norm exactly:
`(rayProj u z)² + (rayPerp u z)² = ‖z‖²`. -/
theorem rayProj_sq_add_rayPerp_sq {u z : ℂ} (hu : ‖u‖ = 1) :
    (rayProj u z) ^ 2 + (rayPerp u z) ^ 2 = ‖z‖ ^ 2 := by
  have hnorm : ‖starRingEnd ℂ u * z‖ = ‖z‖ := by
    rw [Complex.norm_mul, Complex.norm_conj, hu, one_mul]
  have hsq : Complex.normSq (starRingEnd ℂ u * z) = ‖z‖ ^ 2 := by
    have := (Complex.normSq_eq_norm_sq (starRingEnd ℂ u * z))
    rw [this, hnorm]
  have hexp : Complex.normSq (starRingEnd ℂ u * z)
      = (starRingEnd ℂ u * z).re ^ 2 + (starRingEnd ℂ u * z).im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  unfold rayProj rayPerp
  rw [← hexp, hsq]

/-- **Sharp transverse-spread bound.**  For a unit direction `u`,
`(rayPerp u z)² ≤ 2‖z‖·(‖z‖ - rayProj u z)`.

This converts a projection-*deficit* certificate `‖z‖ - rayProj u z ≤ δ` (which the
sector/coherence files produce) into a genuine transverse (angular) spread bound
`(rayPerp u z)² ≤ 2‖z‖·δ`.  The bound is tight as `rayProj → ‖z‖`. -/
theorem rayPerp_sq_le_two_norm_mul_deficit {u z : ℂ} (hu : ‖u‖ = 1) :
    (rayPerp u z) ^ 2 ≤ 2 * ‖z‖ * (‖z‖ - rayProj u z) := by
  have hpyth := rayProj_sq_add_rayPerp_sq (u := u) (z := z) hu
  -- rayPerp² = ‖z‖² - rayProj²  = (‖z‖ - rayProj)(‖z‖ + rayProj)
  have hperp_sq : (rayPerp u z) ^ 2 = (‖z‖ - rayProj u z) * (‖z‖ + rayProj u z) := by
    nlinarith [hpyth]
  rw [hperp_sq]
  -- ‖z‖ + rayProj ≤ 2‖z‖  (since rayProj ≤ ‖z‖) and ‖z‖ - rayProj ≥ 0
  have hle : rayProj u z ≤ ‖z‖ := by
    unfold rayProj
    calc (starRingEnd ℂ u * z).re ≤ ‖starRingEnd ℂ u * z‖ := Complex.re_le_norm _
      _ = ‖z‖ := by rw [Complex.norm_mul, Complex.norm_conj, hu, one_mul]
  have hge : -‖z‖ ≤ rayProj u z := by
    unfold rayProj
    have hb : |(starRingEnd ℂ u * z).re| ≤ ‖starRingEnd ℂ u * z‖ := Complex.abs_re_le_norm _
    rw [Complex.norm_mul, Complex.norm_conj, hu, one_mul] at hb
    exact (abs_le.1 hb).1
  have hnn : 0 ≤ ‖z‖ := norm_nonneg z
  nlinarith [hle, hge, hnn]

/-- **No-deficit ⇒ no transverse spread.**  If a piece attains full projection
(`‖z‖ = rayProj u z`) then its transverse component is exactly zero: it lies *on* the ray.
This is the per-piece converse matching `_DoorIVCommonRayCoherence` (saturation ⇒ collinear). -/
theorem rayPerp_eq_zero_of_no_deficit {u z : ℂ} (hu : ‖u‖ = 1)
    (hfull : ‖z‖ = rayProj u z) : rayPerp u z = 0 := by
  have hbound := rayPerp_sq_le_two_norm_mul_deficit (u := u) (z := z) hu
  rw [← hfull] at hbound
  have : (rayPerp u z) ^ 2 ≤ 0 := by simpa using hbound
  have hsq : (rayPerp u z) ^ 2 = 0 := le_antisymm this (sq_nonneg _)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

/-- Quantitative contrapositive at the piece level: a **nonzero** transverse component forces a
strictly positive projection deficit.  So genuine angular spread is impossible without paying a
strict deficit — the sharp form of "the common ray gives no slack". -/
theorem rayProj_lt_norm_of_rayPerp_ne_zero {u z : ℂ} (hu : ‖u‖ = 1)
    (hperp : rayPerp u z ≠ 0) : rayProj u z < ‖z‖ := by
  by_contra hnot
  push_neg at hnot
  have hle : rayProj u z ≤ ‖z‖ := by
    unfold rayProj
    calc (starRingEnd ℂ u * z).re ≤ ‖starRingEnd ℂ u * z‖ := Complex.re_le_norm _
      _ = ‖z‖ := by rw [Complex.norm_mul, Complex.norm_conj, hu, one_mul]
  have hfull : ‖z‖ = rayProj u z := le_antisymm hnot hle
  exact hperp (rayPerp_eq_zero_of_no_deficit hu hfull)

/-- Real projection is additive (companion to `rayPerp_add`). -/
theorem rayProj_add (u z w : ℂ) : rayProj u (z + w) = rayProj u z + rayProj u w := by
  simp [rayProj, mul_add]

/-- Real projection is additive over a finite list. -/
theorem rayProj_list_sum (u : ℂ) (zs : List ℂ) :
    rayProj u zs.sum = (zs.map (rayProj u)).sum := by
  induction zs with
  | nil => simp [rayProj]
  | cons z zs ih =>
      simp [rayProj_add, ih]

/-! ### Resultant-frame structure

The natural adversarial direction for a list `zs` is its own resultant `R = Σ z_i`, i.e.
`u = R / ‖R‖`.  In that frame the resultant is exactly on the ray (`rayProj = ‖R‖`, `rayPerp = 0`),
so the per-piece transverse components form a **signed set summing to zero** (forced cancellation
structure), and the per-piece projection deficits sum to exactly `(1 - ρ)·L¹` where `ρ = ‖R‖/L¹` is
the coherence.  These are the exact list-level shape of "a coherence deficit is an aggregate angular
obligation". -/

/-- The frame product `conj(R/‖R‖) · R` evaluates to the real number `‖R‖` (as a complex value). -/
theorem frameProd_self_eq_norm {R : ℂ} (hR : R ≠ 0) :
    starRingEnd ℂ (R / (‖R‖ : ℂ)) * R = (‖R‖ : ℂ) := by
  have hRn : (‖R‖ : ℂ) ≠ 0 := by
    simpa [Complex.ofReal_eq_zero, norm_eq_zero] using hR
  rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div]
  have hmul : starRingEnd ℂ R * R = (Complex.normSq R : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj R
  rw [hmul]
  have hns : (Complex.normSq R : ℂ) = (‖R‖ : ℂ) * (‖R‖ : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [hns, mul_div_assoc, div_self hRn, mul_one]

/-- In the resultant's own frame `u = R/‖R‖`, the projection of `R` is its full norm. -/
theorem rayProj_self_eq_norm {R : ℂ} (hR : R ≠ 0) :
    rayProj (R / (‖R‖ : ℂ)) R = ‖R‖ := by
  unfold rayProj
  rw [frameProd_self_eq_norm hR, Complex.ofReal_re]

/-- In the resultant's own frame `u = R/‖R‖`, the resultant has zero transverse component
(`R` lies exactly on its own ray). -/
theorem rayPerp_self_eq_zero {R : ℂ} (hR : R ≠ 0) :
    rayPerp (R / (‖R‖ : ℂ)) R = 0 := by
  unfold rayPerp
  rw [frameProd_self_eq_norm hR, Complex.ofReal_im]

/-- **Resultant-frame transverse cancellation.**  Choosing `u = R/‖R‖` (the resultant's own
direction), the per-piece transverse components sum to zero:
`Σ rayPerp u z_i = 0`.  Thus any genuine per-piece angular spread at this natural adversarial
frame is *signed and cancelling*, not free; an anti-concentration method must control this signed
transverse set, it cannot merely subdivide. -/
theorem sum_rayPerp_resultant_frame_eq_zero (zs : List ℂ) (hR : zs.sum ≠ 0) :
    (zs.map (rayPerp (zs.sum / (‖zs.sum‖ : ℂ)))).sum = 0 := by
  rw [← rayPerp_list_sum]
  exact rayPerp_self_eq_zero hR

/-- **Resultant-frame deficit budget (exact).**  In the resultant frame `u = R/‖R‖`, the total
per-piece projection deficit equals exactly `L¹ - ‖R‖` where `L¹ = Σ ‖z_i‖`.  Equivalently it is
`(1 - ρ)·L¹` with coherence `ρ = ‖R‖/L¹`: the coherence deficit is *exactly* the aggregate
projection deficit at the natural adversarial frame, with no slack. -/
theorem sum_deficit_resultant_frame_eq (zs : List ℂ) (hR : zs.sum ≠ 0) :
    (zs.map (fun z => ‖z‖ - rayProj (zs.sum / (‖zs.sum‖ : ℂ)) z)).sum
      = (zs.map norm).sum - ‖zs.sum‖ := by
  have hsplit : ∀ (u : ℂ) (ws : List ℂ),
      (ws.map (fun z => ‖z‖ - rayProj u z)).sum
        = (ws.map norm).sum - (ws.map (rayProj u)).sum := by
    intro u ws
    induction ws with
    | nil => simp
    | cons z ws ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [hsplit, ← rayProj_list_sum, rayProj_self_eq_norm hR]

end ProximityGap.Frontier.DoorIVTransverseSpread

#print axioms ProximityGap.Frontier.DoorIVTransverseSpread.rayPerp_add
#print axioms ProximityGap.Frontier.DoorIVTransverseSpread.rayPerp_list_sum
#print axioms ProximityGap.Frontier.DoorIVTransverseSpread.rayProj_sq_add_rayPerp_sq
#print axioms ProximityGap.Frontier.DoorIVTransverseSpread.rayPerp_sq_le_two_norm_mul_deficit
#print axioms ProximityGap.Frontier.DoorIVTransverseSpread.rayPerp_eq_zero_of_no_deficit
#print axioms ProximityGap.Frontier.DoorIVTransverseSpread.rayProj_lt_norm_of_rayPerp_ne_zero
#print axioms ProximityGap.Frontier.DoorIVTransverseSpread.rayProj_add
#print axioms ProximityGap.Frontier.DoorIVTransverseSpread.rayProj_list_sum
#print axioms ProximityGap.Frontier.DoorIVTransverseSpread.frameProd_self_eq_norm
#print axioms ProximityGap.Frontier.DoorIVTransverseSpread.rayProj_self_eq_norm
#print axioms ProximityGap.Frontier.DoorIVTransverseSpread.rayPerp_self_eq_zero
#print axioms ProximityGap.Frontier.DoorIVTransverseSpread.sum_rayPerp_resultant_frame_eq_zero
#print axioms ProximityGap.Frontier.DoorIVTransverseSpread.sum_deficit_resultant_frame_eq
