/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# Door IV sector-coherence constraint

Door-(iv) asks for a non-moment anti-concentration theorem for the worst-frequency phase pieces of
`Σ_y e_p (b * y^m)`.  Recent common-ray bricks show exact saturation when all pieces lie on one ray.
This file records the quantitative next obstruction: a whole sector around one ray still prevents a
strict coherence drop.  If every piece has projection at least `c` times its norm along a fixed unit
complex direction, then the normalized coherence is at least `c`.

Consequently, any claimed door-(iv) estimate `ρ ≤ θ` must prove that the worst-frequency pieces are
not merely non-collinear, but leave every sector with projection floor `> θ`.  This is only a
constraint lemma; it is not a CORE bound.
-/

set_option linter.style.longLine false

namespace ProximityGap.Frontier.DoorIVSectorCoherence

/-- Coherence of a finite list of complex pieces: triangle-inequality saturation ratio. -/
noncomputable def complexPieceCoherence (zs : List ℂ) : ℝ :=
  ‖zs.sum‖ / (zs.map norm).sum

/-- The real projection of a complex number onto the unit direction `u`.  We use `conj u * z` so
that the ray `z = t * u`, `t ≥ 0`, has projection `t`. -/
noncomputable def rayProj (u z : ℂ) : ℝ :=
  (starRingEnd ℂ u * z).re

/-- Projection is additive. -/
theorem rayProj_add (u z w : ℂ) : rayProj u (z + w) = rayProj u z + rayProj u w := by
  simp [rayProj, mul_add]

/-- Projection is additive over a finite list. -/
theorem rayProj_list_sum (u : ℂ) (zs : List ℂ) :
    rayProj u zs.sum = (zs.map (rayProj u)).sum := by
  induction zs with
  | nil => simp [rayProj]
  | cons z zs ih =>
      simp [rayProj_add, ih]

/-- A unit-direction projection is bounded above by the norm. -/
theorem rayProj_le_norm_of_unit {u z : ℂ} (hu : ‖u‖ = 1) : rayProj u z ≤ ‖z‖ := by
  unfold rayProj
  calc
    (starRingEnd ℂ u * z).re ≤ ‖starRingEnd ℂ u * z‖ := Complex.re_le_norm _
    _ = ‖z‖ := by
      rw [Complex.norm_mul, Complex.norm_conj, hu, one_mul]

/-- If all pieces have projection at least `c` times their norm along one unit ray, then the total
projection has the same lower bound. -/
theorem sector_projection_sum_lower {zs : List ℂ} {u : ℂ} {c : ℝ}
    (hproj : ∀ z ∈ zs, c * ‖z‖ ≤ rayProj u z) :
    c * (zs.map norm).sum ≤ rayProj u zs.sum := by
  rw [rayProj_list_sum]
  induction zs with
  | nil => simp
  | cons z zs ih =>
      have hz : c * ‖z‖ ≤ rayProj u z := hproj z (by simp)
      have htail : ∀ y ∈ zs, c * ‖y‖ ≤ rayProj u y := by
        intro y hy
        exact hproj y (by simp [hy])
      change c * (‖z‖ + (zs.map norm).sum) ≤ rayProj u z + (zs.map (rayProj u)).sum
      rw [mul_add]
      exact add_le_add hz (ih htail)

/-- **Sector coherence lower bound.**  A list contained in a sector with projection floor `c` along
some unit direction has normalized coherence at least `c` (provided the denominator is positive).
Thus a strict door-(iv) drop must prove genuine angular escape from every such sector. -/
theorem sector_floor_le_complexPieceCoherence {zs : List ℂ} {u : ℂ} {c : ℝ}
    (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum)
    (hproj : ∀ z ∈ zs, c * ‖z‖ ≤ rayProj u z) :
    c ≤ complexPieceCoherence zs := by
  unfold complexPieceCoherence
  have hsum : c * (zs.map norm).sum ≤ rayProj u zs.sum :=
    sector_projection_sum_lower (zs := zs) (u := u) (c := c) hproj
  have hnorm : rayProj u zs.sum ≤ ‖zs.sum‖ := rayProj_le_norm_of_unit hu
  have hmul : c * (zs.map norm).sum ≤ ‖zs.sum‖ := le_trans hsum hnorm
  have hdiv := (le_div_iff₀ hden).2 hmul
  simpa [mul_comm] using hdiv

/-- Defect-budget form of the sector floor.  If, in one unit direction, every piece loses at
most a `δ`-fraction of its norm in ray projection, then the total coherence is still at least
`1 - δ`.  Therefore a Door-IV proof of a `1 - δ` drop must locate a genuinely larger angular defect,
not merely subdivide the sum into many almost-ray-aligned pieces. -/
theorem one_sub_defect_le_complexPieceCoherence_of_rayProj_deficit_le {zs : List ℂ} {u : ℂ} {δ : ℝ}
    (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum)
    (hdef : ∀ z ∈ zs, ‖z‖ - rayProj u z ≤ δ * ‖z‖) :
    1 - δ ≤ complexPieceCoherence zs := by
  refine sector_floor_le_complexPieceCoherence (zs := zs) (u := u) (c := 1 - δ) hu hden ?_
  intro z hz
  have hzdef : ‖z‖ - rayProj u z ≤ δ * ‖z‖ := hdef z hz
  nlinarith

/-- Epsilon/threshold packaging: if the sector floor `c` is above a target `θ`, then the coherence
cannot be bounded by `θ`. -/
theorem not_complexPieceCoherence_le_of_sector_floor {zs : List ℂ} {u : ℂ} {c θ : ℝ}
    (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum)
    (hproj : ∀ z ∈ zs, c * ‖z‖ ≤ rayProj u z) (hθ : θ < c) :
    ¬ complexPieceCoherence zs ≤ θ := by
  intro hcoh
  have hfloor : c ≤ complexPieceCoherence zs :=
    sector_floor_le_complexPieceCoherence (zs := zs) (u := u) (c := c) hu hden hproj
  linarith

/-- Consumer form: a strict coherence bound `ρ ≤ θ` forces escape from every sector whose
projection floor is `c > θ`.  In any unit direction `u`, some piece has projection below
`c · ‖z‖`; otherwise the sector lower bound contradicts the claimed drop. -/
theorem exists_piece_rayProj_lt_of_complexPieceCoherence_le {zs : List ℂ} {u : ℂ} {c θ : ℝ}
    (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum)
    (hcoh : complexPieceCoherence zs ≤ θ) (hθ : θ < c) :
    ∃ z ∈ zs, rayProj u z < c * ‖z‖ := by
  by_contra hnone
  push Not at hnone
  have hproj : ∀ z ∈ zs, c * ‖z‖ ≤ rayProj u z := by
    intro z hz
    exact hnone z hz
  exact not_complexPieceCoherence_le_of_sector_floor
    (zs := zs) (u := u) (c := c) (θ := θ) hu hden hproj hθ hcoh

/-- Epsilon-drop consumer: a positive `1 - ε` coherence saving forces a quantitative sector escape
in every unit direction.  In particular, the pieces cannot all stay in the thinner sector with
projection floor `1 - ε / 2`; some piece must lose at least `ε / 2` of its ray projection. -/
theorem exists_piece_rayProj_lt_one_sub_half_eps_of_complexPieceCoherence_le {zs : List ℂ} {u : ℂ}
    {ε : ℝ} (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum) (hε : 0 < ε)
    (hcoh : complexPieceCoherence zs ≤ 1 - ε) :
    ∃ z ∈ zs, rayProj u z < (1 - ε / 2) * ‖z‖ := by
  refine exists_piece_rayProj_lt_of_complexPieceCoherence_le
    (zs := zs) (u := u) (c := 1 - ε / 2) (θ := 1 - ε) hu hden hcoh ?_
  linarith

/-- General epsilon/drop consumer: a `ρ ≤ 1 - ε` coherence saving forces, for every unit
ray and every smaller budget `δ < ε`, at least one piece to lose more than a `δ`-fraction of its
norm in ray projection.  The earlier `ε / 2` statement is one convenient corollary; this is the
exact probe-facing threshold. -/
theorem exists_piece_rayProj_deficit_gt_delta_of_complexPieceCoherence_le_one_sub {zs : List ℂ}
    {u : ℂ} {δ ε : ℝ} (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum) (hδε : δ < ε)
    (hcoh : complexPieceCoherence zs ≤ 1 - ε) :
    ∃ z ∈ zs, δ * ‖z‖ < ‖z‖ - rayProj u z := by
  obtain ⟨z, hz, hproj⟩ := exists_piece_rayProj_lt_of_complexPieceCoherence_le
    (zs := zs) (u := u) (c := 1 - δ) (θ := 1 - ε) hu hden hcoh (by linarith)
  refine ⟨z, hz, ?_⟩
  nlinarith

/-- The list of ray-projection deficits sums to the total `L¹` mass minus the projection of the
combined vector. -/
theorem rayProj_deficit_sum (u : ℂ) (zs : List ℂ) :
    (zs.map (fun z => ‖z‖ - rayProj u z)).sum =
      (zs.map norm).sum - rayProj u zs.sum := by
  rw [rayProj_list_sum]
  induction zs with
  | nil => simp
  | cons z zs ih =>
      simp [ih]
      ring

/-- **Aggregate sector-defect obligation.**  If the normalized piece coherence is at most `θ`, then
in every unit direction the total projection deficit is at least `(1-θ)` times the `L¹` mass.  Thus a
Door-IV phase split cannot certify a drop merely by naming sectors: it must prove a quantitatively
large aggregate angular defect at the adversarial frequency. -/
theorem aggregate_rayProj_deficit_ge_of_complexPieceCoherence_le {zs : List ℂ} {u : ℂ} {θ : ℝ}
    (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum)
    (hcoh : complexPieceCoherence zs ≤ θ) :
    (1 - θ) * (zs.map norm).sum ≤ (zs.map (fun z => ‖z‖ - rayProj u z)).sum := by
  have hnorm_le : ‖zs.sum‖ ≤ θ * (zs.map norm).sum := by
    unfold complexPieceCoherence at hcoh
    exact (div_le_iff₀ hden).1 hcoh
  have hproj_le_norm : rayProj u zs.sum ≤ ‖zs.sum‖ := rayProj_le_norm_of_unit hu
  rw [rayProj_deficit_sum]
  nlinarith

/-- Epsilon-specialized aggregate sector-defect obligation.  A positive coherence saving
`ρ ≤ 1 - ε` forces at least an `ε` fraction of the total `L¹` mass to appear as aggregate
ray-projection defect in every unit direction.  This is the exact budget a Door-IV angular-spread
argument must pay; a smaller total defect cannot certify the claimed drop. -/
theorem aggregate_rayProj_deficit_ge_eps_of_complexPieceCoherence_le_one_sub {zs : List ℂ} {u : ℂ}
    {ε : ℝ} (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum)
    (hcoh : complexPieceCoherence zs ≤ 1 - ε) :
    ε * (zs.map norm).sum ≤ (zs.map (fun z => ‖z‖ - rayProj u z)).sum := by
  have h := aggregate_rayProj_deficit_ge_of_complexPieceCoherence_le
    (zs := zs) (u := u) (θ := 1 - ε) hu hden hcoh
  simpa [sub_sub_cancel] using h

/-- Contrapositive budget form: if some unit direction has aggregate ray-projection defect below
the `ε · L¹` budget, then the pieces cannot have coherence at most `1 - ε`.  Thus a proposed
sector/angle proof must produce the full aggregate defect, not merely one locally tilted piece. -/
theorem not_complexPieceCoherence_le_one_sub_of_aggregate_rayProj_deficit_lt {zs : List ℂ} {u : ℂ}
    {ε : ℝ} (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum)
    (hdef : (zs.map (fun z => ‖z‖ - rayProj u z)).sum < ε * (zs.map norm).sum) :
    ¬ complexPieceCoherence zs ≤ 1 - ε := by
  intro hcoh
  have hbudget : ε * (zs.map norm).sum ≤ (zs.map (fun z => ‖z‖ - rayProj u z)).sum :=
    aggregate_rayProj_deficit_ge_eps_of_complexPieceCoherence_le_one_sub
      (zs := zs) (u := u) (ε := ε) hu hden hcoh
  linarith

end ProximityGap.Frontier.DoorIVSectorCoherence

#print axioms ProximityGap.Frontier.DoorIVSectorCoherence.rayProj_list_sum
#print axioms ProximityGap.Frontier.DoorIVSectorCoherence.rayProj_le_norm_of_unit
#print axioms ProximityGap.Frontier.DoorIVSectorCoherence.sector_projection_sum_lower
#print axioms
  ProximityGap.Frontier.DoorIVSectorCoherence.sector_floor_le_complexPieceCoherence
#print axioms
  ProximityGap.Frontier.DoorIVSectorCoherence.one_sub_defect_le_complexPieceCoherence_of_rayProj_deficit_le
#print axioms
  ProximityGap.Frontier.DoorIVSectorCoherence.not_complexPieceCoherence_le_of_sector_floor
#print axioms
  ProximityGap.Frontier.DoorIVSectorCoherence.exists_piece_rayProj_lt_of_complexPieceCoherence_le
#print axioms
  ProximityGap.Frontier.DoorIVSectorCoherence.exists_piece_rayProj_lt_one_sub_half_eps_of_complexPieceCoherence_le
#print axioms
  ProximityGap.Frontier.DoorIVSectorCoherence.exists_piece_rayProj_deficit_gt_delta_of_complexPieceCoherence_le_one_sub
#print axioms ProximityGap.Frontier.DoorIVSectorCoherence.rayProj_deficit_sum
#print axioms
  ProximityGap.Frontier.DoorIVSectorCoherence.aggregate_rayProj_deficit_ge_of_complexPieceCoherence_le
#print axioms
  ProximityGap.Frontier.DoorIVSectorCoherence.aggregate_rayProj_deficit_ge_eps_of_complexPieceCoherence_le_one_sub
#print axioms
  ProximityGap.Frontier.DoorIVSectorCoherence.not_complexPieceCoherence_le_one_sub_of_aggregate_rayProj_deficit_lt
