/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumCosetInv

/-!
# Door-(iv) Lane-2 capstone: the half-mass is an EXACT two-dilate sub-period sum (#444)

The index-2 coset split of the period `η_b = Σ_{y∈G} ψ(b·y)` (`G = μ_n`) along the index-2 subgroup
`H = μ_{n/2}` with coset representative `g` (a generator of `μ_n`, so `g·H` is the nontrivial coset and
`G = H ⊔ g·H`) factors the period as

  `η_b = A_b + B_b`,   `A_b = Σ_{z∈H} ψ(b·z) = eta ψ H b`,
                       `B_b = Σ_{z∈H} ψ(b·g·z) = eta ψ H (g·b)`.

So the **second coset-half is the SAME sub-period `A` evaluated at the dilated frequency `g·b`**:
`B_b = A_{g·b}`.  This is the exact algebraic substrate under the half-mass thread
(`[door-iv-halfmass-equivalence]`, `prize ⟺ H(n)=O(√(n·log))`) and under the probed cross-half-phase
constraint (`[door-iv-crosshalf-phase-unstructured]`).  It was used in prose but never kernel-anchored
as a standalone identity; this file is the citable Lane-2 capstone rung.

The headline consequences:
* `eta_image_smul_eq_eta_dilate`: the period over the coset `g·H` (as the image `H.image (g·•)`) equals
  the sub-period at the dilated frequency: `eta ψ (g·H) b = eta ψ H (g·b)`.
* `eta_index_two_split_dilate`: `η_b = eta ψ H b + eta ψ H (g·b)` on a disjoint two-coset cover
  `G = H ∪ g·H`.
* `halfMass_eq_two_dilate`: the half-mass `‖A_b‖+‖B_b‖ = ‖eta ψ H b‖ + ‖eta ψ H (g·b)‖` — the worst-`b`
  prize burden `H(n) = max_b (‖eta ψ H b‖ + ‖eta ψ H (g·b)‖)` is a max over a sub-period magnitude at
  TWO multiplicatively-dilated frequencies `b` and `g·b`.

Scope: an exact reindexing identity over a field, on the in-tree `eta` primitive.  No CORE/cancellation/
completion/capacity claim — it kernel-anchors WHERE the open half-mass burden sits.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

namespace ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The coset-half is a dilated sub-period.**  The period over the multiplicative coset `g·H`
(realized as the image `H.image (g·•)`) equals the sub-period over `H` at the dilated frequency `g·b`:
`Σ_{y∈g·H} ψ(b·y) = Σ_{z∈H} ψ((g·b)·z)`.  This is the key reindex `B_b = A_{g·b}`. -/
theorem eta_image_smul_eq_eta_dilate {ψ : AddChar F ℂ} (H : Finset F) {g b : F} (hg : g ≠ 0) :
    eta ψ (H.image (fun y => g * y)) b = eta ψ H (g * b) := by
  unfold eta
  rw [Finset.sum_image (by
    intro x _ y _ hxy
    exact mul_left_cancel₀ hg hxy)]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  ring

/-- **Index-2 dilation split.**  On a disjoint two-coset cover `G = H ∪ g·H` (the index-2 split of
`μ_n` along `μ_{n/2}` with coset rep `g ≠ 0`), the period factors as the sub-period at `b` plus the
sub-period at the dilated frequency `g·b`:
`η_b = eta ψ H b + eta ψ H (g·b)`. -/
theorem eta_index_two_split_dilate {ψ : AddChar F ℂ} (H : Finset F) {g b : F} (hg : g ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => g * y))) :
    eta ψ (H ∪ H.image (fun y => g * y)) b = eta ψ H b + eta ψ H (g * b) := by
  unfold eta
  rw [Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image (by
    intro x _ y _ hxy
    exact mul_left_cancel₀ hg hxy)]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  ring

/-- **Half-mass as a two-dilate sub-period sum.**  The index-2 half-mass `‖A_b‖ + ‖B_b‖` equals the
sub-period magnitude at the two multiplicatively-dilated frequencies `b` and `g·b`:
`‖eta ψ H b‖ + ‖eta ψ (g·H) b‖ = ‖eta ψ H b‖ + ‖eta ψ H (g·b)‖`. -/
theorem halfMass_eq_two_dilate {ψ : AddChar F ℂ} (H : Finset F) {g b : F} (hg : g ≠ 0) :
    ‖eta ψ H b‖ + ‖eta ψ (H.image (fun y => g * y)) b‖
      = ‖eta ψ H b‖ + ‖eta ψ H (g * b)‖ := by
  rw [eta_image_smul_eq_eta_dilate H hg]

/-- **The period norm equals the two-dilate sub-period combination.**  Combining the dilation split
with the triangle data, the worst-`b` period magnitude is controlled by the two-dilate half-mass:
`‖η_b‖ ≤ ‖eta ψ H b‖ + ‖eta ψ H (g·b)‖`.  Thus the open prize is a bound on the worst-`b` SUM of a
single sub-period at two dilated frequencies — exactly the half-mass equivalence object, now in dilation
form. -/
theorem norm_eta_le_two_dilate {ψ : AddChar F ℂ} (H : Finset F) {g b : F} (hg : g ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => g * y))) :
    ‖eta ψ (H ∪ H.image (fun y => g * y)) b‖ ≤ ‖eta ψ H b‖ + ‖eta ψ H (g * b)‖ := by
  rw [eta_index_two_split_dilate H hg hdisj]
  exact norm_add_le _ _

/-- **Equality form when the two dilates co-ray (the probed worst-`b` fact `ρ(b*)=1`).**  If the two
sub-period dilates `eta ψ H b` and `eta ψ H (g·b)` add coherently (no cancellation, `‖A+B‖=‖A‖+‖B‖`,
the proven same-ray fact at the prize-worst frequency), the period norm equals the two-dilate half-mass
exactly. -/
theorem norm_eta_eq_two_dilate_of_coherent {ψ : AddChar F ℂ} (H : Finset F) {g b : F} (hg : g ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => g * y)))
    (hcoh : ‖eta ψ H b + eta ψ H (g * b)‖ = ‖eta ψ H b‖ + ‖eta ψ H (g * b)‖) :
    ‖eta ψ (H ∪ H.image (fun y => g * y)) b‖ = ‖eta ψ H b‖ + ‖eta ψ H (g * b)‖ := by
  rw [eta_index_two_split_dilate H hg hdisj, hcoh]

end ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm

#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm.eta_image_smul_eq_eta_dilate
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm.eta_index_two_split_dilate
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm.halfMass_eq_two_dilate
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm.norm_eta_le_two_dilate
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm.norm_eta_eq_two_dilate_of_coherent
