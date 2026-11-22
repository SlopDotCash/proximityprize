/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyQuarticTwist
import Mathlib.LinearAlgebra.Prod

/-!
# Determinant pencils on the projective line

For an endomorphism `J` of a two-dimensional space, the brackets of
`(s I + t J)y` with a fixed row vector are homogeneous linear forms in the
parameter. In a non-eigenline column, their projective roots are explicit.
At a singular parameter the four bracket values on any rectangle have square
product.
-/

namespace ProximityGap.PaleyTorusPencil

open ProximityGap.PaleyQuarticTwist (bracket bracket_coordinates)

variable {K : Type*} [Field K]

/-- The endomorphism with homogeneous parameters `(s,t)` in the pencil of `I,J`. -/
def pencil (J : Module.End K (K × K)) (u : K × K) : Module.End K (K × K) :=
  u.1 • LinearMap.id + u.2 • J

/-- Every bracket entry of the pencil is a linear form in its parameters. -/
theorem bracket_pencil (J : Module.End K (K × K)) (u x y : K × K) :
    bracket x (pencil J u y) = u.1 * bracket x y + u.2 * bracket x (J y) := by
  simp [pencil, bracket, Prod.smul_fst, Prod.smul_snd]
  ring

/-- Homogeneous parameter for which the pencil sends the column line to the row line. -/
def collisionParameter (J : Module.End K (K × K)) (x y : K × K) : K × K :=
  (bracket x (J y), -bracket x y)

/-- At the collision parameter the image is the row, scaled by the column determinant. -/
theorem pencil_collision (J : Module.End K (K × K)) (x y : K × K) :
    pencil J (collisionParameter J x y) y = bracket y (J y) • x := by
  ext <;> simp [pencil, collisionParameter, bracket, Prod.smul_fst, Prod.smul_snd] <;> ring

/-- A nonzero row and a column off the eigenlines give a nonzero homogeneous root. -/
theorem collisionParameter_ne_zero (J : Module.End K (K × K)) {x y : K × K}
    (hx : x ≠ 0) (hy : bracket y (J y) ≠ 0) : collisionParameter J x y ≠ 0 := by
  intro h
  have he := pencil_collision J x y
  rw [h] at he
  exact (smul_ne_zero hy hx) (by simpa [pencil] using he.symm)

/-- The bracket value is the projective determinant against the explicit root. -/
theorem bracket_pencil_eq_parameter (J : Module.End K (K × K)) (u x y : K × K) :
    bracket x (pencil J u y) = bracket (collisionParameter J x y) u := by
  rw [bracket_pencil]
  unfold collisionParameter bracket
  dsimp
  ring

/-- Each nonzero homogeneous vector on a given line has a unique scale relative
to a fixed nonzero representative. The scale is nonzero if the vector is. -/
theorem bracket_zero_iff_unique_scale {v u : K × K} (hv : v ≠ 0) :
    bracket v u = 0 ↔ ∃! c : K, u = c • v := by
  constructor
  · intro h
    unfold bracket at h
    by_cases h₁ : v.1 = 0
    · have h₂ : v.2 ≠ 0 := fun hz => hv (Prod.ext h₁ hz)
      have hu : u.1 = 0 := by
        rw [h₁] at h
        simpa [h₂] using h
      refine ⟨u.2 / v.2, Prod.ext ?_ ?_, ?_⟩
      · simp [h₁, hu]
      · simp [div_mul_cancel₀ _ h₂]
      · intro c hc
        apply (eq_div_iff h₂).2
        simpa using (congrArg Prod.snd hc).symm
    · refine ⟨u.1 / v.1, Prod.ext ?_ ?_, ?_⟩
      · simp [div_mul_cancel₀ _ h₁]
      · change u.2 = u.1 / v.1 * v.2
        field_simp [h₁]
        linear_combination h
      · intro c hc
        apply (eq_div_iff h₁).2
        simpa using (congrArg Prod.fst hc).symm
  · rintro ⟨c, rfl, _⟩
    simp [bracket, Prod.smul_fst, Prod.smul_snd]
    ring

/-- The collision parameter is the unique projective root, expressed by a unique
scalar for any chosen homogeneous representative of a root. -/
theorem pencil_zero_iff_unique_scale (J : Module.End K (K × K)) {x y : K × K}
    (hx : x ≠ 0) (hy : bracket y (J y) ≠ 0) (u : K × K) :
    bracket x (pencil J u y) = 0 ↔ ∃! c : K, u = c • collisionParameter J x y := by
  rw [bracket_pencil_eq_parameter,
    bracket_zero_iff_unique_scale (collisionParameter_ne_zero J hx hy)]

private theorem map_coordinates (A : Module.End K (K × K)) (w : K × K) :
    A w = w.1 • A (1, 0) + w.2 • A (0, 1) := by
  rw [← A.map_smul, ← A.map_smul, ← A.map_add]
  congr 1
  ext <;> simp

/-- In a fixed column off the eigenlines, different row lines have different roots. -/
theorem collision_same_column (J : Module.End K (K × K)) (x w y : K × K) :
    bracket (collisionParameter J x y) (collisionParameter J w y) =
      bracket y (J y) * bracket x w := by
  unfold collisionParameter bracket
  dsimp
  ring

/-- In a fixed row off the eigenlines, different column lines have different roots. -/
theorem collision_same_row (J : Module.End K (K × K)) (x y z : K × K) :
    bracket (collisionParameter J x y) (collisionParameter J x z) =
      -(bracket x (J x)) * bracket y z := by
  unfold collisionParameter
  rw [map_coordinates J x, map_coordinates J y, map_coordinates J z]
  simp [bracket, Prod.smul_fst, Prod.smul_snd]
  ring

/-- Determinant of an endomorphism in the standard homogeneous coordinates. -/
def determinant (A : Module.End K (K × K)) : K :=
  bracket (A (1, 0)) (A (0, 1))

/-- The same determinant scales every pair of homogeneous column brackets. -/
theorem bracket_map (A : Module.End K (K × K)) (y z : K × K) :
    bracket (A y) (A z) = determinant A * bracket y z := by
  rw [map_coordinates A y, map_coordinates A z]
  simp [determinant, bracket, Prod.smul_fst, Prod.smul_snd]
  ring

/-- The determinant of the pencil is its homogeneous characteristic quadratic. -/
theorem determinant_pencil (J : Module.End K (K × K)) (u : K × K) :
    determinant (pencil J u) =
      u.1 ^ 2 + u.1 * u.2 * ((J (1, 0)).1 + (J (0, 1)).2) + u.2 ^ 2 * determinant J := by
  simp [determinant, pencil, bracket, Prod.smul_fst, Prod.smul_snd]
  ring

/-- At a singular parameter the four-site product is the square of a diagonal
product. This includes rectangles meeting the kernel or image of the map. -/
theorem singular_rectangle_square (A : Module.End K (K × K)) (hA : determinant A = 0)
    (x w y z : K × K) :
    bracket x (A y) * bracket x (A z) * bracket w (A y) * bracket w (A z) =
      (bracket x (A y) * bracket w (A z)) ^ 2 := by
  have hcols : bracket (A y) (A z) = 0 := by rw [bracket_map, hA, zero_mul]
  have h := bracket_coordinates x w (A y) (A z)
  have hdiag : bracket x (A z) * bracket w (A y) = bracket x (A y) * bracket w (A z) := by
    rw [hcols, mul_zero] at h
    unfold bracket at *
    linear_combination h
  calc
    _ = (bracket x (A y) * bracket w (A z)) * (bracket x (A z) * bracket w (A y)) := by ring
    _ = _ := by rw [hdiag, pow_two]

#print axioms pencil_zero_iff_unique_scale
#print axioms pencil_collision
#print axioms collision_same_row
#print axioms collision_same_column
#print axioms determinant_pencil
#print axioms singular_rectangle_square

end ProximityGap.PaleyTorusPencil
