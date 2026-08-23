/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# Affine block kernels: realizing the projective line as constancy obstructions
# (issue #334, A3 MCA-instance, verified core)

The algebraic heart of the block-line construction for the A3 sharpness instance (the
generator whose Lemma-4.1 obstructions defeat every `UniformObstruction` cover,
`Jo26DichotomySharpness.lean`): on a block of positions indexed by the field itself, the
two-row **affine pattern** `(u, w)(j) = (j, c·j)` has the property that the `λ`-combination
`λ₁·u + λ₂·w` is *constant on the block* exactly when `λ` lies on the line
`{λ : λ₁ + c·λ₂ = 0}` — and the vertical pattern `(0, j)` carves the remaining line
`{λ : λ₂ = 0}`. Ranging over `c : F` plus the vertical block realizes **all `q+1` directions**
of the projective line as block-local constancy kernels (`projLine`-indexed, matching
`Jo26DichotomySharpness.projLine`).

These are the verified bricks the full MCA-level instance will assemble (the remaining open
plumbing — seed badness and the generator block-selection — is catalogued on issue #334);
nothing here claims the instance itself.
-/

namespace ProximityGap

variable {F : Type} [Field F]

/-- The combination of the affine block pattern `(j, c·j)`: `λ₁·j + λ₂·(c·j)`. -/
def affineBlockCombo (c : F) (lam : Fin 2 → F) (j : F) : F :=
  lam 0 * j + lam 1 * (c * j)

/-- The combination of the vertical block pattern `(0, j)`: `λ₂·j`. -/
def verticalBlockCombo (lam : Fin 2 → F) (j : F) : F :=
  lam 1 * j

/-- **The affine block kernel is a line**: the `λ`-combination of the pattern `(j, c·j)` is
constant in `j` iff `λ₁ + c·λ₂ = 0` (in which case it is identically `0`). Needs at least two
points, i.e. a nontrivial field. -/
theorem affineBlockCombo_constant_iff [Nontrivial F] (c : F) (lam : Fin 2 → F) :
    (∃ b : F, ∀ j : F, affineBlockCombo c lam j = b) ↔ lam 0 + c * lam 1 = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    have h0 := hb 0
    have h1 := hb 1
    simp only [affineBlockCombo, mul_zero, add_zero, mul_one] at h0 h1
    -- h0 : 0 = b; h1 : lam 0 + lam 1 * c = b
    rw [← h0] at h1
    linear_combination h1
  · intro h
    refine ⟨0, fun j => ?_⟩
    have : (lam 0 + c * lam 1) * j = 0 := by rw [h]; ring
    calc affineBlockCombo c lam j = (lam 0 + c * lam 1) * j := by
          unfold affineBlockCombo; ring
    _ = 0 := this

/-- **The vertical block kernel is the horizontal line**: the combination of `(0, j)` is
constant iff `λ₂ = 0`. -/
theorem verticalBlockCombo_constant_iff [Nontrivial F] (lam : Fin 2 → F) :
    (∃ b : F, ∀ j : F, verticalBlockCombo lam j = b) ↔ lam 1 = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    have h0 := hb 0
    have h1 := hb 1
    simp only [verticalBlockCombo, mul_zero, mul_one] at h0 h1
    rw [← h0] at h1
    exact h1
  · intro h
    exact ⟨0, fun j => by simp [verticalBlockCombo, h]⟩

/-- **All `q+1` directions are realized**: the constancy kernel of the `c`-affine block is
exactly the span of `(−c, 1)`-shaped vectors (the `projLine (some (−c))`-type direction
... stated kernel-wise), and the vertical block realizes `λ₂ = 0` (the `projLine none`-type
direction). Packaged as: for every `λ ≠ 0` there is a block on which `λ`'s combination is
constant, and distinct nonproportional `λ`'s are separated by some block — i.e. the
block-kernel family is in bijection with the projective line. Here we record the two
membership characterizations; the bijection bookkeeping lives with the instance assembly. -/
theorem affineBlock_kernel_mem_iff [Nontrivial F] (c : F) (lam : Fin 2 → F) :
    (∃ b : F, ∀ j : F, affineBlockCombo c lam j = b) ↔ lam 0 = -c * lam 1 := by
  rw [affineBlockCombo_constant_iff]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.affineBlockCombo_constant_iff
#print axioms ProximityGap.verticalBlockCombo_constant_iff
#print axioms ProximityGap.affineBlock_kernel_mem_iff
