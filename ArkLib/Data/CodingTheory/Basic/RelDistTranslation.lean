/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Translation invariance of the distance to a linear code

For a linear code `C` (a submodule of `ι → F`) and any codeword `c ∈ C`, the relative distance
`δᵣ(·, C)` is invariant under translation by `c`:

  `δᵣ(u + c, C) = δᵣ(u, C)`.

Consequently `δᵣ(·, C)` is constant on each coset of `C` — the structural fact behind the
coset/syndrome decomposition `#{w far from C} = |C| · #{cosets with leader-weight > δn}` used to
analyse the CS25 complete-CA-breakdown covering bound (T4.17, #82).
-/

open scoped NNReal ENNReal

namespace Code

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- **Translation invariance of `δᵣ(·, C)` for a linear code.** For `c ∈ C`,
`δᵣ(u + c, C) = δᵣ(u, C)`. The relative Hamming distance to `C` is invariant under adding a
codeword, because `v ↦ v + c` (resp. `v ↦ v - c`) is a distance-preserving bijection of `C`. -/
theorem relDistFromCode_add_mem (C : Submodule F (ι → F)) (u : ι → F) {c : ι → F} (hc : c ∈ C) :
    relDistFromCode (u + c) (C : Set (ι → F)) = relDistFromCode u (C : Set (ι → F)) := by
  -- pointwise: distance from `u + c` to `v` equals distance from `u` to `v - c`
  have key : ∀ v : ι → F, relHammingDist (u + c) v = relHammingDist u (v - c) := by
    intro v
    have h : hammingDist (u + c) v = hammingDist u (v - c) := by
      have hcomp := hammingDist_comp (fun (i : ι) (x : F) => x + c i) (x := u) (y := v - c)
        (fun i => add_left_injective (c i))
      have e1 : (fun i => u i + c i) = u + c := rfl
      have e2 : (fun i => (v - c) i + c i) = v := by
        funext i; simp [Pi.sub_apply, sub_add_cancel]
      rw [e1, e2] at hcomp
      exact hcomp
    unfold relHammingDist
    rw [h]
  unfold relDistFromCode
  congr 1
  ext d
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, hw, hle⟩
    exact ⟨w - c, C.sub_mem hw hc, by rw [← key w]; exact hle⟩
  · rintro ⟨w, hw, hle⟩
    refine ⟨w + c, C.add_mem hw hc, ?_⟩
    rw [key (w + c), add_sub_cancel_right]; exact hle

/-- `δᵣ(·, C)` is constant on each coset of the linear code `C`: if `u - u' ∈ C` then
`δᵣ(u, C) = δᵣ(u', C)`. Immediate from `relDistFromCode_add_mem` with `c := u - u'`. -/
theorem relDistFromCode_eq_of_sub_mem (C : Submodule F (ι → F)) {u u' : ι → F}
    (h : u - u' ∈ C) :
    relDistFromCode u (C : Set (ι → F)) = relDistFromCode u' (C : Set (ι → F)) := by
  have := relDistFromCode_add_mem C u' h
  rwa [add_sub_cancel] at this

end Code
