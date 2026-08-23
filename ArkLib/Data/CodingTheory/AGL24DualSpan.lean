/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24AppendixAssembly

/-!
# [AGL24] pinning from the zero-pattern dual span (issue #346, brick 25)

The final interface-tightening of the Appendix A reduction: the `PinningProperty` (display
(A.6)) follows from what GM-MDS (Theorem A.2) *literally* provides — a family of dual
vectors, each supported inside a single edge-support, spanning the code's orthogonal
complement (the rows of `M·H` with `M` invertible and `H` a parity-check matrix).

* `dotForm` — the dot-product bilinear form on `ι → F`, with `dotForm_nondegenerate` and
  `dotForm_isRefl` (self-duality through `Pi.single` testing);
* `pinning_of_dual_span` — **the derivation**: each dual vector annihilates `y` (its support
  forces `y = c⁽ʲ⁾` there, and it annihilates `c⁽ʲ⁾`), so `y` lies in the double orthogonal
  of the code — which *is* the code (`orthogonal_orthogonal`).

After this brick the GM-MDS import is stated in its native matrix-free form: produce
zero-pattern dual vectors spanning the dual of the Reed–Solomon code.
-/

open Finset

namespace AGL24

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-- The dot-product bilinear form on `ι → F`. -/
def dotForm : LinearMap.BilinForm F (ι → F) :=
  LinearMap.mk₂ F (fun x y => ∑ i, x i * y i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun a x y => by simp [Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun a x y => by simp [Finset.mul_sum, mul_left_comm])

theorem dotForm_apply (x y : ι → F) : dotForm x y = ∑ i, x i * y i := rfl

theorem dotForm_isRefl : (dotForm (ι := ι) (F := F)).IsRefl := by
  intro x y hxy
  rw [dotForm_apply] at hxy ⊢
  rw [← hxy]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dotForm_separatingLeft : LinearMap.SeparatingLeft (dotForm (ι := ι) (F := F)) := by
  intro x hx
  funext i
  have := hx (Pi.single i 1)
  rw [dotForm_apply] at this
  rw [Finset.sum_eq_single i (fun j _ hne => by
      rw [Pi.single_eq_of_ne hne, mul_zero])
    (fun h => absurd (Finset.mem_univ i) h)] at this
  rw [Pi.single_eq_same, mul_one] at this
  exact this

theorem dotForm_nondegenerate : (dotForm (ι := ι) (F := F)).Nondegenerate := by
  constructor
  · exact dotForm_separatingLeft
  · intro y hy
    funext i
    have := hy (Pi.single i 1)
    rw [dotForm_apply] at this
    rw [Finset.sum_eq_single i (fun j _ hne => by
        rw [Pi.single_eq_of_ne hne, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)] at this
    rw [Pi.single_eq_same, one_mul] at this
    exact this

/-- **Pinning from the zero-pattern dual span** (the native GM-MDS output form): dual
vectors, each supported inside one edge-support, spanning the code's orthogonal complement,
yield the `PinningProperty`. -/
theorem pinning_of_dual_span {t k : ℕ} [Fintype F] [DecidableEq F] [Nonempty ι]
    (φ : ι ↪ F) (e : ι → Finset (Fin (t + 1)))
    {d : ℕ} (h : Fin d → (ι → F))
    (hsupp : ∀ ℓ, ∃ j : Fin (t + 1), ∀ i : ι, j ∉ e i → h ℓ i = 0)
    (hspan : Submodule.span F (Set.range h)
      = dotForm.orthogonal (ReedSolomon.code φ k)) :
    PinningProperty (k := k) φ e := by
  classical
  intro y c hc hagree
  -- y is orthogonal to every generator.
  have hgen : ∀ ℓ, dotForm (h ℓ) y = 0 := by
    intro ℓ
    obtain ⟨j, hj⟩ := hsupp ℓ
    -- On the support of h ℓ, y agrees with c j.
    have hy_eq : dotForm (h ℓ) y = dotForm (h ℓ) (c j) := by
      rw [dotForm_apply, dotForm_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hji : j ∈ e i
      · rw [hagree i j hji]
      · rw [hj i hji, zero_mul, zero_mul]
    rw [hy_eq]
    -- h ℓ annihilates the codeword c j.
    have hmem : h ℓ ∈ dotForm.orthogonal (ReedSolomon.code φ k) := by
      rw [← hspan]
      exact Submodule.subset_span ⟨ℓ, rfl⟩
    have := hmem (c j) (hc j)
    exact dotForm_isRefl _ _ this
  -- Hence y is orthogonal to the whole span = the code's orthogonal.
  have hyorth : y ∈ dotForm.orthogonal (dotForm.orthogonal (ReedSolomon.code φ k)) := by
    rw [← hspan]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨ℓ, rfl⟩ := hv
        exact hgen ℓ
    | zero =>
        show dotForm (0 : ι → F) y = 0
        rw [map_zero, LinearMap.zero_apply]
    | add v w _ _ hv hw =>
        show dotForm (v + w) y = 0
        rw [map_add, LinearMap.add_apply]
        rw [show dotForm v y = 0 from hv, show dotForm w y = 0 from hw, add_zero]
    | smul a v _ hv =>
        show dotForm (a • v) y = 0
        rw [map_smul, LinearMap.smul_apply, show dotForm v y = 0 from hv, smul_zero]
  -- The double orthogonal is the code.
  rw [LinearMap.BilinForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_isRefl]
    at hyorth
  exact hyorth

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.dotForm_nondegenerate
#print axioms AGL24.pinning_of_dual_span
