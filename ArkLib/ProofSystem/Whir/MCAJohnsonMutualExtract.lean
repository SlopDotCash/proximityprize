/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Mutual agreement extraction for the affine line (toward MCA Johnson)

The algebraic core of *mutual* correlated agreement: from two good points
`γ ≠ γ'` on the affine line `f₀ + γ·f₁`, whose proximate Reed–Solomon codewords
`c, c'` agree with the line on a common set `S`, one extracts a genuine *pair*
of degree-`<deg` polynomials `(p₀, p₁)` that simultaneously interpolate
`(f₀, f₁)` on all of `S`. This is precisely the joint/codeword-pair structure
that "mutual correlated agreement" asserts — here derived honestly from the
collinearity `p₁ = (c−c')/(γ−γ')`, `p₀ = c − γ·p₁`. -/

namespace MCAJohnson

open Polynomial

variable {F : Type*} [Field F] {ι : Type*} (domain : ι ↪ F)

/-- **Affine-line mutual extraction.** Two collinear Reed–Solomon proximates of
the line `f₀ + γ·f₁` (at distinct slopes `γ ≠ γ'`), agreeing with the line on a
common set `S`, yield a degree-`<deg` polynomial pair `(p₀, p₁)` interpolating
`(f₀, f₁)` on `S`. -/
theorem affineLine_mutual_extract {deg : ℕ}
    {c c' : F[X]} (hc : c ∈ Polynomial.degreeLT F deg)
    (hc' : c' ∈ Polynomial.degreeLT F deg)
    {γ γ' : F} (hγ : γ ≠ γ') {f₀ f₁ : ι → F} {S : Finset ι}
    (h : ∀ x ∈ S, c.eval (domain x) = f₀ x + γ * f₁ x ∧
                  c'.eval (domain x) = f₀ x + γ' * f₁ x) :
    ∃ p₀ p₁ : F[X], p₀ ∈ Polynomial.degreeLT F deg ∧
        p₁ ∈ Polynomial.degreeLT F deg ∧
        ∀ x ∈ S, p₁.eval (domain x) = f₁ x ∧ p₀.eval (domain x) = f₀ x := by
  have hne : γ - γ' ≠ 0 := sub_ne_zero.mpr hγ
  -- the recovered slope and intercept polynomials
  set p₁ : F[X] := (γ - γ')⁻¹ • (c - c') with hp₁
  set p₀ : F[X] := c - γ • p₁ with hp₀
  have hsub : c - c' ∈ Polynomial.degreeLT F deg := Submodule.sub_mem _ hc hc'
  have hp₁mem : p₁ ∈ Polynomial.degreeLT F deg := Submodule.smul_mem _ _ hsub
  have hp₀mem : p₀ ∈ Polynomial.degreeLT F deg :=
    Submodule.sub_mem _ hc (Submodule.smul_mem _ _ hp₁mem)
  refine ⟨p₀, p₁, hp₀mem, hp₁mem, fun x hx => ?_⟩
  obtain ⟨he, he'⟩ := h x hx
  -- p₁ evaluates to f₁ on S
  have hp₁eval : p₁.eval (domain x) = f₁ x := by
    rw [hp₁, Polynomial.eval_smul, Polynomial.eval_sub, he, he', smul_eq_mul]
    field_simp
    ring
  -- p₀ evaluates to f₀ on S
  have hp₀eval : p₀.eval (domain x) = f₀ x := by
    rw [hp₀, Polynomial.eval_sub, Polynomial.eval_smul, hp₁eval, he, smul_eq_mul]
    ring
  exact ⟨hp₁eval, hp₀eval⟩

end MCAJohnson
