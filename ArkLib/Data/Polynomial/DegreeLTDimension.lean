/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension of the low-degree polynomial space

`Module.finrank R (Polynomial.degreeLT R k) = k`, via the canonical coefficient isomorphism
`Polynomial.degreeLTEquiv : degreeLT R k ≃ₗ[R] (Fin k → R)`.

This is the dimension count underlying polynomial interpolation and the Reed-Solomon /
Berlekamp-Welch / Polishchuk-Spielman existence arguments: the space of degree-`< k` polynomials
is `k`-dimensional, so a system with more constraints than `k` (or, bivariately, than the
bidegree dimension) has a nonzero solution.
-/

namespace Polynomial

variable {R : Type*} [DivisionRing R]

/-- The space of polynomials of degree `< k` over a division ring is `k`-dimensional. -/
@[simp]
theorem finrank_degreeLT (k : ℕ) : Module.finrank R (Polynomial.degreeLT R k) = k := by
  rw [(Polynomial.degreeLTEquiv R k).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

end Polynomial

namespace Polynomial

variable {F : Type*} [Field F]

/-- **Bivariate (Y-degree ≤ 1) interpolation existence, asymmetric degrees.** Given `N` points
`(xⱼ, yⱼ)` with `N < d₀ + d₁`, there is a nonzero pair `(A, B)` with `deg A < d₀`, `deg B < d₁`,
and `A(xⱼ) + yⱼ · B(xⱼ) = 0` at every point. This is the Polishchuk-Spielman /
Berlekamp-Welch existence engine: the pair-space `degreeLT d₀ × degreeLT d₁` has dimension
`d₀ + d₁`, the evaluation map to `F^N` has rank `≤ N < d₀ + d₁`, so its kernel is nontrivial.
With `d₁ = e+1` (locator `E := B`), `d₀ = k+e` (`N := -A`), and `y :=` received values,
`A(αⱼ) + yⱼ E(αⱼ) = 0` is exactly the Berlekamp-Welch key equation `E(αⱼ)·yⱼ = N(αⱼ)` - and
`k + 2e + 1 > n` is the unique-decoding condition. This is the existence half of the BCIKS20
proximity-gap bivariate lift. -/
theorem exists_bivariate_interpolant {J : Type*} [Fintype J] (d₀ d₁ : ℕ) (x y : J → F)
    (hJ : Fintype.card J < d₀ + d₁) :
    ∃ A B : F[X], A ∈ degreeLT F d₀ ∧ B ∈ degreeLT F d₁ ∧ (A ≠ 0 ∨ B ≠ 0) ∧
      ∀ j, A.eval (x j) + y j * B.eval (x j) = 0 := by
  classical
  haveI : FiniteDimensional F (degreeLT F d₀) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv F d₀).symm
  haveI : FiniteDimensional F (degreeLT F d₁) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv F d₁).symm
  -- The evaluation linear map `(A, B) ↦ (j ↦ A(xⱼ) + yⱼ·B(xⱼ))`.
  let T : (degreeLT F d₀ × degreeLT F d₁) →ₗ[F] (J → F) :=
    { toFun := fun AB j => AB.1.val.eval (x j) + y j * AB.2.val.eval (x j)
      map_add' := by
        intro a b
        funext j
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, eval_add, Pi.add_apply]
        ring
      map_smul' := by
        intro c a
        funext j
        simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, smul_eq_C_mul, eval_mul,
          eval_C, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        ring }
  -- Dimension count: `dim (J → F) = N < d₀ + d₁ = dim (degreeLT d₀ × degreeLT d₁)`.
  have hdim : Module.finrank F (J → F) < Module.finrank F (degreeLT F d₀ × degreeLT F d₁) := by
    simp only [Module.finrank_prod, finrank_degreeLT, Module.finrank_fintype_fun_eq_card]
    omega
  have hker : LinearMap.ker T ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨AB, hABmem, hAB0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨AB.1.val, AB.2.val, AB.1.property, AB.2.property, ?_, ?_⟩
  · by_contra h
    push Not at h
    exact hAB0 (Prod.ext (Subtype.ext h.1) (Subtype.ext h.2))
  · intro j
    exact congrFun (LinearMap.mem_ker.mp hABmem) j

/-- **General bivariate interpolation existence (the `(X × Z)` grid).** Given `N` points
`(xₖ, zₖ)` with `N < (dX+1)(dZ+1)`, there is a nonzero bidegree-`(≤ dX, ≤ dZ)` bivariate
polynomial `Q(X, Z) = ∑ⱼ Qⱼ(X)·Zʲ` (each `Qⱼ` of degree `< dX+1`, not all zero) vanishing at
every grid point: `∑ⱼ Qⱼ(xₖ)·zₖʲ = 0`. The bidegree space `Fin (dZ+1) → degreeLT (dX+1)` has
dimension `(dX+1)(dZ+1) > N`, so the evaluation map's kernel is nontrivial. This is the
Polishchuk-Spielman / Sudan / Guruswami-Sudan interpolation engine - the 2-D foundation of the
BCIKS20 exact-radius bivariate lift and of list decoding. -/
theorem exists_bivariate_interpolant_general {J : Type*} [Fintype J] (dX dZ : ℕ) (x z : J → F)
    (hJ : Fintype.card J < (dX + 1) * (dZ + 1)) :
    ∃ Q : Fin (dZ + 1) → F[X], (∀ j, Q j ∈ degreeLT F (dX + 1)) ∧ (∃ j, Q j ≠ 0) ∧
      ∀ k, ∑ j : Fin (dZ + 1), (Q j).eval (x k) * (z k) ^ (j : ℕ) = 0 := by
  classical
  haveI : FiniteDimensional F (degreeLT F (dX + 1)) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv F (dX + 1)).symm
  -- The evaluation map on the bidegree space `Fin (dZ+1) → degreeLT (dX+1)`.
  let T : (Fin (dZ + 1) → degreeLT F (dX + 1)) →ₗ[F] (J → F) :=
    { toFun := fun Q k => ∑ j : Fin (dZ + 1), (Q j).val.eval (x k) * (z k) ^ (j : ℕ)
      map_add' := by
        intro a b
        funext k
        simp only [Pi.add_apply, Submodule.coe_add, eval_add]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      map_smul' := by
        intro c a
        funext k
        simp only [Pi.smul_apply, SetLike.val_smul, smul_eq_C_mul, eval_mul, eval_C,
          RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring }
  have hdim : Module.finrank F (J → F)
      < Module.finrank F (Fin (dZ + 1) → degreeLT F (dX + 1)) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype]
    simp only [finrank_degreeLT, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    exact lt_of_lt_of_eq hJ (Nat.mul_comm _ _)
  have hker : LinearMap.ker T ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨Q, hQmem, hQ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨fun j => (Q j).val, fun j => (Q j).property, ?_, ?_⟩
  · by_contra h
    push Not at h
    exact hQ0 (funext fun j => Subtype.ext (h j))
  · intro k
    exact congrFun (LinearMap.mem_ker.mp hQmem) k

end Polynomial
