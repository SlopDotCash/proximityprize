/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The Siegel lemma and the Guruswami–Sudan interpolation core

This file isolates, as reusable lemmas, the linear-algebra core underlying the
existence of the Guruswami–Sudan interpolant (the "improved count" version of
[BCKHS25], §3.1).  The whole argument rests on a single counting principle —
a finite-dimensional **Siegel lemma**: a linear map out of a vector space of
strictly larger dimension than its target must have a non-trivial kernel.

We provide three layers, from the abstract principle to the concrete
trivariate Guruswami–Sudan interpolant:

1. `ArkLib.siegel_exists_nonzero` : the Siegel lemma for a linear map
   `T : V →ₗ[K] W` between finite-dimensional `K`-vector spaces with
   `finrank K W < finrank K V`: there is `v ≠ 0` with `T v = 0`.

2. `ArkLib.exists_nonzero_constraint_solution` : the combinatorial corollary
   used by Guruswami–Sudan.  Given a finite "monomial" index set `M`, a finite
   "constraint" index set `C` with `#C < #M`, and a constraint matrix
   `a : C → M → K`, there is a non-zero coefficient vector `c : M → K`
   satisfying every constraint `∑ i, c i * a j i = 0`.

3. The trivariate interpolant.  We work with `MvPolynomial (Fin 3) K`:
   * `ArkLib.GS.vanishCon p d` is the `K`-linear "Hasse-derivative" functional
     `Q ↦ coeff d (Q(X + p))`, i.e. reading the `d`-th coefficient of the
     translate of `Q` to the point `p`.  A polynomial vanishes to multiplicity
     `m` at `p` exactly when `vanishCon p d Q = 0` for all `d` of total degree
     `< m` (this is the standard Hasse-derivative characterisation of
     multiplicity; the factorial normalisation is irrelevant to the
     zero/non-zero condition).
   * `ArkLib.GS.exists_nonzero_box_poly` : if a degree box `box` (a finite set
     of monomial exponents) has more monomials than there are vanishing
     constraints `cons`, then there is a non-zero polynomial supported on the
     box satisfying every constraint.
   * `ArkLib.GS.exists_gs_interpolant` : the multiplicity-`m` specialisation,
     where the constraints are `pts ×ˢ derivs` for a finite point set `pts` and
     a finite set `derivs` of derivative orders (for genuine multiplicity-`m`
     vanishing one takes `derivs = {d | d.degree < m}`).  Under the GS count
     `pts.card * derivs.card < box.card` there is a non-zero box-supported `Q`
     that vanishes (`vanishCon p d Q = 0`) at every `(p, d) ∈ pts ×ˢ derivs`.

## References

* [BCKHS25] — Guruswami–Sudan interpolant existence, §3.1 (improved count).
-/

open Module Finset

namespace ArkLib

/-! ## 1. The Siegel lemma -/

/-- **Siegel lemma (finite-dimensional form).**  A linear map `T : V →ₗ[K] W`
between finite-dimensional `K`-vector spaces whose target has strictly smaller
dimension than its source has a non-trivial kernel: there exists `v ≠ 0` with
`T v = 0`.  This is the linear-algebra heart of the Guruswami–Sudan interpolant
existence argument (more unknowns than constraints ⟹ a non-zero solution). -/
theorem siegel_exists_nonzero {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V →ₗ[K] W) (h : finrank K W < finrank K V) :
    ∃ v : V, v ≠ 0 ∧ T v = 0 := by
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective T := LinearMap.ker_eq_bot.mp hbot
    have hle : finrank K V ≤ finrank K W :=
      LinearMap.finrank_le_finrank_of_injective hinj
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv0, by simpa using hv⟩

/-! ## 2. The constraint-matrix corollary -/

/-- The constraint linear map of a matrix `a : C → M → K`, sending a coefficient
vector `c : M → K` to the vector of constraint values `j ↦ ∑ i, c i * a j i`. -/
def constraintMatrixMap {K : Type*} [Field K] {M C : Type*} [Fintype M]
    (a : C → M → K) : (M → K) →ₗ[K] (C → K) where
  toFun c j := ∑ i : M, c i * a j i
  map_add' x y := by ext j; simp [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by ext j; simp [Finset.mul_sum, mul_comm, mul_left_comm]

@[simp] lemma constraintMatrixMap_apply {K : Type*} [Field K] {M C : Type*}
    [Fintype M] (a : C → M → K) (c : M → K) (j : C) :
    constraintMatrixMap a c j = ∑ i : M, c i * a j i := rfl

/-- **Guruswami–Sudan counting corollary (matrix form).**  Given a finite set
`M` of "monomials", a finite set `C` of linear "constraints" with `#C < #M`, and
a constraint matrix `a : C → M → K`, there is a non-zero coefficient vector
`c : M → K` satisfying every constraint `∑ i, c i * a j i = 0`.  Equivalently:
the kernel of the constraint matrix `(M → K) →ₗ[K] (C → K)` is non-trivial. -/
theorem exists_nonzero_constraint_solution {K : Type*} [Field K] {M C : Type*}
    [Fintype M] [Fintype C] (a : C → M → K)
    (h : Fintype.card C < Fintype.card M) :
    ∃ c : M → K, c ≠ 0 ∧ ∀ j : C, ∑ i : M, c i * a j i = 0 := by
  have hrank : finrank K (C → K) < finrank K (M → K) := by
    simpa [finrank_fintype_fun_eq_card] using h
  obtain ⟨c, hc0, hc⟩ := siegel_exists_nonzero (constraintMatrixMap a) hrank
  refine ⟨c, hc0, fun j => ?_⟩
  have := congrFun hc j
  simpa using this

/-! ## 3. The trivariate Guruswami–Sudan interpolant -/

namespace GS

open MvPolynomial

/-- The `K`-linear "Hasse-derivative" functional of order `d` at the point `p`:
it reads the `d`-th coefficient of the translate `Q(X + p)` of `Q`.  A
polynomial `Q` vanishes to multiplicity `m` at `p` iff `vanishCon p d Q = 0`
for every order `d` of total degree `< m`. -/
noncomputable def vanishCon {K : Type*} [CommRing K] (p : Fin 3 → K)
    (d : Fin 3 →₀ ℕ) : MvPolynomial (Fin 3) K →ₗ[K] K :=
  (lcoeff K d) ∘ₗ (aeval (fun i => X i + C (p i))).toLinearMap

/-- The polynomial `∑_{d ∈ box} c d · X^d` built from a coefficient vector on a
degree box, as a `K`-linear map in the coefficients. -/
noncomputable def polyOfLin {K : Type*} [CommRing K] (box : Finset (Fin 3 →₀ ℕ)) :
    (box → K) →ₗ[K] MvPolynomial (Fin 3) K where
  toFun c := ∑ d : box, c d • monomial (d : Fin 3 →₀ ℕ) 1
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r x := by simp [smul_smul, Finset.smul_sum]

/-- The coefficient of `polyOfLin box c` at a box exponent `d` is exactly `c d`. -/
lemma coeff_polyOfLin {K : Type*} [CommRing K] (box : Finset (Fin 3 →₀ ℕ))
    (c : box → K) (d : box) :
    coeff (d : Fin 3 →₀ ℕ) (polyOfLin box c) = c d := by
  show coeff (d : Fin 3 →₀ ℕ) (∑ e : box, c e • monomial (e : Fin 3 →₀ ℕ) 1) = c d
  rw [coeff_sum, Finset.sum_eq_single d]
  · simp [coeff_smul, coeff_monomial]
  · intro b _ hbd
    simp only [coeff_smul, coeff_monomial]
    rw [if_neg (fun h => hbd (Subtype.ext h))]; simp
  · intro h; simp at h

/-- The support of `polyOfLin box c` is contained in the box. -/
lemma support_polyOfLin {K : Type*} [CommRing K] (box : Finset (Fin 3 →₀ ℕ))
    (c : box → K) : (polyOfLin box c).support ⊆ box := by
  show (∑ d : box, c d • monomial (d : Fin 3 →₀ ℕ) 1).support ⊆ box
  refine MvPolynomial.support_sum.trans ?_
  intro e he
  simp only [Finset.mem_biUnion] at he
  obtain ⟨d, _, hd⟩ := he
  have hsub : (c d • monomial (d : Fin 3 →₀ ℕ) (1 : K)).support ⊆ {(d : Fin 3 →₀ ℕ)} := by
    refine MvPolynomial.support_smul.trans ?_
    intro x hx
    rw [MvPolynomial.mem_support_iff, coeff_monomial] at hx
    by_contra hxd
    rw [Finset.mem_singleton] at hxd
    rw [if_neg (fun h => hxd h.symm)] at hx
    exact hx rfl
  have := hsub hd
  rw [Finset.mem_singleton] at this
  rw [this]; exact d.2

/-- A non-zero coefficient vector yields a non-zero polynomial. -/
lemma polyOfLin_ne_zero {K : Type*} [CommRing K] (box : Finset (Fin 3 →₀ ℕ))
    (c : box → K) (hc : c ≠ 0) : polyOfLin box c ≠ 0 := by
  intro hQ
  apply hc
  funext d
  have hcoeff := coeff_polyOfLin box c d
  rw [hQ, coeff_zero] at hcoeff
  simp [hcoeff.symm]

/-- The combined constraint map: a coefficient vector on the box is sent to the
family of constraint values `vanishCon p d (polyOfLin box c)` indexed by the
constraint set `cons`. -/
noncomputable def consMap {K : Type*} [CommRing K] (box : Finset (Fin 3 →₀ ℕ))
    (cons : Finset ((Fin 3 → K) × (Fin 3 →₀ ℕ))) :
    (box → K) →ₗ[K] (cons → K) where
  toFun c := fun pd => vanishCon (pd : (Fin 3 → K) × (Fin 3 →₀ ℕ)).1
    (pd : (Fin 3 → K) × (Fin 3 →₀ ℕ)).2 (polyOfLin box c)
  map_add' x y := by ext pd; simp [map_add]
  map_smul' r x := by ext pd; simp [map_smul]

/-- **Guruswami–Sudan interpolant — coefficient form.**  If a degree box has
strictly more monomials than there are vanishing constraints, then there is a
non-zero coefficient vector on the box whose polynomial satisfies every
constraint.  (`vanishCon p d (polyOfLin box c) = 0` is the order-`d` vanishing
condition at the point `p`.) -/
theorem exists_nonzero_box_coeffs {K : Type*} [Field K]
    (box : Finset (Fin 3 →₀ ℕ)) (cons : Finset ((Fin 3 → K) × (Fin 3 →₀ ℕ)))
    (hcount : cons.card < box.card) :
    ∃ c : box → K, c ≠ 0 ∧
      ∀ pd ∈ cons, vanishCon pd.1 pd.2 (polyOfLin box c) = 0 := by
  have hrank : finrank K (cons → K) < finrank K (box → K) := by
    simpa [finrank_fintype_fun_eq_card] using hcount
  obtain ⟨c, hc0, hc⟩ := siegel_exists_nonzero (consMap box cons) hrank
  refine ⟨c, hc0, fun pd hpd => ?_⟩
  have := congrFun hc ⟨pd, hpd⟩
  simpa [consMap] using this

/-- **Guruswami–Sudan interpolant — polynomial form.**  Under the GS count
`cons.card < box.card`, there is a non-zero polynomial `Q : MvPolynomial (Fin 3) K`
supported on the degree box that satisfies every vanishing constraint. -/
theorem exists_nonzero_box_poly {K : Type*} [Field K]
    (box : Finset (Fin 3 →₀ ℕ)) (cons : Finset ((Fin 3 → K) × (Fin 3 →₀ ℕ)))
    (hcount : cons.card < box.card) :
    ∃ Q : MvPolynomial (Fin 3) K, Q ≠ 0 ∧ Q.support ⊆ box ∧
      ∀ pd ∈ cons, vanishCon pd.1 pd.2 Q = 0 := by
  obtain ⟨c, hc0, hc⟩ := exists_nonzero_box_coeffs box cons hcount
  exact ⟨polyOfLin box c, polyOfLin_ne_zero box c hc0, support_polyOfLin box c, hc⟩

/-- **Guruswami–Sudan multiplicity-`m` interpolant.**  Let `pts` be a finite set
of points in `K^3` and `derivs` a finite set of derivative orders.  For genuine
multiplicity-`m` vanishing one takes `derivs = {d | d.degree < m}`, so that
`derivs.card` is the number of order-`< m` Hasse derivatives in three variables.
If the degree box has more monomials than the total number of constraints,
`pts.card * derivs.card < box.card`, then there is a non-zero box-supported
polynomial `Q` with `vanishCon p d Q = 0` for every point `p ∈ pts` and every
order `d ∈ derivs` — i.e. `Q` vanishes (to the prescribed order pattern) at
every point.  This is the trivariate Guruswami–Sudan interpolant existence
statement obtained by counting unknowns against constraints. -/
theorem exists_gs_interpolant {K : Type*} [Field K]
    (box : Finset (Fin 3 →₀ ℕ)) (pts : Finset (Fin 3 → K))
    (derivs : Finset (Fin 3 →₀ ℕ))
    (hcount : pts.card * derivs.card < box.card) :
    ∃ Q : MvPolynomial (Fin 3) K, Q ≠ 0 ∧ Q.support ⊆ box ∧
      ∀ p ∈ pts, ∀ d ∈ derivs, vanishCon p d Q = 0 := by
  have hc : (pts ×ˢ derivs).card < box.card := by
    rwa [Finset.card_product]
  obtain ⟨Q, hQ0, hQsupp, hQcon⟩ := exists_nonzero_box_poly box (pts ×ˢ derivs) hc
  refine ⟨Q, hQ0, hQsupp, fun p hp d hd => ?_⟩
  exact hQcon (p, d) (Finset.mem_product.mpr ⟨hp, hd⟩)

end GS

end ArkLib
