/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Graded degree budgets descend to divisors

The GS-interpolation chain for proximity gaps tracks, for a trivariate polynomial
`R : F[X][X][Y]`, the graded budget `Bivariate.degreeX (R.coeff j) ≤ D - j` — the
`hRgraded` hypothesis threaded through the Appendix-A weight machinery
(`AlphaWeightAll`, `βHensel_weight_bound_of_structured_invariant_alphaWeight`, …).
That hypothesis is assumed by every consumer and produced by none; the natural
producer is the interpolant itself, whose `(1,·,1)`-weighted budget is part of the
GS construction, together with the fact proved here: **the graded budget is
inherited by divisors**.

`degreeX_coeff_le_of_dvd`: if `Q ≠ 0` satisfies the honest graded budget
`degreeX (Q.coeff j) + j ≤ D` on its support and `R ∣ Q`, then
`degreeX (R.coeff j) ≤ D - j` for every `j`.

The proof transports the graded weight through the per-coefficient variable swap
`Polynomial.Bivariate.swap` (a ring automorphism of `F[X][X]`), under which the
weight becomes `Bivariate.totalDegree` over the base ring `F[X]`; multiplicativity
of `totalDegree` over a domain (`totalDegree_mul`, in-tree) then gives the descent,
and the budget transfers back coefficientwise.
-/

namespace Polynomial.Bivariate

open Polynomial

section CommRing

variable {F : Type} [CommRing F]

/-- The variable swap exchanges the inner `X`-degree (`degreeX`) and the outer
degree (`natDegree`): the outer degree of `swap g` is the `X`-degree of `g`. -/
theorem natDegree_swap (g : F[X][Y]) :
    (Bivariate.swap (R := F) g).natDegree = degreeX g := by
  have h := degreeX_swap (f := Bivariate.swap (R := F) g)
  rw [Bivariate.swap_swap_apply] at h
  simpa [natDegreeY] using h.symm

end CommRing

section Field

variable {F : Type} [Field F]

/-- **Graded budgets descend to divisors.**  If `Q ≠ 0` satisfies the graded budget
`degreeX (Q.coeff j) + j ≤ D` on its support, then so does every divisor `R ∣ Q`,
in the `ℕ`-subtraction form `degreeX (R.coeff j) ≤ D - j` consumed by the
Appendix-A weight machinery (`hRgraded`). -/
theorem degreeX_coeff_le_of_dvd {Q R : F[X][X][Y]} {D : ℕ}
    (hQ : Q ≠ 0) (hdvd : R ∣ Q)
    (hbudget : ∀ j ∈ Q.support, degreeX (Q.coeff j) + j ≤ D) :
    ∀ j, degreeX (R.coeff j) ≤ D - j := by
  classical
  obtain ⟨S, rfl⟩ := hdvd
  have hR : R ≠ 0 := left_ne_zero_of_mul hQ
  have hS : S ≠ 0 := right_ne_zero_of_mul hQ
  -- the per-coefficient swap, as a ring hom on `F[X][X]`
  set σ : F[X][X] →+* F[X][X] :=
    ((Bivariate.swap (R := F)).toAlgHom : F[X][X] →ₐ[F] F[X][X]).toRingHom with hσdef
  have hσapp : ∀ g : F[X][X], σ g = Bivariate.swap (R := F) g := fun _ => rfl
  have hσinj : Function.Injective σ := by
    intro a b hab
    exact (Bivariate.swap (R := F)).injective (by rw [← hσapp, ← hσapp]; exact hab)
  have hσdeg : ∀ g : F[X][X], (σ g).natDegree = degreeX g := by
    intro g; rw [hσapp]; exact natDegree_swap g
  have hmapcoeff : ∀ (P : F[X][X][Y]) (j : ℕ), (P.map σ).coeff j = σ (P.coeff j) :=
    fun P j => Polynomial.coeff_map σ j
  have hmapne : ∀ P : F[X][X][Y], P ≠ 0 → P.map σ ≠ 0 := fun P hP => by
    rwa [Ne, Polynomial.map_eq_zero_iff hσinj]
  -- the transported budget: `totalDegree ((R*S).map σ) ≤ D` over the base ring `F[X]`
  have hbudget' : totalDegree ((R * S).map σ) ≤ D := by
    unfold totalDegree
    refine Finset.sup_le fun j hj => ?_
    have hcoeffne : σ ((R * S).coeff j) ≠ 0 := by
      rw [← hmapcoeff]; exact Polynomial.mem_support_iff.mp hj
    have hne : (R * S).coeff j ≠ 0 := fun h => hcoeffne (by rw [h, map_zero])
    have hle := hbudget j (Polynomial.mem_support_iff.mpr hne)
    calc (((R * S).map σ).coeff j).natDegree + j
        = degreeX ((R * S).coeff j) + j := by rw [hmapcoeff, hσdeg]
      _ ≤ D := hle
  -- multiplicativity of the transported weight over the domain `F[X]`
  have htot : totalDegree (R.map σ) ≤ D := by
    have h1 := totalDegree_mul (F := F[X]) (hmapne R hR) (hmapne S hS)
    calc totalDegree (R.map σ)
        ≤ totalDegree (R.map σ) + totalDegree (S.map σ) := Nat.le_add_right _ _
      _ = totalDegree (R.map σ * S.map σ) := h1.symm
      _ = totalDegree ((R * S).map σ) := by rw [Polynomial.map_mul]
      _ ≤ D := hbudget'
  -- conclude per coefficient
  intro j
  by_cases hj : R.coeff j = 0
  · rw [hj]
    simp [degreeX]
  · have hjs : j ∈ (R.map σ).support := by
      rw [Polynomial.mem_support_iff, hmapcoeff]
      exact fun h => hj (hσinj (h.trans (map_zero σ).symm))
    have h1 : ((R.map σ).coeff j).natDegree + j ≤ totalDegree (R.map σ) :=
      coeff_totalDegree_le _ hjs
    rw [hmapcoeff, hσdeg] at h1
    exact Nat.le_sub_of_add_le (le_trans h1 htot)

end Field

end Polynomial.Bivariate

/-! ## Axiom audit -/
#print axioms Polynomial.Bivariate.natDegree_swap
#print axioms Polynomial.Bivariate.degreeX_coeff_le_of_dvd

namespace Polynomial.Bivariate

open Polynomial

section InnerDegree

variable {F : Type} [Field F]

/-- **Innermost-degree budgets descend to divisors.**  If every double coefficient of
`Q : F[X][X][Y]` has innermost degree at most `B`, so does every double coefficient of any
divisor `R ∣ Q`: the innermost weight `sup_j degreeX (coeff j)` transports through the
per-coefficient swap into `degreeX` over the base `F[X]`, which is superadditive on
products over a domain. -/
theorem coeff_coeff_natDegree_le_of_dvd {Q R : F[X][X][Y]} {B : ℕ}
    (hQ : Q ≠ 0) (hdvd : R ∣ Q)
    (hB : ∀ j i : ℕ, ((Q.coeff j).coeff i).natDegree ≤ B) :
    ∀ j i : ℕ, ((R.coeff j).coeff i).natDegree ≤ B := by
  classical
  obtain ⟨S, rfl⟩ := hdvd
  have hR : R ≠ 0 := left_ne_zero_of_mul hQ
  have hS : S ≠ 0 := right_ne_zero_of_mul hQ
  set σ : F[X][X] →+* F[X][X] :=
    ((Bivariate.swap (R := F)).toAlgHom : F[X][X] →ₐ[F] F[X][X]).toRingHom with hσdef
  have hσapp : ∀ g : F[X][X], σ g = Bivariate.swap (R := F) g := fun _ => rfl
  have hσinj : Function.Injective σ := by
    intro a b hab
    exact (Bivariate.swap (R := F)).injective (by rw [← hσapp, ← hσapp]; exact hab)
  have hσdeg : ∀ g : F[X][X], (σ g).natDegree = degreeX g := by
    intro g; rw [hσapp]; exact natDegree_swap g
  have hmapne : ∀ P : F[X][X][Y], P ≠ 0 → P.map σ ≠ 0 := fun P hP => by
    rwa [Ne, Polynomial.map_eq_zero_iff hσinj]
  -- the transported budget on `Q = R·S`
  have hQbound : degreeX ((R * S).map σ) ≤ B := by
    refine Finset.sup_le fun j hj => ?_
    rw [Polynomial.coeff_map, hσdeg]
    exact Finset.sup_le fun i _ => hB j i
  intro j i
  by_cases hcj : R.coeff j = 0
  · rw [hcj]
    simp
  calc ((R.coeff j).coeff i).natDegree
      ≤ degreeX (R.coeff j) := coeff_natDegree_le_degreeX _ i
    _ = ((R.map σ).coeff j).natDegree := by rw [Polynomial.coeff_map, hσdeg]
    _ ≤ degreeX (R.map σ) := coeff_natDegree_le_degreeX _ j
    _ ≤ degreeX (R.map σ) + degreeX (S.map σ) := Nat.le_add_right _ _
    _ ≤ degreeX ((R.map σ) * (S.map σ)) :=
        degreeX_mul_ge _ _ (hmapne R hR) (hmapne S hS)
    _ = degreeX ((R * S).map σ) := by rw [Polynomial.map_mul]
    _ ≤ B := hQbound

end InnerDegree

end Polynomial.Bivariate

#print axioms Polynomial.Bivariate.coeff_coeff_natDegree_le_of_dvd
