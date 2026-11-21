/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticInterpolation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Dimension obstruction for a common degree-six factor

At 408944638 agreements, the whole degree-seven interpolation space has three
more dimensions than the space of possible affine quotients by a high-degree
cubic-value factor. The count uses the actual linear map of interpolation
constraints and the actual map from coefficients to trivariate polynomials.
-/

set_option autoImplicit false

noncomputable section

open Polynomial Finset
open scoped BigOperators
open ArkLib.ProximityGap.Frontier.SecondPrimeQuarticInterpolation

namespace ArkLib.ProximityGap.Frontier.SecondPrimeDegreeSevenDimension

variable {F ι : Type*} [Field F] [Fintype ι]
variable {s v d t : ℕ}

private theorem surface_sum (c : Monomials s v d t → F) :
    surface c = ∑ j, monomial j.val (∑ i, monomial i.val (∑ a, monomial a.val (c ⟨j,i,a⟩))) := rfl

/-- Linear realization of the supported coefficient vector as a trivariate polynomial. -/
def surfaceLinear : (Monomials s v d t → F) →ₗ[F] Polynomial (Polynomial F[X]) where
  toFun := surface
  map_add' c h := by simp only [surface_sum, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r c := by simp only [surface_sum, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum,
    smul_monomial]

private theorem surfaceLinear_injective :
    Function.Injective (surfaceLinear (s:=s) (v:=v) (d:=d) (t:=t) (F:=F)) := by
  intro x y h
  by_contra hne
  apply surface_ne_zero (sub_ne_zero.mpr hne)
  change surfaceLinear (x-y) = 0
  rw [map_sub, h, sub_self]

private def sumPoly {R : Type*} [Semiring R] {w : ℕ} (f : Fin w → R) : R[X] :=
  ∑ i, monomial i.val (f i)

private theorem hcoeff {R : Type*} [Semiring R] {w : ℕ} (f : Fin w → R) (i : Fin w) :
    (sumPoly f).coeff i.val = f i := by
  classical
  simp [sumPoly,finsetSum_coeff,coeff_monomial,Fin.val_inj]

private theorem read_coefficient (c : Monomials s v d t → F) (m : Monomials s v d t) :
    (((surface c).coeff m.1.val).coeff m.2.1.val).coeff m.2.2.val = c m := by
  change (((sumPoly fun j => sumPoly fun i => sumPoly fun a => c ⟨j,i,a⟩
    ).coeff m.1.val).coeff m.2.1.val).coeff m.2.2.val = _
  rw [hcoeff,hcoeff,hcoeff]

/-- The coefficient representation is exhaustive for the stated degree constraints. -/
theorem exists_coefficients_of_support (Q : Polynomial (Polynomial F[X]))
    (hQ : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
      j ≤ v ∧ i+j ≤ s ∧ a+j*d < t) :
    ∃ c : Monomials s v d t → F, surface c = Q := by
  let c : Monomials s v d t → F := fun m => ((Q.coeff m.1.val).coeff m.2.1.val).coeff m.2.2.val
  refine ⟨c, ?_⟩
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro i
  apply Polynomial.ext
  intro a
  by_cases h : j ≤ v ∧ i+j ≤ s ∧ a+j*d < t
  · let m : Monomials s v d t := ⟨⟨j,by omega⟩,⟨i,by change i < s+1-j; omega⟩,
      ⟨a,by change a < t-j*d; omega⟩⟩
    exact read_coefficient c m
  · have hl : (((surface c).coeff j).coeff i).coeff a = 0 := by
      by_contra hne
      exact h (surface_support c hne)
    have hr : ((Q.coeff j).coeff i).coeff a = 0 := by
      by_contra hne
      exact h (hQ _ _ _ hne)
    rw [hl,hr]

abbrev Vars := Monomials 7 6 67108863 408944638
abbrev Small := Monomials 1 1 67108863 (408944638 - 3*67108863)

private def entry (m : Monomials s v d t) (x a b : F) : F[X] :=
  monomial m.2.1.val (x ^ m.2.2.val) * (C a + X*C b)^m.1.val

/-- Scalar coefficients of the received-line restriction at every coordinate. -/
def constraints (dom : ι ↪ F) (u₀ u₁ : ι → F) :
    (Monomials s v d t → F) →ₗ[F] ((ι × Fin (s+1)) → F) :=
  Matrix.mulVecLin (fun (row : ι × Fin (s+1)) (m : Monomials s v d t) =>
    (entry m (dom row.1) (u₀ row.1) (u₁ row.1)).coeff row.2.val)

/-- The eight scalar coefficients at the target length and agreement threshold. -/
abbrev constraint (dom : ι ↪ F) (u₀ u₁ : ι → F) :=
  constraints (s:=7) (v:=6) (d:=67108863) (t:=408944638) dom u₀ u₁

private theorem card_vars : Fintype.card Vars = 9145679879 := by
  simp only [Vars, Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]

private theorem card_small : Fintype.card Small = 555745284 := by
  simp only [Small, Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]

/-- A lower bound on the dimension of the interpolation kernel. -/
theorem kernel_finrank (dom : ι ↪ F) (u₀ u₁ : ι → F) (hn : Fintype.card ι = 1073741824) :
    555745287 ≤ Module.finrank F (LinearMap.ker (constraint dom u₀ u₁)) := by
  have h := (constraint dom u₀ u₁).finrank_range_add_finrank_ker
  have hle := Submodule.finrank_le (LinearMap.range (constraint dom u₀ u₁))
  rw [Module.finrank_fintype_fun_eq_card, card_vars] at h
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, hn] at hle
  omega

omit [Fintype ι] in
/-- Every interpolation-kernel member vanishes on every rich candidate after folding. -/
theorem kernel_specializes_zero (dom : ι ↪ F) (u₀ u₁ : ι → F) {c : Monomials s v d t → F} (ht : 0 < t)
    (hc : c ∈ LinearMap.ker (constraints dom u₀ u₁)) (g : F) (q : F[X])
    (hq : q.natDegree ≤ d) (S : Finset ι) (hS : t ≤ S.card)
    (ha : ∀ i ∈ S, q.eval (dom i) = u₀ i+g*u₁ i) :
    (surface c).eval₂ (evalRingHom (C g)) q = 0 := by
  classical
  rw [surface_eval]
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f:=fun i : S => dom i.val)
    (dom.injective.comp Subtype.val_injective)
  · intro i
    have hline : ∑ m, C (c m) * entry m (dom i.val) (u₀ i.val) (u₁ i.val) = 0 := by
      ext l
      rw [finsetSum_coeff, coeff_zero]
      by_cases hl : l < s+1
      · have h := congrFun (LinearMap.mem_ker.mp hc) (i.val,⟨l,hl⟩)
        change ∑ m, (entry m (dom i.val) (u₀ i.val) (u₁ i.val)).coeff l*c m = 0 at h
        simp only [coeff_C_mul]
        simpa only [mul_comm] using h
      · apply Finset.sum_eq_zero
        intro m _
        have hab : (C (u₀ i.val) + X*C (u₁ i.val)).natDegree ≤ 1 :=
          natDegree_add_le_of_degree_le (by simp) (natDegree_mul_le.trans (by simp))
        have hj := (natDegree_pow_le (p:=C (u₀ i.val) + X*C (u₁ i.val)) (n:=m.1.val)).trans
          (Nat.mul_le_mul_left _ hab)
        have hi := m.2.1.isLt
        have hdeg : (entry m (dom i.val) (u₀ i.val) (u₁ i.val)).natDegree < l :=
          (natDegree_mul_le.trans (Nat.add_le_add (natDegree_monomial_le _) hj)).trans_lt (by omega)
        rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
    have h := congrArg (Polynomial.eval g) hline
    simp only [specialize, entry, eval_finsetSum, eval_mul, eval_monomial, eval_pow, eval_add,
      eval_X, eval_C, eval_zero, ha i.val i.property] at h ⊢
    convert h using 1
    apply Finset.sum_congr rfl
    intro m _
    ring
  · rw [Fintype.card_coe]
    apply lt_of_le_of_lt _ (by omega : t-1 < S.card)
    apply natDegree_sum_le_of_forall_le
    intro m _
    have hj := (natDegree_pow_le (p:=q) (n:=m.1.val)).trans (Nat.mul_le_mul_left _ hq)
    have hi := m.2.2.isLt
    exact (natDegree_mul_le.trans (Nat.add_le_add (natDegree_monomial_le _) hj)).trans (by omega)

/-- No fixed polynomial can give an affine supported quotient to every member
of the entire interpolation kernel. -/
theorem exists_without_small_quotient (dom : ι ↪ F) (u₀ u₁ : ι → F)
    (hn : Fintype.card ι = 1073741824) (G : Polynomial (Polynomial F[X])) :
    ∃ c ∈ LinearMap.ker (constraint dom u₀ u₁), ∀ h : Small → F, surface c ≠ G*surface h := by
  classical
  by_contra! hall
  let L := LinearMap.ker (constraint dom u₀ u₁)
  let P : L →ₗ[F] Polynomial (Polynomial F[X]) := surfaceLinear.comp L.subtype
  let Q : (Small → F) →ₗ[F] Polynomial (Polynomial F[X]) :=
    (Algebra.lmul F _ G).comp surfaceLinear
  have hPQ : LinearMap.range P ≤ LinearMap.range Q := by
    rintro w ⟨c,rfl⟩
    obtain ⟨h,hh⟩ := hall c.val c.property
    exact ⟨h,hh.symm⟩
  have hlow := kernel_finrank dom u₀ u₁ hn
  have hP := LinearMap.finrank_range_of_inj (f:=P)
    (surfaceLinear_injective.comp Subtype.val_injective)
  have hmid := Submodule.finrank_mono hPQ
  have hQ := LinearMap.finrank_range_le Q
  rw [Module.finrank_fintype_fun_eq_card,card_small] at hQ
  change 555745287 ≤ Module.finrank F L at hlow
  omega

/-- For any fixed factor, one actual received-line interpolant has no polynomial
quotient obeying both the affine total-degree and coordinate-weight restrictions. -/
theorem exists_without_affine_quotient (dom : ι ↪ F) (u₀ u₁ : ι → F)
    (hn : Fintype.card ι = 1073741824) (G : Polynomial (Polynomial F[X])) :
    ∃ c ∈ LinearMap.ker (constraint dom u₀ u₁), ∀ H : Polynomial (Polynomial F[X]),
      (∀ j i a, ((H.coeff j).coeff i).coeff a ≠ 0 →
        i+j ≤ 1 ∧ a+j*67108863 < 408944638-3*67108863) → surface c ≠ G*H := by
  obtain ⟨c,hc,hnq⟩ := exists_without_small_quotient dom u₀ u₁ hn G
  refine ⟨c,hc,fun H hH => ?_⟩
  obtain ⟨h,hh⟩ := exists_coefficients_of_support (s:=1) (v:=1) (d:=67108863)
    (t:=408944638-3*67108863) H (fun j i a h => by
      obtain ⟨h₁,h₂⟩ := hH j i a h
      exact ⟨by omega,h₁,h₂⟩)
  exact hh ▸ hnq h

/-- A total-degree-nine, value-degree-three interpolant at the same endpoint. -/
theorem cubic_nine (dom : ι ↪ F) (u₀ u₁ : ι → F) (hn : Fintype.card ι = 1073741824) :
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 3 ∧ i+j ≤ 9 ∧ a+j*67108863 < 408944638) ∧
      ∀ g : F, ∀ q : F[X], q.natDegree ≤ 67108863 → ∀ S : Finset ι, 408944638 ≤ S.card →
        (∀ i ∈ S, q.eval (dom i) = u₀ i + g*u₁ i) → Q.eval₂ (evalRingHom (C g)) q = 0 := by
  obtain ⟨c,hc,_,hall⟩ := exists_curve (s:=9) (v:=3) (d:=67108863) (t:=408944638)
    dom u₀ u₁ (by decide) (by
      rw [hn]
      simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
      norm_num [Fin.sum_univ_succ])
  refine ⟨surface c,surface_ne_zero hc,fun _ _ _ h => surface_support c h,?_⟩
  intro g q hq S hS hA
  rw [surface_eval]
  exact hall _ _ hq _ hS hA

end ArkLib.ProximityGap.Frontier.SecondPrimeDegreeSevenDimension

#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeDegreeSevenDimension.kernel_finrank
#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeDegreeSevenDimension.kernel_specializes_zero
#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeDegreeSevenDimension.exists_without_small_quotient

#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeDegreeSevenDimension.exists_without_affine_quotient
#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeDegreeSevenDimension.cubic_nine
