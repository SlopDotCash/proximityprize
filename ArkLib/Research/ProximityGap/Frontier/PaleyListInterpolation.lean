/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.Polynomial.FiniteDomainQuotient
import ArkLib.ToMathlib.Polynomial.HasseTaylor.Shift
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The domain vanisher in interpolation with a common symbol list

In sheared coordinates the word with shift `t` accepts coordinate `a` exactly
when `a + t` lies in the permitted symbol set `Q`. If the parameter degree is
below the size of the list, every interpolation polynomial vanishing on all of
these pairs is a multiple of the domain vanisher.
-/

namespace ProximityGap.PaleyListInterpolation

open Polynomial

variable {F : Type*} [Field F]

/-- With shift degree below the symbol list size, the entire permitted grid imposes
exactly divisibility by the domain vanisher, including after the change `T = Y - X`. -/
theorem sheared_vanishing_iff_nodal_dvd (A Q : Finset F) (H : Polynomial F[X])
    (hdeg : H.natDegree < Q.card) :
    (∀ a ∈ A, ∀ y ∈ Q, (H.map (evalRingHom a)).eval (y - a) = 0) ↔
    C (Lagrange.nodal A id) ∣ H := by
  classical
  constructor
  · intro hv
    apply (C_dvd_iff_dvd_coeff _ H).mpr
    intro j
    apply Polynomial.zeroOn_iff_nodal_dvd.mp
    intro a ha
    have hz : H.map (evalRingHom a) = 0 := by
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
        (f := fun y : Q => (y : F) - a) (fun _ _ h => Subtype.ext (sub_left_inj.mp h))
      · exact fun y => hv a ha y y.property
      · rw [Fintype.card_coe]
        exact natDegree_map_le.trans_lt hdeg
    simpa using congrArg (fun P : F[X] => P.coeff j) hz
  · rintro ⟨K, rfl⟩ a ha y _
    have hz : (Lagrange.nodal A id).eval a = 0 := Lagrange.eval_nodal_at_node (v := id) ha
    simp [hz]

private theorem coeff_functional_vanishes (Q : Finset F) (a : F) (H : Polynomial F[X])
    (hdeg : H.natDegree < Q.card) (L : F[X] →ₗ[F] F)
    (hv : ∀ y ∈ Q, L (H.eval (C (y - a))) = 0) (j : ℕ) : L (H.coeff j) = 0 := by
  classical
  let e : Fin Q.card ≃ Q := (Fintype.equivFinOfCardEq (Fintype.card_coe Q)).symm
  let f (i : Fin Q.card) := (e i : F) - a
  have hzero : (fun i : Fin Q.card => L (H.coeff i.val)) = 0 := by
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero (f := f)
      (fun i j hij => e.injective (Subtype.ext (sub_left_inj.mp hij)))
    intro i
    have h := hv (e i) (e i).property
    change L (H.eval (C (f i))) = 0 at h
    rw [eval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range] at h
    simp_rw [← C_pow, mul_comm (H.coeff _) (C _), C_mul'] at h
    simpa only [map_sum, map_smul, smul_eq_mul] using h
  by_cases hj : j < Q.card
  · exact congrFun hzero ⟨j, hj⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

/-- For any order, vanishing to that order in the coordinate variable at each
accepted shift is equivalent to divisibility by the corresponding power of the
domain vanisher. In particular full bivariate multiplicity implies this divisibility. -/
theorem sheared_multiplicity_iff_nodal_pow_dvd (A Q : Finset F) (H : Polynomial F[X])
    (hdeg : H.natDegree < Q.card) (s : ℕ) :
    (∀ a ∈ A, ∀ y ∈ Q, (X - C a) ^ s ∣ H.eval (C (y-a))) ↔
      C ((Lagrange.nodal A id) ^ s) ∣ H := by
  classical
  constructor
  · intro hv
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro j
    rw [Lagrange.nodal, ← Finset.prod_pow]
    apply Finset.prod_dvd_of_coprime
    · exact fun a _ b _ hab => (pairwise_coprime_X_sub_C Function.injective_id hab).pow
    intro a ha
    apply (X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero _ _ _).mpr
    intro k hk
    apply coeff_functional_vanishes Q a H hdeg ((leval a).comp (hasseDeriv k))
    intro y hy
    exact (X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero _ _ _).mp (hv a ha y hy) k hk
  · rintro ⟨K, rfl⟩ a ha y _
    rw [eval_mul, eval_C]
    apply dvd_mul_of_dvd_left
    apply pow_dvd_pow_of_dvd _ s
    exact Finset.dvd_prod_of_mem (fun z : F => X - C z) ha

#print axioms sheared_multiplicity_iff_nodal_pow_dvd
#print axioms sheared_vanishing_iff_nodal_dvd

end ProximityGap.PaleyListInterpolation
