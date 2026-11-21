/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.Tactic

/-! # Sum of finite-coordinate local orders

Taylor substitution at a finite coordinate, followed by formal completion,
identifies native power-series order with the root multiplicity of the
original polynomial.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped PowerSeries BigOperators

namespace ArkLib.ProximityGap.Frontier.PolynomialLocalOrder

variable {K : Type*} [Field K]

/-- The actual local substitution X ↦ α+t on polynomial coefficients. -/
def atPoint (α : K) : K[X] →+* K⟦X⟧ :=
  Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.taylorAlgHom α).toRingHom

@[simp] theorem coefficient_zero (α : K) (f : K[X]) :
    PowerSeries.constantCoeff (atPoint α f) = f.eval α := by
  change PowerSeries.constantCoeff ((Polynomial.taylor α f : K[X]) : K⟦X⟧) = _
  rw [Polynomial.constantCoeff_coe, Polynomial.taylor_coeff_zero]

@[simp] theorem local_parameter (α : K) : atPoint α (X-C α) = PowerSeries.X := by
  change ((Polynomial.taylor α (X-C α) : K[X]) : K⟦X⟧) = _
  simp [Polynomial.taylor_apply]

theorem local_order (α : K) (f : K[X]) (hf : f ≠ 0) :
    (atPoint α f).order = ↑(f.rootMultiplicity α) := by
  obtain ⟨q,hq,hqn⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf α
  have hqc : (atPoint α q).order = 0 := by
    by_contra! h
    apply hqn
    apply (Polynomial.dvd_iff_isRoot).mpr
    exact (coefficient_zero α q).symm.trans (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp h)
  conv_lhs => arg 1; rw [hq]
  rw [map_mul, map_pow, local_parameter, PowerSeries.order_mul, PowerSeries.order_X_pow, hqc, add_zero]

/-- Summing local multiplicities over any finite list of distinct coordinate
values costs at most the coordinate degree of the polynomial. -/
theorem sum_local_orders_le (f : K[X]) (hf : f ≠ 0) (s : Finset K) :
    ∑ α ∈ s, (atPoint α f).order.toNat ≤ f.natDegree := by
  classical
  simp only [local_order _ f hf, ENat.toNat_natCast]
  calc
    _ = ∑ α ∈ s, f.roots.count α := by simp only [Polynomial.count_roots]
    _ ≤ ∑ α ∈ s ∪ f.roots.toFinset, f.roots.count α :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by intros; exact Nat.zero_le _)
    _ = f.roots.card := Multiset.sum_count_eq_card fun a ha => mem_union_right _ (by simpa using ha)
    _ ≤ _ := Polynomial.card_roots' f

/-- Over a separably closed coefficient field, every polynomial of degree
less than the characteristic splits, with arbitrary repeated roots. -/
theorem splits_of_degree_lt_characteristic [IsSepClosed K] (p : ℕ) [CharP K p]
    (f : K[X]) (hf : f.natDegree < p) : f.Splits := by
  revert hf
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero => simp
  | unit u hu => exact fun _ => hu.splits
  | mul a i ha hi ih =>
    intro hd
    rw [natDegree_mul hi.ne_zero ha] at hd
    apply Splits.mul _ (ih (by omega))
    apply IsSepClosed.splits_of_separable
    apply (Polynomial.separable_iff_derivative_ne_zero hi).mpr
    have hpos := Polynomial.natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hi)
    obtain ⟨d,he⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    change i.natDegree = d+1 at he
    have hcast : (i.natDegree : K) ≠ 0 := fun H =>
      Nat.not_dvd_of_pos_of_lt hpos (by omega) ((CharP.cast_eq_zero_iff K p i.natDegree).mp H)
    have hleading : i.coeff (d+1) ≠ 0 := by
      rw [← he]
      exact leadingCoeff_ne_zero.mpr hi.ne_zero
    intro hz
    have h := congrArg (fun g : K[X] => g.coeff d) hz
    rw [coeff_derivative, coeff_zero] at h
    exact (mul_ne_zero hleading (by simpa only [he, Nat.cast_add, Nat.cast_one] using hcast)) h

/-- In low characteristic-relative degree the finite root set of the
polynomial accounts for its complete degree over the separable closure. -/
theorem sum_all_local_orders [IsSepClosed K] (p : ℕ) [CharP K p]
    (f : K[X]) (hf : f ≠ 0) (hd : f.natDegree < p) :
    letI := Classical.decEq K
    ∑ α ∈ f.roots.toFinset, (atPoint α f).order.toNat = f.natDegree := by
  classical
  simp only [local_order _ f hf, ENat.toNat_natCast]
  rw [← (splits_iff_card_roots.mp (splits_of_degree_lt_characteristic p f hd)),
    ← f.roots.toFinset_sum_count_eq]
  simp only [count_roots]

/-- The local coordinate homomorphism is injective. -/
theorem atPoint_injective (α : K) : Function.Injective (atPoint α) :=
  (Polynomial.coe_injective K).comp (Polynomial.taylor_injective α)

/-- Coefficients generating the unit ideal give nonzero fibers for every
homomorphism, including after a coefficient field extension. -/
theorem primitive_map_ne_zero {R S : Type*} [CommRing R] [IsBezout R] [CommRing S] [Nontrivial S]
    (F : R[X]) (hF : F.IsPrimitive) (φ : R →+* S) : F.map φ ≠ 0 := by
  apply Polynomial.IsPrimitive.ne_zero
  apply Polynomial.isPrimitive_of_contentIdeal_eq_top
  rw [Polynomial.contentIdeal_map_eq_map_contentIdeal, (Polynomial.isPrimitive_iff_contentIdeal_eq_top F).mp hF,
    Ideal.map_top]

#print axioms primitive_map_ne_zero
#print axioms sum_all_local_orders
#print axioms local_order
#print axioms sum_local_orders_le

end ArkLib.ProximityGap.Frontier.PolynomialLocalOrder
