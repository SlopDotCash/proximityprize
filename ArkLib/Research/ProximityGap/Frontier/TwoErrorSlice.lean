/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.FiniteDomainQuotient
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Finset.Powerset

/-! # Cross ratios for a two-error slice of a Reed–Solomon list -/

namespace ProximityGap.TwoErrorSlice

open Finset Polynomial

variable {I F : Type*} [Fintype I] [DecidableEq I] [Field F]

/-- Ratio associated with two possible error sites. -/
def ratio (D : I ↪ F) (u v x : I) : F := (D u - D x) / (D v - D x)

/-- The full-domain candidates for a second, disjoint pair of errors. -/
noncomputable def alternatives (D : I ↪ F) (u v : I) (target : F) : Finset (Finset I) := by
  classical
  exact (((univ.erase u).erase v).powersetCard 2).filter
    fun A => (∏ i ∈ A, ratio D u v i) = target

/-- Subtract from three units of local weight. Each sample carries at most six units. -/
def penalty (r : ℕ) : ℕ := if r ≤ 1 then 0 else if r = 2 then 1 else 3

/-- A finite computation on the evaluation domain, uniform in both error magnitudes. -/
def PenaltyCap (D : I ↪ F) (S : ℕ) : Prop :=
  ∀ u v : I, u ≠ v → D u ≠ -D v → ∀ μ : F, μ ≠ 0 →
    (∑ x ∈ (univ.erase u).erase v, penalty (alternatives D u v (μ / ratio D u v x)).card) ≤ S

/-- The twelve-unit cap on the reference 128-site rows. -/
def PenaltyBound (D : I ↪ F) : Prop := PenaltyCap D 12

omit [Fintype I] [DecidableEq I] in
theorem ratio_ne_zero (D : I ↪ F) {u v x : I} (hu : u ≠ x) (hv : v ≠ x) :
    ratio D u v x ≠ 0 := div_ne_zero (sub_ne_zero.mpr (D.injective.ne hu))
      (sub_ne_zero.mpr (D.injective.ne hv))

omit [Fintype I] in
/-- If a nonzero difference polynomial vanishes at all but the alternative pair
of the other sites, evaluating its saturated root factorization determines the
product of the two cross ratios. -/
theorem alternative_product (D : I ↪ F) (u v : I) (V A : Finset I) (hAV : A ⊆ V)
    (f : F[X]) (hd : f.natDegree ≤ (V \ A).card) (hroot : ∀ x ∈ V \ A, f.eval (D x) = 0)
    (hu : f.eval (D u) ≠ 0) (hv : f.eval (D v) ≠ 0) :
    (∏ x ∈ A, ratio D u v x) = (f.eval (D v) / f.eval (D u)) * ∏ x ∈ V, ratio D u v x := by
  classical
  let T := V \ A
  have hn : f ≠ 0 := by rintro rfl; simp at hu
  have hdvd : Lagrange.nodal T D ∣ f := Polynomial.prod_X_sub_C_dvd T D D.injective.injOn f hroot
  have he := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic
    hdvd (show f.natDegree ≤ (Lagrange.nodal T D).natDegree by simpa [T] using hd)
  have hEval (i : I) : f.eval (D i) = f.leadingCoeff * ∏ x ∈ T, (D i-D x) := by
    simpa [eval_mul,Lagrange.eval_nodal] using congrArg (eval (D i)) he
  have hlc := leadingCoeff_ne_zero.mpr hn
  have frac : (∏ x ∈ T, ratio D u v x) = f.eval (D u) / f.eval (D v) := by
    simp only [ratio,prod_div_distrib,hEval]
    field_simp
  have split : (∏ x ∈ T, ratio D u v x) * (∏ x ∈ A, ratio D u v x) =
      ∏ x ∈ V, ratio D u v x := prod_sdiff hAV
  rw [← split,frac]
  field_simp

end ProximityGap.TwoErrorSlice

#print axioms ProximityGap.TwoErrorSlice.alternative_product
