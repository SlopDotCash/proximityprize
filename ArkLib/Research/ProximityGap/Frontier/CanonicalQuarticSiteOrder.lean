/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.WeightedHessianResultant
import ArkLib.Research.ProximityGap.Frontier.MovingCubicVanishingBranch
import Mathlib.RingTheory.Polynomial.Content

/-! # Canonical joint multiplicities for the reverse quartic

The local order is the largest number of vanishing diagonals of the translated
two-variable polynomial. Primitivity excludes an identically zero coordinate
fiber and bounds this genuine joint order by the value degree of the equation.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped Differential BigOperators

namespace ArkLib.ProximityGap.Frontier.CanonicalQuarticSiteOrder

open ScalarHessianLocalOrder WeightedHessianResultant

variable {K : Type} [Field K]

/-- Largest local order up to the value degree. For primitive equations this
is the unrestricted greatest order by `le_siteOrder_iff`. -/
def siteOrder (F : K[X][X]) (a : K) (w : K[X]) : ℕ := by
  classical
  exact Nat.findGreatest (fun r => HasOrder (Polynomial.X-C a) r (F.taylor w)) F.natDegree

theorem siteOrder_le (F : K[X][X]) (a : K) (w : K[X]) : siteOrder F a w ≤ F.natDegree := by
  classical
  exact Nat.findGreatest_le _

theorem order_at_site (F : K[X][X]) (a : K) (w : K[X]) :
    HasOrder (Polynomial.X-C a) (siteOrder F a w) (F.taylor w) := by
  classical
  exact Nat.findGreatest_spec (P := fun r => HasOrder (Polynomial.X-C a) r (F.taylor w))
    (Nat.zero_le _) (fun i => by simp)

/-- A primitive equation over the coordinate polynomial ring has no vertical fiber. -/
theorem primitive_fiber_ne_zero (F : K[X][X]) (hf : F.IsPrimitive) (a : K) :
    F.map (evalRingHom a) ≠ 0 := by
  intro hz
  apply (irreducible_X_sub_C a).not_isUnit
  apply isPrimitive_iff_isUnit_of_C_dvd.mp hf
  apply (C_dvd_iff_dvd_coeff _ _).mpr
  intro i
  apply dvd_iff_isRoot.mpr
  change (evalRingHom a) (F.coeff i) = 0
  have hh := congrArg (fun q : K[X] => q.coeff i) hz
  simpa only [coeff_map, coeff_zero] using hh

private theorem order_le_of_primitive (F : K[X][X]) (hf : F.IsPrimitive) (a : K) (w : K[X])
    (r : ℕ) (hr : HasOrder (Polynomial.X-C a) r (F.taylor w)) : r ≤ F.natDegree := by
  by_contra! h
  have hz : (F.taylor w).map (evalRingHom a) = 0 := by
    apply Polynomial.ext
    intro i
    rw [coeff_map, coeff_zero]
    by_cases hi : i ≤ F.natDegree
    · have hh := (dvd_pow_self (Polynomial.X-C a) (by omega : r-i ≠ 0)).trans (hr i)
      exact dvd_iff_isRoot.mp hh
    · have hh : (F.taylor w).natDegree < i := by rw [natDegree_taylor]; omega
      rw [coeff_eq_zero_of_natDegree_lt hh, map_zero]
  have ht : ((F.map (evalRingHom a)).taylor ((evalRingHom a) w)) = 0 := by
    simpa only [taylor_apply, map_comp, Polynomial.map_add, map_X, map_C] using hz
  exact primitive_fiber_ne_zero F hf a ((taylor_eq_zero _ _).mp ht)

theorem le_siteOrder_iff (F : K[X][X]) (hf : F.IsPrimitive) (a : K) (w : K[X]) (r : ℕ) :
    r ≤ siteOrder F a w ↔ HasOrder (Polynomial.X-C a) r (F.taylor w) := by
  classical
  constructor
  · intro hh i
    exact (pow_dvd_pow _ (Nat.sub_le_sub_right hh i)).trans (order_at_site F a w i)
  · intro hh
    exact Nat.le_findGreatest (order_le_of_primitive F hf a w r hh) hh

private theorem shift_power_dvd_iff (a : K) (q : K[X]) (n : ℕ) :
    (Polynomial.X-C a)^n ∣ q ↔ Polynomial.X^n ∣ q.taylor a := by
  constructor
  · intro h
    have hh := map_dvd (taylorAlgHom a) h
    simpa [map_sub, taylorAlgHom_apply] using hh
  · intro h
    have hh := map_dvd (taylorAlgHom (-a)) h
    simpa [taylorAlgHom_apply, taylor_taylor, sub_eq_add_neg] using hh

/-- Exact coefficient-level description in the two translated indeterminates,
including every mixed derivative order below the multiplicity. -/
theorem le_siteOrder_iff_jet (F : K[X][X]) (hf : F.IsPrimitive) (a : K) (w : K[X]) (r : ℕ) :
    r ≤ siteOrder F a w ↔ ∀ i j, i+j < r →
      (((F.taylor w).coeff i).taylor a).coeff j = 0 := by
  rw [le_siteOrder_iff _ hf]
  constructor
  · intro hh i j hij
    exact X_pow_dvd_iff.mp ((shift_power_dvd_iff a _ _).mp (hh i)) j (by omega)
  · intro hh i
    apply (shift_power_dvd_iff a _ _).mpr
    exact X_pow_dvd_iff.mpr fun j hj => hh i j (by omega)

/-- Unconditional quartic multiplicity conclusion on the non-Hessian-divisibility
branch, expressed in terms of the canonical local orders. -/
theorem secondPrime_quartic_canonical_budget [Differential K[X]]
    {E : Type*} [Field E] (φ : K[X] →+* E) (hinj : Function.Injective φ)
    (F : K[X][X]) (hf : F.natDegree = 4) (hir : Irreducible (F.map φ))
    (hnd : ¬F.map φ ∣ (hessian F).map φ) (hD : ∀ q : K[X], q′.natDegree ≤ q.natDegree)
    (hwF : Polynomial.Bivariate.natWeightedDegree F 1 67108863 ≤ 302954072)
    (S : Finset K) (hS : S.card = 1073741824) (w : K → K[X])
    (hπ : ∀ a ∈ S, (Polynomial.X-C a : K[X])′ = 0) (hw : ∀ a ∈ S, ((w a)′)′ = 0) :
    ∑ a ∈ S, siteOrder F a (w a) ≤ 1412316443 :=
  secondPrime_quartic_site_budget φ hinj F hf hir hnd hD hwF S w _ hS
    (fun a _ => (siteOrder_le F a _).trans hf.le) hπ hw (fun a _ => order_at_site F a _)

private theorem deriv_product {E : Type*} [Field E] [Differential E] (a b : E) :
    (a*b)′ = a*b′+b*a′ := by simpa only [smul_eq_mul] using Differential.deriv.leibniz a b

/-- Scalar differentiation on the rational scalar field `k(Z)`. -/
@[instance_reducible] def scalarFieldDifferential (k : Type) [Field k] : Differential (RatFunc k) :=
  letI := MovingCubicVanishingBranch.coordinateDifferential (k := k)
  GenericDifferentialFunctionField.fractionDifferential k[X] (RatFunc k)

/-- Concrete reverse Hessian. The innermost coordinate polynomial variable is fixed
while the coefficient-field scalar is differentiated. -/
def scalarFieldHessian {k : Type} [Field k] (F : (RatFunc k)[X][X]) : (RatFunc k)[X][X] :=
  letI := scalarFieldDifferential k
  letI := ImplicitDerivativeBidegree.coefficientDifferential (K := RatFunc k)
  hessian F

/-- The production multiplicity sum on the original evaluation domain with actual
received lines `u(a)+Z*v(a)`. The only inputs are domain size, the primitive
component's degree budgets, irreducibility, and nondivisibility by its actual Hessian. -/
theorem secondPrime_quartic_received_budget {k : Type} [Field k]
    (F : (RatFunc k)[X][X]) (hf : F.natDegree = 4)
    (hir : Irreducible (MovingCubicVanishingBranch.genericEquation F))
    (hnd : ¬MovingCubicVanishingBranch.genericEquation F ∣
      MovingCubicVanishingBranch.genericEquation (scalarFieldHessian F))
    (hwF : Polynomial.Bivariate.natWeightedDegree F 1 67108863 ≤ 302954072)
    (D : Finset k) (hD : D.card = 1073741824) (u v : k → k) :
    ∑ a ∈ D, siteOrder F (RatFunc.C a) (C (RatFunc.C (u a)+RatFunc.X*RatFunc.C (v a))) ≤
      1412316443 := by
  classical
  let _ : Differential k[X] := MovingCubicVanishingBranch.coordinateDifferential
  let _ : Differential (RatFunc k) := scalarFieldDifferential k
  let _ : Differential (RatFunc k)[X] := ImplicitDerivativeBidegree.coefficientDifferential
  have hC (a : k) : (RatFunc.C a)′ = 0 := by
    change (algebraMap k[X] (RatFunc k) (C a))′ = 0
    rw [GenericDifferentialFunctionField.fraction_deriv_algebraMap k[X] (RatFunc k)]
    change algebraMap k[X] (RatFunc k) (C a).derivative = 0
    simp
  have hZ : (RatFunc.X : RatFunc k)′ = 1 := by
    change (algebraMap k[X] (RatFunc k) Polynomial.X)′ = 1
    rw [GenericDifferentialFunctionField.fraction_deriv_algebraMap k[X] (RatFunc k)]
    change algebraMap k[X] (RatFunc k) (Polynomial.X : k[X]).derivative = 1
    simp
  let emb : k ↪ RatFunc k := ⟨RatFunc.C, RatFunc.C_injective⟩
  let recover (z : RatFunc k) := z.num.coeff 0
  let line (z : RatFunc k) : RatFunc k := RatFunc.C (u (recover z))+
    RatFunc.X*RatFunc.C (v (recover z))
  have hline (z : RatFunc k) : (line z)′ = RatFunc.C (v (recover z)) := by
    dsimp only [line]
    rw [map_add, hC, deriv_product, hC, hZ]
    simp
  have hbound := secondPrime_quartic_canonical_budget (algebraMap _ (RatFunc (RatFunc k)))
    (RatFunc.algebraMap_injective _) F hf hir hnd ImplicitDerivativeBidegree.coefficientDifferential_degree
    hwF (D.map emb) (by simpa using hD) (fun z => C (line z)) (by
      intro z hz
      obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hz
      change Differential.mapCoeffs (Polynomial.X-C (RatFunc.C a)) = 0
      simp [hC]) (by
      intro z _
      change Differential.mapCoeffs (Differential.mapCoeffs (C (line z))) = 0
      simp only [Differential.mapCoeffs_C, hline, hC, map_zero])
  simpa [emb,line,recover] using hbound

end ArkLib.ProximityGap.Frontier.CanonicalQuarticSiteOrder

open ArkLib.ProximityGap.Frontier.CanonicalQuarticSiteOrder in
#print axioms le_siteOrder_iff_jet
open ArkLib.ProximityGap.Frontier.CanonicalQuarticSiteOrder in
#print axioms secondPrime_quartic_received_budget
