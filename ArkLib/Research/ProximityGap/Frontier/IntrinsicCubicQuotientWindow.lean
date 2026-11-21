/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ActualTerminalQuartic
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeUnrestrictedJetBudget

/-! # Removing the subspace of all polynomial multiples from the auxiliary window

The coordinate/value weight is additive. A quotient has strictly fewer
coordinate slots, uniformly in its value degree; the raw coefficient vector
of the quotient realizes it in exactly the bounded window used in the count.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset Module
open scoped BigOperators
namespace ArkLib.ProximityGap.Frontier.IntrinsicCubicQuotientWindow

open SecondPrimeQuarticInterpolation SecondPrimeDegreeSevenDimension SecondPrimeCoordinateWeight
open TerminalQuarticHessianTransport QuarticIntrinsicAuxiliary

variable {K : Type} [Field K] {s b d t : ℕ}

/-- The source vector interpreted in scalar-innermost order is the same polynomial
as the existing scalar-middle interpolation realization after transposition. -/
theorem permute_section (c : Monomials s b d t → K) : permute (sectionMap c) = surface c := by
  change permute (∑ m : Monomials s b d t, monomial m.1.val
    (monomial m.2.2.val (monomial m.2.1.val (c m)))) =
    ∑ j, monomial j.val (∑ i, monomial i.val (∑ a, monomial a.val (c ⟨j,i,a⟩)))
  rw [map_sum]
  simp only [permute,Polynomial.mapEquiv_apply,map_monomial,RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv,Bivariate.swap_monomial_monomial,Fintype.sum_sigma,Fintype.sum_prod_type,
    map_sum]

/-- All auxiliary vectors represented by raw multiples of the terminal component. -/
def multiples (f : K[X][X][X]) : Submodule K (Monomials s b d t → K) :=
  ((Ideal.span {f}).restrictScalars K).comap surfaceLinear

theorem mem_multiples (f : K[X][X][X]) (c : Monomials s b d t → K) :
    c ∈ multiples f ↔ f ∣ surface c := by
  change surface c ∈ Ideal.span {f} ↔ f ∣ surface c
  exact Ideal.mem_span_singleton (x := surface c) (y := f)

theorem finite_quotient_window (f : K[X][X][X]) (hf : f ≠ 0) (ht : 0 < t)
    (k : ℕ) (hk : t-weight d f ≤ k*d) (hk0 : 0 < k) :
    finrank K (multiples (s := s) (b := b) (d := d) (t := t) f) ≤
      Fintype.card (Monomials s (k-1) d (t-weight d f)) := by
  classical
  let U := multiples (s := s) (b := b) (d := d) (t := t) f
  let L : U →ₗ[K] K[X][X][X] := surfaceLinear.comp U.subtype
  let M : (Monomials s (k-1) d (t-weight d f) → K) →ₗ[K] K[X][X][X] :=
    (Algebra.lmul K _ f).comp surfaceLinear
  have hi : Function.Injective L := by
    intro x y he
    apply Subtype.ext
    by_contra hn
    apply surface_ne_zero (sub_ne_zero.mpr hn)
    change surfaceLinear (x.val-y.val) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr he
  have hinc : LinearMap.range L ≤ LinearMap.range M := by
    rintro _ ⟨c,rfl⟩
    by_cases hc : c.val = 0
    · refine ⟨0,?_⟩
      change M 0 = surfaceLinear c.val
      rw [hc,map_zero,map_zero]
    · have hQ := surface_ne_zero hc
      obtain ⟨H,hH⟩ := (mem_multiples f c.val).mp c.property
      have hnH : H ≠ 0 := by
        intro hz
        exact hQ (by rw [hH,hz,mul_zero])
      have hdiv : H ∣ surface c.val := by rw [hH]; exact dvd_mul_left H f
      have htri := SecondPrimeSectionResultant.factor_triangle hQ hdiv
        (fun j i a hh => (surface_support c.val hh).2.1)
      have hw : weight d (surface c.val) ≤ t-1 := weight_le_of_coeff _ _
        (fun j i a hh => by have := (surface_support c.val hh).2.2; omega)
      rw [hH,weight_mul d f H hf hnH] at hw
      obtain ⟨hc',hform⟩ := exists_coefficients_of_support (s := s) (v := k-1)
        (d := d) (t := t-weight d f) H (by
          intro j i a hne
          have hy : H.coeff j ≠ 0 := fun hz => hne (by simp [hz])
          have hz : (H.coeff j).coeff i ≠ 0 := fun hz => hne (by simp [hz])
          have hI := le_natDegree_of_ne_zero hz
          have hJ := htri j hy
          have hW := coeff_weight_le d H hne
          have hp : j*d < k*d := by omega
          have hj : j < k := Nat.lt_of_mul_lt_mul_right hp
          exact ⟨by omega,by omega,by omega⟩)
      exact ⟨hc', (congrArg (fun B => f*B) hform).trans hH.symm⟩
  have hdim := LinearMap.finrank_range_of_inj (f := L) hi
  have hmono := Submodule.finrank_mono hinc
  have hfin := LinearMap.finrank_range_le M
  rw [Module.finrank_pi] at hfin
  change finrank K U ≤ _
  omega

end ArkLib.ProximityGap.Frontier.IntrinsicCubicQuotientWindow

open ArkLib.ProximityGap.Frontier.IntrinsicCubicQuotientWindow in
#print axioms finite_quotient_window
