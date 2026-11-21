/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Degree loss from coincident values of four polynomial heads

Two products of opposite pair differences vanish once at every triple coincidence and
twice at every fourfold coincidence. A nonconstant cross-ratio leaves one degree free.
The incidence corollaries below apply to the unequal and equal cross-ratio branches of a
four-head power quotient. See the accompanying proof for the coordinate counts.
-/

set_option autoImplicit false

namespace ProximityGap.FourHeadCrossRatio

open Polynomial Finset
variable {F : Type*} [Field F]

/-- A coincidence multiplicity supported on a finite set is charged to degree. -/
private theorem sum_charge_le (D : Finset F) (w : F → ℕ) (P : F[X]) (hp : P ≠ 0)
    (hw : ∀ x ∈ D, (X - C x) ^ w x ∣ P) : ∑ x ∈ D, w x ≤ P.natDegree := by
  classical
  calc
    ∑ x ∈ D, w x ≤ ∑ x ∈ D, P.roots.count x := by
      apply sum_le_sum
      intro x hx
      rw [count_roots, le_rootMultiplicity_iff hp]
      exact hw x hx
    _ = ∑ x ∈ D ∩ P.roots.toFinset, P.roots.count x := by
      refine (sum_subset inter_subset_left fun x hx hx' => ?_).symm
      exact Multiset.count_eq_zero.mpr fun hm => hx' (mem_inter.mpr ⟨hx, Multiset.mem_toFinset.mpr hm⟩)
    _ ≤ ∑ x ∈ P.roots.toFinset, P.roots.count x :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right fun _ _ _ => Nat.zero_le _
    _ = Multiset.card P.roots := P.roots.toFinset_sum_count_eq
    _ ≤ P.natDegree := P.card_roots'

/-- Two nonproportional polynomials of degree at most `d` cannot share `d` roots
counted with multiplicity. -/
theorem pencil_charge_lt (D : Finset F) (w : F → ℕ) (U V : F[X]) (d : ℕ)
    (hv : V ≠ 0) (huv : ∀ c : F, U ≠ C c * V)
    (hU : U.natDegree ≤ d) (hV : V.natDegree ≤ d)
    (hwU : ∀ x ∈ D, (X - C x) ^ w x ∣ U)
    (hwV : ∀ x ∈ D, (X - C x) ^ w x ∣ V) : ∑ x ∈ D, w x < d := by
  by_cases hsmall : V.natDegree < d
  · exact (sum_charge_le D w V hv hwV).trans_lt hsmall
  have hvd : V.natDegree = d := by omega
  have hl : V.coeff d ≠ 0 := by simpa [← hvd, coeff_natDegree] using hv
  let c := U.coeff d / V.coeff d
  let R := U - C c * V
  have hr : R ≠ 0 := sub_ne_zero.mpr (huv c)
  have hR : R.natDegree ≤ d := (natDegree_sub_le ..).trans (max_le hU ((natDegree_C_mul_le ..).trans hV))
  have hc : R.coeff d = 0 := by
    simp only [R, coeff_sub, coeff_C_mul, c]
    field_simp
    ring
  have hRd : R.natDegree < d := by
    by_contra! hn
    have he : R.natDegree = d := by omega
    rw [← he, coeff_natDegree, leadingCoeff_eq_zero] at hc
    exact hr hc
  exact (sum_charge_le D w R hr (fun x hx => dvd_sub (hwU x hx)
    (dvd_mul_of_dvd_right (hwV x hx) _))).trans_lt hRd

/-- At a common equality of four heads, every opposite-pair product has a double zero. -/
theorem fourfold_divides (A B C' D : F[X]) (x : F)
    (h1 : A.eval x = B.eval x) (h2 : C'.eval x = D.eval x) :
    (X - C x) ^ 2 ∣ (A - B) * (C' - D) := by
  have h₁ : X - C x ∣ A - B := dvd_iff_isRoot.mpr (by simpa [IsRoot, eval_sub] using sub_eq_zero.mpr h1)
  have h₂ : X - C x ∣ C' - D := dvd_iff_isRoot.mpr (by simpa [IsRoot, eval_sub] using sub_eq_zero.mpr h2)
  simpa [pow_two] using mul_dvd_mul h₁ h₂

/-- At a triple equality, one factor of either opposite-pair product vanishes. -/
theorem triple_divides (A B C' D : F[X]) (x : F)
    (h : A.eval x = B.eval x ∨ C'.eval x = D.eval x) :
    X - C x ∣ (A - B) * (C' - D) := by
  apply dvd_iff_isRoot.mpr
  rcases h with h | h <;> simp [IsRoot, eval_mul, eval_sub, h]

/-- Opposite-pair products proportional by a scalar different from zero and one
exclude an evaluation at which the largest equality class has exactly two heads. -/
theorem triple_of_repeated (a b c d t : F) (ht : t ≠ 0) (ht' : t ≠ 1)
    (he : (a-b)*(c-d) = t*(a-c)*(b-d))
    (hrep : a=b ∨ a=c ∨ a=d ∨ b=c ∨ b=d ∨ c=d) :
    (a=b ∧ a=c) ∨ (a=b ∧ a=d) ∨ (a=c ∧ a=d) ∨ (b=c ∧ b=d) := by
  rcases hrep with h | h | h | h | h | h <;> subst_vars <;>
    (by_contra! hn; grind [sub_ne_zero, mul_eq_zero])

/-- The incidence inequalities for the nonconstant branch, including a charge for
coordinates matching none of the four heads. -/
theorem nonconstant_charge (n q d r w m holes : ℕ) (hw : w < 2*d)
    (hinc : m + 2*holes ≤ 2*n + q*w + 2*r) :
    m + 2*holes + q ≤ 2*n + 2*(r + q*d) := by
  have h := Nat.mul_le_mul_left q (show w+1 ≤ 2*d by omega)
  nlinarith only [h, hinc]

/-- Under a constant cross-ratio, `a,c` count all-distinct and fourfold base
coordinates. Each common locator root can add at most three matched heads. -/
theorem constant_charge (n M q d r a c m holes k s slack : ℕ)
    (hlen : n = M*q) (hhalf : 2*k = n) (heven : M = 2*s) (hslack : 0 < slack)
    (hdeg : r + q*d + slack ≤ k) (hbase : M + c ≤ a + 2*d)
    (hinc : m + holes + 2*(q*a) ≤ 3*n + q*c + 3*r) :
    m + holes + q + 3*slack ≤ 3*n := by
  have hkd : k = q*s := by nlinarith [hlen, hhalf, heven, congrArg (· * q) heven]
  have hds : d < s := by
    by_contra! h
    have := Nat.mul_le_mul_left q h
    omega
  have hm := Nat.mul_le_mul_left q hbase
  have hs := Nat.mul_le_mul_left q (show d+1 ≤ s by omega)
  nlinarith only [hm, hs, hdeg, hinc, hlen, hhalf, hkd, Nat.zero_le (q*c)]

/-- The nonconstant branch at rate one half with four scalar words. -/
theorem scalar_floor (h e q d m : ℕ) (hdeg : d < 2*h)
    (hinc : 4*(4*h) ≤ m + 4*e) (hcross : m + q ≤ 2*(4*h) + 2*d) :
    4*h + q + 2 ≤ 4*e := by omega

/-- The corresponding one-fresh bound uses an off-line site and a direction of
positive degree, leaving the scalar head differences at degree at most `2*h-2`. -/
theorem fresh_floor (h e q d m : ℕ) (hdeg : d + 2 ≤ 2*h)
    (hinc : 4*(4*h) ≤ m + 4*e + 4) (hcross : m + 2 + q ≤ 2*(4*h) + 2*d) :
    4*h + q + 2 ≤ 4*e := by omega

#print axioms pencil_charge_lt
#print axioms fourfold_divides
#print axioms triple_divides
#print axioms triple_of_repeated
#print axioms nonconstant_charge
#print axioms constant_charge
#print axioms scalar_floor
#print axioms fresh_floor

end ProximityGap.FourHeadCrossRatio
