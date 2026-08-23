/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import CompPoly.Data.MvPolynomial.Notation
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.MvPolyEquiv
import CompPoly.Multivariate.Rename
import CompPoly.Multivariate.Restrict
import ArkLib.Data.MvPolynomial.Degrees

/-!
# Bounded-degree computable multivariate polynomials

This file provides the computable `CMvPolynomial` counterpart of Mathlib's
`MvPolynomial.restrictDegree` carrier.

The goal is to preserve the abstract-facing "bounded degree" interface shape while migrating the
underlying execution path onto `CompPoly.CMvPolynomial`.
-/

namespace CPoly
namespace CMvPolynomial

open MvPolynomial

variable (n : ℕ) (R : Type) [CommSemiring R] (d : ℕ)

/-- Computable multivariate polynomials in `n` variables whose degree in each variable is `≤ d`. -/
abbrev degreeLE : Type _ :=
  { p : CPoly.CMvPolynomial n R // ∀ i : Fin n, p.degreeOf i ≤ d }

namespace degreeLE

variable {n : ℕ} {R : Type} [CommSemiring R] {d : ℕ}

@[simp] theorem coe_mk (p : CPoly.CMvPolynomial n R) (hp : ∀ i : Fin n, p.degreeOf i ≤ d) :
    ((⟨p, hp⟩ : CPoly.CMvPolynomial.degreeLE n R d) : CPoly.CMvPolynomial n R) = p := rfl

/-- Bridge back to Mathlib's `MvPolynomial` bounded-degree carrier. -/
def val [BEq R] [LawfulBEq R] (p : CPoly.CMvPolynomial.degreeLE n R d) : MvPolynomial (Fin n) R :=
  CPoly.fromCMvPolynomial (p : CPoly.CMvPolynomial n R)

theorem property [BEq R] [LawfulBEq R] (p : CPoly.CMvPolynomial.degreeLE n R d) :
    val p ∈ R⦃≤ d⦄[X Fin n] := by
  rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
  intro i
  have hdeg : MvPolynomial.degreeOf i (val p) = (p : CPoly.CMvPolynomial n R).degreeOf i := by
    simpa [val] using
      (congrFun (CPoly.degreeOf_equiv (S := R) (p := (p : CPoly.CMvPolynomial n R))) i).symm
  rw [hdeg]
  exact p.2 i

@[ext] theorem ext {p q : CPoly.CMvPolynomial.degreeLE n R d}
    (h : (p : CPoly.CMvPolynomial n R) = (q : CPoly.CMvPolynomial n R)) : p = q :=
  Subtype.ext h

open CPoly CMvPolynomial in
private theorem degreeOf_restrictDegree_le [BEq R] [LawfulBEq R]
    (d : Nat) (i : Fin n) (p : CPoly.CMvPolynomial n R) :
    (CPoly.CMvPolynomial.restrictDegree d p).degreeOf i ≤ d := by
  unfold CPoly.CMvPolynomial.degreeOf
  exact Finset.sup_le fun m hm =>
    CPoly.degreeOf_le_of_mem_monomials_restrictDegree
      (d := d) (p := p) (i := i) (by simpa using hm)
/-- Canonical bounded-degree wrapper around a raw computable polynomial. -/
def ofCMvPolynomial [BEq R] [LawfulBEq R] (d : ℕ) (p : CPoly.CMvPolynomial n R) :
    CPoly.CMvPolynomial.degreeLE n R d :=
  ⟨CPoly.CMvPolynomial.restrictDegree d p, fun i => degreeOf_restrictDegree_le d i p⟩

instance [BEq R] [LawfulBEq R] : Zero (CPoly.CMvPolynomial.degreeLE n R d) :=
  ⟨ofCMvPolynomial d 0⟩

instance [BEq R] [LawfulBEq R] : OfNat (CPoly.CMvPolynomial.degreeLE n R d) 0 :=
  ⟨0⟩

instance [BEq R] [LawfulBEq R] : Inhabited (CPoly.CMvPolynomial.degreeLE n R d) :=
  ⟨0⟩

section Univariate

variable {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] {d : ℕ}

private def coeffMonomial (k : Fin (d + 1)) : CPoly.CMvMonomial 1 :=
  Vector.ofFn (fun _ => k.val)

private theorem coeffMonomial_injective :
    Function.Injective (coeffMonomial (d := d)) := by
  intro k l h
  apply Fin.ext
  have h0 := congrArg (fun m : CPoly.CMvMonomial 1 => m.get 0) h
  simpa [coeffMonomial] using h0

private theorem coeffMonomial_degreeOf (k : Fin (d + 1)) :
    (coeffMonomial (d := d) k).degreeOf 0 = k.val := by
  simp [coeffMonomial, CPoly.CMvMonomial.degreeOf]

private theorem coeff_monomial (m m' : CPoly.CMvMonomial 1) (c : R) :
    CPoly.CMvPolynomial.coeff m (CPoly.CMvPolynomial.monomial m' c) =
      if m = m' then c else 0 := by
  have h := congrArg
    (fun p : MvPolynomial (Fin 1) R => MvPolynomial.coeff (CPoly.CMvMonomial.toFinsupp m) p)
    (CPoly.fromCMvPolynomial_monomial (R := R) m' c)
  simpa [CPoly.coeff_eq, CPoly.CMvMonomial.ofFinsupp_toFinsupp,
    MvPolynomial.coeff_monomial, CPoly.CMvMonomial.injective_toFinsupp.eq_iff,
    eq_comm] using h

/-- Coefficient vector for a bounded-degree computable univariate polynomial. -/
def coeffVec (p : CPoly.CMvPolynomial.degreeLE 1 R d) : Fin (d + 1) → R :=
  fun k => CPoly.CMvPolynomial.coeff (coeffMonomial (d := d) k) (p : CPoly.CMvPolynomial 1 R)

/-- Build a bounded-degree computable univariate polynomial from its coefficient vector. -/
def ofCoeffVec (coeffs : Fin (d + 1) → R) : CPoly.CMvPolynomial.degreeLE 1 R d :=
  ofCMvPolynomial d (∑ k, CPoly.CMvPolynomial.monomial (coeffMonomial (d := d) k) (coeffs k))

/-- Coefficient of a single monomial built from `coeffMonomial`. -/
private theorem coeff_coeffMonomial (k l : Fin (d + 1)) (c : R) :
    CPoly.CMvPolynomial.coeff (coeffMonomial (d := d) k)
        (CPoly.CMvPolynomial.monomial (coeffMonomial (d := d) l) c) =
      if k = l then c else 0 := by
  rw [coeff_monomial]
  by_cases hkl : k = l
  · subst hkl; simp
  · rw [if_neg hkl, if_neg]
    exact fun h => hkl (coeffMonomial_injective h)

/-- Coefficient of a finite sum of monomials distributes over the sum. -/
private theorem coeff_sum_coeffMonomial (k : Fin (d + 1)) (coeffs : Fin (d + 1) → R) :
    CPoly.CMvPolynomial.coeff (coeffMonomial (d := d) k)
        (∑ l, CPoly.CMvPolynomial.monomial (coeffMonomial (d := d) l) (coeffs l)) =
      coeffs k := by
  classical
  rw [CPoly.coeff_sum]
  simp [coeff_coeffMonomial]

private theorem eq_coeffMonomial_of_degreeOf_le (m : CPoly.CMvMonomial 1)
    (hm : m.degreeOf 0 ≤ d) :
    m = coeffMonomial (d := d) ⟨m.degreeOf 0, Nat.lt_succ_of_le hm⟩ := by
  apply CPoly.CMvMonomial.ext
  intro i hi
  have hi0 : i = 0 := Nat.lt_one_iff.mp hi
  subst i
  change m[0] = (Vector.ofFn (fun _ : Fin 1 => m.degreeOf 0))[0]
  rw [Vector.getElem_ofFn]
  rfl

omit [BEq R] [LawfulBEq R] in
private theorem coeff_eq_zero_of_degreeOf_gt
    (p : CPoly.CMvPolynomial.degreeLE 1 R d) {m : CPoly.CMvMonomial 1}
    (hm : d < m.degreeOf 0) :
    CPoly.CMvPolynomial.coeff m (p : CPoly.CMvPolynomial 1 R) = 0 := by
  by_cases hmem : m ∈ CPoly.Lawful.monomials (p : CPoly.CMvPolynomial 1 R)
  · have hm_le_degree :
        m.degreeOf 0 ≤ (p : CPoly.CMvPolynomial 1 R).degreeOf 0 := by
      unfold CPoly.CMvPolynomial.degreeOf
      exact Finset.le_sup (f := fun m : CPoly.CMvMonomial 1 => m.degreeOf 0)
        (by simpa using hmem)
    exact False.elim (Nat.not_lt_of_ge (hm_le_degree.trans (p.2 0)) hm)
  · have hnot : m ∉ (p : CPoly.CMvPolynomial 1 R) := by
      simpa [CPoly.Lawful.mem_monomials_iff] using hmem
    unfold CPoly.CMvPolynomial.coeff
    simp [hnot]

private theorem coeff_sum_coeffMonomial_of_degreeOf_le (m : CPoly.CMvMonomial 1)
    (hm : m.degreeOf 0 ≤ d) (coeffs : Fin (d + 1) → R) :
    CPoly.CMvPolynomial.coeff m
        (∑ k, CPoly.CMvPolynomial.monomial (coeffMonomial (d := d) k) (coeffs k)) =
      coeffs ⟨m.degreeOf 0, Nat.lt_succ_of_le hm⟩ := by
  let k : Fin (d + 1) := ⟨m.degreeOf 0, Nat.lt_succ_of_le hm⟩
  have hmk : m = coeffMonomial (d := d) k :=
    eq_coeffMonomial_of_degreeOf_le (d := d) m hm
  calc
    CPoly.CMvPolynomial.coeff m
        (∑ k, CPoly.CMvPolynomial.monomial (coeffMonomial (d := d) k) (coeffs k))
        = CPoly.CMvPolynomial.coeff (coeffMonomial (d := d) k)
            (∑ k, CPoly.CMvPolynomial.monomial (coeffMonomial (d := d) k) (coeffs k)) := by
          rw [hmk]
    _ = coeffs k := coeff_sum_coeffMonomial k coeffs

@[simp] theorem coeffVec_ofCoeffVec (coeffs : Fin (d + 1) → R) :
    coeffVec (ofCoeffVec (R := R) (d := d) coeffs) = coeffs := by
  ext k
  have hk : ∀ i : Fin 1, (coeffMonomial (d := d) k).degreeOf i ≤ d := by
    intro i
    fin_cases i
    change (coeffMonomial (d := d) k).degreeOf 0 ≤ d
    rw [coeffMonomial_degreeOf]
    exact Nat.le_of_lt_succ k.2
  simp only [coeffVec, ofCoeffVec, ofCMvPolynomial,
    CPoly.coeff_restrictDegree_eq_self_of_le hk]
  exact coeff_sum_coeffMonomial k coeffs

@[simp] theorem ofCoeffVec_coeffVec (p : CPoly.CMvPolynomial.degreeLE 1 R d) :
    ofCoeffVec (R := R) (d := d) (coeffVec p) = p := by
  ext m
  by_cases hm : m.degreeOf 0 ≤ d
  · rw [show CPoly.CMvPolynomial.coeff m
        (ofCoeffVec (R := R) (d := d) (coeffVec p) : CPoly.CMvPolynomial 1 R) =
        CPoly.CMvPolynomial.coeff m
          (CPoly.CMvPolynomial.restrictDegree d
            (∑ k, CPoly.CMvPolynomial.monomial (coeffMonomial (d := d) k)
              (coeffVec p k))) by rfl]
    rw [CPoly.coeff_restrictDegree, if_pos]
    · rw [coeff_sum_coeffMonomial_of_degreeOf_le m hm]
      let k : Fin (d + 1) := ⟨m.degreeOf 0, Nat.lt_succ_of_le hm⟩
      have hmk : m = coeffMonomial (d := d) k :=
        eq_coeffMonomial_of_degreeOf_le (d := d) m hm
      change CPoly.CMvPolynomial.coeff (coeffMonomial (d := d) k)
          (p : CPoly.CMvPolynomial 1 R) =
        CPoly.CMvPolynomial.coeff m (p : CPoly.CMvPolynomial 1 R)
      rw [← hmk]
    · intro i
      fin_cases i
      exact hm
  · rw [show CPoly.CMvPolynomial.coeff m
        (ofCoeffVec (R := R) (d := d) (coeffVec p) : CPoly.CMvPolynomial 1 R) =
        CPoly.CMvPolynomial.coeff m
          (CPoly.CMvPolynomial.restrictDegree d
            (∑ k, CPoly.CMvPolynomial.monomial (coeffMonomial (d := d) k)
              (coeffVec p k))) by rfl]
    rw [CPoly.coeff_restrictDegree, if_neg]
    · exact (coeff_eq_zero_of_degreeOf_gt (d := d) p (Nat.lt_of_not_ge hm)).symm
    · intro h
      exact hm (h 0)

/-- Bounded-degree computable univariate polynomials are equivalent to coefficient vectors. -/
def coeffEquiv : CPoly.CMvPolynomial.degreeLE 1 R d ≃ (Fin (d + 1) → R) where
  toFun := coeffVec
  invFun := ofCoeffVec (R := R) (d := d)
  left_inv := ofCoeffVec_coeffVec (R := R) (d := d)
  right_inv := coeffVec_ofCoeffVec (R := R) (d := d)

end Univariate

end degreeLE

/-- Stable constructor for the bounded-degree computable carrier. -/
def ofDegreeLE [BEq R] [LawfulBEq R] (d : ℕ) (p : CPoly.CMvPolynomial n R) :
    CPoly.CMvPolynomial.degreeLE n R d :=
  degreeLE.ofCMvPolynomial d p

/-- Computable multilinear polynomials. -/
abbrev multilinear (n : ℕ) (R : Type) [CommSemiring R] : Type _ :=
  CPoly.CMvPolynomial.degreeLE n R 1

/-- Computable multiquadratic polynomials. -/
abbrev multiquadratic (n : ℕ) (R : Type) [CommSemiring R] : Type _ :=
  CPoly.CMvPolynomial.degreeLE n R 2

end CMvPolynomial
end CPoly
