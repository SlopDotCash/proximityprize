/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.ResultantDegree
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-! # Local multiplicity of a Sylvester resultant

If the coefficients of two polynomials at value exponents `i` are divisible
by `π^(r-i)` and `π^(s-i)`, respectively, then `π^(r*s)` divides their
resultant for any nominal value degrees `m≥r`, `n≥s`. This follows from
divisibility of each individual Sylvester determinant term.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.SylvesterLocalMultiplicity

private def triangular (v : ℕ) : ℕ := ∑ i : Fin v, (v-(i:ℕ))

private theorem cutoff_sum {d n : ℕ} (h : d ≤ n) :
    (∑ i : Fin n, (d-(i:ℕ))) = triangular d := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Fin.sum_univ_add]
  simp [triangular, Fin.val_natAdd]

private theorem triangular_add (r s : ℕ) :
    triangular (r+s) = triangular r+triangular s+r*s := by
  unfold triangular
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd, Nat.add_sub_add_left]
  have he (i : Fin r) : r+s-i = (r-i)+s := by have := i.isLt; omega
  simp_rw [he]
  simp [Finset.sum_add_distrib, Nat.add_right_comm]

/-- Divisibility by the product of the two local orders, valid for arbitrary
commutative coefficient rings and nominal degrees. Both the row and column
potentials are truncated natural numbers. -/
theorem pow_dvd_resultant {R : Type*} [CommRing R] (π : R) (F G : R[X])
    {m n r s : ℕ} (hr : r ≤ m) (hs : s ≤ n)
    (hF : ∀ i, π^(r-i) ∣ F.coeff i) (hG : ∀ i, π^(s-i) ∣ G.coeff i) :
    π^(r*s) ∣ resultant F G m n := by
  classical
  let M := sylvester F G m n
  let row : Fin (m+n) → ℕ := fun i => r+s-i
  let col : Fin (m+n) → ℕ := Fin.addCases (fun j : Fin m => r-j) (fun j : Fin n => s-j)
  have hentry (i j : Fin (m+n)) : π^(row i-col j) ∣ M i j := by
    cases j using Fin.addCases with
    | left j =>
      have hh : M i (.castAdd n j) = if (i : ℕ) ∈ Set.Icc (j:ℕ) ((j:ℕ)+n)
        then G.coeff ((i:ℕ)-j) else 0 := by simp [M,sylvester]
      rw [hh]
      split_ifs with h
      · apply (pow_dvd_pow π _).trans (hG _)
        simp only [row,col,Fin.addCases_left]
        have hj := h.1
        omega
      · exact dvd_zero _
    | right j =>
      have hh : M i (.natAdd m j) = if (i : ℕ) ∈ Set.Icc (j:ℕ) ((j:ℕ)+m)
        then F.coeff ((i:ℕ)-j) else 0 := by simp [M,sylvester]
      rw [hh]
      split_ifs with h
      · apply (pow_dvd_pow π _).trans (hF _)
        simp only [row,col,Fin.addCases_right]
        have hj := h.1
        omega
      · exact dvd_zero _
  have hcol : ∑ j, col j = triangular r+triangular s := by
    simp only [col,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right]
    rw [cutoff_sum hr, cutoff_sum hs]
  have hrow : ∑ i, row i = triangular r+triangular s+r*s := by
    exact (cutoff_sum (Nat.add_le_add hr hs)).trans (triangular_add r s)
  change π^(r*s) ∣ M.det
  rw [Matrix.det_apply]
  apply Finset.dvd_sum
  intro σ _
  have heq : ∑ i, row (σ i) = ∑ i, row i := Equiv.sum_comp σ row
  have hsum : ∑ i, row (σ i) ≤ ∑ i, (col i + (row (σ i)-col i)) :=
    Finset.sum_le_sum fun i _ => by omega
  rw [Finset.sum_add_distrib, heq, hcol, hrow] at hsum
  have hp : π^(r*s) ∣ ∏ i, M (σ i) i := by
    apply (pow_dvd_pow π (by omega : r*s ≤ ∑ i, (row (σ i)-col i))).trans
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hentry (σ i) i)
  obtain ⟨v,hv⟩ := hp
  exact ⟨Equiv.Perm.sign σ • v, by rw [hv, mul_smul_comm]⟩

/-- Translating the value variable preserves a resultant when only the second
value degree is padded. -/
theorem resultant_taylor_padded {R : Type*} [CommRing R] (F G : R[X]) (w : R)
    (n : ℕ) (hn : G.natDegree ≤ n) :
    resultant (F.taylor w) (G.taylor w) F.natDegree n = resultant F G F.natDegree n := by
  have hg : (G.taylor w).natDegree = G.natDegree := natDegree_taylor ..
  have hf : (F.taylor w).natDegree = F.natDegree := natDegree_taylor ..
  have h := resultant_taylor F G w
  rw [hf,hg] at h
  rw [← Nat.add_sub_of_le hn,
    resultant_add_right_deg _ _ _ _ _ hg.le,
    resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_taylor_natDegree, coeff_natDegree, h]

/-- Local coefficient divisibility after shifting the value variable estimates the
untranslated Sylvester resultant. -/
theorem pow_dvd_resultant_of_taylor {R : Type*} [CommRing R] (π w : R) (F G : R[X])
    {n r s : ℕ} (hr : r ≤ F.natDegree) (hs : s ≤ n) (hn : G.natDegree ≤ n)
    (hF : ∀ i, π^(r-i) ∣ (F.taylor w).coeff i)
    (hG : ∀ i, π^(s-i) ∣ (G.taylor w).coeff i) :
    π^(r*s) ∣ resultant F G F.natDegree n := by
  rw [← resultant_taylor_padded _ _ w _ hn]
  exact pow_dvd_resultant π _ _ hr hs hF hG

/-- The total of local exponents at distinct coordinate sites is at most the degree
of a nonzero polynomial. -/
theorem sum_local_orders_le_natDegree {K : Type*} [Field K] (Q : K[X]) (hQ : Q ≠ 0)
    (S : Finset K) (v : K → ℕ) (hv : ∀ a ∈ S, (Polynomial.X-C a)^(v a) ∣ Q) :
    ∑ a ∈ S, v a ≤ Q.natDegree := by
  classical
  calc
    ∑ a ∈ S, v a ≤ ∑ a ∈ S, Q.roots.count a := by
      apply Finset.sum_le_sum
      intro a ha
      rw [count_roots, le_rootMultiplicity_iff hQ]
      exact hv a ha
    _ ≤ ∑ a ∈ S ∪ Q.roots.toFinset, Q.roots.count a :=
      Finset.sum_le_sum_of_subset (Finset.subset_union_left)
    _ = Q.roots.card := Multiset.sum_count_eq_card fun a ha =>
      Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha)
    _ ≤ Q.natDegree := card_roots' Q

/-- Summing the translated quartic local bound gives the coefficient seven in
the intrinsic-interpolation multiplicity budget. -/
theorem quartic_site_sum {K : Type*} [Field K] (F G : K[X][X]) (S : Finset K)
    (w : K → K[X]) (r : K → ℕ) (hm : F.natDegree = 4) (hn : G.natDegree ≤ 10)
    (hR : resultant F G 4 10 ≠ 0) (hr : ∀ a ∈ S, r a ≤ 4)
    (hF : ∀ a ∈ S, ∀ i, (Polynomial.X-C a)^(r a-i) ∣ (F.taylor (w a)).coeff i)
    (hG : ∀ a ∈ S, ∀ i, (Polynomial.X-C a)^(3*r a-2-i) ∣ (G.taylor (w a)).coeff i) :
    7*(∑ a ∈ S, r a) ≤ 6*S.card + (resultant F G 4 10).natDegree := by
  have hval := sum_local_orders_le_natDegree (resultant F G 4 10) hR S (fun a => r a*(3*r a-2))
    (by
      intro a ha
      rw [← hm]
      exact pow_dvd_resultant_of_taylor _ _ F G
        (by rw [hm]; exact hr a ha) (by have := hr a ha; omega) hn (hF a ha) (hG a ha))
  have hsmall (a : K) (ha : a ∈ S) : 7*r a ≤ 6 + r a*(3*r a-2) := by
    have hh := hr a ha
    interval_cases h : r a <;> decide
  have hs := Finset.sum_le_sum hsmall
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const, smul_eq_mul] at hs
  omega

end ArkLib.ProximityGap.Frontier.SylvesterLocalMultiplicity

open ArkLib.ProximityGap.Frontier.SylvesterLocalMultiplicity in
#print axioms quartic_site_sum
