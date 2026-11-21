/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.ResultantDegree
import ArkLib.Data.Polynomial.ResultantSpecialization

/-! # The scalar degree of a resultant with total-degree support

If two plane polynomials have total degrees at most `m,m'` and nominal value
degrees `b,b'`, the scalar degree of the value resultant is bounded by
`b*m' + b'*m - b*b'`. Each nonzero determinant term uses the same sum of value
exponents. Accounting for those exponents saves the final product.
-/

set_option autoImplicit false

open Polynomial Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.WeightedSylvesterDegree

/-- Every nonzero coefficient at value exponent `j` has scalar degree at most `m-j`. -/
def TotalDegreeLe {R : Type*} [CommRing R] (f : R[X][X]) (m : ℕ) : Prop :=
  ∀ j, f.coeff j ≠ 0 → (f.coeff j).natDegree + j ≤ m

/-- Weighted support bound for the determinant of the actual Sylvester matrix. The
indices are nominal degrees, so the conclusion includes specialized leading terms
that vanish. -/
theorem natDegree_resultant_le {R : Type*} [CommRing R] (f g : R[X][X])
    {b b' m m' : ℕ} (hf : TotalDegreeLe f m) (hg : TotalDegreeLe g m') :
    (resultant f g b b').natDegree ≤ b*m' + b'*m - b*b' := by
  classical
  let A := sylvester f g b b'
  let w : Fin (b+b') → ℕ := Fin.addCases (fun j => m'+j.val) (fun j => m+j.val)
  have hentry (r j : Fin (b+b')) (hne : A r j ≠ 0) : (A r j).natDegree + r.val ≤ w j := by
    induction j using Fin.addCases with
    | left k =>
        simp only [A, sylvester, Matrix.of_apply, Fin.addCases_left] at hne ⊢
        split_ifs at hne ⊢ with h
        · have hh := hg _ hne
          have hr := h.1
          simp [w]
          omega
        · exact False.elim (hne rfl)
    | right k =>
        simp only [A, sylvester, Matrix.of_apply, Fin.addCases_right] at hne ⊢
        split_ifs at hne ⊢ with h
        · have hh := hf _ hne
          have hr := h.1
          simp [w]
          omega
        · exact False.elim (hne rfl)
  have hweight : (∑ i, w i) + b*b' = (b*m'+b'*m) + ∑ i : Fin (b+b'), i.val := by
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [w, Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    simp only [Nat.cast_id]
    ring
  rw [resultant, Matrix.det_apply']
  apply natDegree_sum_le_of_forall_le
  intro σ _
  change (↑↑(Equiv.Perm.sign σ) * ∏ i, A (σ i) i).natDegree ≤ _
  by_cases hz : ∃ i, A (σ i) i = 0
  · obtain ⟨i,hi⟩ := hz
    rw [Finset.prod_eq_zero (f := fun j => A (σ j) j) (Finset.mem_univ i) hi,
      mul_zero, natDegree_zero]
    exact Nat.zero_le _
  · push Not at hz
    have h := Finset.sum_le_sum (s:=Finset.univ) fun i _ => hentry (σ i) i (hz i)
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ (fun i => i.val)] at h
    have hdeg := (natDegree_prod_le Finset.univ (fun i => A (σ i) i))
    apply natDegree_mul_le.trans
    rw [natDegree_intCast, zero_add]
    omega

/-- Apply the canonical coefficient-degree bound when nominal degrees lie inside both triangles. -/
private theorem resultant_le_of_nominal_le {R : Type*} [CommRing R] (f g : R[X][X])
    {b b' m m' : ℕ} (hbm : b ≤ m) (hbm' : b' ≤ m')
    (hf : TotalDegreeLe f m) (hg : TotalDegreeLe g m') :
    (resultant f g b b').natDegree ≤ b*m' + b'*m - b*b' := by
  have h₁ (i : ℕ) (hi : i ≤ b) : i+(f.coeff i).natDegree ≤ m := by
    by_cases h : f.coeff i = 0
    · simpa [h] using hi.trans hbm
    · simpa [add_comm] using hf i h
  have h₂ (i : ℕ) (hi : i ≤ b') : i+(g.coeff i).natDegree ≤ m' := by
    by_cases h : g.coeff i = 0
    · simpa [h] using hi.trans hbm'
    · simpa [add_comm] using hg i h
  simpa [add_comm] using Polynomial.natDegree_resultant_le_of_coeff_add_le f g b b' m m' h₁ h₂

/-- The degree calculation for the numerator of the order-`d+1` implicit
coordinate derivative of a quintic having value degree three. -/
theorem quintic_cubic_derivative_resultant_bound {R : Type*} [CommRing R]
    (f g : R[X][X]) (d : ℕ) (hf : TotalDegreeLe f 5)
    (hg : TotalDegreeLe g (5+8*d)) :
    (resultant f g 3 (3+4*d)).natDegree ≤ 21+32*d := by
  apply (resultant_le_of_nominal_le f g (by omega) (by omega) hf hg).trans
  omega

/-- Counting distinct scalar specializations with a common value uses the same
weighted bound, including specializations dropping the leading value degree. -/
theorem common_fiber_count {K : Type*} [Field K] (f g : K[X][X])
    {b b' m m' : ℕ} (hfy : f.natDegree ≤ b) (hgy : g.natDegree ≤ b')
    (hpos : b ≠ 0 ∨ b' ≠ 0) (hf : TotalDegreeLe f m) (hg : TotalDegreeLe g m')
    (hres : resultant f g b b' ≠ 0) (S : Finset K)
    (hS : ∀ z ∈ S, ∃ y : K, (f.map (evalRingHom z)).eval y = 0 ∧
      (g.map (evalRingHom z)).eval y = 0) :
    S.card ≤ b*m' + b'*m - b*b' := by
  classical
  apply le_trans _ (natDegree_resultant_le f g hf hg)
  by_contra! h
  apply hres
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun z : S => z.val)
    Subtype.val_injective
  · intro z
    obtain ⟨y,hyf,hyg⟩ := hS _ z.property
    exact map_resultant_eq_zero_of_common_root (evalRingHom z.val) f g hfy hgy hpos y hyf hyg
  · simpa using h

end ArkLib.ProximityGap.Frontier.WeightedSylvesterDegree

#print axioms ArkLib.ProximityGap.Frontier.WeightedSylvesterDegree.natDegree_resultant_le
#print axioms ArkLib.ProximityGap.Frontier.WeightedSylvesterDegree.quintic_cubic_derivative_resultant_bound
#print axioms ArkLib.ProximityGap.Frontier.WeightedSylvesterDegree.common_fiber_count
