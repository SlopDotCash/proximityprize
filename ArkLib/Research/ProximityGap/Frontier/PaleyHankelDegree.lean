/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyDefectMinor
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Degree of the normalized derivative determinant

Adjacent rows eliminate the first column of a Hankel matrix whose successive moments have
ratio `(d−n)/(D−n)`. The remaining moments satisfy the same recurrence with parameters
`d−1,D−2`. This certifies nonvanishing in the coefficient field.
-/

namespace ProximityGap.PaleyHankelDegree

open Finset Matrix Polynomial PaleyDefectMinor

variable {K : Type*} [Field K]

private theorem eliminate {u v d D i j : K} (h : (D-(i+j))*v = (d-(i+j))*u)
    (hn : D-(i+j) ≠ 0) : (D-i)*v - (d-i)*u = (d-D)*j*(u/(D-(i+j))) := by
  field_simp
  linear_combination (D-i)*h

private theorem moment_kernel (h : ℕ) (d D : K) (r : ℕ → K) (h0 : r 0 ≠ 0)
    (hr : ∀ n < 2*h, (D-n)*r (n+1) = (d-n)*r n)
    (hden : ∀ n < 2*h, D-n ≠ 0) (hnum : ∀ n < h, d-n ≠ 0)
    (hgap : ∀ n < h, D-d-n ≠ 0) (hchar : ∀ n < h, ((n+1:ℕ):K) ≠ 0)
    (c : Fin (h+1) → K) (hc : ∀ i : Fin (h+1), ∑ j, r (i.val+j.val)*c j = 0) :
    c = 0 := by
  induction h generalizing d D r with
  | zero =>
    have h := hc 0
    change (∑ j : Fin 1, r (0+j.val)*c j) = 0 at h
    simp only [Fin.sum_univ_one, Fin.val_zero, Nat.add_zero] at h
    funext i
    have hi : i = 0 := Fin.ext (by omega)
    simpa [hi] using (mul_eq_zero.mp h).resolve_left h0
  | succ h ih =>
    let s (k : ℕ) := r (k+1) / (D-((k+1:ℕ):K))
    have hs0 : s 0 ≠ 0 := by
      have h1 := hr 0 (by omega)
      simp only [Nat.cast_zero, sub_zero, Nat.zero_add] at h1
      have hd : d ≠ 0 := by simpa using hnum 0 (by omega)
      have hr1 : r 1 ≠ 0 := fun hz => (mul_ne_zero hd h0) (by rw [← h1, hz, mul_zero])
      exact div_ne_zero hr1 (hden 1 (by omega))
    have hsr (k : ℕ) (hk : k < 2*h) :
        (D-2-k)*s (k+1) = (d-1-k)*s k := by
      have hk1 := hr (k+1) (by omega)
      have hd1 := hden (k+1) (by omega)
      have hd2 := hden (k+1+1) (by omega)
      dsimp [s]
      rw [show D-2-k = D-((k+1+1:ℕ):K) by push_cast; ring,
        show d-1-k = d-((k+1:ℕ):K) by push_cast; ring]
      field_simp
      linear_combination hk1
    let z (j : Fin (h+1)) := ((j.val+1 : ℕ) : K) * c j.succ
    have hrow (i : Fin (h+1)) :
        ∑ j : Fin (h+2),
          ((D-i.val)*r (i.val+j.val+1) - (d-i.val)*r (i.val+j.val))*c j = 0 := by
      simp only [sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
      have h1 := hc i.succ
      have h2 := hc i.castSucc
      simp only [Fin.val_succ, Nat.succ_add] at h1
      simp only [Fin.val_castSucc] at h2
      simp only [h1,h2,mul_zero,sub_self]
    have hzrow (i : Fin (h+1)) : ∑ j, s (i.val+j.val)*z j = 0 := by
      have hh := hrow i
      rw [Fin.sum_univ_succ] at hh
      simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ] at hh
      rw [hr i.val (by omega), sub_self, zero_mul, zero_add] at hh
      have hper (j : Fin (h+1)) :
          ((D-i.val)*r (i.val+(j.val+1)+1) - (d-i.val)*r (i.val+(j.val+1)))*c j.succ =
            (d-D)*(s (i.val+j.val)*z j) := by
        have hk := hr (i.val+(j.val+1)) (by omega)
        have hn := hden (i.val+(j.val+1)) (by omega)
        rw [Nat.cast_add] at hk hn
        rw [eliminate hk hn]
        dsimp only [s, z]
        simp only [Nat.add_assoc, Nat.cast_add]
        ring
      rw [sum_congr rfl (fun j _ => hper j), ← mul_sum] at hh
      apply (mul_eq_zero.mp hh).resolve_left
      have hg : D-d ≠ 0 := by simpa using hgap 0 (by omega)
      exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hg))
    have hz : z = 0 := ih (d-1) (D-2) s hs0 hsr (by
      intro n hn
      convert hden (n+2) (by omega) using 1; push_cast; ring) (by
      intro n hn
      convert hnum (n+1) (by omega) using 1; push_cast; ring) (by
      intro n hn
      convert hgap (n+1) (by omega) using 1; push_cast; ring)
      (fun n hn => hchar n (by omega)) z hzrow
    have htail (j : Fin (h+1)) : c j.succ = 0 :=
      (mul_eq_zero.mp (congrFun hz j)).resolve_left (hchar j.val (by omega))
    have hhead := hc 0
    rw [Fin.sum_univ_succ] at hhead
    simp only [Fin.val_zero, htail, mul_zero, sum_const_zero, add_zero] at hhead
    exact funext (Fin.cases ((mul_eq_zero.mp hhead).resolve_left h0) htail)

variable {p : ℕ} [Fact p.Prime]

private theorem nz_cast {n : ℕ} (hn : 0 < n) (hp : n < p) : (n : ZMod p) ≠ 0 := by
  intro hz
  have h := congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt hp, ZMod.val_zero] at h
  omega

private theorem descending_ne {D : ℕ} (hD : D < p) (k : ℕ) (hk : k ≤ D) :
    (D.descFactorial k : ZMod p) ≠ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Nat.cast_mul]
    exact mul_ne_zero (nz_cast (by omega) (by omega)) (ih (by omega))

/-- The scalar matrix of leading factors in the normalized derivatives has nonzero
determinant at the actual prime, under the degree constraints on the rectangle. -/
theorem scalar_det_ne_zero {d D h : ℕ} (hd : 2*h ≤ d) (hdD : d ≤ D) (hgap : h ≤ D-d)
    (hp : D < p) :
    Matrix.det (fun i j : Fin (h+1) =>
      (d.descFactorial (i.val+j.val) : ZMod p) /
        (D.descFactorial (i.val+j.val) : ZMod p)) ≠ 0 := by
  let r (n : ℕ) := (d.descFactorial n : ZMod p) / (D.descFactorial n : ZMod p)
  intro hdet
  obtain ⟨c, hcn, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hcn
  apply moment_kernel h (d : ZMod p) (D : ZMod p) r (by simp [r]) _ _ _ _ _ c
  · exact fun i => congrFun hc i
  · intro n hn
    have hnD : n < D := by omega
    have hnd : n ≤ d := by omega
    have hDn := descending_ne (p := p) hp n hnD.le
    have hsub : (D : ZMod p)-n ≠ 0 := by
      rw [← Nat.cast_sub hnD.le]; exact nz_cast (by omega) (by omega)
    dsimp only [r]
    simp only [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hnd, Nat.cast_sub hnD.le]
    field_simp
  · intro n hn
    rw [← Nat.cast_sub (show n ≤ D by omega)]
    exact nz_cast (by omega) (by omega)
  · intro n hn
    rw [← Nat.cast_sub (show n ≤ d by omega)]
    exact nz_cast (by omega) (by omega)
  · intro n hn
    rw [← Nat.cast_sub hdD, ← Nat.cast_sub (show n ≤ D-d by omega)]
    exact nz_cast (by omega) (by omega)
  · intro n hn
    exact nz_cast (by omega) (by omega)

private theorem coeff_prod_at_weights {ι : Type*} (S : Finset ι) (P : ι → K[X]) (w : ι → ℕ)
    (hw : ∀ i ∈ S, (P i).natDegree ≤ w i) :
    (∏ i ∈ S, P i).coeff (∑ i ∈ S, w i) = ∏ i ∈ S, (P i).coeff (w i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    simp only [prod_insert ha, sum_insert ha]
    have hS (i) (hi : i ∈ S) := hw i (mem_insert_of_mem hi)
    rw [coeff_mul_add_eq_of_natDegree_le (hw a (mem_insert_self _ _))
      ((natDegree_prod_le _ _).trans (sum_le_sum hS)), ih hS]

private theorem weight_sum {d h : ℕ} (hd : 2*h ≤ d) (σ : Equiv.Perm (Fin (h+1))) :
    ∑ i : Fin (h+1), (d - ((σ i).val+i.val)) = (h+1)*(d-h) := by
  have hidx (i : Fin (h+1)) : (σ i).val+i.val ≤ d := by
    have := (σ i).isLt; omega
  have hsum : (∑ i : Fin (h+1), (d-((σ i).val+i.val))) +
      (∑ i : Fin (h+1), ((σ i).val+i.val)) = (h+1)*d := by
    rw [← sum_add_distrib]
    simp only [Nat.sub_add_cancel (hidx _), sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id]
  have hperm : ∑ i : Fin (h+1), (σ i).val = ∑ i : Fin (h+1), i.val := Equiv.sum_comp σ _
  have htri : (∑ i : Fin (h+1), i.val)*2 = (h+1)*h := by
    simpa only [Finset.sum_range, Nat.add_sub_cancel] using sum_range_id_mul_two (h+1)
  have htotal : (h+1)*(d-h)+(h+1)*h = (h+1)*d := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
  rw [sum_add_distrib, hperm] at hsum
  omega

/-- The coefficient at the common upper degree of the Leibniz products is the determinant
of the normalized leading factors times the expected power of the leading coefficient. -/
theorem coeff_normalizedHankel_det (P : K[X]) (D h : ℕ) (hd : 2*h ≤ P.natDegree) :
    ((normalizedHankel P D h).det).coeff ((h+1)*(P.natDegree-h)) =
      P.leadingCoeff ^ (h+1) *
        Matrix.det (fun i j : Fin (h+1) => (P.natDegree.descFactorial (i.val+j.val) : K) /
          (D.descFactorial (i.val+j.val) : K)) := by
  classical
  let M := normalizedHankel P D h
  let w (i j : Fin (h+1)) := P.natDegree-(i.val+j.val)
  let H : Matrix (Fin (h+1)) (Fin (h+1)) K := fun i j =>
    (P.natDegree.descFactorial (i.val+j.val) : K) / (D.descFactorial (i.val+j.val) : K)
  have hb (i j : Fin (h+1)) : (M i j).natDegree ≤ w i j :=
    (natDegree_C_mul_le _ _).trans (natDegree_iterate_derivative P _)
  have hc (i j : Fin (h+1)) : (M i j).coeff (w i j) = (P.leadingCoeff • H) i j := by
    change (C _ * derivative^[_] P).coeff (P.natDegree-(i.val+j.val)) = P.leadingCoeff * H i j
    rw [coeff_C_mul, coeff_iterate_derivative, Nat.sub_add_cancel (by omega), nsmul_eq_mul,
      coeff_natDegree]
    dsimp [H]
    rw [div_eq_mul_inv]
    ring
  change M.det.coeff _ = P.leadingCoeff ^ (h+1) * H.det
  have hsc : (P.leadingCoeff • H).det = P.leadingCoeff ^ (h+1) * H.det := by
    rw [Matrix.det_smul, Fintype.card_fin]
  rw [← hsc]
  rw [Matrix.det_apply, finsetSum_coeff, Matrix.det_apply]
  refine sum_congr rfl fun σ _ => ?_
  rw [coeff_smul]
  change _ = Equiv.Perm.sign σ • ∏ i, (P.leadingCoeff • H) (σ i) i
  rw [← weight_sum hd σ, coeff_prod_at_weights univ (fun i => M (σ i) i)
    (fun i => w (σ i) i) (fun i _ => hb _ _)]
  simp_rw [hc]

/-- The normalized Hankel polynomial has degree at most the sum of entry-degree bounds
over any permutation. -/
theorem normalizedHankel_det_degree_le (P : K[X]) (D h : ℕ) (hd : 2*h ≤ P.natDegree) :
    (normalizedHankel P D h).det.natDegree ≤ (h+1)*(P.natDegree-h) := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  refine (natDegree_smul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  rw [← weight_sum hd σ]
  exact sum_le_sum fun i _ => (natDegree_C_mul_le _ _).trans (natDegree_iterate_derivative P _)

/-- The polynomial determinant is nonzero, including when its degree is zero. -/
theorem normalizedHankel_det_ne_zero (P : (ZMod p)[X]) (hP : P ≠ 0) (D h : ℕ)
    (hd : 2*h ≤ P.natDegree) (hdD : P.natDegree ≤ D) (hgap : h ≤ D-P.natDegree)
    (hp : D < p) : (normalizedHankel P D h).det ≠ 0 := by
  have hc := coeff_normalizedHankel_det P D h hd
  intro hz
  rw [hz, coeff_zero] at hc
  exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hP))
    (scalar_det_ne_zero hd hdD hgap hp) hc.symm

/-- Exact degree of the normalized polynomial determinant in the prime field. -/
theorem normalizedHankel_det_degree (P : (ZMod p)[X]) (hP : P ≠ 0) (D h : ℕ)
    (hd : 2*h ≤ P.natDegree) (hdD : P.natDegree ≤ D) (hgap : h ≤ D-P.natDegree)
    (hp : D < p) :
    (normalizedHankel P D h).det.natDegree = (h+1)*(P.natDegree-h) := by
  apply (normalizedHankel_det_degree_le P D h hd).antisymm
  apply le_natDegree_of_ne_zero
  rw [coeff_normalizedHankel_det P D h hd]
  exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hP))
    (scalar_det_ne_zero hd hdD hgap hp)

end ProximityGap.PaleyHankelDegree

#print axioms ProximityGap.PaleyHankelDegree.scalar_det_ne_zero
#print axioms ProximityGap.PaleyHankelDegree.coeff_normalizedHankel_det
#print axioms ProximityGap.PaleyHankelDegree.normalizedHankel_det_degree
