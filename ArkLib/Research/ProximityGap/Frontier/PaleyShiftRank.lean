/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyInterpolationContact
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Vandermonde

/-!
# An exact matrix rank at a prescribed quadratic shift

The contact congruence identifies a block of normalized derivative evaluations with a
weighted power-moment matrix. Its first square Vandermonde minor detects every node.
-/

namespace ProximityGap.PaleyShiftRank

open Finset Matrix Polynomial PaleyInterpolationContact

variable {K : Type*} [Field K]

/-- Hankel matrix of power sums of the weighted nodes. -/
noncomputable def moments {e : ℕ} (n : ℕ) (v w : Fin e → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => ∑ u, w u * (v u)^(i.val+j.val)

/-- The weighted moments factor into two rectangular Vandermonde matrices and a diagonal. -/
theorem moments_factor {e : ℕ} (n : ℕ) (v w : Fin e → K) :
    moments n v w = (show Matrix (Fin n) (Fin e) K from fun i u => (v u)^i.val) *
      diagonal w * (show Matrix (Fin e) (Fin n) K from fun u j => (v u)^j.val) := by
  let U : Matrix (Fin n) (Fin e) K := fun i u => (v u)^i.val
  change moments n v w = U * diagonal w * U.transpose
  ext i j : 1
  rw [Matrix.mul_apply]
  change (∑ u, w u*(v u)^(i.val+j.val)) = _
  refine sum_congr rfl fun u _ => ?_
  rw [Matrix.mul_diagonal w U i u, Matrix.transpose_apply, pow_add]
  dsimp [U]
  ring

/-- If the number of nodes fits in the block, its rank is the number of distinct nodes
with nonzero weights. This includes the empty node set and empty block. -/
theorem moments_rank {e n : ℕ} (hen : e ≤ n) (v w : Fin e → K)
    (hv : Function.Injective v) (hw : ∀ u, w u ≠ 0) : (moments n v w).rank = e := by
  classical
  apply le_antisymm
  · rw [moments_factor]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans
      (Matrix.rank_le_width _))
  · let V := Matrix.vandermonde v
    let f : Fin e → Fin n := Fin.castLE hen
    have hf : (moments n v w).submatrix f f = V.transpose * diagonal w * V := by
      calc
        _ = moments e v w := rfl
        _ = _ := moments_factor e v w
    have hdet : (V.transpose * diagonal w * V).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
      have hV := Matrix.det_vandermonde_ne_zero_iff.mpr hv
      exact mul_ne_zero (mul_ne_zero hV (Finset.prod_ne_zero_iff.mpr (fun u _ => hw u))) hV
    have hle := (moments n v w).rank_submatrix_le f f
    rwa [hf, Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at hle

/-- Evaluating the normalized derivatives, allowing a block of size zero. -/
noncomputable def shiftBlock (P : K[X]) (D : ℕ) (b : K) (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  fun i j => (D.descFactorial (i.val+j.val) : K)⁻¹ * (derivative^[i.val+j.val] P).eval b

private theorem eval_derivative_of_contact (P G : K[X]) (b : K) {ν j : ℕ}
    (hc : (X-C b)^ν ∣ P-G) (hj : j < ν) :
    (derivative^[j] P).eval b = (derivative^[j] G).eval b := by
  have h := (dvd_pow_self (X-C b) (show ν-j ≠ 0 by omega)).trans
    (pow_sub_dvd_iterate_derivative_of_pow_dvd j hc)
  have hval := dvd_iff_isRoot.mp h
  change (derivative^[j] (P-G)).eval b = 0 at hval
  rwa [iterate_derivative_sub, eval_sub, sub_eq_zero] at hval

/-- Contact with a sum of shifted powers gives an exact evaluated power-moment matrix.
The nodes are reciprocal symbols and the weights include the original symbol to power `D`. -/
theorem shiftBlock_of_contact {e n ν D : ℕ} (P : K[X]) (b : K) (a c : Fin e → K)
    (ha : ∀ u, b+a u ≠ 0) (hord : ∀ i j : Fin n, i.val+j.val < ν)
    (hD : ∀ i j : Fin n, i.val+j.val ≤ D)
    (hu : ∀ i j : Fin n, (D.descFactorial (i.val+j.val) : K) ≠ 0)
    (hc : (X-C b)^ν ∣ P - ∑ u, C (c u)*(X+C (a u))^D) :
    shiftBlock P D b n = moments n (fun u => (b+a u)⁻¹) (fun u => c u*(b+a u)^D) := by
  ext i j : 1
  let k := i.val+j.val
  change (D.descFactorial k : K)⁻¹ * (derivative^[k] P).eval b = _
  rw [eval_derivative_of_contact _ _ _ hc (hord i j), iterate_derivative_sum, eval_finsetSum,
    mul_sum]
  apply sum_congr rfl
  intro u _
  rw [iterate_derivative_C_mul, iterate_derivative_X_add_pow]
  simp only [nsmul_eq_mul, eval_mul, eval_C, eval_natCast, eval_pow, eval_add, eval_X, inv_pow]
  have hs : (b+a u)^(D-k) = (b+a u)^D * ((b+a u)^k)⁻¹ := by
    rw [← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ (ha u)), ← pow_add,
      Nat.sub_add_cancel (hD i j)]
  rw [hs]
  have hn : (D.descFactorial k : K) ≠ 0 := hu i j
  field_simp
  dsimp only [k]
  ring

variable {p : ℕ} [Fact p.Prime]

/-- The normalized derivative block at the prescribed shift has rank equal to the selected
sign count whenever it is the minority. The size includes the possible zero symbol. -/
theorem rank_of_minority (hp : p ≠ 2) (A : Finset (ZMod p)) (b : ZMod p)
    (ha : 2 ≤ A.card) (hD : p/2+(A.card-2) < p) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    let D := p/2+(A.card-2)
    let E := A.filter fun u => quadraticChar (ZMod p) (b+u) = -σ
    let n := (A.card - (if -b ∈ A then 1 else 0))/2
    E.card ≤ n → (shiftBlock (powerSum A A D) D b n).rank = E.card := by
  classical
  let k := A.card-2
  let D := p/2+k
  let E := A.filter fun u => quadraticChar (ZMod p) (b+u) = -σ
  let n := (A.card - (if -b ∈ A then 1 else 0))/2
  let ν := if -b ∈ A then k else k+1
  let a (i : Fin E.card) : ZMod p := E.equivFin.symm i
  let w (u : ZMod p) := Lagrange.nodalWeight A id u
  let c (i : Fin E.card) := 2 * w (a i)
  have hsite (i : Fin E.card) : a i ∈ E := (E.equivFin.symm i).property
  have hnon (i : Fin E.card) : b+a i ≠ 0 := by
    intro hz
    have hi := (mem_filter.mp (hsite i)).2
    rw [hz, quadraticChar_zero] at hi
    rcases hσ with rfl | rfl <;> norm_num at hi
  have htwo : (2 : ZMod p) ≠ 0 := by
    have h2 : 2 < p := by have := (Fact.out : p.Prime).two_le; omega
    intro hz
    have he := congrArg ZMod.val hz
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from rfl, ZMod.val_natCast_of_lt h2,
      ZMod.val_zero] at he
    contradiction
  have hsum : (∑ i, C (c i)*(X+C (a i))^D) = C 2 * powerSum A E D := by
    let g (u : ZMod p) := C (2*w u)*(X+C u)^D
    change (∑ i, g (E.equivFin.symm i)) = _
    rw [E.equivFin.symm.sum_comp (fun u : E => g u.val)]
    simp [g, w, powerSum, Finset.mul_sum, mul_assoc]
    exact E.sum_attach (fun u : ZMod p => C 2 * (C (Lagrange.nodalWeight A id u) * (X+C u)^D))
  have hcont := minority_contact (K := ZMod p) (by rwa [ZMod.ringChar_zmod_n]) A b
    (show k < A.card by dsimp [k]; omega) hσ
  have hkne : k ≠ A.card-1 := by dsimp [k]; omega
  have hc : (X-C b)^ν ∣ powerSum A A D - ∑ i, C (c i)*(X+C (a i))^D := by
    rw [hsum]
    simpa only [ZMod.card, hkne, ↓reduceIte, C_0, sub_zero, D, E, ν] using hcont
  have hord (i j : Fin n) : i.val+j.val < ν := by
    have hi := i.isLt
    have hj := j.isLt
    dsimp [n] at hi hj
    dsimp [ν,k]
    split_ifs at * <;> omega
  have hjD (i j : Fin n) : i.val+j.val ≤ D := by
    have hi := hord i j
    have h2 := (Fact.out : p.Prime).two_le
    dsimp [ν,D] at *
    split at hi <;> omega
  have hunit (i j : Fin n) : (D.descFactorial (i.val+j.val) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hz
    have hfa : p ∣ D.factorial := Nat.dvd_trans hz
      ⟨(D-(i.val+j.val)).factorial, by rw [mul_comm, Nat.factorial_mul_descFactorial (hjD i j)]⟩
    exact (not_le.mpr hD) ((Fact.out : p.Prime).dvd_factorial.mp hfa)
  change E.card ≤ n → (shiftBlock (powerSum A A D) D b n).rank = E.card
  intro he
  rw [shiftBlock_of_contact _ _ a c hnon hord hjD hunit hc]
  apply moments_rank he
  · intro i j hij
    exact E.equivFin.symm.injective (Subtype.ext (add_left_cancel (inv_inj.mp hij)))
  · intro i
    have hi := (mem_filter.mp (hsite i)).1
    exact mul_ne_zero (mul_ne_zero htwo (Lagrange.nodalWeight_ne_zero (fun _ _ _ _ e => e) hi))
      (pow_ne_zero _ (hnon i))

private theorem sign_card_sum (A : Finset (ZMod p)) (b : ZMod p) :
    (A.filter fun u => quadraticChar (ZMod p) (b+u) = 1).card +
      (A.filter fun u => quadraticChar (ZMod p) (b+u) = -1).card =
        A.card - (if -b ∈ A then 1 else 0) := by
  classical
  let P := A.filter fun u => quadraticChar (ZMod p) (b+u) = 1
  let N := A.filter fun u => quadraticChar (ZMod p) (b+u) = -1
  have hd : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    have h := (mem_filter.mp hu).2.symm.trans (mem_filter.mp hv).2
    norm_num at h
  have hunion : P ∪ N = A.erase (-b) := by
    ext u
    simp only [P, N, mem_union, mem_filter, mem_erase]
    by_cases hz : u = -b
    · simp [hz]
    · have hn : b+u ≠ 0 := fun h => hz (by linear_combination h)
      rcases quadraticChar_dichotomy hn with h | h <;> simp [hz,h]
  change P.card + N.card = _
  rw [← card_union_of_disjoint hd, hunion]
  by_cases h : -b ∈ A <;> simp [h]

/-- The evaluated derivative block has exactly the rank of the minority sign count,
with no hypothesis on which sign is the minority. -/
theorem rank_eq_min_counts (hp : p ≠ 2) (A : Finset (ZMod p)) (b : ZMod p)
    (ha : 2 ≤ A.card) (hD : p/2+(A.card-2) < p) :
    let D := p/2+(A.card-2)
    let n := (A.card - (if -b ∈ A then 1 else 0))/2
    (shiftBlock (powerSum A A D) D b n).rank =
      min (A.filter fun u => quadraticChar (ZMod p) (b+u) = 1).card
        (A.filter fun u => quadraticChar (ZMod p) (b+u) = -1).card := by
  classical
  dsimp only
  have hsum := sign_card_sum A b
  rcases le_total (A.filter fun u => quadraticChar (ZMod p) (b+u) = 1).card
      (A.filter fun u => quadraticChar (ZMod p) (b+u) = -1).card with h | h
  · rw [min_eq_left h]
    have hr := rank_of_minority hp A b ha hD (Or.inr (rfl : (-1:ℤ) = -1))
    simp only [neg_neg] at hr
    exact hr (by omega)
  · rw [min_eq_right h]
    exact rank_of_minority hp A b ha hD (Or.inl (rfl : (1:ℤ) = 1)) (by omega)

/-- Each prescribed row discrepancy is recovered from the polynomial matrix rank and the
number of nonzero symbols on the row. -/
theorem abs_sum_add_two_rank (hp : p ≠ 2) (A : Finset (ZMod p)) (b : ZMod p)
    (ha : 2 ≤ A.card) (hD : p/2+(A.card-2) < p) :
    let D := p/2+(A.card-2)
    let s := A.card - (if -b ∈ A then 1 else 0)
    |∑ u ∈ A, quadraticChar (ZMod p) (b+u)| +
      2 * ((shiftBlock (powerSum A A D) D b (s/2)).rank : ℤ) = (s : ℤ) := by
  classical
  dsimp only
  rw [rank_eq_min_counts hp A b ha hD]
  let P := (A.filter fun u => quadraticChar (ZMod p) (b+u) = 1).card
  let N := (A.filter fun u => quadraticChar (ZMod p) (b+u) = -1).card
  have hsum : (∑ u ∈ A, quadraticChar (ZMod p) (b+u)) = (P : ℤ) - N := by
    calc
      _ = ∑ u ∈ A, ((if quadraticChar (ZMod p) (b+u) = 1 then (1:ℤ) else 0) -
          (if quadraticChar (ZMod p) (b+u) = -1 then (1:ℤ) else 0)) := by
            apply sum_congr rfl
            intro u _
            rcases (quadraticChar_isQuadratic (ZMod p)) (b+u) with h | h | h <;> norm_num [h]
      _ = _ := by rw [sum_sub_distrib, sum_boole, sum_boole]
  rw [hsum]
  change |(P : ℤ) - N| + 2 * ((min P N : ℕ) : ℤ) = _
  have ht : P+N = A.card - (if -b ∈ A then 1 else 0) := sign_card_sum A b
  rcases le_total P N with h | h
  · rw [min_eq_left h, abs_of_nonpos (by omega)]
    omega
  · rw [min_eq_right h, abs_of_nonneg (by omega)]
    omega

end ProximityGap.PaleyShiftRank

#print axioms ProximityGap.PaleyShiftRank.moments_rank
#print axioms ProximityGap.PaleyShiftRank.shiftBlock_of_contact
#print axioms ProximityGap.PaleyShiftRank.rank_eq_min_counts
#print axioms ProximityGap.PaleyShiftRank.abs_sum_add_two_rank
