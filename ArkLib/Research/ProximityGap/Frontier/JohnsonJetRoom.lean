/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterCoreWeightedJets

/-! # Ordinary mixed-jet dimensions at the Johnson crossing -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.JohnsonJetRoom
open Finset QuarterCoreWeightedJets

private abbrev n : ℕ := 1073741824
private abbrev d : ℕ := 536870911
private abbrev t : ℕ := 759250124

private theorem linear_sum (k a h : ℕ) (hpos : ∀ j < k, j*h ≤ a) :
    2 * (∑ j ∈ range k, (a-j*h) : ℕ) =
      (k : ℤ)*(2*(a : ℤ)-(h : ℤ)*((k : ℤ)-1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have prev := ih (fun j hj => hpos j (by omega))
    rw [sum_range_succ, Nat.cast_add, Nat.cast_sub (hpos k (by omega)), Nat.cast_mul, Nat.cast_succ]
    linarith

/-- The crossing is the very first integer error count with squared agreement below nd. -/
theorem crossing : n-t=314491700 ∧ t*t < n*d ∧ n*d < (t+1)*(t+1) := by decide

private theorem johnson_mean {n d t : ℤ} (hd : 0 < d) (hj : t*t ≤ n*d) : 2*t ≤ n+d := by
  by_contra! bad
  have positive := mul_pos hd (sub_pos.mpr bad)
  nlinarith only [positive,hj,sq_nonneg (t-d)]

private theorem full_quadratic {n d t : ℤ} (r l : ℤ) (hr : 0 < r) (hd : 0 < d)
    (hl : r+1 ≤ l) (hj : t*t ≤ n*d) :
    2*l*r*t-d*l*(l-1) ≤ n*r*(r+1) := by
  by_contra! bad
  have positive := mul_pos (show 0 < r*(r+1)*d by positivity) (sub_pos.mpr bad)
  have johnson := mul_nonneg (sq_nonneg (r*(r+1))) (sub_nonneg.mpr hj)
  have extra := mul_nonneg (mul_nonneg (mul_nonneg hr.le (show 0 ≤ l by omega))
    (show 0 ≤ l-r-1 by omega)) (sq_nonneg d)
  nlinarith only [positive,johnson,extra,sq_nonneg (r*(r+1)*t-r*l*d)]

private theorem prefix_bound {n d t : ℕ} (hd : 0 < d) (hnd : d ≤ n) (ht : d ≤ t)
    (hjohn : t*t ≤ n*d) (r k : ℕ) (hr : 0 < r) :
    (∑ j ∈ range k, (r*t-j*d)) ≤ n * ∑ j ∈ range k, (r-j) := by
  have mean := johnson_mean (n := (n : ℤ)) (d := (d : ℤ)) (t := (t : ℤ))
    (by exact_mod_cast hd) (by exact_mod_cast hjohn)
  by_cases hk : k ≤ r
  · have hrow := linear_sum k r 1 (fun j hj => by simpa using (by omega : j ≤ r))
    have hcol := linear_sum k (r*t) d (fun j hj =>
      Nat.mul_le_mul (by omega : j ≤ r) ht)
    simp only [mul_one, Nat.cast_one, one_mul] at hrow
    have suffices_int : (k : ℤ)*(2*(r : ℤ)*t-d*((k : ℤ)-1)) ≤
        (k : ℤ)*(n*(2*(r : ℤ)-((k : ℤ)-1))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have kr : (k : ℤ) ≤ r := by exact_mod_cast hk
      have nonneg := mul_nonneg (show 0 ≤ (r : ℤ) by positivity) (sub_nonneg.mpr mean)
      have gap : 0 ≤ (n : ℤ)-d := by exact sub_nonneg.mpr (by exact_mod_cast hnd)
      have rest := mul_nonneg (sub_nonneg.mpr kr) gap
      linarith only [nonneg, rest, gap]
    push_cast at hrow hcol
    zify
    linarith only [congrArg (fun x : ℤ => (n : ℤ)*x) hrow, hcol, suffices_int]
  · let l := min k (r*t/d+1)
    have hl (j : ℕ) (hj : j < l) : j*d ≤ r*t := by
      apply (Nat.le_div_iff_mul_le hd).1
      have := min_le_right k (r*t/d+1)
      dsimp only [l] at hj
      omega
    have hc : (∑ j ∈ range l, (r*t-j*d)) = ∑ j ∈ range k, (r*t-j*d) := by
      apply sum_subset (range_mono (min_le_left _ _))
      intro j hj hm
      simp only [mem_range] at hj hm
      have hdiv : r*t/d < j := by
        have high : min k (r*t/d+1) ≤ j := Nat.le_of_not_gt hm
        omega
      exact Nat.sub_eq_zero_of_le ((Nat.div_lt_iff_lt_mul hd).1 hdiv).le
    have hs : (∑ j ∈ range r, (r-j)) = ∑ j ∈ range k, (r-j) := by
      apply sum_subset (range_mono (by omega))
      intro j _ hm
      simp only [mem_range] at hm
      omega
    have hcol := linear_sum l (r*t) d hl
    have hrow := linear_sum r r 1 (fun j hj => by simpa using hj.le)
    have hrd : r ≤ r*t/d := (Nat.le_div_iff_mul_le hd).2 (Nat.mul_le_mul_left r ht)
    have hlr : r+1 ≤ l := le_min (by omega) (by omega)
    have hglobal := full_quadratic (n := (n : ℤ)) (d := (d : ℤ)) (t := (t : ℤ))
      (r : ℤ) l (by exact_mod_cast hr) (by exact_mod_cast hd)
      (by exact_mod_cast hlr) (by exact_mod_cast hjohn)
    simp only [one_mul, mul_one, Nat.cast_one] at hrow
    push_cast at hrow hcol
    rw [← hc, ← hs]
    zify
    linarith only [congrArg (fun x : ℤ => (n : ℤ)*x) hrow,hcol,hglobal]

private theorem layer (g : ℕ → ℕ) (s M : ℕ) :
    (∑ j ∈ range M, (s+1-j)*g j) = (∑ j ∈ range M, (s-j)*g j) +
      ∑ j ∈ range (min M (s+1)), g j := by
  have hsplit (j : ℕ) : (s+1-j)*g j =
      (s-j)*g j + (if j<s+1 then g j else 0) := by
    split_ifs with hj
    · rw [show s+1-j = (s-j)+1 by omega, add_mul, one_mul]
    · simp [Nat.sub_eq_zero_of_le (by omega : s+1 ≤ j), Nat.sub_eq_zero_of_le (by omega : s ≤ j)]
  simp_rw [hsplit]
  rw [sum_add_distrib, ← sum_filter]
  have hf : (range M).filter (fun j => j < s+1) = range (min M (s+1)) := by
    ext j
    simp [lt_min_iff]
  rw [hf]

/-- At every ordinary multiplicity and any pair of degree cutoffs, the prefix
inequalities add up with the scalar multiplicities in the supports. -/
private theorem above_degree {n d t : ℕ} (hd : 0 < d) (hnd : d ≤ n) (ht : d ≤ t)
    (hjohn : t*t ≤ n*d) (s v r : ℕ) :
    columnCount s v d (r*t) ≤ n * rowCount s r := by
  have weighted (k : ℕ) :
      (∑ j ∈ range (v+1), (k-j)*(r*t-j*d)) ≤ n * ∑ j ∈ range r, (k-j)*(r-j) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [layer,layer,mul_add]
      apply Nat.add_le_add ih
      by_cases hzero : r = 0
      · simp [hzero]
      have small := sum_le_sum_of_subset_of_nonneg
        (range_mono (min_le_right (v+1) (k+1))) (fun j _ _ => Nat.zero_le (r*t-j*d))
      have same : (∑ j ∈ range (min r (k+1)), (r-j)) = ∑ j ∈ range (k+1), (r-j) := by
        apply sum_subset (range_mono (min_le_right _ _))
        intro j hj hm
        simp only [mem_range] at hj hm
        omega
      rw [same]
      exact small.trans (prefix_bound hd hnd ht hjohn r (k+1) (by omega))
  simpa [columnCount,rowCount,Nat.mul_comm] using weighted (s+1)

/-- Every ordinary Hasse multiplicity and pair of monomial cutoffs has at most
as many coefficients as equations when the agreement is at or below Johnson. -/
theorem uniform_no_room {n d t : ℕ} (hd : 0 < d) (hnd : d ≤ n) (hjohn : t*t ≤ n*d)
    (s v r : ℕ) : columnCount s v d (r*t) ≤ n * rowCount s r := by
  by_cases ht : d ≤ t
  · exact above_degree hd hnd ht hjohn s v r
  calc
    columnCount s v d (r*t) ≤ columnCount s v d (r*d) :=
      sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (Nat.sub_le_sub_right
        (Nat.mul_le_mul_left r (by omega : t ≤ d)) (j*d)))
    _ ≤ _ := above_degree hd hnd le_rfl (Nat.mul_le_mul_right d hnd) s v r

/-- The first integer errors across the ordinary mixed-jet rank boundary
at the four named rates, in decreasing order of rate. -/
theorem production_crossings :
    ∀ p ∈ ([(536870911,314491700),(268435455,536870914),
      (134217727,694116763),(67108863,805306371)] : List (ℕ × ℕ)),
      (n-p.2)^2 ≤ n*p.1 ∧ n*p.1 < (n-p.2+1)^2 := by decide

/-- The half-rate dimension comparison at the named Johnson crossing. -/
theorem no_room (s v r : ℕ) : columnCount s v d (r*t) ≤ n * rowCount s r :=
  uniform_no_room (by decide) (by decide) (by decide) s v r

/-- The strict rank-surplus hypothesis for the concrete mixed Hasse spaces fails
at the crossing and every smaller agreement count on a domain of the named size. -/
theorem no_surplus {I : Type*} [Fintype I] (hn : Fintype.card I = n) (s v r u : ℕ)
    (hu : u ≤ t) :
    Fintype.card (SecondPrimeQuarticInterpolation.Monomials s v d (r*u)) ≤
      Fintype.card I * Fintype.card (HalfSuccessorJetInterpolation.JetRows s r) := by
  rw [hn,card_columns,card_rows]
  calc
    columnCount s v d (r*u) ≤ columnCount s v d (r*t) :=
      sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (Nat.sub_le_sub_right
        (Nat.mul_le_mul_left r hu) (j*d)))
    _ ≤ _ := no_room s v r

#print axioms uniform_no_room
#print axioms no_room
#print axioms no_surplus
end ArkLib.ProximityGap.Frontier.JohnsonJetRoom
