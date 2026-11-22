/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! # A rank obstruction for unrestricted order-two jet simplices

For the full homogeneous layer of degree `t` in the three jet coordinates,
change the value variable to its second-order Taylor residual. A monomial
with residual power `j` costs `(m−3j)₊` independent Taylor conditions at
multiplicity `m`. The other two jet variables have `t−j+1` monomials.
-/
noncomputable section
namespace ProximityGap.SecondOrderSimplexFloor
open Finset

/-- Number of monomials of total jet degree `t` in three variables. -/
def layerSize (t : ℕ) : ℝ := ((t:ℝ)+1)*(t+2)/2

/-- Rank after the triangular Taylor change on the unrestricted layer. -/
def contactRank (m : ℝ) (t : ℕ) : ℝ := ∑ j∈range (t+1),
  ((t:ℝ)+1-j) * max ((m:ℝ)-3*j) 0

private theorem partial_sum (m T : ℝ) (u : ℕ) :
    6*(∑ j∈range u, (T+1-j)*(m-3*j)) = 6*u*(T+1)*m -
      3*(3*(T+1)+m)*u*((u:ℝ)-1)+3*u*((u:ℝ)-1)*(2*u-1) := by
  induction u with
  | zero => simp
  | succ u ih => rw [sum_range_succ]; push_cast; linarith only [ih]

private theorem lower_by_cut (m : ℝ) (t u : ℕ) (hu : u≤t) (q : ℝ) (hq : q∈Set.Icc (0:ℝ) 1) :
    (∑ j∈range u, ((t:ℝ)+1-j)*((m:ℝ)-3*j))+q*(((t:ℝ)+1-u)*((m:ℝ)-3*u)) ≤
      contactRank m t := by
  let f := fun j : ℕ => ((t:ℝ)+1-j)*max ((m:ℝ)-3*j) 0
  have sf (j : ℕ) (hj : j≤t) : 0≤f j := by
    have hr : (j:ℝ)≤t := by exact_mod_cast hj
    exact mul_nonneg (by linarith) (le_max_right ..)
  have fsub (j : ℕ) (hj : j≤t) : ((t:ℝ)+1-j)*((m:ℝ)-3*j)≤f j := by
    apply mul_le_mul_of_nonneg_left (le_max_left ..)
    have hr : (j:ℝ)≤t := by exact_mod_cast hj
    linarith
  have p := sum_le_sum (fun (j : ℕ) (hj : j∈range u) => fsub j ((mem_range.mp hj).le.trans hu))
  have last : q*(((t:ℝ)+1-u)*((m:ℝ)-3*u))≤f u :=
    (mul_le_mul_of_nonneg_left (fsub _ hu) hq.1).trans (mul_le_of_le_one_left (sf _ hu) hq.2)
  have tail : ∑ j∈range (u+1), f j ≤ ∑ j∈range (t+1), f j :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
      (fun j hj _ => sf _ (by have := mem_range.mp hj; omega))
  exact (add_le_add p last).trans ((sum_range_succ ..).symm.le.trans tail)

/-- At every multiplicity and in every homogeneous layer, the full
second-order contact rank dominates the displayed affine function. -/
theorem rank_floor (m : ℝ) (t : ℕ) :
    layerSize t * (3*(m:ℝ)/4-(t:ℝ)/2) ≤ contactRank m t := by
  obtain ⟨l,rfl|rfl⟩ := Nat.even_or_odd' t
  · have c := lower_by_cut m (2*l) l (by omega) (3/4) (by constructor <;> norm_num)
    have s := partial_sum m (2*l) l
    simp only [Nat.cast_mul,Nat.cast_ofNat] at c ⊢
    unfold layerSize
    push_cast
    nlinarith only [c,s, Nat.cast_nonneg (α:=ℝ) l, sq_nonneg (l:ℝ)]
  · have c := lower_by_cut m (2*l+1) (l+1) (by omega) (1/4) (by constructor <;> norm_num)
    have s := partial_sum m (2*l+1) (l+1)
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] at c s ⊢
    unfold layerSize
    push_cast
    nlinarith only [c,s,Nat.cast_nonneg (α:=ℝ) l,sq_nonneg (l:ℝ)]

/-- For degree below `k` the smallest coordinate weight among the three jets
is `k−3`. At half rate and six agreements below three quarters, even
granting every monomial this smallest weight cannot produce a slot surplus. -/
theorem full_layer_no_surplus (n k A m t : ℕ) (hn : 12≤n) (hk : 2*k=n)
    (hA : 4*A+24≤3*n) :
    layerSize t * max ((m:ℝ)*A-((k:ℝ)-3)*t) 0 ≤ n*contactRank m t := by
  have rr : (2:ℝ)*k=n := by exact_mod_cast hk
  have ar : (4:ℝ)*A+24≤3*n := by exact_mod_cast hA
  have nr : (12:ℝ)≤n := by exact_mod_cast hn
  have sz : 0≤layerSize t := by unfold layerSize; positivity
  have rk : 0≤contactRank m t := by
    apply sum_nonneg
    intro j hj
    have jl : j≤t := by simpa [Nat.lt_succ_iff] using mem_range.mp hj
    apply mul_nonneg _ (le_max_right ..)
    have jr : (j:ℝ)≤t := by exact_mod_cast jl
    linarith
  by_cases hp : (m:ℝ)*A-((k:ℝ)-3)*t≤0
  · rw [max_eq_right hp,mul_zero]; positivity
  · rw [max_eq_left (by linarith)]
    have tbound : (t:ℝ)≤2*m := by
      by_contra! h
      have kpos : 0≤(k:ℝ)-3 := by linarith
      nlinarith only [hp, mul_le_mul_of_nonneg_left ar (Nat.cast_nonneg m),
        mul_le_mul_of_nonneg_left h.le kpos, congrArg (fun z : ℝ => z*m) rr]
    have per : (m:ℝ)*A-((k:ℝ)-3)*t ≤ n*(3*m/4-(t:ℝ)/2) := by
      nlinarith only [mul_le_mul_of_nonneg_left ar (Nat.cast_nonneg m),tbound,
        congrArg (fun z : ℝ => z*t) rr]
    calc _ ≤ layerSize t * (n*(3*m/4-(t:ℝ)/2)) := mul_le_mul_of_nonneg_left per sz
         _ = n*(layerSize t*(3*m/4-(t:ℝ)/2)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (rank_floor m t) (Nat.cast_nonneg n)

/-- Stars-and-bars count in one unrestricted degree layer of `d+1` jets. -/
def monomials (d t : ℕ) : ℝ := ((t+d).choose d : ℕ)

private theorem monomials_two (t : ℕ) : monomials 2 t=layerSize t := by
  have h := Nat.choose_succ_right_eq (t+2) 1
  have hc : (t+2).choose 2 * 2=(t+2)*(t+1) := by simpa using h
  have hr : monomials 2 t*2=((t:ℝ)+2)*(t+1) := by unfold monomials; exact_mod_cast hc
  unfold layerSize
  linarith

private theorem monomials_sum (d t : ℕ) :
    ∑ j∈range (t+1), monomials d j = monomials (d+1) t := by
  unfold monomials
  rw [←Nat.cast_sum,Nat.sum_range_add_choose]
  simp only [Nat.add_assoc]

private theorem monomials_moment (d t : ℕ) :
    (∑ j∈range (t+1), monomials d j*j)*(d+2) = monomials (d+1) t*t*(d+1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have step : monomials (d+1) (t+1)=monomials (d+1) t+monomials d (t+1) := by
      rw [←monomials_sum,←monomials_sum,sum_range_succ]
    have shift : monomials (d+1) t*((d:ℝ)+1)=monomials d (t+1)*((t:ℝ)+1) := by
      have h := Nat.choose_succ_right_eq (t+1+d) d
      dsimp [monomials]
      exact_mod_cast (by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h :
        (t+(d+1)).choose (d+1)*(d+1)=(t+1+d).choose d*(t+1))
    rw [sum_range_succ,step]
    push_cast
    linarith only [ih,shift]

/-- Hold `e` additional jet exponents free. After fixing their degrees, the
three initial jets have the remaining total degree. The Taylor residual has
contact `b`; the actual order is `e+2`, hence actual contact `e+3`. -/
def higherRank (b m : ℝ) : ℕ → ℕ → ℝ
  | 0,t => ∑ j∈range (t+1), ((t:ℝ)+1-j)*max (m-b*j) 0
  | e+1,t => ∑ j∈range (t+1), higherRank b m e j

/-- Conditioning on the total degree of the first three coordinates extends
the exact layer obstruction to any number of derivatives. -/
theorem higher_rank_floor (b m : ℝ) (hb : 0<b) (e t : ℕ) :
    monomials (e+2) t*(3*m/4-b*t/(2*(e+3))) ≤ higherRank b m e t := by
  induction e generalizing t with
  | zero =>
    have scaled : (b/3)*contactRank (3*m/b) t = higherRank b m 0 t := by
      unfold contactRank higherRank
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      have eq : (b/3)*(3*m/b-3*j) = m-b*j := by field_simp
      rw [←eq,←mul_zero (b/3),←mul_max_of_nonneg _ _ (by positivity : 0≤b/3)]
      ring
    rw [←scaled]
    have floor := mul_le_mul_of_nonneg_left (rank_floor (3*m/b) t) (by positivity : (0:ℝ)≤b/3)
    convert floor using 1
    simp only [Nat.cast_zero, zero_add,monomials_two]
    field_simp
  | succ e ih =>
    have dpos : (0:ℝ)<2*((e:ℝ)+3) := by positivity
    have dpos' : (0:ℝ)<2*((e:ℝ)+4) := by positivity
    have sumc := monomials_sum (e+2) t
    have mom := monomials_moment (e+2) t
    have w : ∑ j∈range (t+1), monomials (e+2) j*(3*m/4-b*j/(2*(e+3))) =
        (∑ j∈range (t+1), monomials (e+2) j)*(3*m/4) -
        (∑ j∈range (t+1), monomials (e+2) j*j)*(b/(2*(e+3))) := by
      rw [sum_mul,sum_mul,←sum_sub_distrib]
      apply sum_congr rfl
      intro j _
      ring
    refine le_trans ?_ (sum_le_sum (fun j _ => ih j))
    rw [w,sumc]
    push_cast at mom ⊢
    let C := monomials (e+3) t
    let S := ∑ j∈range (t+1), monomials (e+2) j*j
    change S*((e:ℝ)+2+2) = C*t*((e:ℝ)+2+1) at mom
    have rat : S/((e:ℝ)+3) = C*t/((e:ℝ)+4) := by
      apply (div_eq_div_iff (by positivity) (by positivity)).mpr
      linarith only [mom]
    change C*(3*m/4-b*t/(2*((e:ℝ)+1+3))) ≤ C*(3*m/4)-S*(b/(2*((e:ℝ)+3)))
    rw [show (e:ℝ)+1+3=e+4 by ring]
    apply le_of_eq
    calc _ = C*(3*m/4)-(b/2)*(C*t/((e:ℝ)+4)) := by field_simp
         _ = _ := by rw [←rat]; field_simp

private theorem higherRank_nonneg (b m : ℝ) (e t : ℕ) : 0≤higherRank b m e t := by
  induction e generalizing t with
  | zero =>
    apply sum_nonneg
    intro j hj
    apply mul_nonneg _ (le_max_right ..)
    have h : (j:ℝ)≤t := by exact_mod_cast (show j≤t by simpa [Nat.lt_succ_iff] using mem_range.mp hj)
    linarith
  | succ e ih => exact sum_nonneg (fun j _ => ih j)

/-- At half rate no nonnegative weighting of whole homogeneous jet layers,
including challenge-height weights, produces a slots surplus in this range.
The order is `e+2` and the minimum coordinate weight is `k−(e+3)`. -/
theorem all_orders_no_surplus (n k A m e T : ℕ) (w : ℕ→ℝ) (hw : ∀ t,0≤w t)
    (hn : 4*(e+3)≤n) (hk : 2*k=n) (hA : 4*A+8*(e+3)≤3*n) :
    (∑ t∈range T, w t*monomials (e+2) t*max ((m:ℝ)*A-((k:ℝ)-(e+3))*t) 0) ≤
      n*(∑ t∈range T, w t*higherRank ((e:ℝ)+3) m e t) := by
  let b : ℝ := e+3
  have bp : 0<b := by dsimp [b]; positivity
  have rr : (2:ℝ)*k=n := by exact_mod_cast hk
  have ar : (4:ℝ)*A+8*b≤3*n := by dsimp only [b]; exact_mod_cast hA
  have nr : 4*b≤n := by dsimp only [b]; exact_mod_cast hn
  rw [mul_sum]
  apply sum_le_sum
  intro t _
  have sz : 0≤monomials (e+2) t := by unfold monomials; positivity
  have rk := higherRank_nonneg b m e t
  change w t*monomials (e+2) t*max ((m:ℝ)*A-((k:ℝ)-b)*t) 0 ≤ n*(w t*higherRank b m e t)
  by_cases hp : (m:ℝ)*A-((k:ℝ)-b)*t≤0
  · rw [max_eq_right hp,mul_zero]; positivity [hw t]
  · rw [max_eq_left (by linarith)]
    have tbound : (t:ℝ)≤2*m := by
      by_contra! h
      have kpos : 0≤(k:ℝ)-b := by linarith
      nlinarith only [hp, mul_le_mul_of_nonneg_left ar (Nat.cast_nonneg m),
        mul_le_mul_of_nonneg_left h.le kpos, congrArg (fun z : ℝ => z*m) rr]
    have per : (m:ℝ)*A-((k:ℝ)-b)*t ≤ n*(3*m/4-(t:ℝ)/2) := by
      nlinarith only [mul_le_mul_of_nonneg_left ar (Nat.cast_nonneg m),mul_le_mul_of_nonneg_left tbound bp.le,
        congrArg (fun z : ℝ => z*t) rr]
    have bound := higher_rank_floor b m bp e t
    change monomials (e+2) t*(3*(m:ℝ)/4-b*t/(2*b))≤_ at bound
    rw [show b*t/(2*b)=(t:ℝ)/2 by field_simp] at bound
    have p := mul_le_mul_of_nonneg_left per (mul_nonneg (hw t) sz)
    have q := mul_le_mul_of_nonneg_left bound (mul_nonneg (Nat.cast_nonneg n) (hw t))
    linarith only [p,q]

/-- If the coordinate-degree window clips below multiplicity in one monomial,
the column widths in the same layer vary by at most `d*t`. The pure highest
derivative supplies `min m L` independent Taylor orders at the maximal width
`L`. This inequality covers such a clipped layer when its dimension is small
relative to the number of evaluation sites. -/
theorem clipped_layer_no_surplus (N n m L d t : ℕ) (small : L≤m+d*t)
    (ht : t≤2*m) (hN : N*(1+2*d)≤n) : N*L≤n*min m L := by
  rcases le_total m L with ml|lm
  · rw [min_eq_left ml]
    calc N*L ≤ N*(m+d*(2*m)) := Nat.mul_le_mul_left _ (small.trans
           (Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _))
         _ = (N*(1+2*d))*m := by ring
         _ ≤ _ := Nat.mul_le_mul_right _ hN
  · rw [min_eq_right lm]
    exact Nat.mul_le_mul_right _ ((Nat.le_mul_of_pos_right N (by omega : 0<1+2*d)).trans hN)

end ProximityGap.SecondOrderSimplexFloor

#print axioms ProximityGap.SecondOrderSimplexFloor.rank_floor
#print axioms ProximityGap.SecondOrderSimplexFloor.full_layer_no_surplus

#print axioms ProximityGap.SecondOrderSimplexFloor.higher_rank_floor
#print axioms ProximityGap.SecondOrderSimplexFloor.all_orders_no_surplus
#print axioms ProximityGap.SecondOrderSimplexFloor.clipped_layer_no_surplus
