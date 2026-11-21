/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HodgeSectionVariance

/-! # Variance weighted by the smaller of a fibre divisor and its complement

The intersection and ramification estimates on the normalization are given in
`docs/research/proximity-gap/complement-hodge-windows.md`. This file verifies the
moment conversion, the six interpolation surpluses, and every integer allocation.
-/
set_option autoImplicit false
open Polynomial Finset
namespace ArkLib.ProximityGap.Frontier.ComplementHodgeWindows

private theorem tangent (θ z : ℝ) (hθ : 0≤θ) (hz : 0≤z) : 3*z^2*θ-2*z^3 ≤ θ^3 := by
  nlinarith only [mul_nonneg (sq_nonneg (θ-z)) (by linarith : 0≤θ+2*z)]

private theorem half_variance (x g : ℝ) (hx : 0≤x) (hg : 0<g) (hhalf : g≤1/2) :
    min (1/2) (2*x) ≤ (x*(1-2*g)+g^2)/g := by
  apply (le_div_iff₀ hg).mpr
  by_cases h : x ≤ 1/4
  · apply (mul_le_mul_of_nonneg_right (min_le_right _ _) hg.le).trans
    nlinarith only [mul_nonneg hx (sq_nonneg (2*g-1)),
      mul_nonneg (show 0≤1-4*x by linarith) (sq_nonneg g)]
  · apply (mul_le_mul_of_nonneg_right (min_le_left _ _) hg.le).trans
    nlinarith only [sq_nonneg (g-1/2),
      mul_nonneg (show 0≤x-1/4 by linarith) (show 0≤1-2*g by linarith)]

/-- The site cost includes both endpoint fibres, where every discrepancy is exceptional. -/
noncomputable def fibreCost (θ g b : ℝ) : ℝ :=
  if g=0 then b*θ else if g=1 then b*(1-θ) else (θ*(1-2*g)+g^2)/min g (1-g)

/-- A universal cubic lower bound using the complementary fibre weight. The
endpoint `g=0` has variance cost `b*θ` and `g=1` has cost `b*(1−θ)`. -/
theorem complement_moment (θ g b : ℝ) (hθ : 0≤θ) (hθ' : θ≤1) (hb : 2≤b)
    (hg : 0≤g) (hg' : g≤1) :
    (39/40)*θ-θ^3 ≤ (3/4)*
      (if g=0 then b*θ else if g=1 then b*(1-θ) else (θ*(1-2*g)+g^2)/min g (1-g)) := by
  have h₀ : (39/40)*θ-θ^3 ≤ (3/4)*(2*θ) := by nlinarith [pow_nonneg hθ 3]
  have h₁ : (39/40)*θ-θ^3 ≤ (3/4)*(2*(1-θ)) := by
    nlinarith only [tangent θ (109/120) hθ (by norm_num),hθ]
  have hmid : (39/40)*θ-θ^3 ≤ (3/4)*(1/2) := by
    nlinarith only [tangent θ (4/7) hθ (by norm_num),hθ]
  by_cases hz : g=0
  · rw [if_pos hz]
    exact h₀.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hθ) (by norm_num))
  rw [if_neg hz]
  by_cases ho : g=1
  · rw [if_pos ho]
    exact h₁.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (by linarith)) (by norm_num))
  rw [if_neg ho]
  by_cases h : g≤1/2
  · rw [min_eq_left (by linarith)]
    have hc := half_variance θ g hθ (lt_of_le_of_ne hg (Ne.symm hz)) h
    exact (by rcases min_cases (1/2 : ℝ) (2*θ) with ⟨he,_⟩ | ⟨he,_⟩ <;> rw [he] at hc <;> linarith)
  · rw [min_eq_right (by linarith)]
    have hc := half_variance (1-θ) (1-g) (by linarith) (by exact sub_pos.mpr (lt_of_le_of_ne hg' ho)) (by linarith)
    rw [show (1-θ)*(1-2*(1-g))+(1-g)^2 = θ*(1-2*g)+g^2 by ring] at hc
    exact (by rcases min_cases (1/2 : ℝ) (2*(1-θ)) with ⟨he,_⟩ | ⟨he,_⟩ <;> rw [he] at hc <;> linarith)

/-- Unit moment coefficient throughout the strict `t>d` range. The penalty improves
to `77/100` for every nonlinear component of value degree at least three. -/
theorem capacity_moment (θ g b : ℝ) (hθ : 0≤θ) (hθ' : θ≤1) (hb : 2≤b)
    (hg : 0≤g) (hg' : g≤1) :
    θ-θ^3 ≤ (if 3≤b then 77/100 else 1)*fibreCost θ g b := by
  have hsum : θ-θ^3 ≤ 2*(1-θ) := by
    nlinarith only [mul_nonneg (sq_nonneg (1-θ)) (show 0≤θ+2 by linarith)]
  have hnon : 0≤θ-θ^3 := by nlinarith only [mul_nonneg hθ (mul_nonneg (sub_nonneg.mpr hθ') (show 0≤1+θ by linarith))]
  have hmid : θ-θ^3 ≤ (77/100)*(1/2) := by
    nlinarith only [tangent θ (57736/100000) hθ (by norm_num),hθ]
  by_cases hz : g=0
  · simp only [fibreCost,if_pos hz]
    have hh : θ-θ^3 ≤ (77/100)*(b*θ) := by nlinarith [mul_le_mul_of_nonneg_right hb hθ,pow_nonneg hθ 3]
    split_ifs <;> nlinarith only [hh,hnon]
  by_cases ho : g=1
  · simp only [fibreCost,if_neg hz,if_pos ho]
    split_ifs with h
    · nlinarith only [mul_le_mul_of_nonneg_right h (sub_nonneg.mpr hθ'),hsum,sub_nonneg.mpr hθ']
    · nlinarith only [mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hθ'),hsum]
  simp only [fibreCost,if_neg hz,if_neg ho]
  let V := (θ*(1-2*g)+g^2)/min g (1-g)
  change θ-θ^3 ≤ _*V
  have hsmall : θ-θ^3 ≤ (77/100)*V := by
    by_cases hg₂ : g≤1/2
    · dsimp [V]; rw [min_eq_left (by linarith)]
      have h := half_variance θ g hθ (lt_of_le_of_ne hg (Ne.symm hz)) hg₂
      rcases min_cases (1/2 : ℝ) (2*θ) with ⟨he,_⟩ | ⟨he,_⟩ <;> rw [he] at h
      · linarith
      · nlinarith only [h,hθ,pow_nonneg hθ 3]
    · let x := 1-θ
      let f := 1-g
      have hx : 0≤x := sub_nonneg.mpr hθ'
      have hf : 0<f := sub_pos.mpr (lt_of_le_of_ne hg' ho)
      have hv : V=(x*(1-2*f)+f^2)/f := by
        dsimp [V,x,f]; rw [min_eq_right (by linarith)]; congr 1; ring
      rw [hv]
      by_cases hx' : 1/4≤x
      · have h := half_variance x f hx hf (by dsimp [f]; linarith)
        rw [min_eq_left (by linarith)] at h; linarith
      · let u := Real.sqrt x
        have hu : 0≤u := Real.sqrt_nonneg _
        have hux : u^2=x := Real.sq_sqrt hx
        have hu' : u≤1/2 := by nlinarith
        have hθu : θ=1-u^2 := by dsimp [x] at hux; linarith
        have hcost : 2*(u-u^2) ≤ (x*(1-2*f)+f^2)/f := by
          apply (le_div_iff₀ hf).mpr; rw [← hux]; nlinarith only [sq_nonneg (f-u)]
        have hprod : u*(1+u)*(2-u^2) ≤ (1/2)*(1+1/2)*2 := by gcongr <;> nlinarith
        have hmul := mul_le_mul_of_nonneg_right hprod (mul_nonneg hu (show 0≤1-u by linarith))
        rw [hθu]
        nlinarith only [hmul,hcost,mul_nonneg hu (show 0≤1-u by linarith)]
  split_ifs <;> linarith

/-- The rational reciprocal at a pole of the value coordinate divides the
constant coefficient of its reversed defining equation in the local ring. -/
theorem inverse_dvd_constant {R : Type*} [CommRing R] (P : R[X]) (a : R) (ha : P.eval a=0) :
    a ∣ P.coeff 0 := by simpa [ha,coeff_zero_eq_eval_zero] using sub_dvd_eval_sub 0 a P

/-- Sum the cubic site inequality, insert the geometric variance and determinant
bounds, and recover the integer section cap including discarded branches. -/
theorem section_cap {I : Type*} (sites : Finset I) (θ g : I → ℝ) (b : ℕ) (hb : 2≤b)
    (M N B D X t d : ℕ) (hMN : M ≤ B+N) (hden : 40*d<39*t)
    (hθ : ∀ i ∈ sites, 0≤θ i ∧ θ i≤1) (hg : ∀ i ∈ sites, 0≤g i ∧ g i≤1)
    (ht : (t:ℝ) ≤ ∑ i ∈ sites, θ i)
    (htriple : (N:ℝ)*(∑ i ∈ sites, (θ i)^3) ≤ N*d+X)
    (hvariance : (N:ℝ)*(∑ i ∈ sites, (if g i=0 then (b:ℝ)*θ i else if g i=1 then b*(1-θ i)
      else (θ i*(1-2*g i)+(g i)^2)/min (g i) (1-g i))) ≤ D) :
    M ≤ B+(30*D+40*X)/(39*t-40*d) := by
  have hsum := sum_le_sum (s:=sites) (fun i hi => complement_moment (θ i) (g i) b
    (hθ i hi).1 (hθ i hi).2 (by exact_mod_cast hb) (hg i hi).1 (hg i hi).2)
  rw [sum_sub_distrib,←mul_sum,←mul_sum] at hsum
  have h₁ := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N : (0:ℝ)≤N)
  have h₂ := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N : (0:ℝ)≤N)
  have hc : (N:ℝ)*(39*t-40*d) ≤ 30*D+40*X := by nlinarith only [h₁,h₂,htriple,hvariance]
  have hnat : N*(39*t-40*d) ≤ 30*D+40*X := by
    exact_mod_cast (show (N:ℝ)*(↑(39*t-40*d : ℕ):ℝ) ≤ 30*D+40*X by
      simpa [Nat.cast_sub hden.le] using hc)
  exact hMN.trans (Nat.add_le_add_left ((Nat.le_div_iff_mul_le (by omega)).mpr hnat) _)

/-- General degree-dependent component cap. No restriction involving the Johnson
radius enters the conversion of geometric variance and agreement to a label count. -/
theorem capacity_section_cap {I : Type*} (sites : Finset I) (θ g : I → ℝ) (b : ℕ) (hb : 2≤b)
    (M N B D X t d : ℕ) (hMN : M ≤ B+N) (hdt : d<t)
    (hθ : ∀ i ∈ sites, 0≤θ i ∧ θ i≤1) (hg : ∀ i ∈ sites, 0≤g i ∧ g i≤1)
    (ht : (t:ℝ) ≤ ∑ i ∈ sites, θ i)
    (htriple : (N:ℝ)*(∑ i ∈ sites, (θ i)^3) ≤ N*d+X)
    (hvariance : (N:ℝ)*(∑ i ∈ sites, fibreCost (θ i) (g i) b) ≤ D) :
    M ≤ B+((if 3≤b then 77 else 100)*D+100*X)/(100*(t-d)) := by
  have hsum := sum_le_sum (s:=sites) (fun i hi => capacity_moment (θ i) (g i) b
    (hθ i hi).1 (hθ i hi).2 (by exact_mod_cast hb) (hg i hi).1 (hg i hi).2)
  rw [sum_sub_distrib,←mul_sum] at hsum
  have h₁ := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N : (0:ℝ)≤N)
  have h₂ := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N : (0:ℝ)≤N)
  have hnum : (N:ℝ)*(100*(t-d)) ≤ (↑(if 3≤b then 77 else 100 : ℕ):ℝ)*D+100*X := by
    by_cases h : 3≤b
    · have hr : (3:ℝ)≤b := by exact_mod_cast h
      simp only [if_pos h,if_pos hr,Nat.cast_ofNat] at *
      nlinarith only [h₁,h₂,htriple,hvariance]
    · have hr : ¬(3:ℝ)≤b := by exact_mod_cast h
      simp only [if_neg h,if_neg hr,Nat.cast_ofNat,one_mul] at *
      nlinarith only [h₁,h₂,htriple,hvariance]
  have hnat : N*(100*(t-d)) ≤ (if 3≤b then 77 else 100)*D+100*X := by
    exact_mod_cast (show (N:ℝ)*(100*(↑(t-d : ℕ):ℝ)) ≤ (↑(if 3≤b then 77 else 100 : ℕ):ℝ)*D+100*X by
      simpa [Nat.cast_sub hdt.le] using hnum)
  exact hMN.trans (Nat.add_le_add_left ((Nat.le_div_iff_mul_le (by omega)).mpr hnat) _)

structure Window where
  rate : ℕ
  errors : ℕ
  r : ℕ
  v : ℕ
  s : ℕ
  r' : ℕ
  v' : ℕ
  m : ℕ
  group : ℕ
  limit : ℕ

def window (i : Fin 3) : Window :=
  if i=0 then ⟨2,299700000,7,10,3647,13,18,118,3,1630997447⟩
  else if i=1 then ⟨4,516200000,6,12,28435,12,24,129,3,2030538477⟩
  else ⟨8,665900000,4,12,21302,8,24,87,4,2107604375⟩

abbrev n : ℕ := 1073741824

def cutoff (w : Window) : ℕ := max (w.errors/256+1) (w.s*w.v'+w.v*w.m+1)

def heads (w : Window) (j : ℕ) : ℕ :=
  if j<w.group then j*(w.errors+1) else
    let c := n-w.errors-255
    let z := c+(j-1)*(n/w.rate-1)
    min (j*(w.errors+1)) (j*n-(j-1)*((j*c*c+z-1)/z))

def price (w : Window) (l j b : ℕ) : ℕ :=
  if b≤1 then cutoff w else
    let d := n/w.rate-1
    let t := n-w.errors
    let W := w.r*t-1-(l-b)*d
    let m := w.m-j
    if W<b*d ∨ m<b then cutoff w else
      let bx := (2*b-2)*m+1-b*(b-1)
      let bz := (2*b-2)*W+1-b*(b-1)*d
      let numerator := 30*b*(4*m*bx*bz+m*n+bx*bz)+40*(n-d)*(m+1)
      max (cutoff w) (bx+numerator/(39*t-40*d))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
/-- The complete finite price test, including the allowance for scalar-only
factors, the head test, the moment denominator and the final field budget. -/
theorem numerical_certificate : ∀ i : Fin 3,
    let w := window i
    let t := n-w.errors
    let d := n/w.rate-1
    40*d < 39*t ∧ d+w.m*n/cutoff w+3*(w.m*n/(cutoff w-w.m)) < t ∧
    (if w.group=3 then n+2*d < 3*(t-255) else n+4*d < 4*(t-255)) ∧ w.limit ≤ 2*n ∧
    ∀ l j b : Fin 13, l.val≤w.v → j.val≤l.val → w.s+heads w j.val ≤ w.limit ∧
    (1≤b.val → b.val≤l.val-j.val →
      (l.val-j.val)*price w l.val j.val b.val ≤ b.val*(w.limit-w.s-heads w j.val)) := by decide

open HalfSuccessorJetInterpolation SecondPrimeQuarticInterpolation

/-- Positive dimension at both interpolation shapes in each of the three new windows. -/
theorem interpolation_surplus (i : Fin 3) (second : Bool) :
    let w := window i
    let r := if second then w.r' else w.r
    let v := if second then w.v' else w.v
    let s := if second then w.m else w.s
    n*Fintype.card (JetRows s r) < Fintype.card (Monomials s v (n/w.rate-1) (r*(n-w.errors))) := by
  fin_cases i <;> cases second <;>
    simp only [JetRows,Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin] <;>
    norm_num [window,n,Fin.sum_univ_succ] <;> decide

/-- At a smooth branch point, a tame chart of index `e` and a degree-one section
with contact `e*k` give local different contribution `(e−1)*k`. -/
theorem smooth_contact (e k : ℕ) (he : 0<e) (hk : 0<k) : (e-1)*k ≤ e*k-1 := by
  have ha : e-1+1=e := by omega
  have h := congrArg (fun j : ℕ => j*k) ha
  simp only [Nat.add_mul,one_mul] at h
  omega

/-- The normalization genus term pays both the lost distinct branches and one
additional unit at each singular base point. -/
theorem singular_cost {I : Type*} (S : Finset I) (branches delta : I → ℕ)
    (hd : ∀ i ∈ S, 1≤delta i) (hb : ∀ i ∈ S, branches i-1≤delta i) :
    (∑ i ∈ S, (branches i-1))+S.card ≤ 2*∑ i ∈ S, delta i := by
  rw [Finset.mul_sum]
  have h := sum_le_sum (s:=S) (fun i hi => show branches i-1+1 ≤ 2*delta i by
    have := hd i hi; have := hb i hi; omega)
  simpa [sum_add_distrib] using h

def tameWindow (i : Fin 3) : Window :=
  if i=0 then ⟨2,301600000,8,11,1224,15,21,152,3,2075412585⟩
  else if i=1 then ⟨4,517600000,7,13,7818,13,26,147,3,2131667446⟩
  else ⟨8,667400000,5,13,431,8,24,96,4,2146821649⟩

def tamePrice (w : Window) (l j b : ℕ) : ℕ :=
  if b≤1 then cutoff w else
    let d := n/w.rate-1
    let t := n-w.errors
    let W := w.r*t-1-(l-b)*d
    let m := w.m-j
    if W<b*d ∨ m<b then cutoff w else
      let bx := (2*b-2)*m+1-b*(b-1)
      let bz := (2*b-2)*W+1-b*(b-1)*d
      let p := if 3≤b then 77 else 100
      let numerator := p*b*(2*m*bx*bz+m*n+bx*bz)+100*(n-d)*(m+1)
      max (cutoff w) (bx+numerator/(100*(t-d)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
/-- The three improved named thresholds from tame smooth-branch contact and the
unit-coefficient variance bound. -/
theorem tame_numerical_certificate : ∀ i : Fin 3,
    let w := tameWindow i
    let t := n-w.errors
    let d := n/w.rate-1
    d < t ∧ d+w.m*n/cutoff w+3*(w.m*n/(cutoff w-w.m)) < t ∧
    (if w.group=3 then n+2*d < 3*(t-255) else n+4*d < 4*(t-255)) ∧ w.limit ≤ 2*n ∧
    ∀ l j b : Fin 14, l.val≤w.v → j.val≤l.val → w.s+heads w j.val ≤ w.limit ∧
    (1≤b.val → b.val≤l.val-j.val →
      (l.val-j.val)*tamePrice w l.val j.val b.val ≤ b.val*(w.limit-w.s-heads w j.val)) := by decide

/-- Both interpolation kernels in each of the tame ramification windows have positive dimension. -/
theorem tame_interpolation_surplus (i : Fin 3) (second : Bool) :
    let w := tameWindow i
    let r := if second then w.r' else w.r
    let v := if second then w.v' else w.v
    let s := if second then w.m else w.s
    n*Fintype.card (JetRows s r) < Fintype.card (Monomials s v (n/w.rate-1) (r*(n-w.errors))) := by
  fin_cases i <;> cases second <;>
    simp only [JetRows,Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin] <;>
    norm_num [tameWindow,n,Fin.sum_univ_succ] <;> decide

#print axioms smooth_contact
#print axioms singular_cost
#print axioms tame_numerical_certificate
#print axioms tame_interpolation_surplus
#print axioms capacity_section_cap
#print axioms capacity_moment
#print axioms section_cap
#print axioms complement_moment
#print axioms inverse_dvd_constant
#print axioms numerical_certificate
#print axioms interpolation_surplus
end ArkLib.ProximityGap.Frontier.ComplementHodgeWindows
