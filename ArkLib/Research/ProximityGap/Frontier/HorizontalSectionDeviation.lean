/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HodgeSectionLattice

/-! # Absolute deviations at one evaluation site

Distinct horizontal sections are orthogonal. Choosing one sign for each section
bounds the sum of absolute intersection deviations at a fixed site. A chord of
the cubic moment detects sites with both agreements and disagreements.
-/
set_option autoImplicit false
noncomputable section
open Finset
namespace ArkLib.ProximityGap.Frontier.HorizontalSectionDeviation

/-- Cauchy–Schwarz after assigning each orthogonal section the sign of its
intersection with a fixed divisor. -/
theorem absolute_intersections {V I : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (symm : ∀ u v, B u v = B v u)
    (hneg : ∀ u, B u u ≤ 0) (S : Finset I) (C : I → V) (T : V)
    (orth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → B (C i) (C j) = 0) :
    (∑ i ∈ S, |B T (C i)|)^2 ≤ (-B T T)*∑ i ∈ S, -B (C i) (C i) := by
  classical
  let s (i : I) : ℝ := if 0 ≤ B T (C i) then 1 else -1
  let U := ∑ i ∈ S, s i • C i
  have pair (v : V) : B v U = ∑ i ∈ S, s i * B v (C i) := by
    simp [U, map_sum, smul_eq_mul]
  have diag (i : I) (hi : i ∈ S) : B (C i) U = s i * B (C i) (C i) := by
    rw [pair, sum_eq_single i]
    · intro j hj hji
      rw [orth i hi j hj hji.symm, mul_zero]
    · exact fun h => (h hi).elim
  have uu : B U U = ∑ i ∈ S, B (C i) (C i) := by
    rw [pair U]
    refine sum_congr rfl fun i hi => ?_
    rw [symm U (C i), diag i hi]
    by_cases h : 0 ≤ B T (C i) <;> simp [s,h]
  have tu : B T U = ∑ i ∈ S, |B T (C i)| := by
    rw [pair]
    refine sum_congr rfl fun i _ => ?_
    by_cases h : 0 ≤ B T (C i)
    · simp [s,h,abs_of_nonneg h]
    · simp [s,h,abs_of_neg (lt_of_not_ge h)]
  have h := ProximityGap.HodgeSectionLattice.sq_le_mul_of_nonpos B symm T U
    (fun r t => hneg (r • T + t • U))
  rw [tu,uu] at h
  rw [sum_neg_distrib, neg_mul_neg]
  exact h

/-- At a site with an agreement fraction between a and 1−a, the mean absolute
deviation from a fibre degree has both a linear lower bound and a weighted
quadratic lower bound. -/
theorem middle_site (a θ g : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1/2)
    (hl : a ≤ θ) (hu : θ ≤ 1-a) (hg : 0 ≤ g) (hg' : g ≤ 1) :
    let A := θ*(1-g)+(1-θ)*g
    a ≤ A ∧ 4*a*(1-2*a)*min g (1-g) ≤ A^2 := by
  have half (x y : ℝ) (hx : a ≤ x) (hy : 0 ≤ y) (hy' : y ≤ 1/2) :
      a ≤ x*(1-y)+(1-x)*y ∧ 4*a*(1-2*a)*y ≤ (x*(1-y)+(1-x)*y)^2 := by
    have h1 : a+(1-2*a)*y ≤ x*(1-y)+(1-x)*y := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ 1-2*y by linarith)]
    have h2 : 0 ≤ (1-2*a)*y := mul_nonneg (by linarith) hy
    have h3 := pow_le_pow_left₀ (by linarith : 0 ≤ a+(1-2*a)*y) h1 2
    exact ⟨by linarith, by nlinarith only [h3, sq_nonneg (a-(1-2*a)*y)]⟩
  dsimp only
  by_cases h : g ≤ 1/2
  · rw [min_eq_left (by linarith : g ≤ 1-g)]
    exact half θ g hl hg h
  · rw [min_eq_right (by linarith : 1-g ≤ g)]
    simpa only [sub_sub_cancel, add_comm] using half (1-θ) (1-g) (by linarith) (by linarith) (by linarith)

/-- The chord through (a,a³) and (1−a,(1−a)³) lies above the cubic only at
middle sites. Its excess on each such site is at most (1−2a)²/2. -/
theorem chord_count {I : Type*} (sites : Finset I) (θ : I → ℝ) (a : ℝ)
    (hθ : ∀ i ∈ sites, 0 ≤ θ i ∧ θ i ≤ 1) (ha' : a ≤ 1/2) :
    ∑ i ∈ sites, ((1-a+a^2)*θ i-a*(1-a)-(θ i)^3) ≤
      ((sites.filter (fun i => a ≤ θ i ∧ θ i ≤ 1-a)).card:ℝ)*(1-2*a)^2/2 := by
  classical
  let mid := fun i => a ≤ θ i ∧ θ i ≤ 1-a
  let cap := (1-2*a)^2/2
  have hsum : ∑ i ∈ sites, ((1-a+a^2)*θ i-a*(1-a)-(θ i)^3) ≤
      ∑ i ∈ sites, (if mid i then cap else 0) := by
    refine sum_le_sum fun i hi => ?_
    obtain ⟨hn,ho⟩ := hθ i hi
    rw [show (1-a+a^2)*θ i-a*(1-a)-(θ i)^3 = (θ i-a)*(1-a-θ i)*(1+θ i) by ring]
    by_cases h : mid i
    · rw [ite_eq_left_iff.mpr (fun hn => (hn h).elim)]
      have h0 := mul_nonneg (sub_nonneg.mpr h.1) (sub_nonneg.mpr h.2)
      have h2 := mul_le_mul_of_nonneg_left (show 1+θ i ≤ 2 by linarith) h0
      dsimp [cap]
      nlinarith only [h2, sq_nonneg (2*θ i-1)]
    · rw [ite_eq_right_iff.mpr (fun hp => (h hp).elim)]
      have hp : (θ i-a)*(1-a-θ i) ≤ 0 := by
        by_cases hl : a ≤ θ i
        · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl)
            (by have hh : ¬ θ i ≤ 1-a := fun hz => h ⟨hl,hz⟩; linarith)
        · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      exact mul_nonpos_of_nonpos_of_nonneg hp (by linarith)
  calc
    _ ≤ _ := hsum
    _ = _ := by rw [← sum_filter]; simp [mid,cap]; ring

/-- A transverse section has an integer ramification contribution strictly
below the contact order once the normalized tame bound holds. -/
theorem tame_contact {b m c : ℕ} (hb : 0 < b) (hm : 0 < m) (h : b*c ≤ (b-1)*m) :
    c+1 ≤ m := by
  have hlt : (b-1)*m < b*m := Nat.mul_lt_mul_of_pos_right (by omega) hm
  have := Nat.lt_of_mul_lt_mul_left (h.trans_lt hlt)
  omega

/-- One singular point consumes at least one unit in the normalization genus
correction after retaining the contribution from its distinct branches. -/
theorem singular_charge {branches delta : ℕ} (hb : 0 < branches) (hd : 0 < delta)
    (h : branches-1 ≤ delta) : branches ≤ 2*delta := by omega

/-- In the absence of middle sites, the empirical first and third moments
force the retained population times the chord surplus below the triple error. -/
theorem no_middle_population {I : Type*} (sites : Finset I) (θ : I → ℝ) (a t d N X : ℝ)
    (hN : 0 ≤ N) (ha : a ≤ 1/2) (hθ : ∀ i ∈ sites, 0 ≤ θ i ∧ θ i ≤ 1)
    (none : ∀ i ∈ sites, ¬(a ≤ θ i ∧ θ i ≤ 1-a))
    (ht : t ≤ ∑ i ∈ sites, θ i) (htriple : N*(∑ i ∈ sites, (θ i)^3) ≤ N*d+X) :
    N*((1-a+a^2)*t-a*(1-a)*sites.card-d) ≤ X := by
  have hc := chord_count sites θ a hθ ha
  have hf : sites.filter (fun i => a ≤ θ i ∧ θ i ≤ 1-a) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact none i (mem_filter.mp hi).1 (mem_filter.mp hi).2
  rw [hf] at hc
  simp only [card_empty, Nat.cast_zero, zero_mul, zero_div, sum_sub_distrib,
    ← mul_sum, sum_const, nsmul_eq_mul] at hc
  have pos : 0 ≤ 1-a+a^2 := by nlinarith only [sq_nonneg (a-1/2)]
  have hfirst := mul_le_mul_of_nonneg_left ht pos
  have hchord := mul_nonneg hN (sub_nonneg.mpr hc)
  nlinarith only [htriple,hchord,mul_le_mul_of_nonneg_left hfirst hN]

namespace HalfRate

private abbrev n : ℕ := 1073741824
private abbrev d : ℕ := 536870911
private abbrev errors : ℕ := 302850000
private abbrev t : ℕ := n-errors
private abbrev cutoff : ℕ := 50230909
private abbrev firstDegree : ℕ := 2092862

private def headCount (j : ℕ) : ℕ :=
  if j < 3 then j*(errors+1) else
    let core := t-255
    let den := core+(j-1)*d
    min (j*(errors+1)) (j*n-(j-1)*((j*core^2+den-1)/den))

private def rootCeil (x den : ℕ) : ℕ :=
  let r := Nat.sqrt (x/den)
  if r^2*den = x then r else r+1

private def price (l j b : ℕ) : ℕ :=
  if b ≤ 1 then cutoff else
    let W := 9*t-1-(l-b)*d
    let m := 185-j
    if W < b*d ∨ m < b then cutoff else
      let bx := (2*b-2)*m+1-b*(b-1)
      let bz := (2*b-2)*W+1-b*(b-1)*d
      let triple := (n-d)*(m+1)
      let noMiddle := 2500*triple/(2199*t-301*n-2500*d)
      let middle := rootCeil (625*b*m*bx*bz) 126 + (50*(m+bx)+6)/7
      let variance := b*(2*m*bx*(bz-1)+m*n)
      let acrossSites := (2*457^5*variance+500^5*triple) /
        ((5*457^4*500-4*457^5)*t-500^5*d)
      max cutoff (bx + min (max noMiddle middle) acrossSites)

private def columns (r v s : ℕ) : ℕ :=
  ∑ j ∈ range (v+1), (s+1-j)*(r*t-j*d)

private def rows (r s : ℕ) : ℕ := n*∑ j ∈ range r, (r-j)*(s+1-j)

/-- The mixed Hasse spaces have the stated positive surpluses. -/
theorem interpolation_counts :
    columns 9 12 firstDegree = rows 9 firstDegree + 13592 ∧
    columns 17 24 185 = rows 17 185 + 349515892 := by decide

set_option maxRecDepth 18000 in
set_option maxHeartbeats 5000000 in
/-- Every degree allocation respects the second-field budget. Charging each
nonlinear price per ordinate slot gives the slightly rounded total below. -/
theorem numerical_certificate :
    2500*d+301*n < 2199*t ∧
    cutoff = max (errors/256+1) (firstDegree*24+12*185+1) ∧
    d+185*n/cutoff+3*(185*n/(cutoff-185)) < t ∧ n+2*d < 3*(t-255) ∧
    2025212836 ≤ 2*n ∧ ∀ l j b : Fin 13, j.val ≤ l.val →
      firstDegree+headCount j.val ≤ 2025212836 ∧
        (1 ≤ b.val → b.val ≤ l.val-j.val →
          (l.val-j.val)*price l.val j.val b.val ≤ b.val*(2025212836-firstDegree-headCount j.val)) := by
  decide +kernel

#print axioms interpolation_counts
#print axioms numerical_certificate
end HalfRate

#print axioms no_middle_population
#print axioms tame_contact
#print axioms absolute_intersections
#print axioms middle_site
#print axioms chord_count
end ArkLib.ProximityGap.Frontier.HorizontalSectionDeviation
