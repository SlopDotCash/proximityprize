/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation

/-! # Production allocations using projective tangent polars

The underlying Gauss map and normalization arguments are given in
`docs/research/proximity-gap/tangent-polar-windows.md`. This module checks the
interpolation and the assignment of every possible factor degree. -/
set_option autoImplicit false
open Finset Polynomial
namespace ArkLib.ProximityGap.Frontier.TangentPolarWindows
private abbrev n : ℕ := 1073741824

private structure Window where
  rate : ℕ
  errors : ℕ
  order : ℕ
  degree : ℕ
  first : ℕ
  order₂ : ℕ
  degree₂ : ℕ
  second : ℕ
  polar : ℕ
  slope : ℕ
  bound : ℕ

private def window (i : Fin 3) : Window :=
  ![⟨2,309800000,23,32,85457,46,65,1093,8,7,2110558412⟩,
    ⟨4,529350000,18,35,27103,34,68,896,7,5,2141997998⟩,
    ⟨8,671088639,6,16,335,9,26,128,4,2,2128274755⟩] i

private def cutoff (w : Window) : ℕ :=
  max (w.first*w.degree₂+w.degree*w.second+1) (if w.rate=8 then 81920 else w.errors/256+1)

private def headMass (w : Window) (j : ℕ) : ℕ :=
  let d := n/w.rate-1
  let t := n-w.errors
  let c := t-w.errors/cutoff w
  let den := c+(j-1)*d
  let un := (j*c*c+den-1)/den
  let col := min (j*(w.errors+1)) (j*n-(j-1)*un)
  if w.rate ≠ 8 then (if j < 3 then j*(w.errors+1) else col)
  else if j ≤ 3 then j*(w.errors+1)
  else if j = 4 then max col 2125114027
  else if j=5 then max col 2058021547 else col

private def component (b m W t d s a : ℕ) (polar : Bool) : ℕ :=
  let ax := (2*b-2)*W-b*(b-1)*d
  let gz := (2*b-2)*m-b*(b-1)
  let height := 2*ax*gz+2*W*m
  let loss := (gz+m)*n
  let ordinary := (2*t*loss+n*(2*height+m*n))/(t*t-n*d)
  let h := (s+2).choose 2
  let gap := a*h*t-(a+2).choose 3*n-(s*(s+1)*(s+2)/3)*d
  let extra := s*m*(m-1)+h*(a*loss+s*height)/gap
  gz+2*b*m+(if polar then min ordinary extra else ordinary)

private def price (w : Window) (f j b : ℕ) : ℕ :=
  let d := n/w.rate-1
  let t := n-w.errors
  let W := w.order*t-1-(f-b)*d
  let m := w.second-j
  let z := w.polar*(w.polar-1)
  if b≤1 ∨ W<b*d ∨ m<b then cutoff w else
    max (cutoff w) (if w.polar=0 ∨ m≤z then component b m W t d w.polar w.slope false
      else max (component b m W t d w.polar w.slope true)
        (if b≤z then component b z W t d w.polar w.slope false else 0))

/-- Positive denominators for the ordinary tangent count and the projective
minor, and the identity-site and three-head tests for the chosen surfaces. -/
theorem hypotheses (i : Fin 3) :
    let w := window i
    let t := n-w.errors
    let d := n/w.rate-1
    let s := w.polar
    let a := w.slope
    let L := cutoff w
    n*d < t*t ∧ d < t-w.second*n/L-3*(w.second*n/(L-w.second)) ∧
      (w.rate≠8 → n+2*d < 3*(t-w.errors/L)) ∧
      (0<s → (a+2).choose 3*n+s*(s+1)*(s+2)/3*d < a*(s+2).choose 2*t) := by
  revert i
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 18000000 in
private theorem finite_price : ∀ i : Fin 3, ∀ f : Fin ((window i).degree+1),
    ∀ j : Fin (f.val+1), ∀ b : Fin (f.val-j.val+1),
    let w := window i
    let base := headMass w j.val+w.first
    base ≤ w.bound ∧ (0 < b.val →
      (f.val-j.val)*price w f.val j.val b.val ≤ b.val*(w.bound-base+1)-1) := by
  decide +kernel

/-- Every partition into positive factor degrees fits the stated integer cap.
The local price majorants allow a fractional average before the final flooring. -/
theorem allocations {ι : Type*} (S : Finset ι) (value cost : ι → ℕ)
    (i : Fin 3) (f : Fin ((window i).degree+1)) (j : Fin (f.val+1))
    (hv : ∀ a ∈ S, 0 < value a) (he : ∑ a ∈ S, value a = f.val-j.val)
    (hc : ∀ a ∈ S, cost a ≤ price (window i) f.val j.val (value a)) :
    headMass (window i) j.val+(window i).first+∑ a ∈ S, cost a ≤ (window i).bound := by
  classical
  let base := headMass (window i) j.val+(window i).first
  have hb := (finite_price i f j 0).1
  change base ≤ (window i).bound at hb
  by_cases empty : S = ∅
  · simpa [empty] using hb
  obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr empty
  let r := f.val-j.val
  have nonzero : 0 < r := (hv x hx).trans_le ((single_le_sum (fun a _ => Nat.zero_le (value a)) hx).trans_eq he)
  let B := (window i).bound-base+1
  have pos : 0 < B := by dsimp [B]; omega
  have hh (a : ι) (ha : a ∈ S) : r * cost a < value a * B := by
    have hv' := (single_le_sum (fun a _ => Nat.zero_le (value a)) ha).trans_eq he
    have hprice := (finite_price i f j ⟨value a,by omega⟩).2 (hv a ha)
    have hpos := Nat.mul_pos (hv a ha) pos
    have hcost := Nat.mul_le_mul_left r (hc a ha)
    change r*(price (window i) f.val j.val (value a)) ≤ value a*B-1 at hprice
    omega
  have hsum := sum_lt_sum_of_nonempty (nonempty_iff_ne_empty.mpr empty) hh
  rw [← mul_sum,← sum_mul,he] at hsum
  have hlt : (∑ a ∈ S, cost a) < B := Nat.lt_of_mul_lt_mul_left hsum
  change base + _ ≤ _
  dsimp [B] at hlt
  omega

/-- At 2,137,701 error steps past the first integer above Johnson, the conic
minor (five columns) and the full quadratic minor both have positive gap. -/
theorem beyond_johnson :
    let t := 45*n/128
    let d := n/8-1
    t^2 < n*d ∧ n+6*d < 5*t ∧ n+8*d < 6*t ∧ n-t=696254464 ∧
    (let W := 2*t-1
     let A := 2*W-2*d
     let G := 2
     G+8+4+5*((G+2)*n+2*(2*A*G+4*W))/(5*t-n-6*d) = 12093) ∧
    (∀ i : Fin 6, 2 ≤ i.val →
      let b := i.val
      let m := 25
      let W := 2*t-1
      let A := (2*b-2)*W-b*(b-1)*d
      let G := (2*b-2)*m-b*(b-1)
      G+2*b*m+2*m*(m-1)+6*((G+m)*n+2*(2*A*G+2*W*m))/(6*t-n-8*d) ≤ 140161) := by
  decide

open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation

/-- The two mixed-Hasse interpolants exist on the received rows in each
production window, with the sum-of-degrees support used by the prices. -/
theorem surfaces {F : Type} [Field F] {ι : Type*} [Fintype ι]
    (dom : ι ↪ F) (u v : ι → F) (hn : Fintype.card ι = n) (i : Fin 3) (second : Bool) :
    let w := window i
    let d := n/w.rate-1
    let t := n-w.errors
    let r := if second then w.order₂ else w.order
    let b := if second then w.degree₂ else w.degree
    let s := if second then w.second else w.first
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j h x, ((Q.coeff j).coeff h).coeff x ≠ 0 → j ≤ b ∧ h+j ≤ s ∧ x+j*d < r*t) ∧
      ∀ z : F, ∀ q : F[X], q.natDegree ≤ d → ∀ B : Finset ι, t ≤ B.card →
        (∀ x ∈ B, q.eval (dom x) = u x + z*v x) → Q.eval₂ (evalRingHom (C z)) q = 0 := by
  dsimp only
  generalize hw : window i = w
  let d := n/w.rate-1
  let t := n-w.errors
  let r := if second then w.order₂ else w.order
  let b := if second then w.degree₂ else w.degree
  let s := if second then w.second else w.first
  have hnum : 0 < r ∧ 0 < t ∧ r ≤ s+1 ∧
      Fintype.card ι * Fintype.card (JetRows s r) < Fintype.card (Monomials s b d (r*t)) := by
    subst w
    rw [hn]
    fin_cases i <;> cases second <;>
      simp only [JetRows,Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin] <;>
      decide +kernel
  obtain ⟨c,hc,_,hf⟩ := exists_surface dom u v hnum.1 hnum.2.1 hnum.2.2.1 hnum.2.2.2
  exact ⟨surface c,surface_ne_zero hc,fun _ _ _ h => surface_support c h,
    fun z q hq B hB hg => by rw [surface_eval]; exact hf z q hq B hB hg⟩

#print axioms surfaces
#print axioms hypotheses
#print axioms allocations
#print axioms beyond_johnson
end ArkLib.ProximityGap.Frontier.TangentPolarWindows
