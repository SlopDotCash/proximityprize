/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterCommonFactorDegrees

/-! # Half-rate common-factor allocation using sparse surface polars

The Newton-volume and plane-intersection arguments are in
`docs/research/proximity-gap/half-sparse-gauss-window.md`. -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.HalfSparseGaussWindow
open Finset Polynomial
open QuarterCoreWeightedJets (SectionSurface rowCount columnCount card_rows card_columns
  uniform_received_surface)

abbrev n : ℕ := 1073741824
abbrev d : ℕ := 536870911
abbrev e : ℕ := 312800000
abbrev t : ℕ := n-e
abbrev core : ℕ := t-8192
abbrev bound : ℕ := 2115023520

/-- Subtracting the guaranteed local polar contribution at the ordinate point
at infinity gives this affine degree bound. -/
theorem affine_polar_degree (m b : ℤ) :
    m*(m-1)-(m-b)*(m-b-1) = b*(2*m-b-1) := by ring

/-- The exact volume correction discarded in the per-degree denominator
bound is nonpositive for a factor of admissible coordinate weight. -/
theorem sparse_height {b w d m : ℤ} (hb : 0 ≤ b) (hd : 0 ≤ d) (hw : b*d ≤ w) :
    (6*b+2)*w*m-3*b^2*(d*m+w)+2*d*b^3 ≤ m*((6*b+2)*w-3*b^2*d) := by
  have a := mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hw)
  have c := mul_nonneg (mul_nonneg hb (sq_nonneg b)) hd
  linarith only [show b^2*(w-b*d) ≥ 0 from a, show b*b^2*d ≥ 0 from c]

/-- Exact mixed-Hasse surpluses on the two ordinary supports. -/
theorem ranks : columnCount 123104 93 d (66*t) = n * rowCount 123104 66 + 55334760 ∧
    columnCount 8245 181 d (128*t) = n * rowCount 8245 128 + 15817673019 := by decide +kernel

-- Normalizing the two concrete mixed-jet cardinalities traverses up to 181 columns.
set_option maxRecDepth 4096 in
/-- Both actual interpolants vanish on every selected witness section. -/
theorem surfaces {I F : Type} [Fintype I] [Field F] (dom : I ↪ F) (u v : I → F)
    (hn : Fintype.card I = n) (companion : Bool) :
    let r := if companion then 128 else 66
    let b := if companion then 181 else 93
    let s := if companion then 8245 else 123104
    SectionSurface dom u v s b d (r*t) (fun S => t ≤ S.card) := by
  cases companion
  · apply uniform_received_surface dom u v (by decide) (by decide) (by decide)
    rw [hn,card_rows,card_columns]
    exact ranks.1 ▸ Nat.lt_add_of_pos_right (by decide)
  · apply uniform_received_surface dom u v (by decide) (by decide) (by decide)
    rw [hn,card_rows,card_columns]
    exact ranks.2 ▸ Nat.lt_add_of_pos_right (by decide)

private def ceilDiv (a b : ℕ) := (a+b-1)/b
private def discreteUnion (j : ℕ) :=
  let a := 7*j/10
  ceilDiv (2*a*j*core-j*(j-1)*d) (a*(a+1))

def headMass (j : ℕ) :=
  if j < 3 then j*(e+1) else
    let cover := max (discreteUnion j) (ceilDiv (j*core^2) (core+(j-1)*d))
    min (j*(e+1)) (j*n-(j-1)*cover)

/-- Uniform population per unit of actual companion degree for the given
number of rich heads and the individual factor's actual ordinate degree. -/
def unitPrice (j b : ℕ) :=
  let w := 66*t-1-j*d
  let H := (6*b+2)*w-3*b^2*d
  let R := (2*b-1)*n
  let p := min j 2
  let tri := 2*b+ceilDiv ((3-p)*(R+H)) (3*t-(n+2*d+p*8192))
  let six := 12*b+ceilDiv (28*(5*R+6*H)) (140*t-(35*n+112*d))
  let eight := 16*b+ceilDiv (45*(7*R+8*H)) (315*t-(84*n+240*d))
  let other := if j=0 then
      min (if 30<b then six else tri) (if 56<b then eight else tri)
    else if 3≤j then 2*b+ceilDiv (H+R) (t+discreteUnion j-(n+d)) else tri
  4*b-2+min tri other

private def otherLabels (j : ℕ) :=
  headMass j + 123104 + (123104*181+93*8245) + (93-j)*123104 + (8245-j)*21

/-- The integer budget available per scalar/value degree after all other
classes have been charged. -/
def allowance (j : ℕ) := (bound-otherLabels j)/(8245-j)

/-- Tame-characteristic, identity-site and determinant requirements,
including the strictly positive transverse gap for every applicable head count. -/
theorem parameters : 3*core > n+2*d ∧ e < 8192*123104 ∧ 4*n ≤ 20*(t-d) ∧
    n+2*d+2*8192 < 3*t ∧ 35*n+112*d < 140*t ∧ 84*n+240*d < 315*t ∧
    2*66*t*93 < 2^100 ∧ bound < 2*n ∧
    ∀ j : Fin 94, 3 ≤ j.val → 1 ≤ 7*j.val/10 ∧ 7*j.val/10 < j.val ∧
      n+d < t+discreteUnion j.val := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
-- Reduce the two-dimensional grid in actual ordinate degree and rich-head count.
theorem degree_prices : ∀ j : Fin 94, otherLabels j.val ≤ bound ∧
    ∀ b : Fin (93-j.val+1), 2 ≤ b.val → b.val*d ≤ 66*t-1-j.val*d ∧
      unitPrice j.val b.val ≤ allowance j.val := by decide +kernel

/-- The total populations of all six classes, using the sum of actual
scalar/value degrees of the common nonlinear factors. -/
theorem allocation {J : Type*} (S : Finset J) (degree value pop : J → ℕ) (j : Fin 94)
    (heads scalar outside small linear : ℕ) (hheads : heads ≤ headMass j.val)
    (hscalar : scalar ≤ 123104) (houtside : outside ≤ 123104*181+93*8245)
    (hsmall : small ≤ (93-j.val)*123104) (hlinear : linear ≤ (8245-j.val)*21)
    (htotal : ∑ i ∈ S, degree i ≤ 8245-j.val)
    (hvalue : ∀ i ∈ S, 2 ≤ value i ∧ value i ≤ 93-j.val)
    (hpop : ∀ i ∈ S, pop i ≤ degree i * unitPrice j.val (value i)) :
    heads+scalar+outside+small+linear+∑ i ∈ S, pop i ≤ bound := by
  have each (i : J) (hi : i ∈ S) : pop i ≤ degree i * allowance j.val := by
    obtain ⟨hlo,hhi⟩ := hvalue i hi
    exact (hpop i hi).trans (Nat.mul_le_mul_left _ (((degree_prices j).2
      ⟨value i, by omega⟩ hlo).2))
  have cost := sum_le_sum each
  rw [← sum_mul] at cost
  have total := Nat.mul_le_mul_right (allowance j.val) htotal
  have room := Nat.mul_div_le (bound-otherLabels j.val) (8245-j.val)
  have room' : (8245-j.val) * allowance j.val ≤ bound-otherLabels j.val := by
    simpa [allowance, mul_comm] using room
  have base := (degree_prices j).1
  unfold otherLabels at room' base
  omega

#print axioms sparse_height
#print axioms affine_polar_degree
#print axioms surfaces
#print axioms parameters
#print axioms degree_prices
#print axioms allocation
end ArkLib.ProximityGap.Frontier.HalfSparseGaussWindow
