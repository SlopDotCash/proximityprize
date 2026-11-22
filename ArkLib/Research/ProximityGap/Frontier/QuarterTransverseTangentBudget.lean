/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TangentPolarWindows
import ArkLib.Research.ProximityGap.Frontier.TangentHeadWindows

/-! # Quarter-rate tangent populations in the presence of rich collinear cores

The integer certificate allows every residual degree partition at 529,940,000 errors.
The geometric hypotheses supplying the component prices are in the accompanying proof.
-/

set_option autoImplicit false
open Finset
namespace ArkLib.ProximityGap.Frontier.QuarterTransverseTangentBudget

abbrev n : ℕ := 1073741824
abbrev d : ℕ := 268435455
abbrev e : ℕ := 529940000
abbrev t : ℕ := n-e
abbrev c : ℕ := t-255
abbrev cutoff : ℕ := 2802951

/-- The second-order inclusion-exclusion bound at the integer parameter j/2.
For the primitive direction of degree h this lower-bounds the union minus h. -/
def discreteUnion (j : ℕ) : ℕ :=
  let a := j/2
  let denom := a*(a+1)
  (2*a*j*c-j*(j-1)*d+denom-1)/denom

/-- Collinear cores have both an integral packing bound and a Cauchy bound. -/
def headBound (j : ℕ) : ℕ :=
  if j < 3 then j*(e+1) else
    let den := c+(j-1)*d
    let u := max (discreteUnion j) ((j*c*c+den-1)/den)
    min (j*(e+1)) (j*n-(j-1)*u)

/-- Positive cost paid by each regular tangent outside the common affine line. -/
def gap (j : ℕ) : ℕ := if j < 3 then 0 else discreteUnion j+t-(n+d)

/-- Allocate cheap factors to the resultant cutoff and split the actual scalar/value
degree for the high-degree polar. The degree-one polar covers the low part. -/
def price (l j b : ℕ) : ℕ :=
  let W := 19*t-1-(l-b)*d
  let m := if j < 3 then 1051-j else min (1051-j) 909
  let s := if j < 3 then 7 else if j=3 then 18 else 1
  let a := if j < 3 then 5 else if j=3 then 13 else 1
  let split := s*(s-1)
  if b ≤ 1 ∨ W < b*d ∨ m < b then cutoff else
    let high := if split < m then TangentPolarWindows.component b m W t d s a true (gap j) else 0
    let low := if b ≤ split then
      TangentPolarWindows.component b (min m split) W t d 1 1 true (gap j) else 0
    max cutoff (max high low)

/-- The three resultant tests, the Johnson inequality, and the transverse gaps
hold for every head count allowed by the primary value degree. -/
theorem parameters :
    max (e/256+1) (max (37338*74+38*1051+1) (37338*70+38*909+1)) = cutoff ∧
    n*d < t^2 ∧ n+2*d < 3*c ∧ d+1051*n/cutoff+3*(1051*n/(cutoff-1051)) < t ∧
    ∀ j : Fin 39, 3 ≤ j.val → 0 < gap j.val ∧
      (j.val/2)*(j.val/2+1) ≤ j.val*(j.val-1) := by decide

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 120000 in
private theorem prices : ∀ l : Fin 39, ∀ j : Fin (l.val+1), ∀ b : Fin (l.val-j.val+1),
    37338+headBound j.val ≤ 2147483648 ∧ (0 < b.val →
      (l.val-j.val)*price l.val j.val b.val ≤ b.val*(2147483648-(37338+headBound j.val))) := by
  decide +kernel

/-- The component bounds imply the named budget for any family of positive
factor degrees, with a separate allowance for the scalar-only factors. -/
theorem allocations {α : Type*} (S : Finset α) (deg pop : α → ℕ) (l : Fin 39) (j : Fin (l.val+1))
    (hpos : ∀ x ∈ S, 0 < deg x) (hdeg : ∑ x ∈ S, deg x = l.val-j.val)
    (hcost : ∀ x ∈ S, pop x ≤ price l.val j.val (deg x)) :
    37338+headBound j.val+∑ x ∈ S, pop x ≤ 2147483648 := by
  have base := (prices l j ⟨0,by omega⟩).1
  by_cases hz : l.val-j.val=0
  · have he : S=∅ := by
      by_contra hn
      obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr hn
      have h := single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) hx
      rw [hdeg,hz] at h
      exact (hpos x hx).not_ge h
    simpa [he] using base
  · apply TangentHeadWindows.sum_prices S deg pop (Nat.pos_of_ne_zero hz) base hdeg
    intro x hx
    have h := single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) hx
    rw [hdeg] at h
    let b : Fin (l.val-j.val+1) := ⟨deg x,by omega⟩
    exact (Nat.mul_le_mul_left _ (hcost x hx)).trans ((prices l j b).2 (hpos x hx))

#print axioms parameters
#print axioms allocations
end ArkLib.ProximityGap.Frontier.QuarterTransverseTangentBudget
