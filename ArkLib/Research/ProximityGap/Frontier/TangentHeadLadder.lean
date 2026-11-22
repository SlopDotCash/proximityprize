/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Tactic

/-! # Tangent-head ladder at budgets `2^32`, `2^34` and `2^36`

Twelve entries of `docs/research/proximity-gap/tangent-head-ladder.md`: the four
prize rates at integer budgets `2^32`, `2^34` and `2^36`, length `2^30`.

As in `TangentHeadWindows`, the cap of Theorem D′ enters as the definition of a
price; its geometric proof is a written argument. This module verifies, for each
entry, the Johnson-type conditions, the rich-head tests, both surface counts, and
every joint degree allocation with at most `richMax` rich affine heads. The bound
`richMax` on the number of rich heads is the packing count of their joint cores
and is part of the written argument.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.TangentHeadLadder

private theorem sum_prices {ι : Type*} (S : Finset ι) (value cost : ι → ℕ) {R B A : ℕ}
    (hR : 0 < R) (hA : A ≤ B) (he : ∑ i ∈ S, value i = R)
    (h : ∀ i ∈ S, R * cost i ≤ value i * (B-A)) : A + ∑ i ∈ S, cost i ≤ B := by
  have hh := sum_le_sum h
  rw [← mul_sum, ← sum_mul, he] at hh
  have hh' := Nat.le_of_mul_le_mul_left hh hR
  omega

/-- A ladder entry. `group = 0` means that no determinant test forces rich heads
to be collinear; then every rich head is charged `errors + 1` labels. -/
structure Window where
  rate : ℕ
  beta : ℕ
  errors : ℕ
  order : ℕ
  degree : ℕ
  first : ℕ
  order₂ : ℕ
  degree₂ : ℕ
  second : ℕ
  group : ℕ

/-- The length `2^30`. -/
abbrev n : ℕ := 1073741824

/-- The integer budget of an entry. -/
def limit (w : Window) : ℕ := 2 ^ w.beta

/-- Above this many labels a factor divides both interpolants. -/
def cutoff (w : Window) : ℕ :=
  max (w.errors/256+1) (w.first*w.degree₂+w.degree*w.second+1)

/-- Lower bound for the joint core of a rich affine head. -/
def core (w : Window) : ℕ := n-w.errors-255

/-- The packing bound on the number of rich affine heads. -/
def richMax (w : Window) : ℕ :=
  let d := n/w.rate-1
  n*(core w-d)/(core w^2-n*d)

/-- Labels carried by `j` rich affine heads. -/
def mass (w : Window) (j : ℕ) : ℕ :=
  if w.group = 0 ∨ j < w.group then j*(w.errors+1)
  else
    let c := core w
    let z := c+(j-1)*(n/w.rate-1)
    let covered := (j*c*c+z-1)/z
    min (j*(w.errors+1)) (j*n-(j-1)*covered)

/-- The cap of Theorem D′ for a factor of value degree `b` next to `j` rich heads
among factors of total value degree `l`. -/
def price (w : Window) (l j b : ℕ) : ℕ :=
  if b ≤ 1 then cutoff w
  else
    let d := n/w.rate-1
    let t := n-w.errors
    let maxW := w.order*t-1-(l-b)*d
    let m := w.second-j
    if maxW < b*d ∨ m < b then cutoff w
    else
      let bx := (2*b-2)*m+1-b*(b-1)
      let bz := (2*b-2)*maxW+1-b*(b-1)*d
      let budget := 2*bx*bz+b*(maxW*(m-b)+m*(maxW-b*d))
      max (cutoff w) (bx + (m*n*(2*t+n)+2*budget*(t+n))/(t^2-n*d))

/-- Monomials minus mixed jet conditions for order `r`, value degree at most `v`
and total scalar/value degree at most `s`, at weight below `r * t`. -/
def surplusOK (r v s t d : ℕ) : Prop :=
  n * ∑ j ∈ range r, (r-j)*(s+1-j) < ∑ j ∈ range (v+1), (s+1-j)*(r*t-j*d)

instance (r v s t d : ℕ) : Decidable (surplusOK r v s t d) := by
  unfold surplusOK; infer_instance

/-- The numerical conditions of an entry other than the allocations: both
interpolants exist by counting, the entry is below the Johnson radius, rich
cores are above the Johnson size, the affine-head test holds, and the group
size is justified by its determinant test. -/
def Conditions (w : Window) : Prop :=
  let d := n/w.rate-1
  let t := n-w.errors
  surplusOK w.order w.degree w.first t d ∧ surplusOK w.order₂ w.degree₂ w.second t d ∧
  n*d < t^2 ∧ n*d < core w^2 ∧
  d < t-w.second*n/cutoff w-3*(w.second*n/(cutoff w-w.second)) ∧
  (w.group = 3 → n+2*d < 3*core w) ∧ (w.group = 4 → n+4*d < 4*core w)

/-- The proportional-price certificate of an entry for value degrees below `K`. -/
def Priced (w : Window) (K : ℕ) : Prop :=
  ∀ l j b : Fin K, l.val ≤ w.degree → j.val ≤ l.val → j.val ≤ richMax w →
    mass w j.val ≤ limit w ∧
      (1 ≤ b.val → b.val ≤ l.val-j.val →
        (l.val-j.val)*price w l.val j.val b.val ≤ b.val*(limit w-mass w j.val))

/-- A priced entry bounds every degree allocation with at most `richMax` rich
heads by its budget `2 ^ beta`. -/
theorem all_allocations {w : Window} {K : ℕ} (hp : Priced w K)
    {ι : Type*} (S : Finset ι) (value cost : ι → ℕ) (l j : Fin K) (headCost : ℕ)
    (hl : l.val ≤ w.degree) (hj : j.val ≤ l.val) (hrich : j.val ≤ richMax w)
    (hh : headCost ≤ mass w j.val)
    (hv : ∀ a ∈ S, 0 < value a) (he : ∑ a ∈ S, value a = l.val-j.val)
    (hc : ∀ a ∈ S, cost a ≤ price w l.val j.val (value a)) :
    headCost + ∑ a ∈ S, cost a ≤ limit w := by
  classical
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) l.isLt
  have hmax := (hp l j ⟨0, hK⟩ hl hj hrich).1
  by_cases hz : l.val-j.val = 0
  · have hs : S = ∅ := by
      by_contra h
      obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.mpr h
      have hsum := single_le_sum (fun b _ => Nat.zero_le (value b)) ha
      rw [he, hz] at hsum
      exact (hv a ha).not_ge hsum
    simpa [hs] using hh.trans hmax
  · apply (Nat.add_le_add_right hh _).trans
    apply sum_prices S value cost (Nat.pos_of_ne_zero hz) hmax he
    intro a ha
    have hv' := single_le_sum (fun b _ => Nat.zero_le (value b)) ha
    rw [he] at hv'
    have hlt : value a < K := hv'.trans_lt (lt_of_le_of_lt (Nat.sub_le _ _) l.isLt)
    exact (Nat.mul_le_mul_left _ (hc a ha)).trans
      ((hp l j ⟨value a,hlt⟩ hl hj hrich).2 (hv a ha) hv')

/-- Rate `1/2` at budget `2^32`: safe through `307759023` errors. -/
def r2b32 : Window := ⟨2,32,307759023,16,22,13629,32,45,538,3⟩

theorem r2b32_conditions : Conditions r2b32 := by
  unfold Conditions surplusOK
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem r2b32_priced : Priced r2b32 23 := by
  unfold Priced
  decide +kernel

/-- Rate `1/2` at budget `2^34`: safe through `309134539` errors. -/
def r2b34 : Window := ⟨2,34,309134539,20,28,37924,39,55,842,3⟩

theorem r2b34_conditions : Conditions r2b34 := by
  unfold Conditions surplusOK
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem r2b34_priced : Priced r2b34 29 := by
  unfold Priced
  decide +kernel

/-- Rate `1/2` at budget `2^36`: safe through `310191320` errors. -/
def r2b36 : Window := ⟨2,36,310191320,25,35,1789925,51,72,1298,3⟩

theorem r2b36_conditions : Conditions r2b36 := by
  unfold Conditions surplusOK
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem r2b36_priced : Priced r2b36 36 := by
  unfold Priced
  decide +kernel

/-- Rate `1/4` at budget `2^32`: safe through `527124673` errors. -/
def r4b32 : Window := ⟨4,32,527124673,14,27,8712,27,54,541,3⟩

theorem r4b32_conditions : Conditions r4b32 := by
  unfold Conditions surplusOK
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem r4b32_priced : Priced r4b32 28 := by
  unfold Priced
  decide +kernel

/-- Rate `1/4` at budget `2^34`: safe through `529408947` errors. -/
def r4b34 : Window := ⟨4,34,529408947,18,35,321384,34,68,910,3⟩

theorem r4b34_conditions : Conditions r4b34 := by
  unfold Conditions surplusOK
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem r4b34_priced : Priced r4b34 36 := by
  unfold Priced
  decide +kernel

/-- Rate `1/4` at budget `2^36`: safe through `530904312` errors. -/
def r4b36 : Window := ⟨4,36,530904312,22,44,1503703,44,88,1408,3⟩

theorem r4b36_conditions : Conditions r4b36 := by
  unfold Conditions surplusOK
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem r4b36_priced : Priced r4b36 45 := by
  unfold Priced
  decide +kernel

/-- Rate `1/8` at budget `2^32`: safe through `671088385` errors. -/
def r8b32 : Window := ⟨8,32,671088385,6,16,335,9,26,128,4⟩

theorem r8b32_conditions : Conditions r8b32 := by
  unfold Conditions surplusOK
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem r8b32_priced : Priced r8b32 17 := by
  unfold Priced
  decide +kernel

/-- Rate `1/8` at budget `2^34`: safe through `680837212` errors. -/
def r8b34 : Window := ⟨8,34,680837212,9,25,520374,17,49,356,0⟩

theorem r8b34_conditions : Conditions r8b34 := by
  unfold Conditions surplusOK
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem r8b34_priced : Priced r8b34 26 := by
  unfold Priced
  decide +kernel

/-- Rate `1/8` at budget `2^36`: safe through `687671509` errors. -/
def r8b36 : Window := ⟨8,36,687671509,19,53,76589,37,106,1436,0⟩

theorem r8b36_conditions : Conditions r8b36 := by
  unfold Conditions surplusOK
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem r8b36_priced : Priced r8b36 54 := by
  unfold Priced
  decide +kernel

/-- Rate `1/16` at budget `2^32`: safe through `738197249` errors. -/
def r16b32 : Window := ⟨16,32,738197249,2,6,102,3,13,20,4⟩

theorem r16b32_conditions : Conditions r16b32 := by
  unfold Conditions surplusOK
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem r16b32_priced : Priced r16b32 7 := by
  unfold Priced
  decide +kernel

/-- Rate `1/16` at budget `2^34`: safe through `786379766` errors. -/
def r16b34 : Window := ⟨16,34,786379766,5,21,56862,10,42,179,0⟩

theorem r16b34_conditions : Conditions r16b34 := by
  unfold Conditions surplusOK
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem r16b34_priced : Priced r16b34 22 := by
  unfold Priced
  decide +kernel

/-- Rate `1/16` at budget `2^36`: safe through `798744899` errors. -/
def r16b36 : Window := ⟨16,36,798744899,16,62,23006,30,122,1337,0⟩

theorem r16b36_conditions : Conditions r16b36 := by
  unfold Conditions surplusOK
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem r16b36_priced : Priced r16b36 63 := by
  unfold Priced
  decide +kernel

#print axioms r2b32_conditions
#print axioms r2b32_priced
#print axioms r2b34_conditions
#print axioms r2b34_priced
#print axioms r2b36_conditions
#print axioms r2b36_priced
#print axioms r4b32_conditions
#print axioms r4b32_priced
#print axioms r4b34_conditions
#print axioms r4b34_priced
#print axioms r4b36_conditions
#print axioms r4b36_priced
#print axioms r8b32_conditions
#print axioms r8b32_priced
#print axioms r8b34_conditions
#print axioms r8b34_priced
#print axioms r8b36_conditions
#print axioms r8b36_priced
#print axioms r16b32_conditions
#print axioms r16b32_priced
#print axioms r16b34_conditions
#print axioms r16b34_priced
#print axioms r16b36_conditions
#print axioms r16b36_priced
#print axioms all_allocations

end ArkLib.ProximityGap.Frontier.TangentHeadLadder
