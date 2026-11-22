/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.HodgeSectionVariance

/-! # Tangent-head caps and three production interpolation windows

The population cap for a nonlinear factor used here is Theorem D′ of
`docs/research/proximity-gap/section-incidence-hodge-index.md`. Its proof, on the
normalized cover, is a written geometric argument and is not formalized. This
module verifies what turns that cap into the three numerical bounds of
`docs/research/proximity-gap/tangent-head-windows.md`: the Johnson-type
conditions, the rich-head determinant tests, both surface ranks, and every joint
degree allocation.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.TangentHeadWindows

/-- Local proportional residual budgets give a cap for a whole partition. This is
the pricing step of `WeightedHodgeWindows`, repeated here so that this module
depends only on the interpolation substrate. -/
theorem sum_prices {ι : Type*} (S : Finset ι) (value cost : ι → ℕ) {R B A : ℕ}
    (hR : 0 < R) (hA : A ≤ B) (he : ∑ i ∈ S, value i = R)
    (h : ∀ i ∈ S, R * cost i ≤ value i * (B-A)) : A + ∑ i ∈ S, cost i ≤ B := by
  have hh := sum_le_sum h
  rw [← mul_sum, ← sum_mul, he] at hh
  have hh' := Nat.le_of_mul_le_mul_left hh hR
  omega

private structure Window where
  rate : ℕ
  errors : ℕ
  order : ℕ
  degree : ℕ
  first : ℕ
  order₂ : ℕ
  degree₂ : ℕ
  second : ℕ
  group : ℕ

private def win (i : Fin 3) : Window :=
  if i = 0 then ⟨2,306780000,14,19,238338,27,38,412,3⟩
  else if i = 1 then ⟨4,524700000,11,22,2159,21,42,353,3⟩
  else ⟨8,671088385,6,16,335,9,26,128,4⟩

private abbrev n := 1073741824

/-- The integer budget `2n` of the second named prime. -/
private abbrev limit := 2147483648

private def cutoff (w : Window) : ℕ :=
  max (w.errors/256+1) (w.first*w.degree₂+w.degree*w.second+1)

private def mass (w : Window) (j : ℕ) : ℕ :=
  if j < w.group then j*(w.errors+1)
  else
    let c := n-w.errors-255
    let z := c+(j-1)*(n/w.rate-1)
    let covered := (j*c*c+z-1)/z
    min (j*(w.errors+1)) (j*n-(j-1)*covered)

/-- A component on both interpolants obeys the tangent-head price. The cutoff
also covers small populations and components absent from the companion. -/
def factorPrice (n d t cutoff W m b : ℕ) : ℕ :=
  if b ≤ 1 ∨ W < b * d ∨ m < b then cutoff
  else
    let bx := (2 * b - 2) * m + 1 - b * (b - 1)
    let bz := (2 * b - 2) * W + 1 - b * (b - 1) * d
    let budget := 2 * bx * bz + b * (W * (m - b) + m * (W - b * d))
    max cutoff (bx + (m * n * (2 * t + n) + 2 * budget * (t + n)) / (t ^ 2 - n * d))

/-- The cap of Theorem D′ for a factor of value degree `b` next to `j` rich heads
among factors of total value degree `l`. -/
private def price (w : Window) (l j b : ℕ) : ℕ :=
  let d := n / w.rate - 1
  let t := n - w.errors
  factorPrice n d t (cutoff w) (w.order * t - 1 - (l - b) * d) (w.second - j) b

/-- Each window is below the Johnson radius, so the cap applies, and the rich
heads satisfy the determinant test that forces collinearity from `group` on. -/
theorem johnson_and_group : ∀ i : Fin 3,
    n*(n/(win i).rate-1) < (n-(win i).errors)^2 ∧
    ((win i).group = 3 → n+2*(n/(win i).rate-1) < 3*(n-(win i).errors-255)) ∧
    ((win i).group = 4 → n+4*(n/(win i).rate-1) < 4*(n-(win i).errors-255)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem finite_prices : ∀ i : Fin 3, ∀ l j b : Fin 23,
    l.val ≤ (win i).degree → j.val ≤ l.val →
    mass (win i) j.val ≤ limit ∧
      (1 ≤ b.val → b.val ≤ l.val-j.val →
        (l.val-j.val)*price (win i) l.val j.val b.val ≤ b.val*(limit-mass (win i) j.val)) := by
  decide +kernel

/-- Every degree allocation surviving the component and core bounds fits the
128-bit budget `2n` in each of the three windows. -/
theorem all_allocations {ι : Type*} (S : Finset ι) (value cost : ι → ℕ)
    (i : Fin 3) (l j : Fin 23) (headCost : ℕ)
    (hl : l.val ≤ (win i).degree) (hj : j.val ≤ l.val)
    (hh : headCost ≤ mass (win i) j.val)
    (hv : ∀ a ∈ S, 0 < value a) (he : ∑ a ∈ S, value a = l.val-j.val)
    (hc : ∀ a ∈ S, cost a ≤ price (win i) l.val j.val (value a)) :
    headCost + ∑ a ∈ S, cost a ≤ limit := by
  classical
  have hmax := (finite_prices i l j 0 hl hj).1
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
    have hlt : value a < 23 := hv'.trans_lt (lt_of_le_of_lt (Nat.sub_le _ _) l.isLt)
    exact (Nat.mul_le_mul_left _ (hc a ha)).trans
      ((finite_prices i l j ⟨value a,hlt⟩ hl hj).2 (hv a ha) hv')

open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation

/-- Two genuine trivariate surfaces on the received rows at every window. -/
theorem surfaces {F : Type} [Field F] {ι : Type*} [Fintype ι]
    (dom : ι ↪ F) (u v : ι → F) (hn : Fintype.card ι = n)
    (i : Fin 3) (second : Bool) :
    let w := win i
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
  generalize hw : win i = w
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
      simp only [JetRows, Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] <;>
      norm_num [Fin.sum_univ_succ, r, s, b, d, t, win, n] <;> decide +kernel
  obtain ⟨c,hc,_,hf⟩ := exists_surface dom u v hnum.1 hnum.2.1 hnum.2.2.1 hnum.2.2.2
  refine ⟨surface c,surface_ne_zero hc,fun _ _ _ h => surface_support c h,?_⟩
  intro z q hq B hB hg
  rw [surface_eval]
  exact hf z q hq B hB hg

#print axioms johnson_and_group
#print axioms all_allocations
#print axioms surfaces

end ArkLib.ProximityGap.Frontier.TangentHeadWindows
