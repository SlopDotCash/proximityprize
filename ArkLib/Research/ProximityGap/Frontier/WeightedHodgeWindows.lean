/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.HodgeSectionVariance

/-! # Weighted Hodge variance and three production interpolation windows

The normalized-cover and ramification estimates are written geometric arguments.
This module verifies the supporting inequality, surface ranks and joint
degree allocations which turn those estimates into the three numerical bounds.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.WeightedHodgeWindows

/-- Rational third-moment minorant for a Bernoulli variance weighted by the
reciprocal normalized fibre degree. -/
theorem weighted_moment (θ g K : ℝ) (hθ : 0 ≤ θ) (hg : 0 < g) (hK : 0 < K) :
    (5*K^4-4*K^5)*θ-θ^3 ≤ 2*K^5*(θ/g-2*θ+g) := by
  let s := Real.sqrt θ
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have he : s^2 = θ := Real.sq_sqrt hθ
  rw [← he]
  apply sub_nonneg.mp
  have hid : 2*K^5*(s^2/g-2*s^2+g)-((5*K^4-4*K^5)*s^2-(s^2)^3) =
      s*(s-K)^2*(s^3+2*K*s^2+3*K^2*s+4*K^3)+2*K^5*(s-g)^2/g := by
    field_simp
    ring
  rw [hid]
  positivity

/-- Weighted orthogonality, using the individual degree of each nonzero fibre. -/
theorem weighted_cost {ι : Type*} (S : Finset ι) (f a v : ι → ℝ) {c m : ℝ}
    (hc : 0 ≤ c) (hm : 0 ≤ m) (hf : ∀ i ∈ S, 0 < f i)
    (ha : ∀ i ∈ S, a i ≤ m*f i)
    (hi : (∑ i ∈ S, (v i)^2/f i)^2 ≤ c * ∑ i ∈ S, (v i/f i)^2 * a i) :
    ∑ i ∈ S, (v i)^2/f i ≤ m*c := by
  have h₁ : ∑ i ∈ S, (v i/f i)^2*a i ≤ ∑ i ∈ S, (v i)^2/f i*m := by
    apply sum_le_sum
    intro i h
    calc
      _ ≤ (v i/f i)^2*(m*f i) := mul_le_mul_of_nonneg_left (ha i h) (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt (hf i h)]
  rw [← sum_mul] at h₁
  have h₂ := hi.trans (mul_le_mul_of_nonneg_left h₁ hc)
  have hn : 0 ≤ ∑ i ∈ S, (v i)^2/f i :=
    sum_nonneg fun i h => div_nonneg (sq_nonneg _) (hf _ h).le
  by_cases hz : ∑ i ∈ S, (v i)^2/f i = 0
  · rw [hz]
    exact mul_nonneg hm hc
  · apply (mul_le_mul_iff_of_pos_left (lt_of_le_of_ne hn (Ne.symm hz))).mp
    nlinarith only [h₂]

/-- Convert the local proportional residual budgets into a cap for a whole
partition, with no assumption on the order or multiplicity of the degrees. -/
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
  kappa : ℕ
  limit : ℕ
  group : ℕ

private def win (i : Fin 3) : Window :=
  if i = 0 then ⟨2,299100000,7,9,31973,12,17,109,912,2128363411,3⟩
  else if i = 1 then ⟨4,514400000,6,11,6594,11,22,110,832,1963198607,3⟩
  else ⟨8,665600000,4,12,1729,8,24,85,757,2137455396,4⟩

private abbrev n := 1073741824

private def cutoff (w : Window) : ℕ :=
  max (w.errors/256+1) (w.first*w.degree₂+w.degree*w.second+1)

private def mass (w : Window) (j : ℕ) : ℕ :=
  if j < w.group then j*(w.errors+1)
  else
    let c := n-w.errors-255
    let z := c+(j-1)*(n/w.rate-1)
    let covered := (j*c*c+z-1)/z
    min (j*(w.errors+1)) (j*n-(j-1)*covered)

private def price (w : Window) (l j b : ℕ) : ℕ :=
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
      let k := w.kappa
      let den := (5*k^4*1000-4*k^5)*t-d*1000^5
      let num := 2*k^5*b*(4*m*bx*bz + m*n + bx*bz)+(n-d)*(m+1)*1000^5
      max (cutoff w) (bx + num/den)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
private theorem finite_prices : ∀ i : Fin 3, ∀ l j b : Fin 13,
    l.val ≤ (win i).degree → j.val ≤ l.val →
    mass (win i) j.val ≤ (win i).limit ∧
      (1 ≤ b.val → b.val ≤ l.val-j.val →
        (l.val-j.val)*price (win i) l.val j.val b.val ≤ b.val*((win i).limit-mass (win i) j.val)) := by
  decide

/-- Every degree allocation surviving the component and core bounds fits
the 128-bit budget in each of the three numerical windows. -/
theorem all_allocations {ι : Type*} (S : Finset ι) (value cost : ι → ℕ)
    (i : Fin 3) (l j : Fin 13) (headCost : ℕ)
    (hl : l.val ≤ (win i).degree) (hj : j.val ≤ l.val)
    (hh : headCost ≤ mass (win i) j.val)
    (hv : ∀ a ∈ S, 0 < value a) (he : ∑ a ∈ S, value a = l.val-j.val)
    (hc : ∀ a ∈ S, cost a ≤ price (win i) l.val j.val (value a)) :
    headCost + ∑ a ∈ S, cost a ≤ (win i).limit := by
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
    have hlt : value a < 13 := hv'.trans_lt (lt_of_le_of_lt (Nat.sub_le _ _) l.isLt)
    exact (Nat.mul_le_mul_left _ (hc a ha)).trans
      ((finite_prices i l j ⟨value a,hlt⟩ hl hj).2 (hv a ha) hv')

open SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation

/-- Two genuine trivariate surfaces on the received rows at every production window. -/
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

#print axioms weighted_moment
#print axioms weighted_cost
#print axioms all_allocations
#print axioms surfaces

end ArkLib.ProximityGap.Frontier.WeightedHodgeWindows
