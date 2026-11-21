/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Tactic

/-! # A split third-moment bound for the second rate-sixteenth field

A seed secant limits the mass in one coordinate set. Two supporting tangents for
the falling cubic turn that deficit into a lower bound for the third moment.
-/

namespace ProximityGap.SecondPrimeConditionedCubic

open Finset
set_option autoImplicit false

def falling (x : ℚ) := x*(x-1)*(x-2)
private def slope (x : ℚ) := 3*x^2-6*x+2

private theorem tangent (x v : ℚ) (hx : 0 ≤ x) (hv : 2 ≤ v) :
    falling v + slope v * (x-v) ≤ falling x := by
  have h := mul_nonneg (sq_nonneg (x-v)) (show 0 ≤ x+2*v-3 by linarith)
  dsimp [slope, falling]
  nlinarith only [h]

private theorem finset_tangent {I : Type*} (S : Finset I) (f : I → ℚ) (v : ℚ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (hv : 2 ≤ v) :
    S.card * falling v + slope v * ((∑ i ∈ S, f i)- S.card*v) ≤ ∑ i ∈ S, falling (f i) := by
  have h := Finset.sum_le_sum (fun i hi => tangent (f i) v (hf i hi) hv)
  simpa [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] using h

/-- A lower bound for the mass on a finite block gives its ordinary cubic Jensen bound. -/
theorem uniform_cubic {I : Type*} (S : Finset I) (f : I → ℚ) (v : ℚ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (hv : 2 ≤ v) (hm : S.card*v ≤ ∑ i ∈ S, f i) :
    S.card*falling v ≤ ∑ i ∈ S, falling (f i) := by
  have h := mul_nonneg (show 0 ≤ v by linarith) (show 0 ≤ 3*v-6 by linarith)
  have hp : 0 ≤ slope v := by dsimp [slope]; nlinarith only [h]
  have ht := finset_tangent S f v hf hv
  linarith only [ht, mul_nonneg hp (sub_nonneg.mpr hm)]

/-- Two coordinate sets may have different mean incidences. One-sided mass
estimates suffice when the mean constraints push mass towards the higher tangent. -/
theorem split_cubic {I J : Type*} (S : Finset I) (T : Finset J) (f : I → ℚ) (g : J → ℚ)
    (a b : ℚ) (ha : 2 ≤ a) (hab : a ≤ b) (hf : ∀ i ∈ S, 0 ≤ f i) (hg : ∀ j ∈ T, 0 ≤ g j)
    (hsmall : ∑ i ∈ S, f i ≤ S.card*a)
    (htotal : S.card*a+T.card*b ≤ (∑ i ∈ S, f i) + ∑ j ∈ T, g j) :
    S.card*falling a + T.card*falling b ≤ (∑ i ∈ S, falling (f i)) + ∑ j ∈ T, falling (g j) := by
  have hs : slope a ≤ slope b := by
    have h := mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ 3*(b+a)-6 by linarith)
    dsimp [slope]
    nlinarith only [h]
  have hpos : 0 ≤ slope b := by
    have h := mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ 3*b-6 by linarith)
    dsimp [slope]
    nlinarith only [h]
  have hbalance := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hsmall)
  have hgrand := mul_nonneg hpos (sub_nonneg.mpr htotal)
  have h₁ := finset_tangent S f a hf ha
  have h₂ := finset_tangent T g b hg (ha.trans hab)
  nlinarith only [hbalance, hgrand, h₁, h₂]

/-- At the first stage a subfamily shares one coordinate, which is then deleted. -/
theorem first_comparison : let M : ℚ := 852229447; let N : ℚ := 1073741823
    (67108862 + (172000000-67108863-1)/(M-2))*falling M <
      N*falling (M*426114722/N) := by norm_num [falling]

/-- The two tangents on the retained seed and its complement give a larger
margin in every one of the later secant extractions. -/
theorem split_comparison : let M : ℚ := 204602343; let S : ℚ := 172000000
    let T : ℚ := 1073741824-S
    (67108863 + 7*(350093427-67108863-1)/(M-2))*falling M <
      S*falling (M*67108863/S) + T*falling (M*(426114723-67108863)/T) := by norm_num [falling]

/-- Absolute arithmetic parameters for row conditioning, the two line occupancies,
and the three-core covering and count contradictions. -/
theorem production_sizes : let N := 1073741824; let e := 647627101; let t := N-e
    let d := 67108863; let s := 172000000; let z := 350093427
    ((2*N+1)*t+N-1)/N = 852229447 ∧ 2*N+1-3*(e+1) = 204602343 ∧
    1+e/(t-(s-1)) = 3 ∧ 1+e/(t-(z-1)) = 9 ∧ N+6*d < t+3*z ∧ 3*(e+1) < 2*N+1 := by decide

/-- Each cut keeps at least the rounded-up rational fraction of the points. -/
private def slice (num den : ℕ) : ℕ → ℕ → ℕ
  | 0, count => count
  | i+1, count => slice num den i ((count*num+den-1)/den)

/-- With affine dimension sixteen, at most fifteen cuts are needed to find a line. -/
theorem rank_sixteen_sizes : let N := 1073741824; let e := 715827881; let t := N-e
    let d := 67108863; let z := 350457399; let M := 2*N+1
    let cut (m c u : ℕ) := slice (u-d) (c-d) 15 m
    1+e/(t-z+1) = 96 ∧ cut M N t = 18 ∧ t-e/17 = 315806421 ∧
    cut (M-96) (N-315806421) (t-d) = 98 ∧ z ≤ t-e/97 ∧
    cut (M-(e+1)) (N-z) (t-d) = 141 ∧
    cut (M-2*(e+1)) (N-2*z+d) (t-2*d) = 1599 ∧
    cut (M-(3*N-2*(3*z-3*d))) (N-2*z+d) (t-2*d) = 1399 ∧
    cut (M-(4*N-3*(4*z-6*d))) (N-2*z+d) (t-2*d) = 1898 ∧
    N+5*d < 3*z+t ∧ 9*d < 2*(4*z-N) ∧ N+10*d < 5*z := by decide

#print axioms split_cubic
#print axioms first_comparison
#print axioms split_comparison
#print axioms production_sizes
#print axioms rank_sixteen_sizes

end ProximityGap.SecondPrimeConditionedCubic
