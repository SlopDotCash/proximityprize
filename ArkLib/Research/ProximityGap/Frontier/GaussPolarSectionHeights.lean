/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfSuccessorJetInterpolation
import Mathlib.RingTheory.Derivation.MapCoeffs

/-! # Gauss polar heights at half rate

The graph intersection giving the height bound is proved in
`docs/research/proximity-gap/gauss-polar-section-heights.md`. This file checks the section
slope, the interpolants and the full finite allocation using that bound. -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.GaussPolarSectionHeights
open Finset Polynomial SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation
open scoped Differential

/-- On a simple section the slope coordinate of the lifted Gauss map agrees
with the negative derivative of the section. -/
theorem section_slope {K : Type*} [Field K] [Differential K] (f : K[X]) (q : K)
    (zero : f.eval q = 0) (simple : f.derivative.eval q ≠ 0) :
    (Differential.mapCoeffs f).eval q / f.derivative.eval q = -q′ := by
  apply (div_eq_iff simple).2
  have h := Differential.deriv_aeval_eq q f
  have hz : aeval q f = 0 := by simpa using zero
  rw [hz, map_zero] at h
  have relation : (Differential.mapCoeffs f).eval q + f.derivative.eval q * q′ = 0 := by
    simpa using h.symm
  linear_combination relation

abbrev n : ℕ := 1073741824
abbrev d : ℕ := 536870911
abbrev e : ℕ := 312250000
abbrev t : ℕ := n-e
abbrev cap : ℕ := 2131191599
abbrev cutoff : ℕ := 8998790
abbrev core : ℕ := t-e/cutoff

/-- Both mixed Hasse surfaces at the production predecessor. -/
theorem surfaces {F : Type} [Field F] {I : Type*} [Fintype I] (dom : I ↪ F)
    (u v : I → F) (hn : Fintype.card I = n) (second : Bool) :
    let r := if second then 97 else 50
    let b := if second then 137 else 70
    let s := if second then 4712 else 63277
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j i x, ((Q.coeff j).coeff i).coeff x ≠ 0 → j ≤ b ∧ i+j ≤ s ∧ x+j*d < r*t) ∧
      ∀ z : F, ∀ q : F[X], q.natDegree ≤ d → ∀ B : Finset I, t ≤ B.card →
        (∀ x ∈ B, q.eval (dom x) = u x + z*v x) → Q.eval₂ (evalRingHom (C z)) q = 0 := by
  dsimp only
  let r := if second then 97 else 50
  let b := if second then 137 else 70
  let s := if second then 4712 else 63277
  have hnum : 0 < r ∧ 0 < t ∧ r ≤ s+1 ∧
      Fintype.card I * Fintype.card (JetRows s r) < Fintype.card (Monomials s b d (r*t)) := by
    rw [hn]
    cases second <;> simp only [r,b,s,JetRows,Monomials,Fintype.card_sigma,Fintype.card_prod,
      Fintype.card_fin] <;> decide +kernel
  obtain ⟨c,hc,_,hf⟩ := exists_surface dom u v hnum.1 hnum.2.1 hnum.2.2.1 hnum.2.2.2
  exact ⟨surface c,surface_ne_zero hc,fun _ _ _ h => surface_support c h,
    fun z q hq B hB hg => by rw [surface_eval]; exact hf z q hq B hB hg⟩

/-- Positivity, tame degree and identity tests used in the written argument.
The integer 2^100 is below the designated characteristic. -/
theorem hypotheses : 63277*137+70*4712+1 = cutoff ∧ e/256+1 ≤ cutoff ∧
    t > d+4712*n/cutoff+3*(4712*n/(cutoff-4712)) ∧ 3*core > n+2*d ∧
    n*d < t*t ∧ n+2*d+2*255 < 3*t ∧ 2*(50*t)*70 < 2^100 ∧ cap < 2*n := by decide

private def headMass (j : ℕ) : ℕ :=
  let den := core+(j-1)*d
  let union := (j*core^2+den-1)/den
  if j<3 then j*(e+1) else min (j*(e+1)) (j*n-(j-1)*union)

/-- The geometric height input bounds the sum of all retained pole degrees. -/
def height (b w m : ℕ) : ℕ := (6*b+2)*w*m

/-- The per-factor population bound for each possible primary factor degree. -/
def price (f j b : ℕ) : ℕ :=
  if b≤1 then cutoff else
  let w := 50*t-1-(f-b)*d
  let m := 4712-j
  let g := (2*b-2)*m-b*(b-1)
  let h := height b w m
  let r := (g+m)*n
  let fixed := min 2 j
  let ordinary := (2*t*r+n*(2*h+m*n))/(t*t-n*d)
  let triangle := m*(m-1)+(3-fixed)*(r+h)/(3*t-(n+2*d+fixed*255))
  max cutoff (g+2*b*m+min ordinary triangle)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 50000000 in
-- Check all triples of total, extracted and residual factor degrees.
private theorem finite_price : ∀ f : Fin 71, ∀ j : Fin (f.val+1),
    ∀ b : Fin (f.val-j.val+1),
    let base := headMass j.val+63277
    base ≤ cap ∧ (0 < b.val → (f.val-j.val)*price f.val j.val b.val <
      b.val*(cap-base+1)) := by decide +kernel

/-- The sum over any assignment of sections to factors obeying the local
population bounds is at most 2,131,191,599. -/
theorem allocations {I : Type*} (S : Finset I) (value cost : I → ℕ)
    (f : Fin 71) (j : Fin (f.val+1)) (pos : ∀ i ∈ S, 0 < value i)
    (total : ∑ i ∈ S, value i = f.val-j.val)
    (prices : ∀ i ∈ S, cost i ≤ price f.val j.val (value i)) :
    headMass j.val + 63277 + ∑ i ∈ S, cost i ≤ cap := by
  classical
  let base := headMass j.val+63277
  have enough : base ≤ cap := (finite_price f j 0).1
  by_cases empty : S = ∅
  · simpa [empty] using enough
  have one (i : I) (hi : i ∈ S) : (f.val-j.val)*cost i < value i*(cap-base+1) := by
    have hv := (single_le_sum (fun k _ => Nat.zero_le (value k)) hi).trans_eq total
    exact (Nat.mul_le_mul_left _ (prices i hi)).trans_lt
      ((finite_price f j ⟨value i, by omega⟩).2 (pos i hi))
  have h := sum_lt_sum_of_nonempty (nonempty_iff_ne_empty.mpr empty) one
  rw [← mul_sum,← sum_mul,total] at h
  have hk := Nat.lt_of_mul_lt_mul_left h
  change base + _ ≤ cap
  omega

#print axioms section_slope
#print axioms surfaces
#print axioms hypotheses
#print axioms allocations
end ArkLib.ProximityGap.Frontier.GaussPolarSectionHeights
