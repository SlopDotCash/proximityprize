/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticInterpolation
import ArkLib.Research.ProximityGap.Frontier.ThreeHeadDeterminantCover
import ArkLib.Research.ProximityGap.Frontier.HodgeSectionVariance

/-! # The three-head cutoff through dimension 71,582,789

The actual double interpolation, numerical bounds for the geometric component
estimate, and the final noncollinear cover are separate results. The geometric
implication used between these steps is given in the accompanying proof.
-/
set_option autoImplicit false
open Finset Polynomial
namespace ArkLib.ProximityGap.Frontier.SixthDegreeThreeHeadWindow

private abbrev n : ℕ := 1073741824
private abbrev t : ℕ := 357913943
private abbrev d : ℕ := 71582788
private abbrev e : ℕ := n-t
private abbrev cutoff : ℕ := 5000000
private abbrev core : ℕ := t-e/(cutoff-1)

/-- A single multiplicity-two interpolant contains every candidate at the
specified agreement through message dimension 71,582,789. -/
theorem surface {F I : Type} [Field F] [Fintype I] (dom : I ↪ F) (u v : I → F)
    (hn : Fintype.card I = n) :
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → j ≤ 6 ∧ i+j ≤ 25 ∧ a+j*d < 2*t) ∧
      ∀ z : F, ∀ q : F[X], q.natDegree ≤ d → ∀ S : Finset I, t ≤ S.card →
        (∀ i ∈ S, q.eval (dom i) = u i + z*v i) → Q.eval₂ (evalRingHom (C z)) q = 0 := by
  open SecondPrimeQuarticInterpolation in
    obtain ⟨c,hc,hall⟩ := exists_curve_double (s:=25) (v:=6) (d:=d) (t:=t)
      dom u v (by decide) (by decide) (by
        rw [hn]
        simp only [Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
        norm_num [Fin.sum_univ_succ, n, t, d])
    refine ⟨SecondPrimeQuarticInterpolation.surface c, surface_ne_zero hc,
      fun _ _ _ h => surface_support c h, ?_⟩
    intro z q hq S hS ha
    rw [surface_eval]
    exact hall _ _ hq _ hS ha

private def componentCap (b : ℕ) : ℕ :=
  let x := (2*b-2)*25-b*(b-1)+1
  let z := (2*b-2)*(2*t-1)-b*(b-1)*d+1
  x+((8*25*b+2)*x*z+2*25*n+(n-d)*26)/(t-d)

/-- Each nonlinear factor in the written surface population estimate costs
less than five million labels, even using the entire interpolant weight. -/
theorem component_bounds (b : ℕ) (hb : 2 ≤ b) (hb' : b ≤ 6) :
    componentCap b < cutoff := by
  have cert : ∀ i : Fin 7, 2 ≤ i.val → componentCap i.val < cutoff := by decide
  exact cert ⟨b, by omega⟩ hb

private def collinearCap (j : ℕ) : ℕ :=
  let union := j*core-j.choose 2*d
  j*n-(j-1)*union

/-- The collinear joint-core bound has ample slack throughout the six slots. -/
theorem collinear_allocation (j : ℕ) (hj : 3 ≤ j) (hj' : j ≤ 6) :
    collinearCap j+(6-j)*cutoff+25 ≤ 1518239425 := by
  have cert : ∀ i : Fin 7, 3 ≤ i.val →
      collinearCap i.val+(6-i.val)*cutoff+25 ≤ 1518239425 := by decide
  exact cert ⟨j, by omega⟩ hj

/-- Four large cores force collinearity, and the identity-site test for a
value-linear factor succeeds at the same population cutoff. -/
theorem large_core_checks :
    n+4*d < 4*core ∧ d < t-25*n/cutoff-3*(25*n/(cutoff-25)) := by decide

/-- A budget violation with three large heads forces each of their cores to
contain at least t−1 sites. L counts the labels assigned to the specified head. -/
theorem exceptional_core (c L : ℕ)
    (hbig : 2*n < 2*(e+1)+L+3*cutoff+25)
    (hfresh : L*max 1 (t-c) ≤ n-c) : t-1 ≤ c := by
  by_contra! small
  have two : 2 ≤ max 1 (t-c) := (show 2 ≤ t-c by omega).trans (le_max_right ..)
  have h := (Nat.mul_le_mul_left L two).trans hfresh
  have hu : L*2 ≤ 1073741824 := h.trans (Nat.sub_le n c)
  change 2147483648 < 2*(715827881+1)+L+3*5000000+25 at hbig
  omega

/-- At the next degree the strict determinant-cover arithmetical test is an
equality when each of the three cores has exactly t−1 sites. -/
theorem cover_degree_limit : n+5*d < 4*t-3 ∧ n+5*(d+1) = 4*t-3 := by decide

open Code HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines
open HalfPredecessorRateEighthFullWiring HalfPredecessorLineCoreGeometry
open HalfPredecessorRateQuarterDeterminantMultiplicity
open scoped NNReal

/-- The three actual secants cover every selected scalar once their core
populations reach the bound forced by the factor allocation. -/
theorem cover {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F]
    [Fintype F] [DecidableEq F] {K : ℕ} {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily dom K δ u) (hk : 1 ≤ K) (hdeg : K ≤ 71582789)
    (hn : Fintype.card I = n) (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊ = t)
    (a b c : LineParameter F) (ha : a ∈ lineParameters fam) (hb : b ∈ lineParameters fam)
    (hc : c ∈ lineParameters fam) (det : threeLineDeterminant a b c ≠ 0)
    (cores : ∀ x ∈ ({a,b,c} : Finset _), t-1 ≤ (jointCore dom (u 0) (u 1) x.1 x.2).card) :
    fam.G ⊆ pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c := by
  apply ThreeHeadDeterminantCover.cover_of_three_noncollinear fam hk a b c ha hb hc det
  have h₁ := cores a (by simp)
  have h₂ := cores b (by simp)
  have h₃ := cores c (by simp)
  rw [ht,hn]
  dsimp [n,t] at *
  omega

#print axioms surface
#print axioms collinear_allocation
#print axioms exceptional_core
#print axioms cover
end ArkLib.ProximityGap.Frontier.SixthDegreeThreeHeadWindow
