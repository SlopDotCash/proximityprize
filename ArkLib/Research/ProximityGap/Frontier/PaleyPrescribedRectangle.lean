/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import Mathlib.Tactic.NormNum.Prime
import ArkLib.ToMathlib.Polynomial.RootMultiplicity
import ArkLib.Research.ProximityGap.Frontier.PaleyHankelDegree
import ArkLib.Research.ProximityGap.Frontier.PaleyInterpolationContact
import ArkLib.Research.ProximityGap.Frontier.PaleyDefectDiscrepancy

/-!
# A finite discrepancy bound at the specified Paley rectangle
-/

namespace ProximityGap.PaleyPrescribedRectangle

open Finset Polynomial PaleyDefectDiscrepancy PaleyDefectMinor PaleyHankelDegree
open PaleyInterpolationContact
open scoped Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- Per-sign sums of local multiplicities fit in the degree of the signed
interpolation determinant, for every specified set of shifts. -/
theorem sign_charge_le (hp : p ≠ 2) (A B : Finset (ZMod p))
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p/2+1) {x : ℕ} (hx : 0 < x) (hx' : 2*x ≤ A.card)
    {σ : ℤ} (hs : σ=1 ∨ σ=-1) :
    ∑ b ∈ B, charge A.card x (defects A σ b) ≤ x*(p/2+1-x) := by
  let D := p/2+(A.card-1)
  let h := x-1
  let F := powerSum A A D - C (σ : ZMod p)
  let P := (normalizedHankel F D h).det
  have hprime := (Fact.out : p.Prime).two_le
  obtain ⟨v,hv⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have hd : D < p := by dsimp [D]; omega
  have hdeg := (powerSum_degree A ha (D := D) (by dsimp [D]; omega) hd).1
  have hF : F.natDegree = p/2 := by dsimp [F]; rw [natDegree_sub_C,hdeg]; dsimp [D]; omega
  have hne : F ≠ 0 := by intro he; rw [he, natDegree_zero] at hF; omega
  have hl : 2*h ≤ F.natDegree := by rw [hF]; dsimp [h]; omega
  have hupper : F.natDegree ≤ D := by rw [hF]; dsimp [D]; omega
  have hgap : h ≤ D-F.natDegree := by rw [hF]; dsimp [D,h]; omega
  have hP : P ≠ 0 := normalizedHankel_det_ne_zero F hne D h hl hupper hgap hd
  have hPd : P.natDegree = x*(p/2+1-x) := by
    rw [show P.natDegree = _ from normalizedHankel_det_degree F hne D h hl hupper hgap hd, hF]
    dsimp [h]
    congr 1 <;> omega
  rw [← hPd]
  refine (Finset.sum_le_sum fun b (_ : b ∈ B) => ?_).trans
    (Polynomial.sum_rootMultiplicity_le_natDegree (W := P) B)
  apply (le_rootMultiplicity_iff hP).mpr
  let e := defects A σ b
  let ν := if -b ∈ A then A.card-1 else A.card-1+1
  have hn : 2*h ≤ ν := by dsimp [h,ν]; split <;> omega
  have hlocal := minority_determinant hp A b (k := A.card-1) (h := h)
    (by omega) hd hn hs
  let r := x-e
  have hlocal' : (X-C b)^(r*(ν-2*h)+r*(r-1)) ∣ P := by
    simpa [r, e, defects, h, ν, D, P, F, show x-1+1=x by omega] using hlocal
  refine dvd_trans (pow_dvd_pow (X-C b) ?_) hlocal'
  change (x-e)*(A.card-x-e) ≤ r*(ν-2*h)+r*(r-1)
  rw [← Nat.mul_add]
  by_cases he : e < x
  · apply Nat.mul_le_mul_left
    dsimp [ν,h,r]
    split <;> omega
  · have hzero : r=0 := by dsimp [r]; omega
    simp [hzero, show x-e=0 by omega]

/-- Explicit finite bound for arbitrary prescribed prime-field sets. -/
theorem discrepancy_sq (hp : p ≠ 2) (A B : Finset (ZMod p))
    (ha : 2 ≤ A.card) (ha' : A.card ≤ p/2+1) {x : ℕ} (hx : 0 < x) (hx' : 2*x ≤ A.card) :
    (|∑ b ∈ B, ∑ u ∈ A, quadraticChar (ZMod p) (b+u)| +
      ((B.filter fun b => -b ∈ A).card : ℤ))^2 ≤
        (B.card : ℤ)^2 * ((A.card : ℤ)-2*x)^2 + 4*B.card*(x*(p/2+1-x) : ℕ) :=
  discrepancy_sq_of_budgets A B x _ hx' fun _ hs => sign_charge_le hp A B ha ha' hx hx' hs

local instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- All 256-by-256 rectangles in the field of order 65537 have at most this
signed excess, including the diagonal correction. -/
theorem discrepancy_65537 (A B : Finset (ZMod 65537)) (ha : A.card = 256) (hb : B.card = 256) :
    |∑ b ∈ B, ∑ u ∈ A, quadraticChar (ZMod 65537) (b+u)| +
        ((B.filter fun b => -b ∈ A).card : ℤ) ≤ 56719 := by
  have hw := discrepancy_sq (p := 65537) (by decide) A B (by omega) (by omega)
    (x := 64) (by decide) (by omega)
  rw [ha,hb] at hw
  let s := |∑ b ∈ B, ∑ u ∈ A, quadraticChar (ZMod 65537) (b+u)| +
    ((B.filter fun b => -b ∈ A).card : ℤ)
  change s^2 ≤ 3217096704 at hw
  change s ≤ 56719
  by_contra! he
  have hbig : (56720 : ℤ)^2 ≤ s^2 := pow_le_pow_left₀ (by decide) (by omega) 2
  omega

end ProximityGap.PaleyPrescribedRectangle

#print axioms ProximityGap.PaleyPrescribedRectangle.discrepancy_sq

#print axioms ProximityGap.PaleyPrescribedRectangle.discrepancy_65537
