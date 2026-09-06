/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowCrossWitness

/-!
# Binary RS realizability as Vandermonde locator divisibility

If three polynomial evaluations take at most two values at every coordinate of a carrier, then
at least one pair agrees at each coordinate.  Hence the carrier locator divides the product of
the three pairwise differences.  This is the direct algebraic constraint behind the saturated
three-rider binary reduction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterBinaryVandermondeDivisibility

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} [NeZero n]

/-- Three-point Vandermonde product. -/
noncomputable def vandermondeThree (p₁ p₂ p₃ : F[X]) : F[X] :=
  (p₁ - p₂) * (p₁ - p₃) * (p₂ - p₃)

/-- **Binary-value locator divisibility.**  Pointwise use of at most two values among three
polynomials forces the carrier locator to divide their Vandermonde product. -/
theorem carrierLocator_dvd_vandermondeThree_of_binary
    (dom : Fin n ↪ F) (Cset : Finset (Fin n)) (p₁ p₂ p₃ : F[X])
    (hbinary : ∀ x ∈ Cset,
      p₁.eval (dom x) = p₂.eval (dom x) ∨
      p₁.eval (dom x) = p₃.eval (dom x) ∨
      p₂.eval (dom x) = p₃.eval (dom x)) :
    (Cset.prod fun x => X - C (dom x)) ∣ vandermondeThree p₁ p₂ p₃ := by
  by_cases hzero : vandermondeThree p₁ p₂ p₃ = 0
  · rw [hzero]
    exact dvd_zero _
  apply ProximityGap.WBPencil.vanishing_prod_dvd dom hzero
  intro x hx
  rcases hbinary x hx with h12 | h13 | h23
  · simp [vandermondeThree, h12]
  · simp [vandermondeThree, h13]
  · simp [vandermondeThree, h23]

/-- Degree of the three-point Vandermonde product for degree-`<k` directions. -/
theorem vandermondeThree_natDegree_le
    (p₁ p₂ p₃ : F[X])
    (h₁ : p₁.natDegree < k) (h₂ : p₂.natDegree < k) (h₃ : p₃.natDegree < k) :
    (vandermondeThree p₁ p₂ p₃).natDegree ≤ 3 * (k - 1) := by
  rw [vandermondeThree]
  calc
    ((p₁ - p₂) * (p₁ - p₃) * (p₂ - p₃)).natDegree ≤
        (p₁ - p₂).natDegree + (p₁ - p₃).natDegree + (p₂ - p₃).natDegree := by
      exact (natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _))
    _ ≤ (k - 1) + (k - 1) + (k - 1) := by
      gcongr
      · exact (natDegree_sub_le _ _).trans (max_le (by omega) (by omega))
      · exact (natDegree_sub_le _ _).trans (max_le (by omega) (by omega))
      · exact (natDegree_sub_le _ _).trans (max_le (by omega) (by omega))
    _ = 3 * (k - 1) := by omega

/-- Above the cubic degree threshold, binary realizability forces two of the three polynomials
to coincide. -/
theorem two_eq_of_binary_of_three_mul_lt_card
    (dom : Fin n ↪ F) (Cset : Finset (Fin n)) (p₁ p₂ p₃ : F[X])
    (h₁ : p₁.natDegree < k) (h₂ : p₂.natDegree < k) (h₃ : p₃.natDegree < k)
    (hbinary : ∀ x ∈ Cset,
      p₁.eval (dom x) = p₂.eval (dom x) ∨
      p₁.eval (dom x) = p₃.eval (dom x) ∨
      p₂.eval (dom x) = p₃.eval (dom x))
    (hlarge : 3 * (k - 1) < Cset.card) :
    p₁ = p₂ ∨ p₁ = p₃ ∨ p₂ = p₃ := by
  have hdvd := carrierLocator_dvd_vandermondeThree_of_binary dom Cset p₁ p₂ p₃ hbinary
  have hlocDegree : (Cset.prod fun x => X - C (dom x)).natDegree = Cset.card := by
    rw [natDegree_prod_of_monic _ _ fun x _ => monic_X_sub_C (dom x)]
    simp
  have hvzero : vandermondeThree p₁ p₂ p₃ = 0 := by
    by_contra hne
    have hdeg := natDegree_le_of_dvd hdvd hne
    rw [hlocDegree] at hdeg
    exact (not_le_of_gt hlarge) (hdeg.trans (vandermondeThree_natDegree_le p₁ p₂ p₃ h₁ h₂ h₃))
  rw [vandermondeThree] at hvzero
  rcases mul_eq_zero.mp hvzero with hprod | h23
  · rcases mul_eq_zero.mp hprod with h12 | h13
    · exact Or.inl (sub_eq_zero.mp h12)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h13))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h23))

/-- At literal P1 parameters the cubic root-count criterion is unavailable: the complement
carrier is strictly smaller than `3(k-1)`. -/
theorem p1_binaryVandermonde_cubic_degree_barrier :
    480946858 < 3 * (268435456 - 1) := by norm_num

/-- **Mason--Stothers direction no-go.**  The carrier radical is already larger than the
maximum degree of one direction difference.  Thus the naive polynomial-abc conclusion
`maxDegree ≤ radicalDegree-1` is numerically compatible and yields no contradiction. -/
theorem p1_mason_carrier_radical_inequality_already_satisfied :
    268435456 - 1 ≤ 480946858 - 1 := by norm_num

/-- The cubic Vandermonde budget is literally the sum of the three pairwise RS root budgets. -/
theorem p1_vandermonde_budget_eq_three_pair_budgets :
    3 * (268435456 - 1) =
      (268435456 - 1) + (268435456 - 1) + (268435456 - 1) := by norm_num

end ArkLib.ProximityGap.Frontier.P1RateQuarterBinaryVandermondeDivisibility

open ArkLib.ProximityGap.Frontier.P1RateQuarterBinaryVandermondeDivisibility

#print axioms carrierLocator_dvd_vandermondeThree_of_binary
#print axioms two_eq_of_binary_of_three_mul_lt_card
#print axioms p1_binaryVandermonde_cubic_degree_barrier
#print axioms p1_mason_carrier_radical_inequality_already_satisfied
#print axioms p1_vandermonde_budget_eq_three_pair_budgets
