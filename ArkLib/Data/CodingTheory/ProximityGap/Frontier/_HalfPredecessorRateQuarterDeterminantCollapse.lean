/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GK16RootCounting
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLineCoreGeometry

/-!
# Rate-quarter determinant collapse for three decoded lines

For a decoded polynomial line `line = (a,r)`, its joint core is the set of coordinates where
the received pair `(u0,u1)` equals `(a,r)`.  Given three lines, form the Pluecker determinant

```text
Delta = (a2-a1)(r3-r1) - (a3-a1)(r2-r1).
```

Every coordinate lying in two line cores is a root of `Delta`.  A coordinate lying in all three
cores is a double root: all four entries of the determinant vanish there.  The root-multiplicity
budget therefore gives

```text
  |pairOverlap| + |tripleOverlap| <= deg Delta <= 2(k-1)
```

unless `Delta = 0`.  Here `pairOverlap` is the union of the three pairwise core intersections,
so the left side counts a coordinate in exactly two cores once and a coordinate in all three
cores twice.  This is precisely `sum_x max(coreMultiplicity(x)-1,0)`.

The conclusion `Delta = 0` is the rational-line collapse from the rate-quarter cocircuit route:
the three polynomial pairs are affinely collinear over `F(X)`.  This file proves the determinant
and multiplicity part only; turning a collapsed cluster into a global scalar injection remains a
separate incidence argument.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- A decoded polynomial line, represented by its intercept and slope polynomials. -/
abbrev PolynomialLine (F : Type) [Semiring F] := F[X] × F[X]

/-- The `2 x 2` determinant of the differences of three polynomial lines. -/
noncomputable def lineDeterminant (line1 line2 line3 : PolynomialLine F) : F[X] :=
  (line2.1 - line1.1) * (line3.2 - line1.2) -
    (line3.1 - line1.1) * (line2.2 - line1.2)

/-- Coordinates belonging to at least two of the three joint cores. -/
def pairOverlap (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 line3 : PolynomialLine F) : Finset ι :=
  (jointCore dom u0 u1 line1.1 line1.2 ∩
      jointCore dom u0 u1 line2.1 line2.2) ∪
    (jointCore dom u0 u1 line1.1 line1.2 ∩
      jointCore dom u0 u1 line3.1 line3.2) ∪
    (jointCore dom u0 u1 line2.1 line2.2 ∩
      jointCore dom u0 u1 line3.1 line3.2)

/-- Coordinates belonging to all three joint cores. -/
def tripleOverlap (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 line3 : PolynomialLine F) : Finset ι :=
  (jointCore dom u0 u1 line1.1 line1.2 ∩
      jointCore dom u0 u1 line2.1 line2.2) ∩
    jointCore dom u0 u1 line3.1 line3.2

/-- The union of the three joint cores. -/
def coreUnion (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 line3 : PolynomialLine F) : Finset ι :=
  jointCore dom u0 u1 line1.1 line1.2 ∪
    jointCore dom u0 u1 line2.1 line2.2 ∪
    jointCore dom u0 u1 line3.1 line3.2

/-- Every triple-overlap coordinate is, in particular, a pair-overlap coordinate. -/
theorem tripleOverlap_subset_pairOverlap
    (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 line3 : PolynomialLine F) :
    tripleOverlap dom u0 u1 line1 line2 line3 ⊆
      pairOverlap dom u0 u1 line1 line2 line3 := by
  intro i hi
  simp only [tripleOverlap, pairOverlap, mem_inter, mem_union] at hi ⊢
  exact Or.inl (Or.inl hi.1)

/-- Exact inclusion-exclusion bookkeeping for three cores.  The weighted overlap plus the
union size equals the sum of the three core sizes. -/
theorem pairOverlap_card_add_tripleOverlap_card_add_coreUnion_card
    (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 line3 : PolynomialLine F) :
    (pairOverlap dom u0 u1 line1 line2 line3).card +
          (tripleOverlap dom u0 u1 line1 line2 line3).card +
        (coreUnion dom u0 u1 line1 line2 line3).card =
      (jointCore dom u0 u1 line1.1 line1.2).card +
          (jointCore dom u0 u1 line2.1 line2.2).card +
        (jointCore dom u0 u1 line3.1 line3.2).card := by
  let D1 := jointCore dom u0 u1 line1.1 line1.2
  let D2 := jointCore dom u0 u1 line2.1 line2.2
  let D3 := jointCore dom u0 u1 line3.1 line3.2
  let P := D1 ∩ D2 ∪ D1 ∩ D3 ∪ D2 ∩ D3
  let T := (D1 ∩ D2) ∩ D3
  let U := D1 ∪ D2 ∪ D3
  have hpoint : ∀ i : ι,
      (if i ∈ P then (1 : Nat) else 0) +
            (if i ∈ T then (1 : Nat) else 0) +
          (if i ∈ U then (1 : Nat) else 0) =
        (if i ∈ D1 then (1 : Nat) else 0) +
            (if i ∈ D2 then (1 : Nat) else 0) +
          (if i ∈ D3 then (1 : Nat) else 0) := by
    intro i
    by_cases h1 : i ∈ D1 <;>
      by_cases h2 : i ∈ D2 <;>
        by_cases h3 : i ∈ D3 <;>
          simp [P, T, U, h1, h2, h3]
  have hsum := Finset.sum_congr rfl fun i (_hi : i ∈ (Finset.univ : Finset ι)) => hpoint i
  simp only [Finset.sum_add_distrib] at hsum
  have hcard (S : Finset ι) :
      (∑ i : ι, if i ∈ S then (1 : Nat) else 0) = S.card := by
    simpa using (Finset.card_filter (fun i : ι => i ∈ S) Finset.univ).symm
  rw [hcard P, hcard T, hcard U, hcard D1, hcard D2, hcard D3] at hsum
  simpa only [pairOverlap, tripleOverlap, coreUnion, D1, D2, D3, P, T, U] using hsum

/-- A pair-overlap coordinate is a root of the three-line determinant. -/
theorem lineDeterminant_eval_eq_zero_of_mem_pairOverlap
    (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 line3 : PolynomialLine F) {i : ι}
    (hi : i ∈ pairOverlap dom u0 u1 line1 line2 line3) :
    (lineDeterminant line1 line2 line3).eval (dom i) = 0 := by
  simp only [pairOverlap, mem_union, mem_inter] at hi
  simp only [lineDeterminant, eval_sub, eval_mul]
  rcases hi with (hi12 | hi13) | hi23
  · simp only [jointCore, mem_filter, mem_univ, true_and] at hi12
    rw [hi12.1.1, hi12.2.1, hi12.1.2, hi12.2.2]
    ring
  · simp only [jointCore, mem_filter, mem_univ, true_and] at hi13
    rw [hi13.1.1, hi13.2.1, hi13.1.2, hi13.2.2]
    ring
  · simp only [jointCore, mem_filter, mem_univ, true_and] at hi23
    rw [hi23.1.1, hi23.2.1, hi23.1.2, hi23.2.2]
    ring

/-- Every pair-overlap coordinate contributes at least one unit of root multiplicity. -/
theorem one_le_rootMultiplicity_lineDeterminant_of_mem_pairOverlap
    (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 line3 : PolynomialLine F)
    (hne : lineDeterminant line1 line2 line3 ≠ 0) {i : ι}
    (hi : i ∈ pairOverlap dom u0 u1 line1 line2 line3) :
    1 ≤ (lineDeterminant line1 line2 line3).rootMultiplicity (dom i) := by
  apply (Polynomial.le_rootMultiplicity_iff hne).mpr
  simpa using Polynomial.dvd_iff_isRoot.mpr
    (lineDeterminant_eval_eq_zero_of_mem_pairOverlap dom u0 u1 line1 line2 line3 hi)

/-- Every triple-overlap coordinate is a double root of the three-line determinant. -/
theorem two_le_rootMultiplicity_lineDeterminant_of_mem_tripleOverlap
    (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 line3 : PolynomialLine F)
    (hne : lineDeterminant line1 line2 line3 ≠ 0) {i : ι}
    (hi : i ∈ tripleOverlap dom u0 u1 line1 line2 line3) :
    2 ≤ (lineDeterminant line1 line2 line3).rootMultiplicity (dom i) := by
  simp only [tripleOverlap, mem_inter, jointCore, mem_filter, mem_univ, true_and] at hi
  let L : F[X] := X - C (dom i)
  have ha21 : L ∣ line2.1 - line1.1 := by
    have hev : (line2.1 - line1.1).eval (dom i) = 0 := by
      simp only [eval_sub]
      rw [hi.1.2.1, hi.1.1.1]
      ring
    simpa only [L] using Polynomial.dvd_iff_isRoot.mpr hev
  have ha31 : L ∣ line3.1 - line1.1 := by
    have hev : (line3.1 - line1.1).eval (dom i) = 0 := by
      simp only [eval_sub]
      rw [hi.2.1, hi.1.1.1]
      ring
    simpa only [L] using Polynomial.dvd_iff_isRoot.mpr hev
  have hr21 : L ∣ line2.2 - line1.2 := by
    have hev : (line2.2 - line1.2).eval (dom i) = 0 := by
      simp only [eval_sub]
      rw [hi.1.2.2, hi.1.1.2]
      ring
    simpa only [L] using Polynomial.dvd_iff_isRoot.mpr hev
  have hr31 : L ∣ line3.2 - line1.2 := by
    have hev : (line3.2 - line1.2).eval (dom i) = 0 := by
      simp only [eval_sub]
      rw [hi.2.2, hi.1.1.2]
      ring
    simpa only [L] using Polynomial.dvd_iff_isRoot.mpr hev
  obtain ⟨A21, hA21⟩ := ha21
  obtain ⟨A31, hA31⟩ := ha31
  obtain ⟨R21, hR21⟩ := hr21
  obtain ⟨R31, hR31⟩ := hr31
  have hfirst : L ^ 2 ∣
      (line2.1 - line1.1) * (line3.2 - line1.2) := by
    refine ⟨A21 * R31, ?_⟩
    rw [hA21, hR31]
    ring
  have hsecond : L ^ 2 ∣
      (line3.1 - line1.1) * (line2.2 - line1.2) := by
    refine ⟨A31 * R21, ?_⟩
    rw [hA31, hR21]
    ring
  apply (Polynomial.le_rootMultiplicity_iff hne).mpr
  simpa only [lineDeterminant, L] using dvd_sub hfirst hsecond

/-- The determinant of three degree-`<k` polynomial lines has degree at most `2(k-1)`. -/
theorem lineDeterminant_natDegree_le_two_mul_pred
    {k : Nat} (hk : 1 ≤ k)
    (line1 line2 line3 : PolynomialLine F)
    (hdeg : ∀ line ∈ ({line1, line2, line3} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k) :
    (lineDeterminant line1 line2 line3).natDegree ≤ 2 * (k - 1) := by
  have h1 := hdeg line1 (by simp)
  have h2 := hdeg line2 (by simp)
  have h3 := hdeg line3 (by simp)
  have ha21 : (line2.1 - line1.1).natDegree ≤ k - 1 := by
    exact le_trans (Polynomial.natDegree_sub_le _ _) (by omega)
  have ha31 : (line3.1 - line1.1).natDegree ≤ k - 1 := by
    exact le_trans (Polynomial.natDegree_sub_le _ _) (by omega)
  have hr21 : (line2.2 - line1.2).natDegree ≤ k - 1 := by
    exact le_trans (Polynomial.natDegree_sub_le _ _) (by omega)
  have hr31 : (line3.2 - line1.2).natDegree ≤ k - 1 := by
    exact le_trans (Polynomial.natDegree_sub_le _ _) (by omega)
  apply le_trans (Polynomial.natDegree_sub_le _ _)
  apply max_le
  · exact le_trans Polynomial.natDegree_mul_le (by omega)
  · exact le_trans Polynomial.natDegree_mul_le (by omega)

/-- **Weighted overlap budget.**  If the three-line determinant is nonzero, a coordinate in
exactly two joint cores consumes one degree and a coordinate in all three consumes two degrees. -/
theorem pairOverlap_card_add_tripleOverlap_card_le_natDegree
    (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 line3 : PolynomialLine F)
    (hne : lineDeterminant line1 line2 line3 ≠ 0) :
    (pairOverlap dom u0 u1 line1 line2 line3).card +
        (tripleOverlap dom u0 u1 line1 line2 line3).card ≤
      (lineDeterminant line1 line2 line3).natDegree := by
  let P := pairOverlap dom u0 u1 line1 line2 line3
  let T := tripleOverlap dom u0 u1 line1 line2 line3
  let Delta := lineDeterminant line1 line2 line3
  have hpoint : ∀ i : ι,
      (if i ∈ P then 1 else 0) + (if i ∈ T then 1 else 0) ≤
        Delta.rootMultiplicity (dom i) := by
    intro i
    by_cases hiT : i ∈ T
    · have hiP : i ∈ P := by
        exact tripleOverlap_subset_pairOverlap dom u0 u1 line1 line2 line3 hiT
      simp only [hiP, hiT, if_true]
      exact two_le_rootMultiplicity_lineDeterminant_of_mem_tripleOverlap
        dom u0 u1 line1 line2 line3 hne hiT
    · by_cases hiP : i ∈ P
      · simp only [hiP, hiT, if_true, if_false, add_zero]
        exact one_le_rootMultiplicity_lineDeterminant_of_mem_pairOverlap
          dom u0 u1 line1 line2 line3 hne hiP
      · simp only [hiP, hiT, if_false, zero_add]
        exact Nat.zero_le _
  have hsum :
      (∑ i : ι, ((if i ∈ P then 1 else 0) + (if i ∈ T then 1 else 0))) ≤
        ∑ i : ι, Delta.rootMultiplicity (dom i) := by
    exact Finset.sum_le_sum fun i _ => hpoint i
  have hleft :
      (∑ i : ι, ((if i ∈ P then 1 else 0) + (if i ∈ T then 1 else 0))) =
        P.card + T.card := by
    simp only [Finset.sum_add_distrib]
    simp [P, T]
  have hdomain :
      (∑ i : ι, Delta.rootMultiplicity (dom i)) =
        ∑ x ∈ (Finset.univ.image dom), Delta.rootMultiplicity x := by
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact dom.injective hij
  rw [hleft, hdomain] at hsum
  exact hsum.trans (Polynomial.sum_rootMultiplicity_le_natDegree Delta hne _)

/-- A noncollapsed degree-`<k` triple has weighted overlap at most `2(k-1)`. -/
theorem pairOverlap_card_add_tripleOverlap_card_le_two_mul_pred
    {k : Nat} (hk : 1 ≤ k)
    (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 line3 : PolynomialLine F)
    (hdeg : ∀ line ∈ ({line1, line2, line3} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hne : lineDeterminant line1 line2 line3 ≠ 0) :
    (pairOverlap dom u0 u1 line1 line2 line3).card +
        (tripleOverlap dom u0 u1 line1 line2 line3).card ≤
      2 * (k - 1) :=
  (pairOverlap_card_add_tripleOverlap_card_le_natDegree
    dom u0 u1 line1 line2 line3 hne).trans
      (lineDeterminant_natDegree_le_two_mul_pred hk line1 line2 line3 hdeg)

/-- **Three-line determinant-collapse dichotomy.**  More than `2(k-1)` weighted overlap
forces the three decoded polynomial pairs onto one rational affine line. -/
theorem lineDeterminant_eq_zero_of_two_mul_pred_lt_weighted_overlap
    {k : Nat} (hk : 1 ≤ k)
    (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 line3 : PolynomialLine F)
    (hdeg : ∀ line ∈ ({line1, line2, line3} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hlarge : 2 * (k - 1) <
      (pairOverlap dom u0 u1 line1 line2 line3).card +
        (tripleOverlap dom u0 u1 line1 line2 line3).card) :
    lineDeterminant line1 line2 line3 = 0 := by
  by_contra hne
  exact (not_lt_of_ge
    (pairOverlap_card_add_tripleOverlap_card_le_two_mul_pred
      hk dom u0 u1 line1 line2 line3 hdeg hne)) hlarge

/-- **Core-sum form of determinant collapse.**  If the three core cardinalities exceed their
union by more than `2(k-1)`, then the three polynomial lines have zero determinant.  This is the
literal root-multiplicity inequality used by the rate-quarter cocircuit recursion. -/
theorem lineDeterminant_eq_zero_of_two_mul_pred_add_coreUnion_lt_coreSum
    {k : Nat} (hk : 1 ≤ k)
    (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 line3 : PolynomialLine F)
    (hdeg : ∀ line ∈ ({line1, line2, line3} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hlarge :
      2 * (k - 1) + (coreUnion dom u0 u1 line1 line2 line3).card <
        (jointCore dom u0 u1 line1.1 line1.2).card +
            (jointCore dom u0 u1 line2.1 line2.2).card +
          (jointCore dom u0 u1 line3.1 line3.2).card) :
    lineDeterminant line1 line2 line3 = 0 := by
  apply lineDeterminant_eq_zero_of_two_mul_pred_lt_weighted_overlap
    hk dom u0 u1 line1 line2 line3 hdeg
  have hid := pairOverlap_card_add_tripleOverlap_card_add_coreUnion_card
    dom u0 u1 line1 line2 line3
  omega

/-- **Three half-domain cores collapse.**  At length `2h` and rate at most `1/4`, three
degree-`<k` decoded lines whose joint cores each contain at least `h` coordinates necessarily
have zero determinant.  In particular, three maximum-core equality clusters in the sharp
two-line packing configuration cannot be rationally independent. -/
theorem lineDeterminant_eq_zero_of_three_halfSized_cores
    {k h : Nat} (hk : 1 ≤ k)
    (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 line3 : PolynomialLine F)
    (hn : Fintype.card ι = 2 * h) (hrate : 2 * k ≤ h)
    (hdeg : ∀ line ∈ ({line1, line2, line3} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hcore1 : h ≤ (jointCore dom u0 u1 line1.1 line1.2).card)
    (hcore2 : h ≤ (jointCore dom u0 u1 line2.1 line2.2).card)
    (hcore3 : h ≤ (jointCore dom u0 u1 line3.1 line3.2).card) :
    lineDeterminant line1 line2 line3 = 0 := by
  apply lineDeterminant_eq_zero_of_two_mul_pred_add_coreUnion_lt_coreSum
    hk dom u0 u1 line1 line2 line3 hdeg
  have hU : (coreUnion dom u0 u1 line1 line2 line3).card ≤ 2 * h := by
    rw [← hn]
    exact Finset.card_le_univ _
  omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse

/-! ## Axiom audit -/

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse.two_le_rootMultiplicity_lineDeterminant_of_mem_tripleOverlap
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse.pairOverlap_card_add_tripleOverlap_card_le_natDegree
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse.lineDeterminant_eq_zero_of_two_mul_pred_lt_weighted_overlap
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse.lineDeterminant_eq_zero_of_two_mul_pred_add_coreUnion_lt_coreSum
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse.lineDeterminant_eq_zero_of_three_halfSized_cores
