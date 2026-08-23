/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKC12TranslateIntersectionReduction

/-!
# The cyclotomic half-cap and its alignment limitation

Betsumiya--Hirasaka--Komatsu--Munemasa prove that a cyclotomic number attached to a
subgroup of order `n` is at most `ceil(n/2)` when the field characteristic satisfies
`p > 3*n/2 - 1`.  Both certified production primes satisfy this hypothesis by a vast margin.
After identifying the nonzero values of the marked-difference row

`W_G(t) = #{(x,y) in G^2 : 2*y-x=t}`

with cyclotomic intersection numbers, their theorem therefore suggests the strong pointwise
input `W_G(t) <= n/2`.

This file audits the direction of that input.  Even granting the exact row mass, two occupied
classes, the half cap, and the complete marginal square mass, the cross alignment with a second
row can still be either zero or maximal.  The four-cell witness below is already at the exact
production scale.  Hence the cyclotomic half-cap is useful structural information, but it cannot
by itself prove the lower bound on `C12 = sum_t W_G(t) R_r(t)`.  One still needs correlated
placement of the actual adjacent-rank row `R_r`.

No formalization of the cited cyclotomic-number theorem is claimed here.  This is an exact
arithmetic applicability check and a sharp information-theoretic no-go for using its conclusion
alone.  Issue #466.
-/

set_option autoImplicit false
set_option exponentiation.threshold 1024

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKC12CyclotomicHalfCapNoGo

open ArkLib.ProximityGap.Frontier.BGKC12TranslateIntersectionReduction

/-! ## The marked row is literally a cyclotomic plus-one intersection -/

section CyclotomicIdentification

variable {F : Type*} [Field F] [DecidableEq F]

/-- Multiplicative dilation of a finite set. -/
def scaledFinset (c : F) (G : Finset F) : Finset F :=
  G.image fun x => c * x

/-- The ordinary cyclotomic-number shape `#{z in A : z+1 in B}`. -/
def plusOneIntersection (A B : Finset F) : Nat :=
  (A.filter fun z => z + 1 ∈ B).card

/-- **Exact cyclotomic identification.**  Away from `t=0` and characteristic two, the marked
difference row is a plus-one intersection between the two multiplicative dilates
`(-2/t)G` and `(-1/t)G`.  Thus any theorem uniformly bounding cyclotomic numbers applies to the
nonzero `W_G(t)` values with no loss or analogy. -/
theorem doubledTranslateIntersection_eq_scaled_plusOneIntersection
    (G : Finset F) {t : F} (ht : t ≠ 0) (h2 : (2 : F) ≠ 0) :
    doubledTranslateIntersection G t =
      plusOneIntersection (scaledFinset ((-2 : F) / t) G)
        (scaledFinset ((-1 : F) / t) G) := by
  classical
  unfold doubledTranslateIntersection plusOneIntersection scaledFinset
  refine Finset.card_bij (fun y _hy => ((-2 : F) / t) * y) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_image.mpr ⟨y, hy.1, rfl⟩, ?_⟩
    refine Finset.mem_image.mpr ⟨2 * y - t, hy.2, ?_⟩
    field_simp
    ring
  · intro y hy y' hy' heq
    apply mul_left_cancel₀ (div_ne_zero (neg_ne_zero.mpr h2) ht)
    exact heq
  · intro z hz
    simp only [Finset.mem_filter] at hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz.1
    obtain ⟨x, hx, hEq⟩ := Finset.mem_image.mp hz.2
    have hphase :
        ((-2 : F) / t) * y + 1 = ((-1 : F) / t) * (2 * y - t) := by
      field_simp
      ring
    have hb : ((-1 : F) / t) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr one_ne_zero) ht
    have hxEq : x = 2 * y - t := by
      apply mul_left_cancel₀ hb
      exact hEq.trans hphase
    refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, rfl⟩
    exact hxEq ▸ hx

end CyclotomicIdentification

/-! ## The production primes lie in the half-cap regime -/

/-- Production subgroup order, repeated locally to keep this scratch lane olean-independent. -/
def productionN : Nat := 2 ^ 30

/-- First certified production prime, repeated as an integer for the applicability audit. -/
def productionP1 : Nat := productionN * (2 ^ 128 + 192) + 1

/-- Second certified production prime. -/
def productionP2 : Nat := productionN * (2 ^ 129 + 13) + 1

/-- The exact half of the production subgroup order. -/
def productionHalf : Nat := 2 ^ 29

theorem productionN_eq_twice_half : productionN = 2 * productionHalf := by
  norm_num [productionN, productionHalf]

/-- Denominator-free form of `p > 3*n/2 - 1` for both certified production primes. -/
theorem production_primes_in_cyclotomic_halfCap_range :
    3 * productionN < 2 * (productionP1 + 1) /\
      3 * productionN < 2 * (productionP2 + 1) := by
  norm_num [productionN, productionP1, productionP2]

/-! ## Exact capped-row countermodel -/

/-- Two half-mass atoms in the first two cyclotomic classes. -/
def leftHalfRow : Fin 4 → Nat :=
  ![productionHalf, productionHalf, 0, 0]

/-- A right row aligned with the same two classes. -/
def alignedHalfRow : Fin 4 → Nat :=
  ![productionHalf, productionHalf, 0, 0]

/-- The same right marginal placed on the other two classes. -/
def disjointHalfRow : Fin 4 → Nat :=
  ![0, 0, productionHalf, productionHalf]

theorem leftHalfRow_mass :
    ∑ i : Fin 4, leftHalfRow i = productionN := by
  norm_num [leftHalfRow, productionHalf, productionN, Fin.sum_univ_succ]

theorem alignedHalfRow_mass :
    ∑ i : Fin 4, alignedHalfRow i = productionN := by
  norm_num [alignedHalfRow, productionHalf, productionN, Fin.sum_univ_succ]

theorem disjointHalfRow_mass :
    ∑ i : Fin 4, disjointHalfRow i = productionN := by
  norm_num [disjointHalfRow, productionHalf, productionN, Fin.sum_univ_succ]

/-- Every entry obeys the proposed cyclotomic half cap. -/
theorem all_rows_pointwise_half_capped :
    (∀ i, leftHalfRow i ≤ productionHalf) /\
      (∀ i, alignedHalfRow i ≤ productionHalf) /\
      (∀ i, disjointHalfRow i ≤ productionHalf) := by
  constructor
  · intro i
    fin_cases i <;> simp [leftHalfRow]
  constructor
  · intro i
    fin_cases i <;> simp [alignedHalfRow]
  · intro i
    fin_cases i <;> simp [disjointHalfRow]

/-- The aligned and disjoint right rows have identical complete `L2` marginal data. -/
theorem right_rows_squareMass_equal :
    (∑ i : Fin 4, alignedHalfRow i ^ 2) =
      ∑ i : Fin 4, disjointHalfRow i ^ 2 := by
  norm_num [alignedHalfRow, disjointHalfRow, Fin.sum_univ_succ]

/-- Alignment attains the largest value compatible with these two half atoms. -/
theorem aligned_cross_inner_exact :
    (∑ i : Fin 4, leftHalfRow i * alignedHalfRow i) =
      2 * productionHalf ^ 2 := by
  norm_num [leftHalfRow, alignedHalfRow, Fin.sum_univ_succ]
  ring

/-- Moving only the right row to two other classes annihilates the cross alignment. -/
theorem disjoint_cross_inner_exact :
    (∑ i : Fin 4, leftHalfRow i * disjointHalfRow i) = 0 := by
  norm_num [leftHalfRow, disjointHalfRow, Fin.sum_univ_succ]

/-- **Half-cap no-go.**  Exact mass, the production half cap, and identical marginal square
mass do not force any positive cross correlation. -/
theorem cyclotomic_halfCap_does_not_force_positive_alignment :
    (∑ i : Fin 4, leftHalfRow i) = productionN /\
    (∑ i : Fin 4, alignedHalfRow i) =
      (∑ i : Fin 4, disjointHalfRow i) /\
    (∀ i, leftHalfRow i ≤ productionHalf) /\
    (∀ i, alignedHalfRow i ≤ productionHalf) /\
    (∀ i, disjointHalfRow i ≤ productionHalf) /\
    (∑ i : Fin 4, alignedHalfRow i ^ 2) =
      (∑ i : Fin 4, disjointHalfRow i ^ 2) /\
    (∑ i : Fin 4, leftHalfRow i * alignedHalfRow i) =
      2 * productionHalf ^ 2 /\
    (∑ i : Fin 4, leftHalfRow i * disjointHalfRow i) = 0 := by
  refine ⟨leftHalfRow_mass, alignedHalfRow_mass.trans disjointHalfRow_mass.symm, ?_⟩
  exact ⟨all_rows_pointwise_half_capped.1,
    all_rows_pointwise_half_capped.2.1,
    all_rows_pointwise_half_capped.2.2,
    right_rows_squareMass_equal,
    aligned_cross_inner_exact,
    disjoint_cross_inner_exact⟩

/-! ## Axiom audit -/

#print axioms production_primes_in_cyclotomic_halfCap_range
#print axioms doubledTranslateIntersection_eq_scaled_plusOneIntersection
#print axioms cyclotomic_halfCap_does_not_force_positive_alignment

end ArkLib.ProximityGap.Frontier.BGKC12CyclotomicHalfCapNoGo
