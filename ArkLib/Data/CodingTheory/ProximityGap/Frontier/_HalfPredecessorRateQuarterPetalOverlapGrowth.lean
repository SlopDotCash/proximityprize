/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorSecantLines

/-!
# Rate-quarter half predecessor: petal overlap and union growth

For three decoded-line cores `D0,D1,D2`, write the two petals outside the
reference core as

```text
  P1 = D1 \ D0,    P2 = D2 \ D0.
```

The determinant multiplicity appearing in the three-line collapse theorem has
the exact decomposition

```text
weightedOverlap(D0,D1,D2)
  = |D0 inter D1| + |D0 inter D2| + |P1 inter P2|.
```

Thus a noncollapsed triple has the concrete petal-overlap cap

```text
|P1 inter P2| <= 2(k-1) - |D0 inter D1| - |D0 inter D2|,
```

while violation forces determinant collapse.  Combining this identity with
`|P1 union P2| + |P1 inter P2| = |P1| + |P2|` gives the exact union-growth
recurrence

```text
|P1| + |P2| + |D0 inter D1| + |D0 inter D2|
  <= 2(k-1) + |P1 union P2|.
```

The last theorem specializes the result to canonical secants of a selected
rich-point family.  This advances the fresh-petal pruning branch but does not
close it: a global iteration still needs either lower bounds on the two base
intersections or a rule selecting many noncollapsed petals.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalOverlapGrowth

attribute [local instance] Classical.propDecidable

/-! ## Exact finite-set bookkeeping -/

variable {U : Type} [Fintype U] [DecidableEq U]

/-- The part of `D1` outside the reference core `D0`. -/
def corePetal (D0 D1 : Finset U) : Finset U := D1 \ D0

/-- **Exact petal decomposition of weighted three-core overlap.**  The union
of pair intersections counts a coordinate in exactly two cores once and a
triple-core coordinate once; the additional triple intersection counts the
latter a second time.  Splitting relative to `D0` gives the right-hand side. -/
theorem weightedOverlap_eq_base_add_base_add_petalInter
    (D0 D1 D2 : Finset U) :
    ((D0 ∩ D1) ∪ (D0 ∩ D2) ∪ (D1 ∩ D2)).card +
        ((D0 ∩ D1) ∩ D2).card =
      (D0 ∩ D1).card + (D0 ∩ D2).card +
        (corePetal D0 D1 ∩ corePetal D0 D2).card := by
  let W := (D0 ∩ D1) ∪ (D0 ∩ D2) ∪ (D1 ∩ D2)
  let T := (D0 ∩ D1) ∩ D2
  let P1 := corePetal D0 D1
  let P2 := corePetal D0 D2
  have hpoint : ∀ x : U,
      (if x ∈ W then (1 : Nat) else 0) +
          (if x ∈ T then (1 : Nat) else 0) =
        (if x ∈ D0 ∩ D1 then (1 : Nat) else 0) +
          (if x ∈ D0 ∩ D2 then (1 : Nat) else 0) +
            (if x ∈ P1 ∩ P2 then (1 : Nat) else 0) := by
    intro x
    by_cases h0 : x ∈ D0 <;>
      by_cases h1 : x ∈ D1 <;>
        by_cases h2 : x ∈ D2 <;>
          simp [W, T, P1, P2, corePetal, h0, h1, h2]
  have hsum := Finset.sum_congr rfl
    (fun x (_hx : x ∈ (Finset.univ : Finset U)) => hpoint x)
  simp only [Finset.sum_add_distrib] at hsum
  have hcard (S : Finset U) :
      (∑ x : U, if x ∈ S then (1 : Nat) else 0) = S.card := by
    simpa using (Finset.card_filter (fun x : U => x ∈ S) Finset.univ).symm
  rw [hcard W, hcard T, hcard (D0 ∩ D1), hcard (D0 ∩ D2),
    hcard (P1 ∩ P2)] at hsum
  simpa only [W, T, P1, P2] using hsum

/-- Three-set Bonferroni in the form used to iterate petal growth: the sum of
the three set sizes is at most their union plus their three pair overlaps. -/
theorem three_card_le_union_add_pairInter
    (A B C : Finset U) :
    A.card + B.card + C.card ≤
      (A ∪ B ∪ C).card +
        (A ∩ B).card + (A ∩ C).card + (B ∩ C).card := by
  let V := A ∪ B ∪ C
  have hpoint : ∀ x : U,
      (if x ∈ A then (1 : Nat) else 0) +
          (if x ∈ B then (1 : Nat) else 0) +
          (if x ∈ C then (1 : Nat) else 0) ≤
        (if x ∈ V then (1 : Nat) else 0) +
          (if x ∈ A ∩ B then (1 : Nat) else 0) +
          (if x ∈ A ∩ C then (1 : Nat) else 0) +
          (if x ∈ B ∩ C then (1 : Nat) else 0) := by
    intro x
    by_cases hA : x ∈ A <;>
      by_cases hB : x ∈ B <;>
        by_cases hC : x ∈ C <;>
          simp [V, hA, hB, hC]
  have hsum :
      (∑ x : U,
          ((if x ∈ A then (1 : Nat) else 0) +
            (if x ∈ B then (1 : Nat) else 0) +
            (if x ∈ C then (1 : Nat) else 0))) ≤
        ∑ x : U,
          ((if x ∈ V then (1 : Nat) else 0) +
            (if x ∈ A ∩ B then (1 : Nat) else 0) +
            (if x ∈ A ∩ C then (1 : Nat) else 0) +
            (if x ∈ B ∩ C then (1 : Nat) else 0)) := by
    exact Finset.sum_le_sum fun x _ => hpoint x
  simp only [Finset.sum_add_distrib] at hsum
  have hcard (S : Finset U) :
      (∑ x : U, if x ∈ S then (1 : Nat) else 0) = S.card := by
    simpa using (Finset.card_filter (fun x : U => x ∈ S) Finset.univ).symm
  rw [hcard A, hcard B, hcard C, hcard V, hcard (A ∩ B),
    hcard (A ∩ C), hcard (B ∩ C)] at hsum
  simpa only [V] using hsum

/-! ## Polynomial-line consequences -/

variable {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The joint-core petal of `target` outside the joint core of `source`. -/
def lineCorePetal (dom : iota ↪ F) (u0 u1 : iota → F)
    (source target : PolynomialLine F) : Finset iota :=
  jointCore dom u0 u1 target.1 target.2 \
    jointCore dom u0 u1 source.1 source.2

/-- The determinant module's weighted overlap is exactly two base-core
intersections plus the intersection of the two petals. -/
theorem pairOverlap_add_tripleOverlap_eq_base_add_petalInter
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 line2 : PolynomialLine F) :
    (pairOverlap dom u0 u1 line0 line1 line2).card +
        (tripleOverlap dom u0 u1 line0 line1 line2).card =
      (jointCore dom u0 u1 line0.1 line0.2 ∩
          jointCore dom u0 u1 line1.1 line1.2).card +
        (jointCore dom u0 u1 line0.1 line0.2 ∩
          jointCore dom u0 u1 line2.1 line2.2).card +
        (lineCorePetal dom u0 u1 line0 line1 ∩
          lineCorePetal dom u0 u1 line0 line2).card := by
  simpa only [pairOverlap, tripleOverlap, lineCorePetal, corePetal] using
    weightedOverlap_eq_base_add_base_add_petalInter
      (jointCore dom u0 u1 line0.1 line0.2)
      (jointCore dom u0 u1 line1.1 line1.2)
      (jointCore dom u0 u1 line2.1 line2.2)

/-- A noncollapsed triple's two petals have overlap bounded by the determinant
degree budget after charging the two intersections with the reference core. -/
theorem base_add_base_add_petalInter_le_two_mul_pred_of_determinant_ne_zero
    {k : Nat} (hk : 1 ≤ k)
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 line2 : PolynomialLine F)
    (hdeg : ∀ line ∈ ({line0, line1, line2} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hne : lineDeterminant line0 line1 line2 ≠ 0) :
    (jointCore dom u0 u1 line0.1 line0.2 ∩
          jointCore dom u0 u1 line1.1 line1.2).card +
        (jointCore dom u0 u1 line0.1 line0.2 ∩
          jointCore dom u0 u1 line2.1 line2.2).card +
        (lineCorePetal dom u0 u1 line0 line1 ∩
          lineCorePetal dom u0 u1 line0 line2).card ≤
      2 * (k - 1) := by
  have hcap := pairOverlap_card_add_tripleOverlap_card_le_two_mul_pred
    hk dom u0 u1 line0 line1 line2 hdeg hne
  rw [pairOverlap_add_tripleOverlap_eq_base_add_petalInter] at hcap
  exact hcap

/-- Explicit subtraction form of the noncollapsed petal-overlap cap. -/
theorem petalInter_card_le_degree_budget_sub_base_of_determinant_ne_zero
    {k : Nat} (hk : 1 ≤ k)
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 line2 : PolynomialLine F)
    (hdeg : ∀ line ∈ ({line0, line1, line2} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hne : lineDeterminant line0 line1 line2 ≠ 0) :
    (lineCorePetal dom u0 u1 line0 line1 ∩
        lineCorePetal dom u0 u1 line0 line2).card ≤
      2 * (k - 1) -
        ((jointCore dom u0 u1 line0.1 line0.2 ∩
            jointCore dom u0 u1 line1.1 line1.2).card +
          (jointCore dom u0 u1 line0.1 line0.2 ∩
            jointCore dom u0 u1 line2.1 line2.2).card) := by
  have hcap :=
    base_add_base_add_petalInter_le_two_mul_pred_of_determinant_ne_zero
      hk dom u0 u1 line0 line1 line2 hdeg hne
  omega

/-- If the two base intersections plus the petal overlap exceed the degree
budget, the three polynomial lines are determinant-collapsed. -/
theorem lineDeterminant_eq_zero_of_two_mul_pred_lt_base_add_petalInter
    {k : Nat} (hk : 1 ≤ k)
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 line2 : PolynomialLine F)
    (hdeg : ∀ line ∈ ({line0, line1, line2} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hlarge : 2 * (k - 1) <
      (jointCore dom u0 u1 line0.1 line0.2 ∩
            jointCore dom u0 u1 line1.1 line1.2).card +
          (jointCore dom u0 u1 line0.1 line0.2 ∩
            jointCore dom u0 u1 line2.1 line2.2).card +
          (lineCorePetal dom u0 u1 line0 line1 ∩
            lineCorePetal dom u0 u1 line0 line2).card) :
    lineDeterminant line0 line1 line2 = 0 := by
  apply lineDeterminant_eq_zero_of_two_mul_pred_lt_weighted_overlap
    hk dom u0 u1 line0 line1 line2 hdeg
  rw [pairOverlap_add_tripleOverlap_eq_base_add_petalInter]
  exact hlarge

/-- **Noncollapsed two-petal union growth.**  Unless the determinant vanishes,
the union of two petals must pay for both petal sizes and both intersections
with the reference core, up to the degree budget `2(k-1)`. -/
theorem petal_card_add_petal_card_add_base_le_union_add_two_mul_pred
    {k : Nat} (hk : 1 ≤ k)
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 line2 : PolynomialLine F)
    (hdeg : ∀ line ∈ ({line0, line1, line2} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hne : lineDeterminant line0 line1 line2 ≠ 0) :
    (lineCorePetal dom u0 u1 line0 line1).card +
          (lineCorePetal dom u0 u1 line0 line2).card +
        (jointCore dom u0 u1 line0.1 line0.2 ∩
            jointCore dom u0 u1 line1.1 line1.2).card +
      (jointCore dom u0 u1 line0.1 line0.2 ∩
          jointCore dom u0 u1 line2.1 line2.2).card ≤
    (lineCorePetal dom u0 u1 line0 line1 ∪
        lineCorePetal dom u0 u1 line0 line2).card + 2 * (k - 1) := by
  have hcap :=
    base_add_base_add_petalInter_le_two_mul_pred_of_determinant_ne_zero
      hk dom u0 u1 line0 line1 line2 hdeg hne
  have hunion := Finset.card_union_add_card_inter
    (lineCorePetal dom u0 u1 line0 line1)
    (lineCorePetal dom u0 u1 line0 line2)
  omega

/-- Small union is the equivalent overlap-side trigger for determinant
collapse. -/
theorem lineDeterminant_eq_zero_of_union_add_two_mul_pred_lt_petals_add_base
    {k : Nat} (hk : 1 ≤ k)
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 line2 : PolynomialLine F)
    (hdeg : ∀ line ∈ ({line0, line1, line2} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hsmall :
      (lineCorePetal dom u0 u1 line0 line1 ∪
            lineCorePetal dom u0 u1 line0 line2).card + 2 * (k - 1) <
        (lineCorePetal dom u0 u1 line0 line1).card +
            (lineCorePetal dom u0 u1 line0 line2).card +
          (jointCore dom u0 u1 line0.1 line0.2 ∩
              jointCore dom u0 u1 line1.1 line1.2).card +
          (jointCore dom u0 u1 line0.1 line0.2 ∩
              jointCore dom u0 u1 line2.1 line2.2).card) :
    lineDeterminant line0 line1 line2 = 0 := by
  apply lineDeterminant_eq_zero_of_two_mul_pred_lt_base_add_petalInter
    hk dom u0 u1 line0 line1 line2 hdeg
  have hunion := Finset.card_union_add_card_inter
    (lineCorePetal dom u0 u1 line0 line1)
    (lineCorePetal dom u0 u1 line0 line2)
  omega

/-- Two petals of size at least `s+1` either determinant-collapse or force the
quantitative union-growth recurrence with an explicit `2(s+1)` contribution. -/
theorem lineDeterminant_eq_zero_or_two_mul_succ_add_base_le_union_add_budget
    {k s : Nat} (hk : 1 ≤ k)
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 line2 : PolynomialLine F)
    (hdeg : ∀ line ∈ ({line0, line1, line2} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hpetal1 : s < (lineCorePetal dom u0 u1 line0 line1).card)
    (hpetal2 : s < (lineCorePetal dom u0 u1 line0 line2).card) :
    lineDeterminant line0 line1 line2 = 0 ∨
      2 * (s + 1) +
          (jointCore dom u0 u1 line0.1 line0.2 ∩
              jointCore dom u0 u1 line1.1 line1.2).card +
          (jointCore dom u0 u1 line0.1 line0.2 ∩
              jointCore dom u0 u1 line2.1 line2.2).card ≤
        (lineCorePetal dom u0 u1 line0 line1 ∪
            lineCorePetal dom u0 u1 line0 line2).card + 2 * (k - 1) := by
  by_cases hdet : lineDeterminant line0 line1 line2 = 0
  · exact Or.inl hdet
  apply Or.inr
  have hgrowth :=
    petal_card_add_petal_card_add_base_le_union_add_two_mul_pred
      hk dom u0 u1 line0 line1 line2 hdeg hdet
  omega

/-! ## Three-petal iteration -/

/-- **Three-petal union growth.**  If none of the three determinant triples
formed by a reference line and a pair of target lines collapses, then the union
of the three petals pays for all three petal sizes and twice all three base
intersections, up to the summed degree budget `6(k-1)`. -/
theorem three_petal_card_sum_add_two_mul_base_le_union_add_six_mul_pred
    {k : Nat} (hk : 1 ≤ k)
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 line2 line3 : PolynomialLine F)
    (hdeg : ∀ line ∈
      ({line0, line1, line2, line3} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hne12 : lineDeterminant line0 line1 line2 ≠ 0)
    (hne13 : lineDeterminant line0 line1 line3 ≠ 0)
    (hne23 : lineDeterminant line0 line2 line3 ≠ 0) :
    (lineCorePetal dom u0 u1 line0 line1).card +
          (lineCorePetal dom u0 u1 line0 line2).card +
          (lineCorePetal dom u0 u1 line0 line3).card +
        2 * ((jointCore dom u0 u1 line0.1 line0.2 ∩
                jointCore dom u0 u1 line1.1 line1.2).card +
              (jointCore dom u0 u1 line0.1 line0.2 ∩
                jointCore dom u0 u1 line2.1 line2.2).card +
              (jointCore dom u0 u1 line0.1 line0.2 ∩
                jointCore dom u0 u1 line3.1 line3.2).card) ≤
      (lineCorePetal dom u0 u1 line0 line1 ∪
          lineCorePetal dom u0 u1 line0 line2 ∪
          lineCorePetal dom u0 u1 line0 line3).card + 6 * (k - 1) := by
  let P1 := lineCorePetal dom u0 u1 line0 line1
  let P2 := lineCorePetal dom u0 u1 line0 line2
  let P3 := lineCorePetal dom u0 u1 line0 line3
  let B1 := (jointCore dom u0 u1 line0.1 line0.2 ∩
    jointCore dom u0 u1 line1.1 line1.2).card
  let B2 := (jointCore dom u0 u1 line0.1 line0.2 ∩
    jointCore dom u0 u1 line2.1 line2.2).card
  let B3 := (jointCore dom u0 u1 line0.1 line0.2 ∩
    jointCore dom u0 u1 line3.1 line3.2).card
  have hdeg12 : ∀ line ∈
      ({line0, line1, line2} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k := by
    intro line hline
    simp only [Finset.mem_insert, Finset.mem_singleton] at hline ⊢
    aesop
  have hdeg13 : ∀ line ∈
      ({line0, line1, line3} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k := by
    intro line hline
    simp only [Finset.mem_insert, Finset.mem_singleton] at hline ⊢
    aesop
  have hdeg23 : ∀ line ∈
      ({line0, line2, line3} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k := by
    intro line hline
    simp only [Finset.mem_insert, Finset.mem_singleton] at hline ⊢
    aesop
  have hcap12 :=
    base_add_base_add_petalInter_le_two_mul_pred_of_determinant_ne_zero
      hk dom u0 u1 line0 line1 line2 hdeg12 hne12
  have hcap13 :=
    base_add_base_add_petalInter_le_two_mul_pred_of_determinant_ne_zero
      hk dom u0 u1 line0 line1 line3 hdeg13 hne13
  have hcap23 :=
    base_add_base_add_petalInter_le_two_mul_pred_of_determinant_ne_zero
      hk dom u0 u1 line0 line2 line3 hdeg23 hne23
  change B1 + B2 + (P1 ∩ P2).card ≤ 2 * (k - 1) at hcap12
  change B1 + B3 + (P1 ∩ P3).card ≤ 2 * (k - 1) at hcap13
  change B2 + B3 + (P2 ∩ P3).card ≤ 2 * (k - 1) at hcap23
  have hbonf := three_card_le_union_add_pairInter P1 P2 P3
  change P1.card + P2.card + P3.card ≤
    (P1 ∪ P2 ∪ P3).card +
      (P1 ∩ P2).card + (P1 ∩ P3).card + (P2 ∩ P3).card at hbonf
  change P1.card + P2.card + P3.card + 2 * (B1 + B2 + B3) ≤
    (P1 ∪ P2 ∪ P3).card + 6 * (k - 1)
  omega

/-- Three large petals either contain a determinant-collapsed pair relative to
the reference line, or their total union satisfies the explicit three-petal
growth recurrence. -/
theorem determinant_collapse_or_three_large_petals_union_growth
    {k s : Nat} (hk : 1 ≤ k)
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 line2 line3 : PolynomialLine F)
    (hdeg : ∀ line ∈
      ({line0, line1, line2, line3} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hpetal1 : s < (lineCorePetal dom u0 u1 line0 line1).card)
    (hpetal2 : s < (lineCorePetal dom u0 u1 line0 line2).card)
    (hpetal3 : s < (lineCorePetal dom u0 u1 line0 line3).card) :
    lineDeterminant line0 line1 line2 = 0 ∨
      lineDeterminant line0 line1 line3 = 0 ∨
      lineDeterminant line0 line2 line3 = 0 ∨
      3 * (s + 1) +
          2 * ((jointCore dom u0 u1 line0.1 line0.2 ∩
                  jointCore dom u0 u1 line1.1 line1.2).card +
                (jointCore dom u0 u1 line0.1 line0.2 ∩
                  jointCore dom u0 u1 line2.1 line2.2).card +
                (jointCore dom u0 u1 line0.1 line0.2 ∩
                  jointCore dom u0 u1 line3.1 line3.2).card) ≤
        (lineCorePetal dom u0 u1 line0 line1 ∪
            lineCorePetal dom u0 u1 line0 line2 ∪
            lineCorePetal dom u0 u1 line0 line3).card + 6 * (k - 1) := by
  by_cases h12 : lineDeterminant line0 line1 line2 = 0
  · exact Or.inl h12
  by_cases h13 : lineDeterminant line0 line1 line3 = 0
  · exact Or.inr (Or.inl h13)
  by_cases h23 : lineDeterminant line0 line2 line3 = 0
  · exact Or.inr (Or.inr (Or.inl h23))
  apply Or.inr
  apply Or.inr
  apply Or.inr
  have hgrowth :=
    three_petal_card_sum_add_two_mul_base_le_union_add_six_mul_pred
      hk dom u0 u1 line0 line1 line2 line3 hdeg h12 h13 h23
  omega

/-! ## Canonical secant-family wrapper -/

/-- **Canonical secant overlap dichotomy.**  For any two selected pairs, the
petals of their canonical secant cores relative to a relevant reference line
either lie in one determinant-collapsed cluster or obey the exact union-growth
recurrence.  Outsider pairs produced by fresh-petal pruning satisfy the selected
point hypotheses automatically. -/
theorem canonical_secant_petals_collapse_or_union_growth
    {dom : iota ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u) (hk : 1 ≤ k)
    (line0 : LineParameter F) (hline0 : line0 ∈ lineParameters family)
    {gamma1 beta1 gamma2 beta2 : F}
    (hgamma1 : gamma1 ∈ family.G) (hbeta1 : beta1 ∈ family.G)
    (hne1 : gamma1 ≠ beta1)
    (hgamma2 : gamma2 ∈ family.G) (hbeta2 : beta2 ∈ family.G)
    (hne2 : gamma2 ≠ beta2) :
    let line1 := secantParameter family gamma1 beta1
    let line2 := secantParameter family gamma2 beta2
    lineDeterminant line0 line1 line2 = 0 ∨
      (lineCorePetal dom (u 0) (u 1) line0 line1).card +
            (lineCorePetal dom (u 0) (u 1) line0 line2).card +
          (jointCore dom (u 0) (u 1) line0.1 line0.2 ∩
              jointCore dom (u 0) (u 1) line1.1 line1.2).card +
        (jointCore dom (u 0) (u 1) line0.1 line0.2 ∩
            jointCore dom (u 0) (u 1) line2.1 line2.2).card ≤
      (lineCorePetal dom (u 0) (u 1) line0 line1 ∪
          lineCorePetal dom (u 0) (u 1) line0 line2).card + 2 * (k - 1) := by
  dsimp only
  let line1 := secantParameter family gamma1 beta1
  let line2 := secantParameter family gamma2 beta2
  have hline1 : line1 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hgamma1 hbeta1 hne1
  have hline2 : line2 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hgamma2 hbeta2 hne2
  by_cases hdet : lineDeterminant line0 line1 line2 = 0
  · exact Or.inl hdet
  apply Or.inr
  apply petal_card_add_petal_card_add_base_le_union_add_two_mul_pred
    hk dom (u 0) (u 1) line0 line1 line2
  · intro line hline
    simp only [Finset.mem_insert, Finset.mem_singleton] at hline
    rcases hline with (rfl | rfl | rfl)
    · exact lineParameter_degree_lt family hline0
    · exact lineParameter_degree_lt family hline1
    · exact lineParameter_degree_lt family hline2
  · exact hdet

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalOverlapGrowth

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalOverlapGrowth
#print axioms weightedOverlap_eq_base_add_base_add_petalInter
#print axioms petalInter_card_le_degree_budget_sub_base_of_determinant_ne_zero
#print axioms lineDeterminant_eq_zero_of_two_mul_pred_lt_base_add_petalInter
#print axioms petal_card_add_petal_card_add_base_le_union_add_two_mul_pred
#print axioms lineDeterminant_eq_zero_or_two_mul_succ_add_base_le_union_add_budget
#print axioms three_petal_card_sum_add_two_mul_base_le_union_add_six_mul_pred
#print axioms determinant_collapse_or_three_large_petals_union_growth
#print axioms canonical_secant_petals_collapse_or_union_growth
