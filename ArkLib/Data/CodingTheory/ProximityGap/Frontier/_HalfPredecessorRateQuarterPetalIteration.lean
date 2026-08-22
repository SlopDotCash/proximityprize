/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterFreshPetalPruning
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterPetalOverlapGrowth

/-!
# Rate-quarter half predecessor: anchored petal iteration

Fresh-petal pruning forces one canonical secant petal of size at least
`floor(k / 3) + 2` from every saturated intermediate core in a counterexample.
The determinant overlap bounds can then be based at this forced petal.

This file rewrites the two- and three-petal union bounds as genuine increment
bounds.  If `P1` is the anchor petal, a noncollapsed companion `P2` satisfies

```text
  |P2| + |D0 inter D1| + |D0 inter D2|
    <= |P2 \\ P1| + 2(k - 1).
```

For two companions, absence of all three determinant collapses similarly
forces

```text
  |P2| + |P3| + 2(B1 + B2 + B3)
    <= |(P2 union P3) \\ P1| + 6(k - 1).
```

The final theorem composes these facts with saturated intermediate-core
pruning: a family larger than the domain has a large canonical anchor petal
for which both increment rules hold uniformly over every further selected
secant.  This is stronger than merely producing one large petal or bounding
one pairwise overlap.  It isolates the remaining global issue precisely:
construct enough noncollapsed companions whose charged increments exhaust the
complement of the source core.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalPruning
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalOverlapGrowth

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalIteration

attribute [local instance] Classical.propDecidable

/-! ## Removing an anchor from union growth -/

variable {U : Type} [Fintype U] [DecidableEq U]

/-- A two-set union is the disjoint contribution of the anchor and the part
of the target not already covered by the anchor. -/
theorem card_union_eq_anchor_add_new (anchor target : Finset U) :
    (anchor ∪ target).card =
      anchor.card + (target \ anchor).card := by
  have hsplit := Finset.card_sdiff_add_card target anchor
  rw [Finset.union_comm] at hsplit
  omega

/-! ## Exact one- and two-companion increments -/

variable {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **One-companion increment.**  Relative to an anchor petal `P1`, a
noncollapsed target petal `P2` must pay its size and both base-intersection
charges using coordinates in `P2 \\ P1`, up to the determinant degree budget.

Unlike the union form, this statement can be iterated: its right-hand side
measures only coordinates genuinely new beyond the chosen anchor. -/
theorem companion_petal_add_base_le_new_add_two_mul_pred
    {k : Nat} (hk : 1 ≤ k)
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 line2 : PolynomialLine F)
    (hdeg : ∀ line ∈ ({line0, line1, line2} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hne : lineDeterminant line0 line1 line2 ≠ 0) :
    (lineCorePetal dom u0 u1 line0 line2).card +
          (jointCore dom u0 u1 line0.1 line0.2 ∩
              jointCore dom u0 u1 line1.1 line1.2).card +
        (jointCore dom u0 u1 line0.1 line0.2 ∩
            jointCore dom u0 u1 line2.1 line2.2).card ≤
      (lineCorePetal dom u0 u1 line0 line2 \
          lineCorePetal dom u0 u1 line0 line1).card + 2 * (k - 1) := by
  have hgrowth :=
    petal_card_add_petal_card_add_base_le_union_add_two_mul_pred
      hk dom u0 u1 line0 line1 line2 hdeg hne
  have hsplit := card_union_eq_anchor_add_new
    (lineCorePetal dom u0 u1 line0 line1)
    (lineCorePetal dom u0 u1 line0 line2)
  omega

/-- **Two-companion increment.**  If none of the three determinant triples
through the source line collapses, two target petals jointly pay their sizes
and all three doubled base charges using only coordinates outside the anchor
petal, up to the summed degree budget. -/
theorem two_companion_petals_add_two_mul_base_le_new_union_add_six_mul_pred
    {k : Nat} (hk : 1 ≤ k)
    (dom : iota ↪ F) (u0 u1 : iota → F)
    (line0 line1 line2 line3 : PolynomialLine F)
    (hdeg : ∀ line ∈
      ({line0, line1, line2, line3} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k)
    (hne12 : lineDeterminant line0 line1 line2 ≠ 0)
    (hne13 : lineDeterminant line0 line1 line3 ≠ 0)
    (hne23 : lineDeterminant line0 line2 line3 ≠ 0) :
    (lineCorePetal dom u0 u1 line0 line2).card +
          (lineCorePetal dom u0 u1 line0 line3).card +
        2 * ((jointCore dom u0 u1 line0.1 line0.2 ∩
                jointCore dom u0 u1 line1.1 line1.2).card +
              (jointCore dom u0 u1 line0.1 line0.2 ∩
                jointCore dom u0 u1 line2.1 line2.2).card +
              (jointCore dom u0 u1 line0.1 line0.2 ∩
                jointCore dom u0 u1 line3.1 line3.2).card) ≤
      ((lineCorePetal dom u0 u1 line0 line2 ∪
            lineCorePetal dom u0 u1 line0 line3) \
          lineCorePetal dom u0 u1 line0 line1).card + 6 * (k - 1) := by
  have hgrowth :=
    three_petal_card_sum_add_two_mul_base_le_union_add_six_mul_pred
      hk dom u0 u1 line0 line1 line2 line3 hdeg hne12 hne13 hne23
  have hsplit :
      (lineCorePetal dom u0 u1 line0 line1 ∪
          lineCorePetal dom u0 u1 line0 line2 ∪
          lineCorePetal dom u0 u1 line0 line3).card =
        (lineCorePetal dom u0 u1 line0 line1).card +
          ((lineCorePetal dom u0 u1 line0 line2 ∪
                lineCorePetal dom u0 u1 line0 line3) \
            lineCorePetal dom u0 u1 line0 line1).card := by
    simpa only [Finset.union_assoc] using
      card_union_eq_anchor_add_new
        (lineCorePetal dom u0 u1 line0 line1)
        (lineCorePetal dom u0 u1 line0 line2 ∪
          lineCorePetal dom u0 u1 line0 line3)
  omega

/-- Three canonical secants based at one relevant line either contain a
determinant-collapsed pair or satisfy the exact two-companion increment bound
outside the first secant petal. -/
theorem canonical_three_secants_collapse_or_companion_increment
    {dom : iota ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u) (hk : 1 ≤ k)
    (line0 : LineParameter F) (hline0 : line0 ∈ lineParameters family)
    {gamma1 beta1 gamma2 beta2 gamma3 beta3 : F}
    (hgamma1 : gamma1 ∈ family.G) (hbeta1 : beta1 ∈ family.G)
    (hne1 : gamma1 ≠ beta1)
    (hgamma2 : gamma2 ∈ family.G) (hbeta2 : beta2 ∈ family.G)
    (hne2 : gamma2 ≠ beta2)
    (hgamma3 : gamma3 ∈ family.G) (hbeta3 : beta3 ∈ family.G)
    (hne3 : gamma3 ≠ beta3) :
    let line1 := secantParameter family gamma1 beta1
    let line2 := secantParameter family gamma2 beta2
    let line3 := secantParameter family gamma3 beta3
    lineDeterminant line0 line1 line2 = 0 ∨
      lineDeterminant line0 line1 line3 = 0 ∨
      lineDeterminant line0 line2 line3 = 0 ∨
      (lineCorePetal dom (u 0) (u 1) line0 line2).card +
            (lineCorePetal dom (u 0) (u 1) line0 line3).card +
          2 * ((jointCore dom (u 0) (u 1) line0.1 line0.2 ∩
                  jointCore dom (u 0) (u 1) line1.1 line1.2).card +
                (jointCore dom (u 0) (u 1) line0.1 line0.2 ∩
                  jointCore dom (u 0) (u 1) line2.1 line2.2).card +
                (jointCore dom (u 0) (u 1) line0.1 line0.2 ∩
                  jointCore dom (u 0) (u 1) line3.1 line3.2).card) ≤
        ((lineCorePetal dom (u 0) (u 1) line0 line2 ∪
              lineCorePetal dom (u 0) (u 1) line0 line3) \
            lineCorePetal dom (u 0) (u 1) line0 line1).card +
          6 * (k - 1) := by
  dsimp only
  let line1 := secantParameter family gamma1 beta1
  let line2 := secantParameter family gamma2 beta2
  let line3 := secantParameter family gamma3 beta3
  have hline1 : line1 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hgamma1 hbeta1 hne1
  have hline2 : line2 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hgamma2 hbeta2 hne2
  have hline3 : line3 ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hgamma3 hbeta3 hne3
  have hdeg : ∀ line ∈
      ({line0, line1, line2, line3} : Finset (PolynomialLine F)),
      line.1.natDegree < k ∧ line.2.natDegree < k := by
    intro line hline
    simp only [Finset.mem_insert, Finset.mem_singleton] at hline
    rcases hline with (rfl | rfl | rfl | rfl)
    · exact lineParameter_degree_lt family hline0
    · exact lineParameter_degree_lt family hline1
    · exact lineParameter_degree_lt family hline2
    · exact lineParameter_degree_lt family hline3
  by_cases h12 : lineDeterminant line0 line1 line2 = 0
  · exact Or.inl h12
  by_cases h13 : lineDeterminant line0 line1 line3 = 0
  · exact Or.inr (Or.inl h13)
  by_cases h23 : lineDeterminant line0 line2 line3 = 0
  · exact Or.inr (Or.inr (Or.inl h23))
  exact Or.inr (Or.inr (Or.inr
    (two_companion_petals_add_two_mul_base_le_new_union_add_six_mul_pred
      hk dom (u 0) (u 1) line0 line1 line2 line3 hdeg h12 h13 h23)))

/-! ## Uniform rules carried by a selected anchor -/

/-- Every selected companion of an anchor either determinant-collapses with
it or obeys the exact new-coordinate increment. -/
noncomputable def OneCompanionIncrementRule
    {dom : iota ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (line0 : LineParameter F) (gamma1 beta1 : F) : Prop :=
  ∀ gamma2 ∈ family.G, ∀ beta2 ∈ family.G, gamma2 ≠ beta2 →
    let line1 := secantParameter family gamma1 beta1
    let line2 := secantParameter family gamma2 beta2
    lineDeterminant line0 line1 line2 = 0 ∨
      (lineCorePetal dom (u 0) (u 1) line0 line2).card +
            (jointCore dom (u 0) (u 1) line0.1 line0.2 ∩
                jointCore dom (u 0) (u 1) line1.1 line1.2).card +
          (jointCore dom (u 0) (u 1) line0.1 line0.2 ∩
              jointCore dom (u 0) (u 1) line2.1 line2.2).card ≤
        (lineCorePetal dom (u 0) (u 1) line0 line2 \
            lineCorePetal dom (u 0) (u 1) line0 line1).card + 2 * (k - 1)

/-- Every two selected companions of an anchor either contain a determinant
collapse or obey the exact joint new-coordinate increment. -/
noncomputable def TwoCompanionIncrementRule
    {dom : iota ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (line0 : LineParameter F) (gamma1 beta1 : F) : Prop :=
  ∀ gamma2 ∈ family.G, ∀ beta2 ∈ family.G, gamma2 ≠ beta2 →
    ∀ gamma3 ∈ family.G, ∀ beta3 ∈ family.G, gamma3 ≠ beta3 →
      let line1 := secantParameter family gamma1 beta1
      let line2 := secantParameter family gamma2 beta2
      let line3 := secantParameter family gamma3 beta3
      lineDeterminant line0 line1 line2 = 0 ∨
        lineDeterminant line0 line1 line3 = 0 ∨
        lineDeterminant line0 line2 line3 = 0 ∨
        (lineCorePetal dom (u 0) (u 1) line0 line2).card +
              (lineCorePetal dom (u 0) (u 1) line0 line3).card +
            2 * ((jointCore dom (u 0) (u 1) line0.1 line0.2 ∩
                    jointCore dom (u 0) (u 1) line1.1 line1.2).card +
                  (jointCore dom (u 0) (u 1) line0.1 line0.2 ∩
                    jointCore dom (u 0) (u 1) line2.1 line2.2).card +
                  (jointCore dom (u 0) (u 1) line0.1 line0.2 ∩
                    jointCore dom (u 0) (u 1) line3.1 line3.2).card) ≤
          ((lineCorePetal dom (u 0) (u 1) line0 line2 ∪
                lineCorePetal dom (u 0) (u 1) line0 line3) \
              lineCorePetal dom (u 0) (u 1) line0 line1).card +
            6 * (k - 1)

/-- A selected anchor carries the uniform one-companion increment rule. -/
theorem oneCompanionIncrementRule_of_selected_anchor
    {dom : iota ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u) (hk : 1 ≤ k)
    (line0 : LineParameter F) (hline0 : line0 ∈ lineParameters family)
    {gamma1 beta1 : F}
    (hgamma1 : gamma1 ∈ family.G) (hbeta1 : beta1 ∈ family.G)
    (hne1 : gamma1 ≠ beta1) :
    OneCompanionIncrementRule family line0 gamma1 beta1 := by
  intro gamma2 hgamma2 beta2 hbeta2 hne2
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
  apply companion_petal_add_base_le_new_add_two_mul_pred
    hk dom (u 0) (u 1) line0 line1 line2
  · intro line hline
    simp only [Finset.mem_insert, Finset.mem_singleton] at hline
    rcases hline with (rfl | rfl | rfl)
    · exact lineParameter_degree_lt family hline0
    · exact lineParameter_degree_lt family hline1
    · exact lineParameter_degree_lt family hline2
  · exact hdet

/-- A selected anchor carries the uniform two-companion increment rule. -/
theorem twoCompanionIncrementRule_of_selected_anchor
    {dom : iota ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u) (hk : 1 ≤ k)
    (line0 : LineParameter F) (hline0 : line0 ∈ lineParameters family)
    {gamma1 beta1 : F}
    (hgamma1 : gamma1 ∈ family.G) (hbeta1 : beta1 ∈ family.G)
    (hne1 : gamma1 ≠ beta1) :
    TwoCompanionIncrementRule family line0 gamma1 beta1 := by
  intro gamma2 hgamma2 beta2 hbeta2 hne2
  intro gamma3 hgamma3 beta3 hbeta3 hne3
  exact canonical_three_secants_collapse_or_companion_increment
    family hk line0 hline0 hgamma1 hbeta1 hne1
      hgamma2 hbeta2 hne2 hgamma3 hbeta3 hne3

/-! ## Composition with saturated intermediate-core pruning -/

/-- The pruning petal is definitionally the determinant module's line-core
petal for the same canonical secant. -/
theorem secantPetal_eq_lineCorePetal
    {dom : iota ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (line0 : LineParameter F) (gamma beta : F) :
    secantPetal family line0 gamma beta =
      lineCorePetal dom (u 0) (u 1) line0
        (secantParameter family gamma beta) := by
  rfl

/-- **Forced anchored petal iteration at saturated rate one quarter.**

If an intermediate core occurs in a family larger than the domain, pruning
selects outsider endpoints whose canonical secant has at least
`floor(k / 3) + 2` coordinates beyond the source core.  The same forced
secant is simultaneously a uniform anchor for:

* every one-companion new-coordinate increment; and
* every two-companion joint increment, modulo one of the three explicit
  determinant collapses.

Thus the existential choice made by fresh-petal pruning is compatible with
all later companion choices; no extra selection hypothesis is needed. -/
theorem exists_large_anchor_with_uniform_companion_increments_of_saturated_intermediate
    {dom : iota ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card iota = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card iota : NNReal)⌉₊ = h + 1)
    (hsaturated : h = 2 * k) (hcard : 2 * h < family.G.card)
    {line0 : LineParameter F} (hline0 : line0 ∈ lineParameters family)
    (hlower : h / 2 + 2 ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hupper :
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card < h) :
    ∃ gamma1 ∈ outsideLine family line0,
      ∃ beta1 ∈ outsideLine family line0, gamma1 ≠ beta1 ∧
        k / 3 + 1 < (secantPetal family line0 gamma1 beta1).card ∧
        OneCompanionIncrementRule family line0 gamma1 beta1 ∧
        TwoCompanionIncrementRule family line0 gamma1 beta1 := by
  obtain ⟨gamma1, hgammaOut, beta1, hbetaOut, hne1, hlarge⟩ :=
    exists_outside_secantPetal_card_gt_third_of_saturated_intermediate
      family hk hn hthreshold hsaturated hcard hline0 hlower hupper
  have hgamma1 : gamma1 ∈ family.G :=
    ((mem_outsideLine_iff family line0 gamma1).mp hgammaOut).1
  have hbeta1 : beta1 ∈ family.G :=
    ((mem_outsideLine_iff family line0 beta1).mp hbetaOut).1
  refine ⟨gamma1, hgammaOut, beta1, hbetaOut, hne1, hlarge, ?_, ?_⟩
  · exact oneCompanionIncrementRule_of_selected_anchor
      family hk line0 hline0 hgamma1 hbeta1 hne1
  · exact twoCompanionIncrementRule_of_selected_anchor
      family hk line0 hline0 hgamma1 hbeta1 hne1

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalIteration

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalIteration
#print axioms companion_petal_add_base_le_new_add_two_mul_pred
#print axioms two_companion_petals_add_two_mul_base_le_new_union_add_six_mul_pred
#print axioms canonical_three_secants_collapse_or_companion_increment
#print axioms oneCompanionIncrementRule_of_selected_anchor
#print axioms twoCompanionIncrementRule_of_selected_anchor
#print axioms exists_large_anchor_with_uniform_companion_increments_of_saturated_intermediate
