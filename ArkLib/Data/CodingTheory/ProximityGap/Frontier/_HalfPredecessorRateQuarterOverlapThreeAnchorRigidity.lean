/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeFactorization

/-!
# Rate-quarter half predecessor: overlap-three anchor rigidity

The two-block reconciliation identity has extra content on the three common
core coordinates.  Its affine right-hand side vanishes there, so the two
scaled root locators agree at every common-core anchor.  The overlap-three
partition also keeps those anchors out of both saturated root blocks, making
both locator values nonzero.  Consequently the quotient of the two locators
is constant on all three anchors.

This is an exact algebraic constraint, not a counting bound: the final
theorem explicitly exhibits the three distinct anchors on which the locator
quotient collides.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeRigidity
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeFactorization

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeAnchorRigidity

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Evaluation of a root locator at an evaluation-domain coordinate. -/
noncomputable def locatorValue
    (dom : I ↪ F) (S : Finset I) (i : I) : F :=
  (domainRootProduct dom S).eval (dom i)

/-- The quotient of two locator values at an evaluation-domain coordinate. -/
noncomputable def locatorQuotient
    (dom : I ↪ F) (S1 S2 : Finset I) (i : I) : F :=
  locatorValue dom S1 i / locatorValue dom S2 i

/-- The locator evaluates as the product of the corresponding coordinate
differences. -/
theorem locatorValue_eq_prod
    (dom : I ↪ F) (S : Finset I) (i : I) :
    locatorValue dom S i = ∏ j ∈ S, (dom i - dom j) := by
  simp [locatorValue, domainRootProduct, eval_prod]

/-- A locator does not vanish at a coordinate outside its root block. -/
theorem locatorValue_ne_zero_of_not_mem
    (dom : I ↪ F) (S : Finset I) {i : I} (hi : i ∉ S) :
    locatorValue dom S i ≠ 0 := by
  rw [locatorValue_eq_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (dom.injective.ne fun hij => hi (hij ▸ hj))

/-- On a common-core coordinate, the affine difference on the right-hand
side of a two-block reconciliation identity vanishes. -/
theorem scaled_locator_eq_at_common_core
    (dom : I ↪ F) (u0 u1 : I → F) (gamma c1 c2 : F)
    (line1 line2 : F[X] × F[X]) (S1 S2 : Finset I)
    (hreconcile :
      C c1 * domainRootProduct dom S1 -
          C c2 * domainRootProduct dom S2 =
        (line2.1 - line1.1) + C gamma * (line2.2 - line1.2))
    {i : I}
    (hi : i ∈ jointCore dom u0 u1 line1.1 line1.2 ∩
      jointCore dom u0 u1 line2.1 line2.2) :
    c1 * locatorValue dom S1 i = c2 * locatorValue dom S2 i := by
  have hi1 := (Finset.mem_inter.mp hi).1
  have hi2 := (Finset.mem_inter.mp hi).2
  simp only [jointCore, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
  have heval := congrArg (fun p : F[X] => p.eval (dom i)) hreconcile
  simp only [eval_sub, eval_mul, eval_C, eval_add] at heval
  rw [hi1.1, hi2.1, hi1.2, hi2.2] at heval
  apply sub_eq_zero.mp
  simpa only [locatorValue, sub_self, mul_zero, add_zero] using heval

/-- The complete anchor constraint supplied by one reconciliation identity.
Besides the scaled identity, it records nonvanishing, every pairwise
cross-multiplied identity, and constancy of the locator quotient. -/
structure LocatorAnchorRigidity
    (dom : I ↪ F) (S1 S2 anchors : Finset I) (c1 c2 : F) : Prop where
  c1_ne_zero : c1 ≠ 0
  c2_ne_zero : c2 ≠ 0
  scaled_eq : ∀ i ∈ anchors,
    c1 * locatorValue dom S1 i = c2 * locatorValue dom S2 i
  first_locator_ne_zero : ∀ i ∈ anchors, locatorValue dom S1 i ≠ 0
  second_locator_ne_zero : ∀ i ∈ anchors, locatorValue dom S2 i ≠ 0
  cross_eq : ∀ i ∈ anchors, ∀ j ∈ anchors,
    locatorValue dom S1 i * locatorValue dom S2 j =
      locatorValue dom S1 j * locatorValue dom S2 i
  quotient_eq : ∀ i ∈ anchors, ∀ j ∈ anchors,
    locatorQuotient dom S1 S2 i = locatorQuotient dom S1 S2 j

/-- Scaled equality with a nonzero scale on root-free anchors forces all
pairwise cross identities and quotient equality. -/
theorem locatorAnchorRigidity_of_scaled_eq
    (dom : I ↪ F) (S1 S2 anchors : Finset I) (c1 c2 : F)
    (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0)
    (hscaled : ∀ i ∈ anchors,
      c1 * locatorValue dom S1 i = c2 * locatorValue dom S2 i)
    (hnot1 : ∀ i ∈ anchors, i ∉ S1)
    (hnot2 : ∀ i ∈ anchors, i ∉ S2) :
    LocatorAnchorRigidity dom S1 S2 anchors c1 c2 := by
  have hne1 : ∀ i ∈ anchors, locatorValue dom S1 i ≠ 0 := by
    intro i hi
    exact locatorValue_ne_zero_of_not_mem dom S1 (hnot1 i hi)
  have hne2 : ∀ i ∈ anchors, locatorValue dom S2 i ≠ 0 := by
    intro i hi
    exact locatorValue_ne_zero_of_not_mem dom S2 (hnot2 i hi)
  have hcross : ∀ i ∈ anchors, ∀ j ∈ anchors,
      locatorValue dom S1 i * locatorValue dom S2 j =
        locatorValue dom S1 j * locatorValue dom S2 i := by
    intro i hi j hj
    apply mul_left_cancel₀ hc1
    calc
      c1 * (locatorValue dom S1 i * locatorValue dom S2 j) =
          (c1 * locatorValue dom S1 i) * locatorValue dom S2 j := by ring
      _ = (c2 * locatorValue dom S2 i) * locatorValue dom S2 j := by
        rw [hscaled i hi]
      _ = (c2 * locatorValue dom S2 j) * locatorValue dom S2 i := by ring
      _ = (c1 * locatorValue dom S1 j) * locatorValue dom S2 i := by
        rw [← hscaled j hj]
      _ = c1 * (locatorValue dom S1 j * locatorValue dom S2 i) := by ring
  refine
    { c1_ne_zero := hc1
      c2_ne_zero := hc2
      scaled_eq := hscaled
      first_locator_ne_zero := hne1
      second_locator_ne_zero := hne2
      cross_eq := hcross
      quotient_eq := ?_ }
  intro i hi j hj
  rw [locatorQuotient, locatorQuotient,
    div_eq_div_iff (hne2 i hi) (hne2 j hj)]
  exact hcross i hi j hj

/-! ## Canonical overlap-three specialization -/

/-- **Canonical overlap-three anchor rigidity.**  The two saturated locator
blocks are root-free on the common core, and their quotient is constant on
that full anchor set. -/
theorem overlap_three_anchor_rigidity
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hsaturated : h = 2 * k)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = h)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = h)
    (hinter :
      (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 3)
    {gamma : F} (hgamma : gamma ∈ family.G)
    (hoff1 : family.q gamma ≠ line1.1 + C gamma * line1.2)
    (hoff2 : family.q gamma ≠ line2.1 + C gamma * line2.2) :
    ∃ c1 c2 : F,
      LocatorAnchorRigidity dom
        (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1)
        (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2)
        (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
          jointCore dom (u 0) (u 1) line2.1 line2.2) c1 c2 := by
  obtain ⟨c1, c2, hc1, hc2, hreconcile⟩ :=
    overlap_three_two_block_reconciliation
      family hk hn hsaturated hthreshold line1 line2 hline1 hline2
        hcore1 hcore2 hinter hgamma hoff1 hoff2
  have hrigid := fullAgreement_overlap_three_rigidity
    family hk hn hsaturated hthreshold line1 line2 hline1 hline2
      hcore1 hcore2 hinter hgamma hoff1 hoff2
  let A := fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let D1 := jointCore dom (u 0) (u 1) line1.1 line1.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let S1 := overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1
  let S2 := overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2
  let anchors := D1 ∩ D2
  have hno : A ∩ anchors = ∅ := by
    simpa only [A, anchors, D1, D2] using hrigid.no_common_core_agreement
  have hnotA : ∀ i ∈ anchors, i ∉ A := by
    intro i hi hiA
    have hiEmpty : i ∈ (∅ : Finset I) := by
      rw [← hno]
      exact Finset.mem_inter.mpr ⟨hiA, hi⟩
    simpa using hiEmpty
  have hnot1 : ∀ i ∈ anchors, i ∉ S1 := by
    intro i hi hiS
    apply hnotA i hi
    change i ∈ A ∩ D1 at hiS
    exact (Finset.mem_inter.mp hiS).1
  have hnot2 : ∀ i ∈ anchors, i ∉ S2 := by
    intro i hi hiS
    apply hnotA i hi
    change i ∈ A ∩ D2 at hiS
    exact (Finset.mem_inter.mp hiS).1
  have hscaled : ∀ i ∈ anchors,
      c1 * locatorValue dom S1 i = c2 * locatorValue dom S2 i := by
    intro i hi
    apply scaled_locator_eq_at_common_core
      dom (u 0) (u 1) gamma c1 c2 line1 line2 S1 S2
    · simpa only [S1, S2] using hreconcile
    · simpa only [anchors, D1, D2] using hi
  have hcert := locatorAnchorRigidity_of_scaled_eq
    dom S1 S2 anchors c1 c2 hc1 hc2 hscaled hnot1 hnot2
  refine ⟨c1, c2, ?_⟩
  simpa only [S1, S2, anchors, D1, D2] using hcert

/-- A three-point anchor certificate explicitly produces three distinct
coordinates carrying the same locator quotient. -/
theorem three_distinct_equal_quotient_anchors
    (dom : I ↪ F) (S1 S2 anchors : Finset I)
    {c1 c2 : F}
    (hcard : anchors.card = 3)
    (hcert : LocatorAnchorRigidity dom S1 S2 anchors c1 c2) :
    ∃ i j l : I,
      i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      anchors = {i, j, l} ∧
      locatorQuotient dom S1 S2 i = locatorQuotient dom S1 S2 j ∧
      locatorQuotient dom S1 S2 i = locatorQuotient dom S1 S2 l := by
  obtain ⟨i, j, l, hij, hil, hjl, hanchors⟩ := Finset.card_eq_three.mp hcard
  have hi : i ∈ anchors := by rw [hanchors]; simp
  have hj : j ∈ anchors := by rw [hanchors]; simp
  have hl : l ∈ anchors := by rw [hanchors]; simp
  exact ⟨i, j, l, hij, hil, hjl, hanchors,
    hcert.quotient_eq i hi j hj, hcert.quotient_eq i hi l hl⟩

/-- **Three-anchor collision for the canonical overlap-three cell.**  This is
the concrete noninjectivity consequence of the reconciliation identity; it
does not assert any bound on the number of compatible cells. -/
theorem overlap_three_three_distinct_equal_quotient_anchors
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hsaturated : h = 2 * k)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = h)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = h)
    (hinter :
      (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 3)
    {gamma : F} (hgamma : gamma ∈ family.G)
    (hoff1 : family.q gamma ≠ line1.1 + C gamma * line1.2)
    (hoff2 : family.q gamma ≠ line2.1 + C gamma * line2.2) :
    ∃ i j l : I,
      i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
          jointCore dom (u 0) (u 1) line2.1 line2.2 = {i, j, l} ∧
      locatorQuotient dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1)
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2) i =
        locatorQuotient dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1)
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2) j ∧
      locatorQuotient dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1)
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2) i =
        locatorQuotient dom
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1)
          (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2) l := by
  obtain ⟨c1, c2, hcert⟩ := overlap_three_anchor_rigidity
    family hk hn hsaturated hthreshold line1 line2 hline1 hline2
      hcore1 hcore2 hinter hgamma hoff1 hoff2
  exact three_distinct_equal_quotient_anchors
    dom
      (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line1)
      (overlapRootBlock dom (u 0) (u 1) gamma (family.q gamma) line2)
      (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2)
      hinter hcert

#print axioms locatorValue_ne_zero_of_not_mem
#print axioms scaled_locator_eq_at_common_core
#print axioms overlap_three_anchor_rigidity
#print axioms overlap_three_three_distinct_equal_quotient_anchors

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeAnchorRigidity
