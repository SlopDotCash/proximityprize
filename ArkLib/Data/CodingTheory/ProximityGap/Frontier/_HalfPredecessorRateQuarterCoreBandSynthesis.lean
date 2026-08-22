/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterObtuse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterComplementaryCores
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantCollapse

/-!
# Rate-quarter half predecessor: core-band synthesis

This file composes the endpoint obtuse bound with the complementary-core and
determinant-collapse branches.  In a family larger than the domain, the obtuse
bound produces a canonical secant core of size at least `floor(h / 2) + 2`.
If that core has size below `h`, then it lies in the previously unlocalized
intermediate band.  The quantitative two-core cover theorem shows that this
core cannot have an almost-complementary relevant partner: every union with a
relevant core misses at least three coordinates at rate at most one quarter.

The file also connects the abstract determinant theorem to the rich-point
family API: any three relevant line cores of size at least `h` belong to one
determinant-collapsed cluster.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis

attribute [local instance] Classical.propDecidable

variable {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Coordinates not covered by either of two decoded-line joint cores. -/
def uncoveredByTwoLineCores (dom : ι ↪ F) (u0 u1 : ι → F)
    (line1 line2 : LineParameter F) : Finset ι :=
  Finset.univ \ (jointCore dom u0 u1 line1.1 line1.2 ∪
    jointCore dom u0 u1 line2.1 line2.2)

/-- Three relevant decoded lines with half-domain joint cores satisfy the
determinant-collapse relation.  This is the family-level handoff to the
collapsed-cluster injection API. -/
theorem lineDeterminant_eq_zero_of_three_relevant_half_core_lines
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h) (hrate : 2 * k ≤ h)
    (line1 line2 line3 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hline3 : line3 ∈ lineParameters family)
    (hcore1 : h ≤ (jointCore dom (u 0) (u 1) line1.1 line1.2).card)
    (hcore2 : h ≤ (jointCore dom (u 0) (u 1) line2.1 line2.2).card)
    (hcore3 : h ≤ (jointCore dom (u 0) (u 1) line3.1 line3.2).card) :
    lineDeterminant line1 line2 line3 = 0 := by
  apply lineDeterminant_eq_zero_of_three_halfSized_cores
    hk dom (u 0) (u 1) line1 line2 line3 hn hrate
  · intro line hline
    simp only [Finset.mem_insert, Finset.mem_singleton] at hline
    rcases hline with (rfl | rfl | rfl)
    · exact lineParameter_degree_lt family hline1
    · exact lineParameter_degree_lt family hline2
    · exact lineParameter_degree_lt family hline3
  · exact hcore1
  · exact hcore2
  · exact hcore3

/-- **Exact core-band localization.**  At rate at most one quarter, a rich-point
family is bounded by the domain unless either

* some relevant line has a joint core of size at least `h`, or
* a relevant line has an intermediate core in
  `[floor(h / 2) + 2, h - 1]`, and its union with every relevant core misses
  enough coordinates to defeat the complementary-core argument.

The exact failed-cover inequality is retained.  Its rate-quarter consequence
is that every such union misses at least three coordinates. -/
theorem card_le_two_mul_or_high_core_or_intermediate_core_without_complement
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h) :
    family.G.card ≤ 2 * h ∨
      (∃ line ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card) ∨
      ∃ line ∈ lineParameters family,
        h / 2 + 2 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∧
        (jointCore dom (u 0) (u 1) line.1 line.2).card < h ∧
        ∀ line2 ∈ lineParameters family,
          h + 1 ≤
              (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card +
                2 * (k - 1) ∧
            3 ≤ (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card := by
  by_cases hcard : family.G.card ≤ 2 * h
  · exact Or.inl hcard
  have hobtuse := card_le_two_mul_or_exists_pair_core_ge_half_add_two
    family hn hthreshold
  rcases hobtuse with hle | ⟨gamma, hgamma, beta, hbeta, hne, hlarge⟩
  · exact (hcard hle).elim
  let line := secantParameter family gamma beta
  have hline : line ∈ lineParameters family :=
    secantParameter_mem_lineParameters family hgamma hbeta hne
  have hgammaOn : gamma ∈ pointsOn family line :=
    first_point_mem_pointsOn_secant family hgamma
  have hbetaOn : beta ∈ pointsOn family line :=
    second_point_mem_pointsOn_secant family hbeta hne
  have hgammaEq := (mem_pointsOn_iff family line gamma).mp hgammaOn |>.2
  have hbetaEq := (mem_pointsOn_iff family line beta).mp hbetaOn |>.2
  have hcoreEq :
      fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
          fullAgreement dom (u 0) (u 1) beta (family.q beta) =
        jointCore dom (u 0) (u 1) line.1 line.2 := by
    rw [hgammaEq, hbetaEq]
    exact fullAgreement_inter_eq_jointCore
      dom (u 0) (u 1) line.1 line.2 hne
  have hcoreLarge :
      h / 2 + 2 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card := by
    rw [← hcoreEq]
    exact hlarge
  by_cases hhigh : h ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card
  · exact Or.inr (Or.inl ⟨line, hline, hhigh⟩)
  apply Or.inr
  apply Or.inr
  refine ⟨line, hline, hcoreLarge, Nat.lt_of_not_ge hhigh, ?_⟩
  intro line2 hline2
  have hexact :
      h + 1 ≤
          (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card +
            2 * (k - 1) := by
    by_contra hnot
    have hmissing :
        (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card +
            2 * (k - 1) < h + 1 := by
      omega
    have hle := card_le_two_mul_of_small_core_complement
      family hk hn hthreshold.ge line line2 hline hline2
      (by simpa only [uncoveredByTwoLineCores] using hmissing)
    exact hcard hle
  have hthree :
      3 ≤ (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card := by
    omega
  exact ⟨hexact, hthree⟩

/-- Every relevant line in a counterexample fails the strict large-core
collapse inequality.  This is the subtraction-free ceiling that can be
composed with the core-band localization. -/
theorem relevant_core_two_mul_add_three_le_of_card_gt_two_mul
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h) (hcard : 2 * h < family.G.card)
    {line : LineParameter F} (hline : line ∈ lineParameters family) :
    2 * (jointCore dom (u 0) (u 1) line.1 line.2).card + 3 ≤
      h + 4 * (k - 1) := by
  by_contra hnot
  have hlarge :
      h + 4 * (k - 1) <
        2 * (jointCore dom (u 0) (u 1) line.1 line.2).card + 3 := by
    omega
  exact largeCore_contradiction_of_card_gt_two_mul
    family (by omega) hk hn hthreshold.ge hline hcard hlarge

/-- **Large-core-sharpened core-band localization.**  This strengthens
`card_le_two_mul_or_high_core_or_intermediate_core_without_complement` by
attaching the failed large-core-collapse inequality to either residual line.
Thus the residual intermediate core is simultaneously too small for the
large-core triple collapse and too isolated for the complementary-core
collapse. -/
theorem card_le_two_mul_or_bounded_high_core_or_bounded_intermediate_core
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hrate : 2 * k ≤ h) :
    family.G.card ≤ 2 * h ∨
      (∃ line ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∧
        2 * (jointCore dom (u 0) (u 1) line.1 line.2).card + 3 ≤
          h + 4 * (k - 1)) ∨
      ∃ line ∈ lineParameters family,
        h / 2 + 2 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∧
        (jointCore dom (u 0) (u 1) line.1 line.2).card < h ∧
        2 * (jointCore dom (u 0) (u 1) line.1 line.2).card + 3 ≤
          h + 4 * (k - 1) ∧
        ∀ line2 ∈ lineParameters family,
          h + 1 ≤
              (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card +
                2 * (k - 1) ∧
            3 ≤ (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card := by
  by_cases hcard : family.G.card ≤ 2 * h
  · exact Or.inl hcard
  have hcard' : 2 * h < family.G.card := by omega
  rcases card_le_two_mul_or_high_core_or_intermediate_core_without_complement
      family hk hn hthreshold hrate with hle | hhigh | hmid
  · exact (hcard hle).elim
  · obtain ⟨line, hline, hcore⟩ := hhigh
    exact Or.inr (Or.inl ⟨line, hline, hcore,
      relevant_core_two_mul_add_three_le_of_card_gt_two_mul
        family hk hn hthreshold hrate hcard' hline⟩)
  · obtain ⟨line, hline, hlower, hupper, hisolated⟩ := hmid
    exact Or.inr (Or.inr ⟨line, hline, hlower, hupper,
      relevant_core_two_mul_add_three_le_of_card_gt_two_mul
        family hk hn hthreshold hrate hcard' hline,
      hisolated⟩)

/-- At the saturated rate `h = 2k`, the large-core ceiling becomes the exact
integral bound `|D| ≤ 3k - 4` on either residual core. -/
theorem card_le_two_mul_or_saturated_high_core_or_saturated_intermediate_core
    {dom : ι ↪ F} {k h : ℕ} {delta : ℝ≥0}
    {u : WordStack F (Fin 2) ι}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card ι = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card ι : ℝ≥0)⌉₊ = h + 1)
    (hsaturated : h = 2 * k) :
    family.G.card ≤ 2 * h ∨
      (∃ line ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∧
        (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 3 * k - 4) ∨
      ∃ line ∈ lineParameters family,
        h / 2 + 2 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∧
        (jointCore dom (u 0) (u 1) line.1 line.2).card < h ∧
        (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 3 * k - 4 ∧
        ∀ line2 ∈ lineParameters family,
          h + 1 ≤
              (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card +
                2 * (k - 1) ∧
            3 ≤ (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card := by
  have hrate : 2 * k ≤ h := by omega
  rcases card_le_two_mul_or_bounded_high_core_or_bounded_intermediate_core
      family hk hn hthreshold hrate with hle | hhigh | hmid
  · exact Or.inl hle
  · obtain ⟨line, hline, hlower, hupper⟩ := hhigh
    apply Or.inr
    apply Or.inl
    refine ⟨line, hline, hlower, ?_⟩
    omega
  · obtain ⟨line, hline, hlower, hlt, hupper, hisolated⟩ := hmid
    apply Or.inr
    apply Or.inr
    refine ⟨line, hline, hlower, hlt, ?_, hisolated⟩
    omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis
#print axioms lineDeterminant_eq_zero_of_three_relevant_half_core_lines
#print axioms card_le_two_mul_or_high_core_or_intermediate_core_without_complement
#print axioms relevant_core_two_mul_add_three_le_of_card_gt_two_mul
#print axioms card_le_two_mul_or_bounded_high_core_or_bounded_intermediate_core
#print axioms card_le_two_mul_or_saturated_high_core_or_saturated_intermediate_core
