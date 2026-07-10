/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCorePetalGrowth

/-!
# Rate-quarter half predecessor: global petal synthesis

This file closes the local-to-global handoff between the saturated core-band
localization and the two quantitative fresh-petal arguments.

At `h = 2k`, every family larger than its `2h`-coordinate domain has one of
two explicit witness packages:

* a high relevant core, with a canonical outsider secant petal of size at
  least `floor(k / 2) + 3`; or
* an intermediate relevant core in `[k + 2, 2k - 1]`, with a canonical
  outsider secant petal of size at least `floor(k / 3) + 2`.

The intermediate package retains both obstructions already proved by the
core-band theorem: the sharp large-core ceiling and, for every relevant
partner, the exact failed-cover inequality together with at least three
uncovered coordinates.  Thus no branch or auxiliary witness remains
conditional once `|G| > 2h` is assumed.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterFreshPetalPruning
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCorePetalGrowth

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterGlobalPetalSynthesis

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **Global saturated petal dichotomy.**  At rate one quarter, a
counterexample has either a high core with a half-scale fresh secant petal, or
an intermediate core with a third-scale fresh secant petal.

All bounds are stated directly in terms of `k`:

* the high core lies in `[2k, 3k - 4]`;
* the intermediate core lies in `[k + 2, 2k - 1]` and also satisfies the
  global ceiling `|D| <= 3k - 4`;
* every relevant partner of the intermediate core leaves at least three
  coordinates uncovered and satisfies the exact failed-cover inequality.

The secant endpoints in both branches are outsiders from the displayed source
line, so the petal witnesses are canonical and immediately usable by the
determinant and anchored-iteration APIs. -/
theorem exists_high_core_half_petal_or_intermediate_third_petal_of_card_gt_two_mul
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = h + 1)
    (hsaturated : h = 2 * k) (hcard : 2 * h < family.G.card) :
    (∃ line ∈ lineParameters family,
      2 * k ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∧
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 3 * k - 4 ∧
      ∃ gamma ∈ outsideLine family line,
        ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
          k / 2 + 3 ≤ (secantPetal family line gamma beta).card) ∨
    ∃ line ∈ lineParameters family,
      k + 2 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∧
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 2 * k - 1 ∧
      (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 3 * k - 4 ∧
      (∀ line2 ∈ lineParameters family,
        2 * k + 1 ≤
            (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card +
              2 * (k - 1) ∧
          3 ≤
            (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card) ∧
      ∃ gamma ∈ outsideLine family line,
        ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
          k / 3 + 2 ≤ (secantPetal family line gamma beta).card := by
  rcases card_le_two_mul_or_saturated_high_core_or_saturated_intermediate_core
      family hk hn hthreshold hsaturated with hle | hhigh | hmid
  · omega
  · obtain ⟨line, hline, hcore, hcoreCap⟩ := hhigh
    obtain ⟨gamma, hgamma, beta, hbeta, hne, hpetal⟩ :=
      exists_saturated_high_core_petal_ge_half_add_three
        family hk hn hthreshold hsaturated hcard hline hcore
    exact Or.inl
      ⟨line, hline, by omega, hcoreCap,
        gamma, hgamma, beta, hbeta, hne, hpetal⟩
  · obtain ⟨line, hline, hcoreLower, hcoreLt, hcoreCap, hisolated⟩ := hmid
    obtain ⟨gamma, hgamma, beta, hbeta, hne, hpetal⟩ :=
      exists_outside_secantPetal_card_gt_third_of_saturated_intermediate
        family hk hn hthreshold hsaturated hcard hline hcoreLower hcoreLt
    apply Or.inr
    refine ⟨line, hline, by omega, by omega, hcoreCap, ?_,
      gamma, hgamma, beta, hbeta, hne, by omega⟩
    intro line2 hline2
    obtain ⟨hexact, hthree⟩ := hisolated line2 hline2
    exact ⟨by omega, hthree⟩

/-- Dichotomy form without a counterexample hypothesis.  Either the family is
bounded by the domain or it carries one of the two complete global petal
witness packages from
`exists_high_core_half_petal_or_intermediate_third_petal_of_card_gt_two_mul`. -/
theorem card_le_two_mul_or_high_core_half_petal_or_intermediate_third_petal
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = h + 1)
    (hsaturated : h = 2 * k) :
    family.G.card ≤ 2 * h ∨
      (∃ line ∈ lineParameters family,
        2 * k ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∧
        (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 3 * k - 4 ∧
        ∃ gamma ∈ outsideLine family line,
          ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
            k / 2 + 3 ≤ (secantPetal family line gamma beta).card) ∨
      ∃ line ∈ lineParameters family,
        k + 2 ≤ (jointCore dom (u 0) (u 1) line.1 line.2).card ∧
        (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 2 * k - 1 ∧
        (jointCore dom (u 0) (u 1) line.1 line.2).card ≤ 3 * k - 4 ∧
        (∀ line2 ∈ lineParameters family,
          2 * k + 1 ≤
              (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card +
                2 * (k - 1) ∧
            3 ≤
              (uncoveredByTwoLineCores dom (u 0) (u 1) line line2).card) ∧
        ∃ gamma ∈ outsideLine family line,
          ∃ beta ∈ outsideLine family line, gamma ≠ beta ∧
            k / 3 + 2 ≤ (secantPetal family line gamma beta).card := by
  by_cases hcard : family.G.card ≤ 2 * h
  · exact Or.inl hcard
  · exact Or.inr <|
      exists_high_core_half_petal_or_intermediate_third_petal_of_card_gt_two_mul
        family hk hn hthreshold hsaturated (by omega)

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterGlobalPetalSynthesis

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterGlobalPetalSynthesis
#print axioms exists_high_core_half_petal_or_intermediate_third_petal_of_card_gt_two_mul
#print axioms card_le_two_mul_or_high_core_half_petal_or_intermediate_third_petal
