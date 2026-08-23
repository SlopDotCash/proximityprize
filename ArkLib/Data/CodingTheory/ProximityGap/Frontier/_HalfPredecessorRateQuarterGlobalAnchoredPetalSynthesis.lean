/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterGlobalPetalSynthesis
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterPetalIteration

/-!
# Rate-quarter half predecessor: global anchored petal synthesis

The global petal synthesis selects a quantitatively large canonical secant
petal in either the high-core or intermediate-core branch.  The anchored
iteration API applies to every selected secant.  This file composes those two
facts without changing the witnesses: the same outsider pair that realizes
the half-scale or third-scale petal is a uniform anchor for every later one-
and two-companion comparison.

Consequently, every saturated rate-quarter counterexample has one of two
complete packages:

* a high core in `[2k, 3k - 4]`, a petal of size at least
  `floor(k / 2) + 3`, and both anchored increment rules; or
* an intermediate core in `[k + 2, 2k - 1]`, a petal of size at least
  `floor(k / 3) + 2`, the exact all-partner isolation data, and both anchored
  increment rules.

The companion rules are universal after the anchor is selected, so later
secants may be chosen adaptively without reopening the pruning argument.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPetalIteration
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterGlobalPetalSynthesis

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterGlobalAnchoredPetalSynthesis

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **Global anchored-petal dichotomy at saturated rate one quarter.**

If `|G| > 2h` and `h = 2k`, either a high core or an intermediate core carries
a quantitatively large canonical outsider secant petal.  In both branches the
displayed secant is also a uniform anchor for `OneCompanionIncrementRule` and
`TwoCompanionIncrementRule`.

The intermediate branch preserves the exact failed-cover inequality against
every relevant partner, its three-uncovered-coordinate consequence, and the
sharp `3k - 4` core ceiling. -/
theorem exists_anchored_high_core_half_petal_or_intermediate_third_petal_of_card_gt_two_mul
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
          k / 2 + 3 ≤ (secantPetal family line gamma beta).card ∧
          OneCompanionIncrementRule family line gamma beta ∧
          TwoCompanionIncrementRule family line gamma beta) ∨
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
          k / 3 + 2 ≤ (secantPetal family line gamma beta).card ∧
          OneCompanionIncrementRule family line gamma beta ∧
          TwoCompanionIncrementRule family line gamma beta := by
  rcases
      exists_high_core_half_petal_or_intermediate_third_petal_of_card_gt_two_mul
        family hk hn hthreshold hsaturated hcard with hhigh | hmid
  · obtain ⟨line, hline, hcoreLower, hcoreUpper,
        gamma, hgammaOut, beta, hbetaOut, hne, hpetal⟩ := hhigh
    have hgamma : gamma ∈ family.G :=
      ((mem_outsideLine_iff family line gamma).mp hgammaOut).1
    have hbeta : beta ∈ family.G :=
      ((mem_outsideLine_iff family line beta).mp hbetaOut).1
    have hone := oneCompanionIncrementRule_of_selected_anchor
      family hk line hline hgamma hbeta hne
    have htwo := twoCompanionIncrementRule_of_selected_anchor
      family hk line hline hgamma hbeta hne
    exact Or.inl
      ⟨line, hline, hcoreLower, hcoreUpper,
        gamma, hgammaOut, beta, hbetaOut, hne, hpetal, hone, htwo⟩
  · obtain ⟨line, hline, hcoreLower, hcoreUpper, hcoreCeiling,
        hisolated, gamma, hgammaOut, beta, hbetaOut, hne, hpetal⟩ := hmid
    have hgamma : gamma ∈ family.G :=
      ((mem_outsideLine_iff family line gamma).mp hgammaOut).1
    have hbeta : beta ∈ family.G :=
      ((mem_outsideLine_iff family line beta).mp hbetaOut).1
    have hone := oneCompanionIncrementRule_of_selected_anchor
      family hk line hline hgamma hbeta hne
    have htwo := twoCompanionIncrementRule_of_selected_anchor
      family hk line hline hgamma hbeta hne
    exact Or.inr
      ⟨line, hline, hcoreLower, hcoreUpper, hcoreCeiling, hisolated,
        gamma, hgammaOut, beta, hbetaOut, hne, hpetal, hone, htwo⟩

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterGlobalAnchoredPetalSynthesis

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterGlobalAnchoredPetalSynthesis
#print axioms exists_anchored_high_core_half_petal_or_intermediate_third_petal_of_card_gt_two_mul
