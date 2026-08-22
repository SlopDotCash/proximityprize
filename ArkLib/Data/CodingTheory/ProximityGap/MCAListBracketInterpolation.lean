/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.EpsMCAInterleavedList

/-!
# The LD⇔MCA bracket interpolation (#357 S2): one ledger for both prize quantities

[ABF26] §5 asks (informally) whether the interleaved list-decoding profile of a code
*controls* its MCA threshold — the "collapse" question. This repository holds both halves of
the dictionary as verified code: the upper transport
`epsMCA_le_of_interleavedList_card_le` (a uniform interleaved list bound `L` at the collapse
floor prices `ε_mca ≤ (1 + 2δn·L)/q`) and the lower engine
`epsMCA_ge_card_div_of_mcaEvent_set` (any stack with a bad-scalar set `G` prices
`ε_mca ≥ |G|/q`; `DeepQuotientTransfer` feeds it from list configurations losslessly). This
file welds the two halves **through the `mcaDeltaStar` ledger**, making the collapse
question a quantitative statement about one number:

* `mcaDeltaStar_eq_of_jump` — **the jump-pin engine** (extracted from the R1 exact-point
  assembly): if every radius below `δ₀` is good and `δ₀` itself is bad, then
  `mcaDeltaStar = δ₀` exactly. Every future exact-`δ*` value enters the ledger through this
  single lemma.
* `le_mcaDeltaStar_of_interleavedList_profile` — list certificate ⟹ ledger lower bracket,
  at explicit price `(1 + (n − (2t−n))·L)/q ≤ ε*`.
* `mcaDeltaStar_le_of_badStack` — bad-stack certificate ⟹ ledger upper bracket, at
  explicit price `ε* < |G|/q`.
* **`mcaDeltaStar_eq_of_certificates_meet`** — the quantified collapse: if list
  certificates with admissible prices exist at every radius below `δ₀`, and a bad stack
  with `|G|/q > ε*` exists at `δ₀`, then `δ*_MCA` **equals** `δ₀`. The ABF26 §5 question
  becomes: *for which codes do the two certificate families meet?* — with the loss
  accounted exactly: the good side pays the collapse-floor factor `(1 + 2δn·L)`, the bad
  side is lossless in the count.

The R1 instance (`MCADeltaStarExactPoint.lean`) is precisely the toy case where the two
families meet at `δ₀ = 1/4`; this file makes the pattern available for every future rung.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- [ABF26] ePrint 2026/680 §5. Issue #357 (S2 in the campaign dossier).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAThresholdLedger ProximityGap.MCAWitnessSpread
open Round17CAPair InterleavedMCACollapse

namespace ProximityGap.MCAListBracketInterpolation

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **The jump-pin engine.** If every radius strictly below `δ₀` is good
(`ε_mca ≤ ε*`) and `δ₀` itself is bad (`ε* < ε_mca`), then the MCA threshold equals `δ₀`
exactly — the supremum of good radii sits at the jump and is not attained. Extracted from
the R1 exact-point assembly; every exact-`δ*` value enters the ledger through this lemma. -/
theorem mcaDeltaStar_eq_of_jump (C : Set (ι → A)) (εstar : ℝ≥0∞) {δ₀ : ℝ≥0}
    (hδ₀ : δ₀ ≤ 1)
    (hgood : ∀ δ : ℝ≥0, δ < δ₀ → epsMCA (F := F) (A := A) C δ ≤ εstar)
    (hbad : εstar < epsMCA (F := F) (A := A) C δ₀) :
    mcaDeltaStar (F := F) (A := A) C εstar = δ₀ := by
  refine le_antisymm (mcaDeltaStar_le_of_bad C εstar hbad) ?_
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨δ, hδ1, hδ2⟩ := exists_between hcon
  have hle := le_mcaDeltaStar_of_good (F := F) (A := A) C εstar
    (le_trans hδ2.le hδ₀) (hgood δ hδ2)
  exact absurd (lt_of_le_of_lt hle hδ1) (lt_irrefl _)

open Classical in
/-- **List certificate ⟹ ledger lower bracket.** A uniform interleaved list bound `L` at
the collapse floor of radius `δ`, whose price `(1 + (n − (2t−n))·L)/q` clears `ε*`, puts
`δ` below the MCA threshold. -/
theorem le_mcaDeltaStar_of_interleavedList_profile (C : Finset (ι → F))
    (hC : PairClosed C) {δ : ℝ≥0} (hδ : δ ≤ 1) (L : ℕ)
    (hL : ∀ u₀ u₁ : ι → F,
      (interleavedList C u₀ u₁
        (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)).card ≤ L)
    {εstar : ℝ≥0∞}
    (hprice : ((1 + (Fintype.card ι -
        (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) * L : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := F) (↑C : Set (ι → F)) εstar :=
  le_mcaDeltaStar_of_good _ _ hδ
    (le_trans (epsMCA_le_of_interleavedList_card_le C hC δ L hL) hprice)

open Classical in
/-- **Bad-stack certificate ⟹ ledger upper bracket.** Any stack carrying a bad-scalar set
`G` with `|G|/q > ε*` at radius `δbad` caps the MCA threshold at `δbad`. (The
`DeepQuotientTransfer` engine produces such stacks losslessly from interleaved
list-decoding configurations.) -/
theorem mcaDeltaStar_le_of_badStack (C : Set (ι → A)) {εstar : ℝ≥0∞} {δbad : ℝ≥0}
    (u : WordStack A (Fin 2) ι) (G : Finset F)
    (hG : ∀ γ ∈ G, mcaEvent (F := F) C δbad (u 0) (u 1) γ)
    (hprice : εstar < (G.card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := A) C εstar ≤ δbad :=
  mcaDeltaStar_le_of_bad C εstar
    (lt_of_lt_of_le hprice (epsMCA_ge_card_div_of_mcaEvent_set C δbad u G hG))

open Classical in
/-- **The quantified ABF26 §5 collapse.** If interleaved-list certificates with admissible
prices exist at *every* radius below `δ₀`, and a bad stack with `|G|/q > ε*` exists *at*
`δ₀`, then the MCA threshold is pinned **exactly**:

  `mcaDeltaStar(C, ε*) = δ₀`.

The collapse question "does the interleaved list profile control `δ*_MCA`?" is hereby
reduced to the meeting of two certificate families, with the loss priced explicitly: the
good side pays the collapse-floor factor `(1 + (n − (2t−n))·L)`, the bad side is lossless
in the count. The R1 instance is the toy case where the families meet at `δ₀ = 1/4`. -/
theorem mcaDeltaStar_eq_of_certificates_meet (C : Finset (ι → F)) (hC : PairClosed C)
    {δ₀ : ℝ≥0} (hδ₀ : δ₀ ≤ 1) {εstar : ℝ≥0∞} (Lof : ℝ≥0 → ℕ)
    (hupper : ∀ δ : ℝ≥0, δ < δ₀ → ∀ u₀ u₁ : ι → F,
      (interleavedList C u₀ u₁
        (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)).card ≤ Lof δ)
    (hpriceGood : ∀ δ : ℝ≥0, δ < δ₀ →
      ((1 + (Fintype.card ι -
        (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) * Lof δ : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (u : WordStack F (Fin 2) ι) (G : Finset F)
    (hG : ∀ γ ∈ G, mcaEvent (F := F) (↑C : Set (ι → F)) δ₀ (u 0) (u 1) γ)
    (hpriceBad : εstar < (G.card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F) (↑C : Set (ι → F)) εstar = δ₀ := by
  refine mcaDeltaStar_eq_of_jump _ _ hδ₀ (fun δ hδ => ?_) ?_
  · exact le_trans
      (epsMCA_le_of_interleavedList_card_le C hC δ (Lof δ) (hupper δ hδ))
      (hpriceGood δ hδ)
  · exact lt_of_lt_of_le hpriceBad
      (epsMCA_ge_card_div_of_mcaEvent_set (↑C : Set (ι → F)) δ₀ u G hG)

/-! ## Source audit -/

#print axioms mcaDeltaStar_eq_of_jump
#print axioms le_mcaDeltaStar_of_interleavedList_profile
#print axioms mcaDeltaStar_le_of_badStack
#print axioms mcaDeltaStar_eq_of_certificates_meet

end ProximityGap.MCAListBracketInterpolation
