/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.EpsMCAInterleavedList
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# The δ* sandwich: pinning `mcaDeltaStar` between list-decoding data (#357, R1)

The campaign's R1 hypothesis: δ* is governed, on both sides, by interleaved
list-decoding behaviour.  This file welds the two in-tree dictionary halves into the
two-sided bracket on the formal threshold `mcaDeltaStar` — making "pin δ*" formally
equivalent to supplying list data at the two radii until they meet:

* **Good side** (`mcaDeltaStar_ge_of_interleavedList`): an interleaved list-size bound
  `L` at radius `δ` with `(1 + (n − (2t − n))·L)/q ≤ ε*` forces `δ ≤ mcaDeltaStar` —
  composing `epsMCA_le_of_interleavedList_card_le` (the LD⇒MCA upper dictionary) with
  the bracket lemma `le_mcaDeltaStar_of_good`.
* **Bad side** (`mcaDeltaStar_le_of_badFamily`): any stack with a bad-scalar family
  `G` of mass `ε* < |G|/q` at radius `δbad` forces `mcaDeltaStar ≤ δbad` — composing
  `epsMCA_ge_card_div_of_mcaEvent_set` (the witness-spread lower dictionary, fed by
  the DEEP-quotient transfer engine) with `mcaDeltaStar_le_of_bad`.
* **The sandwich** (`mcaDeltaStar_sandwich`): both at once,
  `δgood ≤ mcaDeltaStar C ε* ≤ δbad`.

Pinning δ* for a given code and `ε*` is now *literally* the statement that the two
kinds of list data exist at radii `δgood, δbad` with `δbad − δgood → 0`: the upper
data is interleaved list-decodability (the open beyond-Johnson question for explicit
RS), the lower data is a separated list configuration (KKH26-style constructions,
supplied in-tree by `deep_quotient_epsMCA_lower_bound`).  The conjecture-level content
of the problem is exactly the gap between the radii at which the two suppliers
currently operate.
-/

open Finset Code InterleavedMCACollapse Round17CAPair
open scoped NNReal ENNReal ProbabilityTheory BigOperators

namespace ProximityGap.MCAThresholdLedger

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **Good side of the sandwich.**  An interleaved list bound at the collapse floor,
strong enough that the dictionary bound sits below `ε*`, pushes `mcaDeltaStar` up to
`δ`. -/
theorem mcaDeltaStar_ge_of_interleavedList (C : Finset (ι → F))
    (hC : Round17CAPair.PairClosed C) (εstar : ℝ≥0∞) {δ : ℝ≥0} (hδ : δ ≤ 1) (L : ℕ)
    (hL : ∀ u₀ u₁ : ι → F,
      (InterleavedMCACollapse.interleavedList C u₀ u₁
        (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)).card ≤ L)
    (hε : ((1 + (Fintype.card ι -
        (2 * ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) * L : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := F) (↑C : Set (ι → F)) εstar :=
  le_mcaDeltaStar_of_good _ _ hδ
    (le_trans (ProximityGap.epsMCA_le_of_interleavedList_card_le C hC δ L hL) hε)

open Classical in
/-- **Bad side of the sandwich.**  A bad-scalar family of probability mass exceeding
`ε*` at radius `δbad` pushes `mcaDeltaStar` down to `δbad`. -/
theorem mcaDeltaStar_le_of_badFamily (C : Set (ι → A)) (εstar : ℝ≥0∞) {δbad : ℝ≥0}
    (u : WordStack A (Fin 2) ι) (G : Finset F)
    (hG : ∀ γ ∈ G, mcaEvent C δbad (u 0) (u 1) γ)
    (hε : εstar < (G.card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := A) C εstar ≤ δbad :=
  mcaDeltaStar_le_of_bad C εstar
    (lt_of_lt_of_le hε
      (ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set C δbad u G hG))

open Classical in
/-- **The δ\* sandwich (R1).**  Interleaved list data at `δgood` and a bad family at
`δbad` bracket the formal threshold:

  `δgood ≤ mcaDeltaStar C ε* ≤ δbad`.

The threshold problem for `(C, ε*)` is *equivalent* to driving the two data sources
toward a common radius. -/
theorem mcaDeltaStar_sandwich (C : Finset (ι → F))
    (hC : Round17CAPair.PairClosed C) (εstar : ℝ≥0∞)
    {δgood δbad : ℝ≥0} (hδg : δgood ≤ 1) (L : ℕ)
    (hL : ∀ u₀ u₁ : ι → F,
      (InterleavedMCACollapse.interleavedList C u₀ u₁
        (2 * ⌈(1 - δgood) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)).card ≤ L)
    (hε : ((1 + (Fintype.card ι -
        (2 * ⌈(1 - δgood) * (Fintype.card ι : ℝ≥0)⌉₊ - Fintype.card ι)) * L : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (u : WordStack F (Fin 2) ι) (G : Finset F)
    (hG : ∀ γ ∈ G, mcaEvent (↑C : Set (ι → F)) δbad (u 0) (u 1) γ)
    (hbad : εstar < (G.card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    δgood ≤ mcaDeltaStar (F := F) (A := F) (↑C : Set (ι → F)) εstar ∧
      mcaDeltaStar (F := F) (A := F) (↑C : Set (ι → F)) εstar ≤ δbad :=
  ⟨mcaDeltaStar_ge_of_interleavedList C hC εstar hδg L hL hε,
    mcaDeltaStar_le_of_badFamily (↑C : Set (ι → F)) εstar u G hG hbad⟩

end ProximityGap.MCAThresholdLedger

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MCAThresholdLedger.mcaDeltaStar_ge_of_interleavedList
#print axioms ProximityGap.MCAThresholdLedger.mcaDeltaStar_le_of_badFamily
#print axioms ProximityGap.MCAThresholdLedger.mcaDeltaStar_sandwich
