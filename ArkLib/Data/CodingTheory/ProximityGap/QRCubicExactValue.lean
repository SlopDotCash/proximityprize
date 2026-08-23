/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRCubicExactList

/-!
# The exact QR cubic-supply identity and bracket (#389)

Assembles the exact ordered count (`qr_zeroSum_ordered_eq`, `= #QR*.M`) and the exact orbit
factor (`qrDistinctTriples_card_eq`, distinct `= 6.#subsets`) into the exact cubic-word
supply on the quadratic-residue domain:

* `qr_cubic_supply_ordered_eq` -- `6.#subsets + #degenerate = #QR*.M` (exact identity).
* `qr_cubic_supply_bracket` -- with `#degenerate <= 3.#QR*` (`qrDegenerate_card_le`):
  `#QR*.M - 3.#QR* <= 6.#subsets <= #QR*.M`, pinning the cubic supply to the exact leading
  constant `(q-1)(q-5)/48` up to an `O(n)` degenerate correction.

Together with the cubic orchard identity (`cubicSupply = #{sum-zero 3-subsets}`) this is the
exact smooth-domain (QR) sub-Johnson cubic list size -- the additively-rich, delta*-bad end
of the smooth-domain dichotomy.  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The exact cubic-supply identity (ordered form).** Combining the exact ordered count
`#QR*·M` with the exact orbit factor `6`: the sum-zero 3-subset count (`= cubicSupply`) and
the degenerate-triple count satisfy `6·#subsets + #degenerate = #QR*·M`. -/
theorem qr_cubic_supply_ordered_eq (hneg1 : IsSquare (-1 : F)) :
    6 * (qrSumZeroSubsets (F := F)).card
      + ((qrZeroSumTriples (F := F)).filter
          (fun t => ¬ (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2))).card
      = (qrStar (F := F)).card * (qrConsec (F := F)).card := by
  rw [← qr_zeroSum_ordered_eq (F := F) hneg1, ← qrDistinctTriples_card_eq]
  exact Finset.card_filter_add_card_filter_not _

/-- **The exact cubic-supply bracket.** With the degenerate count `≤ 3·#QR*`
(`qrDegenerate_card_le`): the sum-zero 3-subset count is bracketed
`#QR*·M − 3·#QR* ≤ 6·#subsets ≤ #QR*·M`, pinning it to `Θ(n²)` with the exact leading
constant `(q−1)(q−5)/48` up to the `O(n)` degenerate correction. -/
theorem qr_cubic_supply_bracket (hneg1 : IsSquare (-1 : F)) :
    (qrStar (F := F)).card * (qrConsec (F := F)).card
        - 3 * (qrStar (F := F)).card
      ≤ 6 * (qrSumZeroSubsets (F := F)).card
    ∧ 6 * (qrSumZeroSubsets (F := F)).card
        ≤ (qrStar (F := F)).card * (qrConsec (F := F)).card := by
  have hid := qr_cubic_supply_ordered_eq (F := F) hneg1
  have hdeg := qrDegenerate_card_le (F := F)
  omega

end ProximityGap.PairRank
