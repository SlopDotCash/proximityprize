/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRDegenerateCount

/-!
# The exact QR cubic-supply closed form (#389)

Final numeric step of the QR cubic-supply arc.

* `qrNegTwo_card_eq` -- `#qrNegTwo = #QR*` if `-2` is a square, else `0` (for `a in QR*`,
  `-2a` is a nonzero square iff `-2` is, since `a` is a nonzero square).
* `qr_cubic_supply_closed` -- division-free: `48.#subsets + 24.#qrNegTwo + 6q = q^2 + 5`
  (`-1` a square, char != 2, 3), from `qr_cubic_supply_exact` and the cyclotomic
  cardinalities `2.#QR*+1 = q`, `4.M+5 = q`.

Specialising `#qrNegTwo` via the mod-8 `-2`-square law (`-2` a square iff `q = 1 (mod 8)`,
given `q = 1 (mod 4)` from `-1` a square) yields the exact cubic-word list size on the QR
domain: `48.#subsets = (q-1)(q-5)` when `q = 5 (mod 8)`, `(q-1)(q-17)` when `q = 1 (mod 8)`,
i.e. `(q-1)(q-5)/48` resp. `(q-1)(q-17)/48` -- the additively-rich delta*-bad end of the
smooth-domain dichotomy, in exact closed form.  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- For a nonzero square `a`, `−2·a` is a nonzero square iff `−2` is a square. -/
theorem mem_qrStar_neg_two_mul {a : F} (h2 : (2 : F) ≠ 0) (ha : a ∈ qrStar (F := F)) :
    (-2 * a ∈ qrStar (F := F)) ↔ IsSquare (-2 : F) := by
  obtain ⟨ha0, s, rfl⟩ := mem_qrStar.mp ha
  rw [mem_qrStar]
  have hs0 : s ≠ 0 := by rintro rfl; simp at ha0
  constructor
  · rintro ⟨_, hsq⟩
    have hinv : IsSquare (s⁻¹ * s⁻¹) := ⟨s⁻¹, rfl⟩
    have hmul : IsSquare ((-2 * (s * s)) * (s⁻¹ * s⁻¹)) := IsSquare.mul hsq hinv
    have he : (-2 * (s * s)) * (s⁻¹ * s⁻¹) = -2 := by field_simp
    rwa [he] at hmul
  · intro hsq
    have hss : IsSquare (s * s) := ⟨s, rfl⟩
    refine ⟨?_, IsSquare.mul hsq hss⟩
    simp only [ne_eq, mul_eq_zero, neg_eq_zero, not_or]
    exact ⟨h2, hs0, hs0⟩

/-- **The minus-two-closed square count**: `#qrNegTwo = #QR*` if `−2` is a square, else `0`. -/
theorem qrNegTwo_card_eq (h2 : (2 : F) ≠ 0) :
    (qrNegTwo (F := F)).card
      = if IsSquare (-2 : F) then (qrStar (F := F)).card else 0 := by
  classical
  by_cases h : IsSquare (-2 : F)
  · rw [if_pos h, qrNegTwo, Finset.filter_true_of_mem]
    intro a ha; exact (mem_qrStar_neg_two_mul h2 ha).mpr h
  · rw [if_neg h, qrNegTwo, Finset.filter_false_of_mem, Finset.card_empty]
    intro a ha hmem; exact h ((mem_qrStar_neg_two_mul h2 ha).mp hmem)

/-- **The exact QR cubic-supply closed form** (division-free): with `q = |F|`,
`48·#subsets + 24·#qrNegTwo + 6q = q² + 5` (`−1` a square, char ≠ 2, 3).  Specialising
`#qrNegTwo` (= `#QR* = (q−1)/2` if `−2` is a square, else `0`) gives
`48·#subsets = (q−1)(q−5)` resp. `(q−1)(q−17)`. -/
theorem qr_cubic_supply_closed (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hneg1 : IsSquare (-1 : F)) :
    48 * (qrSumZeroSubsets (F := F)).card + 24 * (qrNegTwo (F := F)).card
        + 6 * Fintype.card F
      = Fintype.card F ^ 2 + 5 := by
  have hexact := qr_cubic_supply_exact (F := F) hneg1 h3
  have hs := qrStar_card_eq (F := F) h2
  have hm := qrConsec_card_eq (F := F) h2 hneg1
  nlinarith [hexact, hs, hm, Nat.mul_le_mul (le_refl (2 * (qrStar (F := F)).card))
    (le_refl (4 * (qrConsec (F := F)).card))]

end ProximityGap.PairRank
