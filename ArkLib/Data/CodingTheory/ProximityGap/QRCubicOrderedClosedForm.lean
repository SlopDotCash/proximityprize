/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRZeroSumTripleScaling

/-!
# The exact ordered zero-sum QR triple count in closed form (#389)

`qr_zeroSum_ordered_eq` proved the ordered zero-sum triples of nonzero squares equal
`#QR* · M`.  Substituting the two cyclotomic cardinalities — `2·#QR* + 1 = q`
(`card_units_squares`) and `4·M + 5 = q` (`qr_shift_count`) — gives the closed form
`#QR* · M = (q−1)(q−5)/8`, here in the division-free `ℕ` shape:

> **`qr_zeroSum_ordered_card`** — `8·#{(a,b,c) ∈ (QR*)³ : a+b+c=0} + 6·q = q² + 5`.

This is `Θ(q²) = Θ(n²)` ordered triples (`n = #QR* = (q−1)/2`): the QR (index-2) domain
is **additively rich**, so its near-capacity cubic supply is quadratic — the
`δ*`-unfavourable end of the smooth-domain spectrum, in sharp contrast to the 2-power
NTT domain `μ_16 ⊂ F₂₅₇` where the cubic supply is exactly `0`
(`cubicSupply_mu16_F257_eq_zero`).  The smooth-domain `δ*` depends on the *arithmetic of
the subgroup*, not merely on smoothness; the production 2-power FFT domains are the good
ones.  Issue #389.
-/

namespace ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The exact ordered zero-sum QR triple count**, division-free over `ℕ`:
`8·#ordered + 6q = q² + 5`, i.e. `#ordered = (q−1)(q−5)/8 = Θ(n²)`. -/
theorem qr_zeroSum_ordered_card (h2 : (2 : F) ≠ 0) (hneg1 : IsSquare (-1 : F)) :
    8 * (qrZeroSumTriples (F := F)).card + 6 * Fintype.card F
      = Fintype.card F ^ 2 + 5 := by
  have hord := qr_zeroSum_ordered_eq (F := F) hneg1
  have hs := qrStar_card_eq (F := F) h2
  have hm := qrConsec_card_eq (F := F) h2 hneg1
  -- abbreviate
  set q := Fintype.card F
  set s := (qrStar (F := F)).card
  set m := (qrConsec (F := F)).card
  rw [hord]
  -- 8·s·m + 6q = q² + 5, from 2s+1 = q and 4m+5 = q
  nlinarith [hs, hm, Nat.mul_le_mul (le_refl (2 * s)) (le_refl (4 * m))]

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.qr_zeroSum_ordered_card
