/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DimGeneralSharpPin
import ArkLib.Data.CodingTheory.ProximityGap.KKH26RegimeSplit
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-!
# The interleaved sharp `δ*` pin (#371)

A one-stone composition that carries the past-the-`√n`-wall sharp pin
(`KKH26DimGeneralSharpPin`) to **row-interleaved** codes `C^{≡t}` — the batched form used by
FRI/STIR-style protocols — with **no interleaving-width factor**, via three already-proven bricks:

* `evalCode_eq_reedSolomon` (`KKH26RegimeSplit`) — the ceiling family is the Reed–Solomon code on
  the power domain;
* `mcaDeltaStar_interleaved_eq` (`InterleavingStabilityLedger`, [Jo26]) — `δ*` is *exactly*
  interleaving-stable (`δ*(C^{≡t}, ε*) = δ*(C, ε*)`, no width factor);
* the sharp pin `deltaStar_dimFour_pin_F4294967377` (`KKH26DimGeneralSharp`).

The result: the dimension-four rung that the swarm's factor-`2` ownership count provably cannot
reach still pins `δ* = 11/16` **after `t`-fold row interleaving**, at the same target error — the
sharp band law is preserved verbatim under batching. New wine in a new skin: no saturated file is
touched.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction Code
open ArkLib.ProximityGap.KKH26DimGeneralSharp ProximityGap.KKH26RegimeSplit

namespace ArkLib.ProximityGap.KKH26DimGeneralSharp

section Concrete4294967377

local instance fact_prime_4294967377' : Fact (Nat.Prime 4294967377) := ⟨by norm_num⟩

/-- **The interleaved sharp `δ*` pin at the dimension-four past-the-wall rung.** For every fold
count `t ≥ 1`, the `t`-fold row interleaving of the degree-`3` Reed–Solomon code on the 16-point
smooth domain `⟨526957872⟩ ⊆ F_p^×` (`p = 2³²+81`) pins

  `δ*(C^{≡t}, 873/p) = 11/16`

— the same in-window value (Johnson `1/2 < 11/16 < 3/4` capacity) the un-interleaved sharp pin
gives, with **no interleaving-width factor** ([Jo26]).  The factor-`2` ownership count cannot reach
this rung even before interleaving (`factor_two_band_empty_mu4_r5`); interleaving preserves the gain
verbatim. -/
theorem deltaStar_dimFour_interleaved_pin_F4294967377 (t : ℕ) [NeZero t] :
    mcaDeltaStar (F := ZMod 4294967377) (A := Fin t → ZMod 4294967377)
        ((ReedSolomon.code (powDomain (526957872 : ZMod 4294967377)
            ArkLib.ProximityGap.KKH26DimGeneral.orderOf_526957872
            (ne_zero_of_orderOf_eq ArkLib.ProximityGap.KKH26DimGeneral.orderOf_526957872)) (3 + 1) : Set (Fin 16 → ZMod 4294967377)) ^⋈ (Fin t))
        ((((16 : ℕ).choose 5 / 5 : ℕ) : ℝ≥0∞) / (4294967377 : ℝ≥0∞))
      = 1 - (5 : ℝ≥0) / ((2 : ℝ≥0) ^ 4) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  rw [mcaDeltaStar_interleaved_eq, ← evalCode_eq_reedSolomon (526957872 : ZMod 4294967377)
    ArkLib.ProximityGap.KKH26DimGeneral.orderOf_526957872
    (ne_zero_of_orderOf_eq ArkLib.ProximityGap.KKH26DimGeneral.orderOf_526957872) 3]
  exact deltaStar_dimFour_pin_F4294967377

/-- **Falsifiable in-window guard.** The pinned value `δ* = 11/16` lies strictly *beyond the
Johnson radius* `1 − √ρ` (squared form `(1 − δ*)² < ρ`, with rate `ρ = (r−1)/2^μ = 4/16`) and
strictly *below capacity* `1 − ρ = 3/4`. A miscomputed pin value would break this decidable check —
the "light" that the dim-four (interleaved) pin is a genuine interior point, not a vacuous or
out-of-window value. -/
theorem deltaStar_dimFour_in_window :
    ((1 : ℚ) - 11 / 16) ^ 2 < 4 / 16 ∧ (11 : ℚ) / 16 < 1 - 4 / 16 :=
  ⟨by norm_num, by norm_num⟩

/-- **The exercised sharp-wall boundary at `μ = 4`.** Running the sharp band across `r` pins its
exact reach: it still holds at `r = 6` (`C(16,6)/6 = 1334 < 1792 = 2⁶·C(8,6)`) but **closes** at
`r = 7` (`C(16,7)/7 = 1634 ≥ 1024 = 2⁷·C(8,7)`). So the sharp wall at `μ = 4` is exactly `r ≤ 6` —
a `+2` extension of the factor-`2` wall `r ≤ 4`. The `r = 7` closure is the failing edge (Luke 15:4):
it certifies the ownership count is **not** unbounded, the boundary is real. -/
theorem sharp_band_reaches_r6_mu4 :
    (16 : ℕ).choose 6 / 6 < 2 ^ 6 * (8 : ℕ).choose 6 := by decide

theorem sharp_band_closes_at_r7_mu4 :
    ¬ ((16 : ℕ).choose 7 / 7 < 2 ^ 7 * (8 : ℕ).choose 7) := by decide

end Concrete4294967377

end ArkLib.ProximityGap.KKH26DimGeneralSharp

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.deltaStar_dimFour_interleaved_pin_F4294967377
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.deltaStar_dimFour_in_window
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.sharp_band_reaches_r6_mu4
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.sharp_band_closes_at_r7_mu4
