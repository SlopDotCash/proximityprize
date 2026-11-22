/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoErrorPrimeBand
import ArkLib.Research.ProximityGap.Frontier.AuxiliarySixRows

/-! # Exact four-rate list thresholds for smooth 128-site domains in a prime band -/

namespace ProximityGap.Smooth128PrimeBand

open Code GrandChallenges TwoErrorPrimeBand
open AuxiliaryRatioSlotData AuxiliaryRatioSlotFacts
open scoped NNReal ENNReal

private instance : NeZero (128 : F) := ⟨by decide⟩

variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]

/-- The first over-budget error counts are 63, 97, 113 and 121 in decreasing
rate order. The equivalence includes arbitrary real radii and all positive widths. -/
theorem thresholds {p : ℕ} [Fact p.Prime] (band : InBand p)
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=128)
    (j : Fin 4) (m : ℕ) (hm : 0<m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → ZMod p))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card (ZMod p) : ENNReal) ↔
        δ < (FourRateList128.firstBad j : ℝ)/128 :=
  smooth_thresholds_of_six domain (root : F) primitive (fun _ => rfl) AuxiliarySixRows.six
    band D hn j m hm δ

/-- The list-decoding prize on every smooth 128-site domain over a prime in
the numerical band, at each positive interleaving width. -/
theorem prize {p : ℕ} [Fact p.Prime] (band : InBand p)
    (D : I ↪ ZMod p) [ReedSolomon.Smooth D] (hn : Fintype.card I=128)
    (m : ℕ) (hm : 0<m) : listDecodingPrize D m :=
  smooth_prize_of_six domain (root : F) primitive (fun _ => rfl) AuxiliarySixRows.six
    band D hn m hm

open ArkLib.ProximityGap.Frontier.DyadicLogWitness237 (P)

/-- Exact thresholds on the specified 237-bit field. -/
theorem thresholds237 (D : I ↪ ZMod P) [ReedSolomon.Smooth D] (hn : Fintype.card I=128)
    (j : Fin 4) (m : ℕ) (hm : 0<m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code D (prizeDimension (ι := I) j) : Set (I → ZMod P))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card (ZMod P) : ENNReal) ↔
        δ < (FourRateList128.firstBad j : ℝ)/128 :=
  thresholds inBand237 D hn j m hm δ

/-- The specified field satisfies the sponsor's list-decoding prize predicate
at every smooth 128-site domain and every positive width. -/
theorem prize237 (D : I ↪ ZMod P) [ReedSolomon.Smooth D] (hn : Fintype.card I=128)
    (m : ℕ) (hm : 0<m) : listDecodingPrize D m :=
  prize inBand237 D hn m hm

end ProximityGap.Smooth128PrimeBand

#print axioms ProximityGap.Smooth128PrimeBand.thresholds
#print axioms ProximityGap.Smooth128PrimeBand.prize
#print axioms ProximityGap.Smooth128PrimeBand.prize237
