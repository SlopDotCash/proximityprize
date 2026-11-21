/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FourRateList128
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.NormNum.Prime

/-!
# Four exact list-decoding thresholds on the 128th roots of unity in GF(641^26)

At security error `2^-128`, the first over-budget radii for dimensions
`64, 32, 16, 8` are `63/128, 97/128, 113/128, 121/128`. The same thresholds
hold for every positive interleaving width. At half rate the product fibers
of 65-subsets give the lower bound one agreement beyond the dimension.
-/

namespace ProximityGap.FourRateList641

open Code GrandChallenges
open scoped NNReal ENNReal

instance : Fact (Nat.Prime 641) := ⟨by norm_num⟩

/-- The 243-bit alphabet. -/
abbrev K := GaloisField 641 26

noncomputable instance : Fintype K := Fintype.ofFinite K
noncomputable instance : DecidableEq K := Classical.decEq K

/-- The subgroup of 128th roots of unity used as the coordinate type. -/
noncomputable def H : Subgroup Kˣ := rootsOfUnity 128 K

noncomputable instance : Fintype H := Fintype.ofFinite H

theorem card_K : Fintype.card K = 641^26 :=
  Nat.card_eq_fintype_card.symm.trans (GaloisField.card 641 26 (by decide))

theorem card_H : Fintype.card H = 128 := by
  have h : IsPrimitiveRoot (21 : ZMod 641) 128 := IsPrimitiveRoot.iff_orderOf.mpr
    (orderOf_eq_prime_pow (p := 2) (n := 6) (by decide) (by decide))
  rw [← Nat.card_eq_fintype_card]
  exact (h.map_of_injective (algebraMap (ZMod 641) K).injective).card_rootsOfUnity

/-- The subgroup inclusion defining the evaluation domain. -/
noncomputable abbrev domain : H ↪ K := FourRateList128.domain H

noncomputable instance : ReedSolomon.Smooth domain := FourRateList128.smooth H card_H

/-- First over-budget error count, ordered by decreasing prize rate. -/
def firstBad : Fin 4 → ℕ := FourRateList128.firstBad

theorem budget_window : FourRateList128.BudgetWindow (Fintype.card K) := by
  rw [card_K]
  constructor <;> simp only [Nat.choose_eq_descFactorial_div_factorial] <;> decide

/-- Exact list thresholds at every real radius and every positive width. -/
theorem list_threshold (j : Fin 4) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    (Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code domain (prizeDimension (ι := H) j) : Set (H → K))) δ : ENNReal) ≤
      ((prizeThreshold : ℝ≥0) : ENNReal) * (Fintype.card K : ENNReal) ↔
        δ < (firstBad j : ℝ)/128 :=
  FourRateList128.list_threshold H card_H budget_window j m hm δ

/-- Adjacent grid witnesses for the four prize rates. -/
noncomputable def resolution (j : Fin 4) (m : ℕ) (hm : 0 < m) :
    GrandListResolution (ReedSolomon.code domain (prizeDimension (ι := H) j) : Set (H → K))
      m (prizeThreshold : ℝ≥0) :=
  FourRateList128.resolution H card_H budget_window j m hm

/-- The complete four-rate prize proposition at every positive width. -/
theorem listDecodingPrize_all_rates (m : ℕ) (hm : 0 < m) : listDecodingPrize domain m :=
  FourRateList128.listDecodingPrize_all_rates H card_H budget_window m hm

#print axioms list_threshold
#print axioms listDecodingPrize_all_rates

end ProximityGap.FourRateList641
