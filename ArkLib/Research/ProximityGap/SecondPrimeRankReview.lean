/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAStepFunction
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA
import ArkLib.Research.ProximityGap.RankExecutable
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCubicExact

/-! # The numerical rank answer at the second prime -/

namespace ProximityPrize.SecondPrimeRankReview
open Code CoreDefinitions FullPrizeReview ProximityGap ProximityGap.GrandChallenges
open MCAThresholdLedger
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F]

/-- The interior operational supremum specifies all nonnegative real radii, including the
status of the endpoint itself. -/
theorem safe_iff_of_interior_supremum (C : Set (I → F)) (ε b : ℝ≥0)
    (hb : b < 1) (he : mcaDeltaStar (F := F) C (ε : ℝ≥0∞) = b) (δ : ℝ≥0) :
    epsMCA (F := F) C δ ≤ (ε : ℝ≥0∞) ↔ δ < b := by
  classical
  subst b
  constructor
  · intro h
    by_contra! hle
    exact (MCAStepFunction.lt_epsMCA_mcaDeltaStar_of_lt_one C _ hb).not_ge
      ((epsMCA_mono C hle).trans h)
  · intro h
    by_contra! hbad
    exact h.not_ge (mcaDeltaStar_le_of_bad C _ hbad)

/-- For an arbitrary injective domain, a computed interior supremum gives the same output as
the finite support-rank test. No condition on the rate or smoothness is needed. -/
theorem rankAnswer_of_interior_supremum (D : I ↪ F) (ε : ℝ≥0) (k : ℕ)
    (e : Fin (Fintype.card I + 1)) (he : e.val < Fintype.card I)
    (hstar : mcaDeltaStar (F := F) (ReedSolomon.code D k : Set (I → F)) (ε : ℝ≥0∞) =
      (e.val : ℝ≥0) / Fintype.card I) :
    RankReview.mcaAnswer D ε k = some e := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  let E := (Fintype.equivFin I).symm
  let labels := (Finset.univ : Finset F).toList
  have hf (g : F) : g ∈ labels := by simp [labels]
  let C : Set (I → F) := ReedSolomon.code D k
  let n := Fintype.card I
  let B := RankReview.budget F ε
  let safe (i : Fin (n + 1)) := SimultaneousSupportGaussian.anchoredSafe E labels D k B (n - i.val)
  have hn : 0 < (n : ℝ≥0) := by exact_mod_cast Fintype.card_pos (α := I)
  have hb : (e.val : ℝ≥0) / n < 1 := (div_lt_one hn).mpr (by exact_mod_cast he)
  have hs (i : Fin (n + 1)) : safe i = true ↔ i < e := by
    let δ := (i.val : ℝ≥0) / n
    have hg := SimultaneousSupportGaussian.anchoredSafe_iff E labels hf D k B i.val Fintype.card_pos
    change safe i = true ↔ mcaError (AffineLineGenerator F) (ReedSolomon.code D k)
      (δ : ℝ) ≤ (B : ℝ≥0∞) / Fintype.card F at hg
    rw [← epsMCA_eq_mcaError] at hg
    have hf' := SimultaneousSupportRank.epsMCA_le_iff_floor_budget C δ ε
    have hb' := safe_iff_of_interior_supremum C ε _ hb hstar δ
    refine hg.trans (hf'.symm.trans (hb'.trans ?_))
    rw [div_lt_div_iff_of_pos_right hn]
    exact_mod_cast Iff.rfl
  have hit : ∃ i : Fin (n + 1), !safe i := ⟨e, by simpa using (hs e).not.mpr (lt_irrefl _)⟩
  rw [← RankExecutable.mcaBoundary_eq E labels hf D ε k, RankExecutable.mcaBoundary_eq_scan E labels hf D]
  change Fin.find? (fun i => !safe i) = some e
  rw [Fin.find?_eq_some_find_of_exists hit, Option.some.injEq, Fin.find_eq_iff]
  exact ⟨by simpa using (hs e).not.mpr (lt_irrefl _),
    fun i hi => by simpa using (hs i).mpr hi⟩

section Named
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.SecondPrimeCubicExact
open ArkLib.ProximityGap.PrizeShapePrimeP30Second
open ProximityGap.TerminalCollinearHeadCount

local instance : Fact P.Prime := ⟨prime_P⟩

private theorem code_threshold :
    mcaDeltaStar (F := ZMod P) (ReedSolomon.code secondDomain (2 ^ 26) :
      Set (Fin (2 ^ 30) → ZMod P)) ((prizeThreshold : ℝ≥0) : ℝ≥0∞) =
      (715827882 : ℝ≥0) / 1073741824 := by
  have hc := KKH26RegimeSplit.evalCode_eq_reedSolomon g orderOf_g
    (KKH26RegimeSplit.ne_zero_of_orderOf_eq orderOf_g) (2 ^ 26 - 1)
  rw [show 2 ^ 26 - 1 + 1 = (2 ^ 26 : ℕ) by decide] at hc
  rw [← show evalCode g (2 ^ 30) (2 ^ 26 - 1) =
    (ReedSolomon.code secondDomain (2 ^ 26) : Set (Fin (2 ^ 30) → ZMod P)) from hc]
  convert secondPrime_rateSixteenth using 2
  norm_num [prizeThreshold, epsStar]

/-- The rank test first fails at 715827882 errors for the genuine rate-sixteenth code
on the second named subgroup. -/
theorem formulaValue :
    RankReview.mcaAnswer secondDomain (prizeThreshold : ℝ≥0) (2 ^ 26) =
      some ⟨715827882, by rw [Fintype.card_fin]; decide⟩ := by
  have hn : Fintype.card (Fin (2 ^ 30)) = 1073741824 := (Fintype.card_fin _).trans (by decide)
  let e : Fin (Fintype.card (Fin (2 ^ 30)) + 1) := ⟨715827882, by rw [hn]; decide⟩
  have hv : e.val = 715827882 := rfl
  have he : e.val < Fintype.card (Fin (2 ^ 30)) := by rw [hv, hn]; decide
  apply rankAnswer_of_interior_supremum secondDomain (prizeThreshold : ℝ≥0) (2 ^ 26) e he
  rw [hv, hn]
  exact code_threshold

/-- Every real radius below the fraction passes the canonical security test, and the
endpoint and every larger radius fail it. -/
theorem safe_iff (δ : ℝ≥0) :
    epsMCA (F := ZMod P) (ReedSolomon.code secondDomain (2 ^ 26) :
      Set (Fin (2 ^ 30) → ZMod P)) δ ≤ ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ↔
      δ < (715827882 : ℝ≥0) / 1073741824 :=
  safe_iff_of_interior_supremum _ _ _ (by norm_num) code_threshold δ

/-- The final safe integer error count is one less than the first failing count. -/
theorem grid_safe_iff (e : ℕ) :
    epsMCA (F := ZMod P) (ReedSolomon.code secondDomain (2 ^ 26) :
      Set (Fin (2 ^ 30) → ZMod P)) ((e : ℝ≥0) / 1073741824) ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ↔ e ≤ 715827881 := by
  rw [safe_iff, div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ≥0) < 1073741824)]
  exact_mod_cast (show e < 715827882 ↔ e ≤ 715827881 by omega)

/-- The same strict boundary applies at every positive interleaving width for line-MCA. -/
theorem interleaved_safe_iff (m : ℕ) [NeZero m] (δ : ℝ≥0) :
    epsMCA (F := ZMod P) (A := Fin m → ZMod P)
      ((ReedSolomon.code secondDomain (2 ^ 26) : Set (Fin (2 ^ 30) → ZMod P)) ^⋈ (Fin m)) δ ≤
        ((prizeThreshold : ℝ≥0) : ℝ≥0∞) ↔ δ < (715827882 : ℝ≥0) / 1073741824 := by
  rw [epsMCA_interleaved_eq]
  exact safe_iff δ

/-- Every exhaustive presentation of the executable finite rank scan returns the same integer
answer. The result follows by proof and does not require running the full production scan. -/
theorem executableValue (E : Fin (Fintype.card (Fin (2 ^ 30))) ≃ Fin (2 ^ 30))
    (labels : List (ZMod P)) (hf : ∀ g, g ∈ labels) :
    (RankExecutable.mcaBoundary E labels secondDomain (2 ^ 26) 2147483648).map Fin.val =
      some 715827882 := by
  let _ : SampleableType (ZMod P) := SampleableType.ofFintype _
  have hb := RankExecutable.prizeBudget (ZMod P)
  rw [ZMod.card] at hb
  have h := RankExecutable.mcaBoundary_eq E labels hf secondDomain (prizeThreshold : ℝ≥0) (2 ^ 26)
  rw [hb, show P / 2 ^ 128 = 2147483648 by decide, formulaValue] at h
  exact congrArg (Option.map Fin.val) h

end Named
end ProximityPrize.SecondPrimeRankReview
