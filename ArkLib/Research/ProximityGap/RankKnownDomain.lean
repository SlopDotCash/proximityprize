/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.RankReview
import ArkLib.Research.ProximityGap.KnownDomainReview

/-! # Consistency of the finite rank formula with the four known prime-field thresholds

The numerical length-128 proof and the support-rank proof predict the same boundaries.
Uniqueness lets us compare the predictions without executing the large finite enumeration.
-/

namespace FullPrizeReview
open scoped NNReal

/-- The safe radii through one uniquely determine the boundary of a positive-length code. -/
theorem correctBoundary_unique {n : ℕ} (hn : 0 < n) {a b : Boundary n} {safe : ℝ≥0 → Prop}
    (ha : correctBoundary n a safe) (hb : correctBoundary n b safe) : a = b := by
  have hpos : 0 < (n : ℝ≥0) := by exact_mod_cast hn
  have hgrid (e : Fin (n + 1)) : (e.val : ℝ≥0) / n ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast Nat.le_of_lt_succ e.isLt) (by positivity)
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j =>
      have hs := (ha _ (hgrid j)).mpr trivial
      exact False.elim ((lt_irrefl _) ((hb _ (hgrid j)).mp hs))
  | some i =>
    cases b with
    | none =>
      have hs := (hb _ (hgrid i)).mpr trivial
      exact False.elim ((lt_irrefl _) ((ha _ (hgrid i)).mp hs))
    | some j =>
      congr 1
      apply le_antisymm
      · by_contra! h
        have hlt : (j.val : ℝ≥0) / n < (i.val : ℝ≥0) / n :=
          (div_lt_div_iff_of_pos_right hpos).mpr (by exact_mod_cast h)
        have hs := (ha _ (hgrid j)).mpr hlt
        exact (lt_irrefl _) ((hb _ (hgrid j)).mp hs)
      · by_contra! h
        have hlt : (i.val : ℝ≥0) / n < (j.val : ℝ≥0) / n :=
          (div_lt_div_iff_of_pos_right hpos).mpr (by exact_mod_cast h)
        have hs := (hb _ (hgrid i)).mpr hlt
        exact (lt_irrefl _) ((ha _ (hgrid i)).mp hs)

end FullPrizeReview

namespace ProximityPrize.RankKnownDomain
open ProximityGap ProximityGap.GrandChallenges FourRateListPrime246 FullPrizeReview
open scoped NNReal

/-- At every eligible dimension the rank test has the known MCA boundary, and at every
positive width its list prediction is the known numerical first failing count. -/
theorem agreesWithPrime246 (k : ℕ) (hk : hasPrizeRate (Fintype.card H) k) :
    RankReview.mcaAnswer domain (prizeThreshold : ℝ≥0) k = KnownDomainReview.mcaAnswer k ∧
    ∀ m : ℕ, 0 < m →
      RankReview.listAnswer domain (prizeThreshold : ℝ≥0) k m =
        KnownDomainReview.listAnswer k m := by
  obtain ⟨hM, hL⟩ := RankReview.correctForEveryDomain domain (prizeThreshold : ℝ≥0) k hk
  obtain ⟨hM', hL'⟩ := KnownDomainReview.correctForPrime246 k hk
  exact ⟨correctBoundary_unique Fintype.card_pos hM hM',
    fun m hm => correctBoundary_unique Fintype.card_pos (hL m hm) (hL' m hm)⟩

/-- The rank answers give these four pairs of first failing counts in decreasing rate order.
An absent MCA count means that every radius through one passes. -/
theorem numericalBoundaries (m : ℕ) (hm : 0 < m) :
    [64, 32, 16, 8].map (fun k =>
      ((RankReview.mcaAnswer domain (prizeThreshold : ℝ≥0) k).map Fin.val,
       (RankReview.listAnswer domain (prizeThreshold : ℝ≥0) k m).map Fin.val)) =
    [(some 62, some 63), (none, some 97), (none, some 113), (none, some 121)] := by
  have h64 := agreesWithPrime246 64 (by norm_num [hasPrizeRate, card_H])
  have h32 := agreesWithPrime246 32 (by norm_num [hasPrizeRate, card_H])
  have h16 := agreesWithPrime246 16 (by norm_num [hasPrizeRate, card_H])
  have h8 := agreesWithPrime246 8 (by norm_num [hasPrizeRate, card_H])
  simp only [List.map_cons, List.map_nil, h64.1, h64.2 m hm, h32.1, h32.2 m hm,
    h16.1, h16.2 m hm, h8.1, h8.2 m hm]
  rfl

#print axioms numericalBoundaries
#print axioms FullPrizeReview.correctBoundary_unique
#print axioms agreesWithPrime246
end ProximityPrize.RankKnownDomain
