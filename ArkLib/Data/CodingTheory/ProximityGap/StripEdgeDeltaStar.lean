/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MonomialStripExplosion
import ArkLib.Data.CodingTheory.ProximityGap.MCAStaircaseMaster
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# Exact δ* at the strip edge: the explosion as a bad certificate (#357)

The strip explosion (`MonomialStripExplosion.strip_eps_ge`) composed with the master
collapse (`MCAStaircaseMaster.epsMCA_le_div_card_of_dist`) and the bracket ledger pins
a **new closed-form exact δ\* family with a strictly wider `ε*`-band than the
granularity ladder**.  For smooth `μ_n = ⟨γ⟩`, `g ∣ n`, and the three dimensions
`k ∈ (n − 3g, n − 3g + 3]` (where the collapse budget `3(g−1) + k ≤ n` and the
explosion window `n − 3g < k ≤ n − 2g` intersect):

  `mcaDeltaStar(RS[F, μ_n, k], ε*) = g/n`  for **every** `ε* ∈ [g/q, (n/g)/q)`.

The granularity ladder (`mcaDeltaStar_eq_granularity` / `GranularityLadderRS`) pins this
value only on `ε* ∈ [g/q, (g+1)/q)` — its bad certificate is the `(g+1)`-spike, worth
`(g+1)/q`.  The explosion certificate is worth `(n/g)/q`, widening the pinned band by
the factor `(n/g − g)/1`-ish; at `(F₁₉, μ₁₈, k ∈ {10,11,12})` the band grows from
`[3/19, 4/19)` to `[3/19, 6/19)`.  These are the first exact δ\* values whose bad half
is the strip-explosion family.

## References

Issue #357; `MonomialStripExplosion.lean` (bad side), `MCAStaircaseMaster.lean` (good
side), `MCAThresholdLedger.lean` (the bracket engine), `GranularityLadderRS.lean` (the
narrower-band predecessor).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.StripEdgeDeltaStar

open scoped NNReal ENNReal ProbabilityTheory
open Finset Polynomial
open ProximityGap Code
open ProximityGap.CensusLowerBound
open ProximityGap.SmoothLadderInstance
open ProximityGap.MonomialStripExplosion
open ProximityGap.MCAThresholdLedger

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n g k : ℕ}

/-- The evaluation code has no nonzero codeword on `≤ m` points when `m + k ≤ n`
(root counting). -/
theorem evalCode_noWeightLE {m : ℕ} (dom : Fin n → F) (hinj : Function.Injective dom)
    (hmk : m + k ≤ n) (hk1 : 1 ≤ k) :
    MCAStaircaseMaster.NoWeightLE (evalCode dom k) m := by
  rintro w ⟨P, hPdeg, hPw⟩ ⟨T, hT, hvan⟩
  have hPz : P = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (f := P) (s := (Finset.univ \ T).image dom) ?_ ?_
    · have hcard : ((Finset.univ \ T).image dom).card = n - T.card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_sdiff,
          Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      rw [hcard]
      calc P.degree ≤ (P.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
        _ ≤ ((k - 1 : ℕ) : WithBot ℕ) := by exact_mod_cast hPdeg
        _ < ((n - T.card : ℕ) : WithBot ℕ) := by
            exact_mod_cast (by omega : k - 1 < n - T.card)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [← hPw i]
      exact hvan i (Finset.mem_sdiff.mp hi).2
  funext i
  rw [hPw i, hPz]
  simp

open Classical in
/-- **Exact δ\* at the strip edge.**  For `μ_n = ⟨γ⟩`, `g ∣ n`,
`n − 3g < k`, `k ≤ n − 2g`, `3(g−1) + k ≤ n`, `1 ≤ g`, `2g < n`, and every
`ε* ∈ [g/|F|, (n/g)/|F|)`:

  `mcaDeltaStar(RS[F, μ_n, k], ε*) = g/n` — with the bad half supplied by the
  strip-explosion family (worth `(n/g)/q`, not the spike's `(g+1)/q`). -/
theorem mcaDeltaStar_eq_strip_edge [Nonempty (Fin n)] (γ : F) (hord : orderOf γ = n)
    (hg1 : 1 ≤ g) (hgn : g ∣ n) (hk_lo : n - 3 * g < k) (hk_hi : k ≤ n - 2 * g)
    (hn2g : 2 * g < n) (hk3 : 3 * (g - 1) + k ≤ n) {εstar : ℝ≥0∞}
    (hlo : (g : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((n / g : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F)
      (evalCode (smoothDom γ n) k : Set (Fin n → F)) εstar
      = (g : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0) := by
  have hk1 : 1 ≤ k := by omega
  have hinj : Function.Injective (smoothDom γ n) := smoothDom_injective γ hord
  have hnpos : 0 < n := by omega
  have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by
    rw [Fintype.card_fin]
  refine le_antisymm ?_ ?_
  · -- upper bracket: the explosion makes δ = g/n bad
    refine mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hhi ?_)
    have := strip_eps_ge (g := g) (k := k) γ hord hg1 hgn hk_lo hk_hi hn2g (F := F)
    rwa [hcardn]
  · -- lower bracket: every radius below g/n is good (master collapse at band g)
    by_contra h
    push_neg at h
    obtain ⟨c, hc1, hc2⟩ := exists_between h
    have hgood : epsMCA (F := F) (A := F)
        (evalCode (smoothDom γ n) k : Set (Fin n → F)) c ≤ εstar := by
      refine le_trans (MCAStaircaseMaster.epsMCA_le_div_card_of_dist _ g hg1
        (evalCode_noWeightLE (smoothDom γ n) hinj (by omega) hk1)
        (by rw [Fintype.card_fin]; omega) ?_) hlo
      -- c·n < g from c < g/n
      rw [hcardn]
      calc c * (n : ℝ≥0) < ((g : ℝ≥0) / (Fintype.card (Fin n) : ℝ≥0)) * n := by
            have hn0 : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hnpos
            exact mul_lt_mul_of_pos_right hc2 hn0
        _ = (g : ℝ≥0) := by
            rw [hcardn]
            field_simp
    have hcle : c ≤ 1 := by
      refine le_of_lt (lt_of_lt_of_le hc2 ?_)
      rw [hcardn, div_le_one (by exact_mod_cast hnpos : (0 : ℝ≥0) < (n : ℝ≥0))]
      exact_mod_cast (by omega : g ≤ n)
    have hle := le_mcaDeltaStar_of_good (F := F) (A := F)
      (evalCode (smoothDom γ n) k : Set (Fin n → F)) εstar hcle hgood
    exact absurd hle (not_le.mpr hc1)

end ProximityGap.StripEdgeDeltaStar

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.StripEdgeDeltaStar.evalCode_noWeightLE
#print axioms ProximityGap.StripEdgeDeltaStar.mcaDeltaStar_eq_strip_edge
