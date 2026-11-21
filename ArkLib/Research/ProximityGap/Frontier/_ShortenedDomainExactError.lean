/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier._ShortenedDomainGoodSide
import ArkLib.Research.ProximityGap.Frontier._PackingBudgetFirstJump

/-!
# Exact worst-case MCA error on the overlap-packing interval

At each eligible integer error count `e`, overlap packing gives `2e+2` bad challenges.
Shortening into a code of length `2e+2` gives the same upper bound for every stack.
This determines the error probability before choosing a security budget.
-/

open scoped NNReal ENNReal
open _root_.ProximityGap ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.ShortenedDomainExactError

/-- The effective scalar count is exactly `2e+2` whenever both the shortening and
overlap constructions fit. The field-size hypotheses concern available evaluation points
and fresh challenge values, respectively. -/
theorem epsMCA_eq_overlap {p n k e : ℕ} [Fact p.Prime] [NeZero n] {g : ZMod p}
    (hg : orderOf g = n) (hk : 2 ≤ k) (hehalf : n ≤ 2 * e)
    (hecap : e + k + 1 ≤ n) (hlarge : 1699 ≤ e + 1)
    (hfield : 2 * e + 2 ≤ p) (hfresh : 2 * (2 * e - n + 2) ≤ p - n)
    (hrate : 8 * (k + (2 * e + 2 - n)) ≤ 2 * e + 2) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1)) ((e : ℝ≥0) / n) =
      ((2 * e + 2 : ℕ) : ℝ≥0∞) / p := by
  let N := 2 * e + 2
  have hhalf : N / 2 = e + 1 := by dsimp [N]; omega
  let _ : NeZero N := ⟨by dsimp [N]; omega⟩
  have hg0 := KKH26RegimeSplit.ne_zero_of_orderOf_eq hg
  let dom := KKH26RegimeSplit.powDomain g hg hg0
  have hcode : evalCode g n (k - 1) = (ReedSolomon.code dom k : Set (Fin n → ZMod p)) := by
    simpa only [dom, show k - 1 + 1 = k by omega] using
      KKH26RegimeSplit.evalCode_eq_reedSolomon g hg hg0 (k - 1)
  apply le_antisymm
  · rw [hcode]
    have hpred : PrizeShapeRateHalfBracket.predecessorRadius n (N / 2) = (e : ℝ≥0) / n := by
      simp [PrizeShapeRateHalfBracket.predecessorRadius, hhalf]
    rw [← hpred]
    have h := epsMCA_le_of_badCount_le (F := ZMod p) (A := ZMod p)
      (ReedSolomon.code dom k : Set (Fin n → ZMod p))
      (PrizeShapeRateHalfBracket.predecessorRadius n (N / 2)) N
      (fun u => ShortenedDomainGoodSide.predecessor_badCount_le (N := N) dom
        (by change n ≤ 2 * e + 2; omega)
        (by simpa only [ZMod.card] using hfield)
        (by change 2 * e + 2 = 2 * ((2 * e + 2) / 2); omega)
        (by omega) (by omega) (by omega) hrate u)
    simpa only [N, ZMod.card] using h
  · have h := PackingBudgetFirstJump.overlap_epsMCA_lower_bound_of_supply
        hg hk hehalf hecap hfresh
    have hn : (n : ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
    have he : e ≤ n := by omega
    have hbound : (e : ℝ≥0) / n ≤ 1 := (div_le_one (by positivity)).2 (by exact_mod_cast he)
    have hsub : ((n - e : ℕ) : ℝ≥0) / n = 1 - (e : ℝ≥0) / n := by
      rw [Nat.cast_tsub, tsub_div, div_self hn]
    rwa [hsub, tsub_tsub_cancel_of_le hbound] at h

end ArkLib.ProximityGap.Frontier.ShortenedDomainExactError

#print axioms ArkLib.ProximityGap.Frontier.ShortenedDomainExactError.epsMCA_eq_overlap
