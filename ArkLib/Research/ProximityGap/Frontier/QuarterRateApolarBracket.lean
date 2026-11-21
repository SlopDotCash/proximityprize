/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarPowerBound
import ArkLib.Research.ProximityGap.Frontier.TwoHeadLinearBudget
import ArkLib.Research.ProximityGap.Frontier._P1RateQuarterAdjacentExactPin

/-! # Exact two-head mass on arbitrary domains and the first-prime quarter-rate bracket

At length `k + 2e` with `2 ≤ k ≤ e + 1`, the apolar upper bound and two-head
construction agree at `e` errors. For the first designated prime this certifies
safety at `3/8`. The next Hamming step is a lower bound on the operational supremum.
-/

namespace ArkLib.ProximityGap.Frontier.QuarterRateApolarBracket

open Code _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger
open HalfPredecessorBadEventRichPointBridge PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

/-- On every finite-field domain the worst-case numerator is exactly `2(e + 1)` at this step. -/
theorem endpoint_mass {F I : Type} [Field F] [Fintype F]
    [Fintype I] [Nonempty I] (dom : I ↪ F) (k e : ℕ)
    (hn : Fintype.card I = k + 2 * e) (hk : 2 ≤ k) (hlow : k ≤ e + 1) :
    epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F))
      ((e : ℝ≥0) / Fintype.card I) = ((2 * (e + 1) : ℕ) : ℝ≥0∞) / Fintype.card F := by
  classical
  apply le_antisymm
  · apply epsMCA_le_of_badCount_le
    intro u
    let δ : ℝ≥0 := e / Fintype.card I
    let fam := canonicalBadScalarRichPointFamily dom δ u (by omega : 1 ≤ k)
    change fam.G.card ≤ 2 * (e + 1)
    have hc : (Fintype.card I : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hceil : Fintype.card I - e ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ := by
      dsimp only [δ]
      rw [tsub_mul, one_mul, div_mul_cancel₀ _ hc, ← Nat.cast_tsub, Nat.ceil_natCast]
    have h := ApolarPowerBound.endpoint fam rfl hn (by omega) (by omega) hceil
    have hdiv : (Fintype.card I + 1) / (e + 1) = 2 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    rwa [hdiv] at h
  · exact TwoHeadLinearBudget.errors dom (by omega) (by omega) (by omega)

open Polynomial in
/-- When two degree-at-most-d row differences vanish at d common sites, all
additional folded coincidences outside these sites use at most one scalar. -/
theorem saturated_overlap {F : Type*} [Field F] (p q : F[X]) (S G : Finset F)
    (distinct : p ≠ 0 ∨ q ≠ 0) (hp : p.natDegree ≤ S.card) (hq : q.natDegree ≤ S.card)
    (core : ∀ x ∈ S, p.eval x = 0 ∧ q.eval x = 0)
    (fresh : ∀ z ∈ G, ∃ x ∉ S, p.eval x + z * q.eval x = 0) :
    G.card ≤ 1 := by
  classical
  have fold (z : F) (hz : z ∈ G) : p + C z * q = 0 := by
    obtain ⟨x, hx, he⟩ := fresh z hz
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (insert x S)
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa only [eval_add, eval_mul, eval_C] using he
      · simp only [eval_add, eval_mul, eval_C, (core i hi).1, (core i hi).2, mul_zero, add_zero]
    · rw [Finset.card_insert_of_notMem hx]
      exact Nat.lt_succ_of_le ((natDegree_add_le ..).trans
        (max_le hp ((natDegree_C_mul_le ..).trans hq)))
  apply Finset.card_le_one.mpr
  intro z hz w hw
  have h := congrArg₂ (· - ·) (fold z hz) (fold w hw)
  have hdiff : (C z - C w) * q = 0 := by linear_combination h
  rcases mul_eq_zero.mp hdiff with he | he
  · exact C_injective (sub_eq_zero.mp he)
  · have hzero : p = 0 := by simpa [he] using fold z hz
    exact (distinct.elim (· hzero) (· he)).elim

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterCanonicalCodeBridge P1RateQuarterScaleArithmetic

local instance : Fact P.Prime := ⟨prime_P⟩
local instance : NeZero N := ⟨by decide⟩

/-- Literal closed bounds on the first designated prime at quarter rate. -/
theorem named_bracket :
    let radius := mcaDeltaStar (F := ZMod P) canonicalCode ((((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹)
    (402653185 : ℝ≥0) / 1073741824 ≤ radius ∧ radius ≤ 480946859 / 1073741824 := by
  dsimp only
  constructor
  · apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good (a := 402653185)
      (by decide) (by decide : 402653185 ≤ N)
    change epsMCA (F := ZMod P) canonicalCode ((402653184 : ℝ≥0) / N) ≤ _
    have mass := endpoint_mass canonicalDomain k 402653184 (by rw [Fintype.card_fin]; decide)
      (by decide) (by decide)
    rw [Fintype.card_fin, ZMod.card] at mass
    apply mass.le.trans
    exact natCast_div_le_inv_of_mul_le (Q := 2 ^ 128) (by decide) prime_P.pos (by decide)
  · exact P1RateQuarterAdjacentExactPin.canonical_mcaDeltaStar_le_common_delta

#print axioms endpoint_mass
#print axioms saturated_overlap
#print axioms named_bracket

end ArkLib.ProximityGap.Frontier.QuarterRateApolarBracket
