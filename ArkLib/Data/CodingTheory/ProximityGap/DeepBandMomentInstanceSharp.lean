/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSecondMomentEpsSharp
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandMomentInstance

/-!
# The SHARP machine, witnessed: `ε_mca ≥ 129/131` below capacity (#389)

The sharp route-2 pipeline at the same concrete point as
`DeepBandMomentInstance.lean` — `RS[F₁₃₁, {0,…,127}, k = 2]`, band `m = 1`
(radius `δ = 31/32`, one step below capacity `63/64`), `M = 8` — with the sharp
closed-form parameters `(L, V) = (Λ', P·Λ'/q) = (627, 51 059 816)`
(`Λ' = P/q² + C'/q + 3 = 621 + 3 + 3`):

* `deep_band_floor_instance_sharp` — **`ε_mca(C, 31/32) ≥ 129/131`** — versus
  the unsharpened instance's `72/131`: with the deep term a factor `q` lower,
  the witnessed failure mass rises from majority to `q − 2` of `q` — the
  saturation the route-2 payoff probe measured, now machine-checked;
* `deep_band_deltaStar_instance_sharp` — `mcaDeltaStar(C, ε*) ≤ 31/32` for
  every `ε* < 129/131`, in particular the production `ε* = 2⁻¹²⁸`.

One binomial inequality in (`P²q⁵ + D·q⁶ + P·q⁷ + V·q⁸ ≤ 2Λ'·P·q⁷`,
`D ≤ P·C(4,3)·C(125,1)`), a near-saturated δ* bracket out.  Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

open Classical in
/-- The SHARP numeric moment budget at
`(n, k, m, q, M, L, V) = (128, 2, 1, 131, 8, 627, 51 059 816)`. -/
theorem budget_instance_sharp :
    ((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)).card ^ 2
          * (Fintype.card F131) ^ (8 - (2 * 1 + 1))
        + (((((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)) ×ˢ
            (((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ 2 < (p.1 ∩ p.2).card)).card)
          * (Fintype.card F131) ^ (8 - (1 + 1))
        + ((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)).card
          * (Fintype.card F131) ^ (8 - 1)
        + 51059816 * (Fintype.card F131) ^ 8
      ≤ 2 * 627 * (((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)).card
          * (Fintype.card F131) ^ (8 - 1)) := by
  have hD := deepPairs_card_le (n := 128) 2 1
  have hD' : (((((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)) ×ˢ
      (((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)))).filter
      (fun p => p.1 ≠ p.2 ∧ 2 < (p.1 ∩ p.2).card)).card)
      ≤ 5334000000 := by
    refine le_trans hD (le_of_eq ?_)
    rw [P_value]
    norm_num [Nat.choose_eq_descFactorial_div_factorial]
  rw [P_value, q_value]
  calc 10668000 ^ 2 * 131 ^ (8 - (2 * 1 + 1))
        + ((((((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)) ×ˢ
            (((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ 2 < (p.1 ∩ p.2).card)).card))
          * 131 ^ (8 - (1 + 1))
        + 10668000 * 131 ^ (8 - 1)
        + 51059816 * 131 ^ 8
      ≤ 10668000 ^ 2 * 131 ^ (8 - (2 * 1 + 1))
        + 5334000000 * 131 ^ (8 - (1 + 1))
        + 10668000 * 131 ^ (8 - 1)
        + 51059816 * 131 ^ 8 := by
        refine Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.add_le_add_left ?_ _) _) _
        exact Nat.mul_le_mul_right _ hD'
    _ ≤ 2 * 627 * (10668000 * 131 ^ (8 - 1)) := by norm_num

open Classical in
/-- **The SHARP witnessed floor: `ε_mca(RS[F₁₃₁, 128 pts, 2], 31/32) ≥ 129/131`** —
`q − 2` of the `q` scalars bad, one granularity step below capacity; the
unsharpened machine delivered `72/131` at the same point. -/
theorem deep_band_floor_instance_sharp :
    ∃ Q₀ : F131[X],
      ((129 : ℕ) : ℝ≥0∞) / 131
        ≤ epsMCA (F := F131) (A := F131)
            ((rsCode dom131 2 : Submodule F131 (Fin 128 → F131)) :
              Set (Fin 128 → F131)) (31/32) := by
  have hhi : (1 - (31/32 : ℝ≥0)) * (Fintype.card (Fin 128) : ℝ≥0)
      ≤ ((2 + 1 + 1 : ℕ) : ℝ≥0) := by
    have h132 : (1 : ℝ≥0) - 31/32 = 1/32 := by
      rw [tsub_eq_iff_eq_add_of_le (by
        rw [div_le_one (by norm_num : (0:ℝ≥0) < 32)]
        norm_num)]
      rw [← NNReal.coe_inj]
      push_cast
      norm_num
    rw [h132, Fintype.card_fin]
    rw [← NNReal.coe_le_coe]
    push_cast
    norm_num
  obtain ⟨Q₀, hQ₀⟩ := deep_band_epsMCA_of_moments_sharp (m := 1) (M := 8)
    (L := 627) (V := 51059816) dom131 (by norm_num) hhi (by norm_num)
    budget_instance_sharp
  refine ⟨Q₀, le_trans (le_of_eq ?_) hQ₀⟩
  rw [q_value]
  norm_num

open Classical in
/-- **The SHARP witnessed `δ*` bracket**: for every `ε* < 129/131` — including
the production `ε* = 2⁻¹²⁸` — `mcaDeltaStar(RS[F₁₃₁, 128 pts, 2], ε*) ≤ 31/32`. -/
theorem deep_band_deltaStar_instance_sharp {εstar : ℝ≥0∞}
    (hε : εstar < ((129 : ℕ) : ℝ≥0∞) / 131) :
    MCAThresholdLedger.mcaDeltaStar (F := F131) (A := F131)
      ((rsCode dom131 2 : Submodule F131 (Fin 128 → F131)) :
        Set (Fin 128 → F131)) εstar ≤ 31/32 := by
  obtain ⟨Q₀, hfloor⟩ := deep_band_floor_instance_sharp
  exact MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hε hfloor)

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.budget_instance_sharp
#print axioms ProximityGap.PairRank.deep_band_floor_instance_sharp
#print axioms ProximityGap.PairRank.deep_band_deltaStar_instance_sharp
