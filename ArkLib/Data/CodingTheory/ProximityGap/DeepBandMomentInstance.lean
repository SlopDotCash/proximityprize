/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandSecondMomentEps

/-!
# The second-moment machine, witnessed (#389, route 2, the non-vacuity instance)

The full route-2 pipeline instantiated end-to-end at a concrete parameter
point: `RS[F₁₃₁, {0,…,127}, k = 2]`, band `m = 1` (radius `δ = 31/32`, one
granularity step **below** the capacity radius `63/64`), generator width
`M = 8`, moment parameters `(L, V) = (1050, 79 591 252)`:

* `deep_band_floor_instance` — **`ε_mca(C, 31/32) ≥ 72/131`** — a
  majority-mass MCA failure strictly below capacity, with no hypotheses;
* `deep_band_deltaStar_instance` — the ledger bracket
  **`mcaDeltaStar(C, ε*) ≤ 31/32` for every `ε* < 72/131`** — covering in
  particular the production target `ε* = 2⁻¹²⁸`.

The entire derivation is the one binomial inequality
`P²·q⁵ + (D+P)·q⁷ + V·q⁸ ≤ 2L·P·q⁷` (`P = C(128,4) = 10 668 000`,
`D ≤ P·C(4,3)·C(125,1)` by `deepPairs_card_le`, `q = 131`), checked by
`norm_num` — the demonstration that the second-moment route produces
machine-checked `δ*` brackets from per-parameter arithmetic alone.

Round-81 comparison at the same point: `C(n,k+m+1)/(2·q^m·C(n,k)) ≈ 5` bad
scalars; the second moment delivers `72` — and as a *fraction of the field*,
a constant. Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

abbrev F131 := ZMod 131

instance primeFact_DeepBandMomentInstance_1 : Fact (Nat.Prime 131) := ⟨by decide⟩

/-- The 128-point evaluation domain `{0, 1, …, 127} ⊆ F₁₃₁`. -/
def dom131 : Fin 128 ↪ F131 :=
  ⟨fun i => ((i : ℕ) : F131), by
    intro i j hij
    have hi : ((i : ℕ) : F131).val = (i : ℕ) := by
      rw [ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (lt_trans i.isLt (by norm_num))
    have hj : ((j : ℕ) : F131).val = (j : ℕ) := by
      rw [ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (lt_trans j.isLt (by norm_num))
    have hij' : ((i : ℕ) : F131) = ((j : ℕ) : F131) := hij
    exact Fin.ext (by rw [← hi, ← hj, hij'])⟩

/-- `C(128, 4) = 10 668 000` (via the descending factorial; the bare `choose`
recursion is not kernel-feasible). -/
theorem choose_128_4 : Nat.choose 128 4 = 10668000 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The core count at the instance. -/
theorem P_value :
    ((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)).card
      = 10668000 := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact choose_128_4

/-- The field size at the instance. -/
theorem q_value : Fintype.card F131 = 131 := by
  simp [ZMod.card]

open Classical in
/-- The numeric moment budget at
`(n, k, m, q, M, L, V) = (128, 2, 1, 131, 8, 1050, 79 591 252)`. -/
theorem budget_instance :
    ((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)).card ^ 2
          * (Fintype.card F131) ^ (8 - (2 * 1 + 1))
        + (((((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)) ×ˢ
            (((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)))).filter
            (fun p => p.1 ≠ p.2 ∧ 2 < (p.1 ∩ p.2).card)).card
          + ((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)).card)
          * (Fintype.card F131) ^ (8 - 1)
        + 79591252 * (Fintype.card F131) ^ 8
      ≤ 2 * 1050 * (((Finset.univ : Finset (Fin 128)).powersetCard (2 + 1 + 1)).card
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
            (fun p => p.1 ≠ p.2 ∧ 2 < (p.1 ∩ p.2).card)).card)
          + 10668000) * 131 ^ (8 - 1)
        + 79591252 * 131 ^ 8
      ≤ 10668000 ^ 2 * 131 ^ (8 - (2 * 1 + 1))
        + (5334000000 + 10668000) * 131 ^ (8 - 1)
        + 79591252 * 131 ^ 8 := by
        refine Nat.add_le_add_right (Nat.add_le_add_left ?_ _) _
        exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hD' _)
    _ ≤ 2 * 1050 * (10668000 * 131 ^ (8 - 1)) := by norm_num

open Classical in
/-- **The witnessed floor: `ε_mca(RS[F₁₃₁, 128 pts, 2], 31/32) ≥ 72/131`.**
A majority-mass MCA failure one granularity step below capacity, delivered
end-to-end by the second-moment machine. -/
theorem deep_band_floor_instance :
    ∃ Q₀ : F131[X],
      ((72 : ℕ) : ℝ≥0∞) / 131
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
  obtain ⟨Q₀, hQ₀⟩ := deep_band_epsMCA_of_moments (m := 1) (M := 8)
    (L := 1050) (V := 79591252) dom131 (by norm_num) hhi (by norm_num)
    budget_instance
  refine ⟨Q₀, le_trans (le_of_eq ?_) hQ₀⟩
  rw [q_value]
  norm_num

open Classical in
/-- **The witnessed `δ*` bracket**: for every error target `ε* < 72/131` —
including the production `ε* = 2⁻¹²⁸` —

  `mcaDeltaStar(RS[F₁₃₁, 128 pts, 2], ε*) ≤ 31/32`,

one granularity step strictly below the capacity radius `63/64`. -/
theorem deep_band_deltaStar_instance {εstar : ℝ≥0∞}
    (hε : εstar < ((72 : ℕ) : ℝ≥0∞) / 131) :
    MCAThresholdLedger.mcaDeltaStar (F := F131) (A := F131)
      ((rsCode dom131 2 : Submodule F131 (Fin 128 → F131)) :
        Set (Fin 128 → F131)) εstar ≤ 31/32 := by
  obtain ⟨Q₀, hfloor⟩ := deep_band_floor_instance
  exact MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le hε hfloor)

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.budget_instance
#print axioms ProximityGap.PairRank.deep_band_floor_instance
#print axioms ProximityGap.PairRank.deep_band_deltaStar_instance
