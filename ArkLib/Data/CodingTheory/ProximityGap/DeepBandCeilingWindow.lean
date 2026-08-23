/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandDeltaStarCeiling

/-!
# The deep-band δ* ceiling as an instantiable window condition (#389)

`DeepBandDeltaStarCeiling.mcaDeltaStar_le_of_deep_band` is the per-band ceiling, but its
budget hypothesis `hnum` carries the second-moment normaliser `Λ` with three nested ℕ
divisions — awkward to discharge at a parameter point.  This file packages the clean
**window condition** that drives it:

> In the witness-mass *window* `ε*·q^{m+1}·(C'+2) + q^m ≤ C(n,k+m+1) < q^{m+1}`, the
> Nat-truncated `Λ` collapses to the constant `C'+2` (because `P/q^{m+1} = 0`), and the
> budget `hnum` holds — so `δ* ≤ 1 − (k+m+1)/n`.

Here `C' = C(k+m+1,k+1)·C(n−k−1,m)`.  This is exactly the regime of the analytic ceiling
`δ* ≤ 1 − ρ − H(ρ)/(β log₂n − H'(ρ))` (`probe_ceiling_constant.py`): near the entropy
frontier the witness-mass density `C(n,a)/q^{m+1}` drops below `1`, so the truncation
applies and the consumer fires.  `mcaDeltaStar_le_of_ceiling_window` turns the per-instance
consumer into a one-inequality-in, δ*-bracket-out theorem.  Issue #389; axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code
open ProximityGap.MCAThresholdLedger

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The deep-band δ\* ceiling, window form.**  Write `P := C(n,k+m+1)`,
`C' := C(k+m+1,k+1)·C(n−(k+1),m)`, `q := |F|`.  If the witness mass sits in the window

  `ε*·q^{m+1}·(C'+2) + q^m ≤ P < q^{m+1}`   (so the Nat-truncated `Λ = C'+2`),

then `mcaDeltaStar (rsCode dom k) ε* ≤ δ` at every band radius `(1−δ)n ≤ k+m+1`.
The single hypothesis `hwin` is the budget after the truncation collapse; the proof
discharges the consumer's `hnum`. -/
theorem mcaDeltaStar_le_of_ceiling_window (dom : Fin n ↪ F) {k m : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ ((k + m + 1 : ℕ) : ℝ≥0))
    (εstar : ℝ≥0∞) (hε : εstar ≠ ⊤)
    (hPhi : ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
        < (Fintype.card F) ^ (m + 1))
    (hwin : εstar * ((Fintype.card F : ℝ≥0∞)
          * (↑((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2) : ℝ≥0∞) ^ 2) + 1
        ≤ (↑(((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
              * ((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2)
            / (Fintype.card F) ^ m) : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar ≤ δ := by
  classical
  refine mcaDeltaStar_le_of_deep_band dom hk hhi εstar ?_
  -- the Nat-truncated Λ collapses: P/q^{m+1} = 0
  have hzero : ((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).card
      / (Fintype.card F) ^ (m + 1) = 0 := Nat.div_eq_of_lt hPhi
  rw [hzero, Nat.zero_add]
  -- goal is now hnum with Λ = C'+2; finiteness for the `+1` slack
  have hfin : εstar * ((Fintype.card F : ℝ≥0∞)
      * (↑((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2) : ℝ≥0∞) ^ 2) ≠ ⊤ := by
    refine ENNReal.mul_ne_top hε (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_)
    exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  calc εstar * ((Fintype.card F : ℝ≥0∞)
          * (↑((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2) : ℝ≥0∞) ^ 2)
      < εstar * ((Fintype.card F : ℝ≥0∞)
          * (↑((k + m + 1).choose (k + 1) * (n - (k + 1)).choose m + 2) : ℝ≥0∞) ^ 2) + 1 :=
        ENNReal.lt_add_right hfin one_ne_zero
    _ ≤ _ := hwin

instance primeFact_DeepBandCeilingWindow_1 : Fact (Nat.Prime 31) := ⟨by decide⟩

/-- **Non-vacuity, in-window.**  `RS[F₃₁, 10 pts, k=2]`, band `m = 1` (agreement `t = 4`,
radius `δ = 3/5`): `P = C(10,4) = 210 ∈ [q^m, q^{m+1}) = [31, 961)`, so the window
condition holds and `mcaDeltaStar ≤ 3/5` for the prize threshold `ε* = 2⁻¹²⁸`.  The
radius `3/5` is strictly inside the window `(1−√ρ, 1−ρ) = (0.553…, 0.8)` for rate
`ρ = 1/5` — a machine-checked in-window δ* ceiling from the window theorem. -/
theorem mcaDeltaStar_F31_window (dom : Fin 10 ↪ ZMod 31) :
    mcaDeltaStar (F := ZMod 31) (A := ZMod 31)
        ((rsCode dom 2 : Submodule (ZMod 31) (Fin 10 → ZMod 31)) :
          Set (Fin 10 → ZMod 31)) ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ ≤ (3 / 5 : ℝ≥0) := by
  have hpc : ((Finset.univ : Finset (Fin 10)).powersetCard (2 + 1 + 1)).card = 210 := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]; decide
  have hcard : Fintype.card (ZMod 31) = 31 := by simp [ZMod.card]
  refine mcaDeltaStar_le_of_ceiling_window (m := 1) dom (by norm_num) ?_
    ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ (by simp) ?_ ?_
  · -- hhi : (1 − 3/5)·10 ≤ 4
    have hle : (3 : ℝ≥0) / 5 ≤ 1 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
    rw [Fintype.card_fin, ← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hle]
    push_cast
    norm_num
  · -- hPhi : P < 31^2
    rw [hpc, hcard]; norm_num
  · -- hwin : ε*·(31·30²) + 1 ≤ ⌊210·30/31⌋ = 203
    rw [hpc, hcard]
    have hchoose : (2 + 1 + 1).choose (2 + 1) * (10 - (2 + 1)).choose 1 + 2 = 30 := by decide
    rw [hchoose]
    -- goal: (2^128)⁻¹ * (31 * (30:ℝ≥0∞)^2) + 1 ≤ ↑(210 * 30 / 31^1)
    have hrhs : (210 * 30 / 31 ^ 1 : ℕ) = 203 := by norm_num
    rw [hrhs]
    have hsmall : ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ * (31 * (30 : ℝ≥0∞) ^ 2) ≤ 1 := by
      rw [ENNReal.inv_mul_le_iff (by positivity) (by simp), mul_one]
      norm_num
    calc ((2 : ℝ≥0∞) ^ (128 : ℕ))⁻¹ * (31 * (30 : ℝ≥0∞) ^ 2) + 1
        ≤ 1 + 1 := by gcongr
      _ ≤ ((203 : ℕ) : ℝ≥0∞) := by norm_num

/-! ## Source audit -/

#print axioms mcaDeltaStar_le_of_ceiling_window

end ProximityGap.PairRank
