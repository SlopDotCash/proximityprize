/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SmoothCubicCapstone

/-!
# The cubic/energy supply is SILENT at prize scale (#389, O163)

`Research/ProximityPrize/DISPROOF_LOG.md` O163 states (in PROSE) that the GV/Stepanov
additive-energy bound `E(μ_n) ≲ n^{8/3}` makes the energy/cubic supply *silent* at prize
parameters.  This file proves **absolute** supply bounds `S < 2^128` for the cubic word's
explainable-3-core count `S` when `n ≤ 2^40` (one conditional on a named GV input, one
unconditional).

**Budget normalization (corrected).**  O163 compared `S` with `ε*·q = 2^128`.  With
`ε* = 2^-128` the actual budget is `ε*·q = q / 2^128`, which equals `2^128` only at `q = 2^256`;
for `q < 2^256` it is SMALLER than `2^128` (for `q ≈ 2^158` it is `≈ 2^30`).  So `S < 2^128`
alone does NOT give `S < ε*·q`.  The comparison with the real, field-size-dependent budget is
proved here only under an explicit field-size premise:
`cubicSupply_mul_two_pow_128_lt_card` gives `S · 2^128 < q` (i.e. `S < ε*·q`) when
`2^248 ≤ q`.  Moreover `S` counts explainable 3-cores, not distinct bad scalars; no bound on
`ε_mca` follows from this file without a separate core-to-bad-scalar argument.

The energy bound is **never asserted** here: it enters only as the named hypothesis
`GVRepBound G M` (`r(t) ≤ M` for `t ≠ 0`, with `M³ ≤ 64·|G|²`), exactly the in-tree
`TZPrimeSupply`-style residual.  The Garcia–Voloch / Heath-Brown–Konyagin theorem
(`E(μ_n) ≲ n^{8/3}`, registered for the Stepanov formalization) is the source of the
hypothesis, but is cited, not proven.

* `cubicSupply_silent_at_prize_scale` — under the named GV input and `n ≤ 2^40`, the cubic
  word's explainable-3-core count `S` satisfies the absolute bound `S < 2^128` (not a
  comparison with `ε*·q`, see above).
* `cubicSupply_silent_unconditional` — the same absolute bound with no energy input
  (`S ≤ C(n,3) ≤ 2^120`).
* `cubicSupply_mul_two_pow_128_lt_card` — `S · 2^128 < q` when `n ≤ 2^40` and `2^248 ≤ q`.

The sharper HBK `5/2` energy form (`HBKEnergyBound G C`,
`zeroSumTriples_pow_le_of_hbkEnergyBound`) gives a tighter `≈ 2^70` supply, but carries a
free literature constant `C`; the GV route used here needs no extra constant residual (the
constant `260` is fixed by `GVRepBound`), so the GV route is the cleaner silence brick.

## The numeric envelope (GV `8/3` route)

`cubicSupply_pow_le_of_gvRepBound` gives `S⁶ ≤ 260·n¹¹`.  With `n ≤ 2^40`,
`260·n¹¹ ≤ 260·(2^40)¹¹ = 260·2^440 < 2^449`, while `(2^128)⁶ = 2^768`.  So
`S⁶ < (2^128)⁶`, and strict monotonicity of `x ↦ x⁶` on `ℕ` gives `S < 2^128`.
Margin: `2^768 / 2^449 = 2^319`; the conditional supply estimate is `≈ 2^74.7` (O163's loose
prose `≈ 2^85` is a conservative over-estimate).  Whether `2^74.7` is below the actual budget
`q / 2^128` depends on `q` (it is when `q ≳ 2^203`, not at `q ≈ 2^158`); this file proves no
such comparison for the GV estimate.
-/

open Finset

namespace ProximityGap.Cubic

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership
open ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The bare numeric envelope of the GV `8/3` route at prize scale:
`260·(2^40)¹¹ < (2^128)⁶`, i.e. `260·2^440 < 2^768`. -/
theorem gv_supply_envelope_lt : 260 * (2 ^ 40 : ℕ) ^ 11 < (2 ^ 128 : ℕ) ^ 6 := by
  -- 260·(2^40)^11 = 260·2^440 ≤ 2^9·2^440 = 2^449 < 2^768 = (2^128)^6
  have hl : 260 * (2 ^ 40 : ℕ) ^ 11 ≤ 2 ^ 449 := by
    have h1 : (2 ^ 40 : ℕ) ^ 11 = 2 ^ 440 := by rw [← pow_mul]
    have h2 : (260 : ℕ) ≤ 2 ^ 9 := by norm_num
    calc 260 * (2 ^ 40 : ℕ) ^ 11 = 260 * 2 ^ 440 := by rw [h1]
      _ ≤ 2 ^ 9 * 2 ^ 440 := Nat.mul_le_mul_right _ h2
      _ = 2 ^ 449 := by rw [← pow_add]
  have hr : (2 ^ 128 : ℕ) ^ 6 = 2 ^ 768 := by rw [← pow_mul]
  have hlt : (2 : ℕ) ^ 449 < 2 ^ 768 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  rw [hr]
  exact lt_of_le_of_lt hl hlt

open Classical in
/-- **Absolute cubic/energy supply bound `S < 2^128`** (O163, conditional on the named GV
input).  Under `GVRepBound (image dom univ) M` — the in-tree integer-clean form of the cited
Garcia–Voloch / Stepanov bound `E(μ_n) ≲ n^{8/3}`, kept as a HYPOTHESIS, never asserted —
and `n ≤ 2^40` (the prize domain bound), the cubic word's explainable-3-core supply `S`
satisfies `S < 2^128`.

This is an absolute bound, NOT `S < ε*·q`: with `ε* = 2^-128` and `q < 2^256` the budget
`ε*·q = q / 2^128` is smaller than `2^128`, and the statement has no field-size premise.  It
also bounds 3-cores, not distinct bad scalars, so it gives no bound on `ε_mca` by itself.  The
proof chains the landed capstone `S⁶ ≤ 260·n¹¹` with the numeric envelope
`260·(2^40)¹¹ < (2^128)⁶` and strict monotonicity of `x ↦ x⁶`. -/
theorem cubicSupply_silent_at_prize_scale (dom : Fin n ↪ F) {M : ℕ}
    (hn : n ≤ 2 ^ 40)
    (h : GVRepBound (Finset.image dom Finset.univ) M) :
    (((Finset.univ.powersetCard 3).filter
        (fun T => ExplainableOn dom 2 (cubicWord dom) T)).card) < 2 ^ 128 := by
  set S := (((Finset.univ.powersetCard 3).filter
      (fun T => ExplainableOn dom 2 (cubicWord dom) T)).card) with hS
  -- the landed capstone: S^6 ≤ 260·n^11
  have hcap : S ^ 6 ≤ 260 * n ^ 11 := cubicSupply_pow_le_of_gvRepBound dom h
  -- monotone in n ≤ 2^40
  have hmono : (260 : ℕ) * n ^ 11 ≤ 260 * (2 ^ 40) ^ 11 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 11)
  -- chain to the prize-scale envelope
  have hSpow : S ^ 6 < (2 ^ 128 : ℕ) ^ 6 :=
    lt_of_le_of_lt (le_trans hcap hmono) gv_supply_envelope_lt
  -- strip the ^6 by strict monotonicity of x ↦ x^6 on ℕ
  exact lt_of_pow_lt_pow_left₀ 6 (Nat.zero_le _) hSpow

set_option linter.unusedSectionVars false in
open Classical in
/-- **Absolute cubic supply bound `S < 2^128` — UNCONDITIONALLY.**  For `n ≤ 2^40` the cubic
explainable-3-core count is at most the total number of 3-subsets
`C(n,3) ≤ n³ ≤ (2^40)³ = 2^120 < 2^128`; no additive-energy bound is needed.  So
`cubicSupply_silent_at_prize_scale`'s `GVRepBound` hypothesis is removable for this absolute
bound — the GV/Stepanov energy bound buys only a *tighter* estimate (`≈ 2^74.7`).

As with the conditional version, this is NOT a comparison with the prize budget
`ε*·q = q / 2^128` (smaller than `2^128` whenever `q < 2^256`); see
`cubicSupply_mul_two_pow_128_lt_card` for the comparison under an explicit field-size premise. -/
theorem cubicSupply_silent_unconditional (dom : Fin n ↪ F) (hn : n ≤ 2 ^ 40) :
    (((Finset.univ.powersetCard 3).filter
        (fun T => ExplainableOn dom 2 (cubicWord dom) T)).card) < 2 ^ 128 := by
  calc (((Finset.univ.powersetCard 3).filter
          (fun T => ExplainableOn dom 2 (cubicWord dom) T)).card)
      ≤ (Finset.univ.powersetCard 3 : Finset (Finset (Fin n))).card := Finset.card_filter_le _ _
    _ = Nat.choose n 3 := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    _ ≤ n ^ 3 := Nat.choose_le_pow n 3
    _ ≤ (2 ^ 40) ^ 3 := Nat.pow_le_pow_left hn 3
    _ = 2 ^ 120 := by rw [← pow_mul]
    _ < 2 ^ 128 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)

set_option linter.unusedSectionVars false in
open Classical in
/-- **Comparison with the actual prize budget, under an explicit field-size premise.**  With
`ε* = 2^-128` the budget is `ε*·q = q / 2^128`.  For `n ≤ 2^40` and `2^248 < q`, the cubic
explainable-3-core count satisfies `S · 2^128 < q`, i.e. `S < ε*·q`.  (Via the trivial bound
`S ≤ C(n,3) ≤ 2^120`.)  Without such a premise on `q` the absolute bound `S < 2^128` does not
imply `S < ε*·q`.  This still bounds 3-cores, not distinct bad scalars. -/
theorem cubicSupply_mul_two_pow_128_lt_card (dom : Fin n ↪ F) (hn : n ≤ 2 ^ 40)
    (hq : 2 ^ 248 < Fintype.card F) :
    (((Finset.univ.powersetCard 3).filter
        (fun T => ExplainableOn dom 2 (cubicWord dom) T)).card) * 2 ^ 128
      < Fintype.card F := by
  have hS : (((Finset.univ.powersetCard 3).filter
      (fun T => ExplainableOn dom 2 (cubicWord dom) T)).card) ≤ 2 ^ 120 :=
    calc (((Finset.univ.powersetCard 3).filter
            (fun T => ExplainableOn dom 2 (cubicWord dom) T)).card)
        ≤ (Finset.univ.powersetCard 3 : Finset (Finset (Fin n))).card :=
          Finset.card_filter_le _ _
      _ = Nat.choose n 3 := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      _ ≤ n ^ 3 := Nat.choose_le_pow n 3
      _ ≤ (2 ^ 40) ^ 3 := Nat.pow_le_pow_left hn 3
      _ = 2 ^ 120 := by rw [← pow_mul]
  calc _ ≤ 2 ^ 120 * 2 ^ 128 := Nat.mul_le_mul_right _ hS
    _ = 2 ^ 248 := by rw [← pow_add]
    _ < Fintype.card F := hq

end ProximityGap.Cubic

#print axioms ProximityGap.Cubic.cubicSupply_silent_at_prize_scale
#print axioms ProximityGap.Cubic.cubicSupply_silent_unconditional
#print axioms ProximityGap.Cubic.cubicSupply_mul_two_pow_128_lt_card
