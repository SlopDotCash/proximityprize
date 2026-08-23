/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWindowInteriorExact
import ArkLib.Data.CodingTheory.ProximityGap.MCAAntichainLYM
import ArkLib.Data.CodingTheory.ProximityGap.MCAExactPin

/-!
# The first exact `δ*` PIN strictly inside the proximity window (#357)

`MCAWindowInteriorExact.lean` produced the first exact *value* `ε_mca(C, 2/5) = 10/11` for
`C = RS[F₁₁, (1,2,3,4,5), 2]` at an interior radius (`δ = 2/5 ∈ (Johnson 0.368, capacity 0.6)`,
rate `ρ = 2/5`). This file turns that value into an exact **threshold pin** — the grand-challenge
target, two `mcaDeltaStar` brackets that *meet*:

  **`mcaDeltaStar(RS[F₁₁, (1,2,3,4,5), 2], 5/11) = 2/5`**  (`mcaDeltaStar_window_interior_eq`),

with `2/5` strictly inside the window `(1−√ρ, 1−ρ)`. This is, to our knowledge, the **first exact
`δ*` value pinned strictly inside the open Johnson–capacity window for any code** — the regime
where the Proximity Prize is open.

The pin assembles three landed facts through the open-interval combinator
(`mcaDeltaStar_eq_of_good_below_of_bad_above`, `MCAExactPin.lean`):

* **bad at `2/5`** — `epsMCA_window_eq` gives `ε_mca(C, 2/5) = 10/11 > 5/11`;
* **bad above `2/5`** — `epsMCA_mono` propagates it: `ε_mca(C, δ) ≥ 10/11` for `δ ≥ 2/5`;
* **good below `2/5`** — the sharp ceiling `epsMCA_le_choose_ceil_div`: for `δ < 2/5` the witness
  floor is `≥ 4`, so the bad scalars form an antichain of `≥ 4`-sets in a 5-point universe, capped
  by `C(5,4) = 5`, hence `ε_mca(C, δ) ≤ 5/11`.

The good and bad sides **meet exactly** at the granularity jump `δ = 2/5` (where the witness floor
drops from `4` to `3`, opening the extra `C(5,3) − C(5,4) = 5` bad scalars). The pin is the jump.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger
open ProximityGap.MCAWindowInteriorExact

namespace ProximityGap.MCAWindowInteriorPin

/-- The interior threshold `ε* = 5/11 = C(5,4)/q`, between the good-side ceiling `C(5,4)/q` and
the bad value `C(5,3)/q = 10/11`. -/
noncomputable def epsStar : ℝ≥0∞ := (5 : ℝ≥0∞) / 11

/-- **Good below the jump.** For every radius `δ < 2/5`, the universal LYM ceiling at the integer
witness floor `⌈(1−δ)·5⌉ ≥ 4` gives `ε_mca(C, δ) ≤ C(5,4)/q = 5/11 = ε*`. -/
theorem epsMCA_good_below (δ : ℝ≥0) (hδ : δ < 2/5) :
    epsMCA (F := F11) (A := F11)
        (ReedSolomon.code domain5 2 : Set (Fin 5 → F11)) δ ≤ epsStar := by
  set c5 : ℝ≥0 := (Fintype.card (Fin 5) : ℝ≥0) with hc5
  have hc5val : c5 = 5 := by rw [hc5, Fintype.card_fin]; norm_num
  -- witness floor `⌈(1−δ)·5⌉ ≥ 4`, since `(1−δ)·5 > 3`
  have hx : (3 : ℝ≥0) < ((1 : ℝ≥0) - δ) * c5 := by
    rw [hc5val]
    have h1 : (3 : ℝ≥0)/5 < 1 - δ := by
      rw [lt_tsub_iff_left]
      calc δ + 3/5 < 2/5 + 3/5 := by gcongr
        _ = 1 := by norm_num
    calc (3 : ℝ≥0) = (3/5) * 5 := by norm_num
      _ < (1 - δ) * 5 := by
            exact mul_lt_mul_of_pos_right h1 (by norm_num)
  have hceil4 : 4 ≤ ⌈((1 : ℝ≥0) - δ) * c5⌉₊ :=
    (Nat.lt_ceil).mpr (by exact_mod_cast hx)
  have hhalf : Fintype.card (Fin 5) ≤ 2 * ⌈((1 : ℝ≥0) - δ) * c5⌉₊ := by
    rw [Fintype.card_fin]; omega
  have hbound := ProximityGap.MCAAntichainLYM.epsMCA_le_choose_ceil_div (F := F11) (A := F11)
    (ReedSolomon.code domain5 2) δ hhalf
  refine hbound.trans ?_
  have hF : Fintype.card F11 = 11 := ZMod.card 11
  rw [hF]
  have hchoose : (Fintype.card (Fin 5)).choose ⌈((1 : ℝ≥0) - δ) * c5⌉₊ ≤ 5 := by
    rw [Fintype.card_fin]
    set t := ⌈((1 : ℝ≥0) - δ) * c5⌉₊ with ht
    have ht4 : 4 ≤ t := hceil4
    rcases Nat.lt_or_ge t 6 with h6 | h6
    · interval_cases t <;> decide
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; omega
  rw [epsStar]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast hchoose

/-- **Bad at and above the jump.** `ε_mca(C, δ) ≥ 10/11 > 5/11 = ε*` for every `δ ≥ 2/5`, from the
exact interior value at `2/5` and monotonicity of `ε_mca` in `δ`. -/
theorem epsMCA_bad_above (δ : ℝ≥0) (hδ : 2/5 ≤ δ) :
    epsStar < epsMCA (F := F11) (A := F11)
        (ReedSolomon.code domain5 2 : Set (Fin 5 → F11)) δ := by
  have hmono := epsMCA_mono (F := F11) (A := F11)
    (ReedSolomon.code domain5 2 : Set (Fin 5 → F11)) hδ
  rw [epsMCA_window_eq] at hmono
  refine lt_of_lt_of_le ?_ hmono
  rw [epsStar]
  exact ENNReal.div_lt_div_right (by norm_num) (by norm_num) (by norm_num)

/-- **THE INTERIOR PIN.** `δ*(RS[F₁₁,(1,2,3,4,5),2], 5/11) = 2/5`, with `2/5` strictly inside the
open Johnson–capacity window `(1−√ρ, 1−ρ)` for rate `ρ = 2/5`. The first exact `δ*` value pinned
inside the proximity window for any code; the brackets meet at the granularity jump. -/
theorem mcaDeltaStar_window_interior_eq :
    mcaDeltaStar (F := F11) (A := F11)
        (ReedSolomon.code domain5 2 : Set (Fin 5 → F11)) epsStar = 2/5 := by
  refine mcaDeltaStar_eq_of_good_below_of_bad_above
    (ReedSolomon.code domain5 2 : Set (Fin 5 → F11)) epsStar ?_ ?_ ?_
  · rw [div_le_one (by norm_num : (0:ℝ≥0) < 5)]; norm_num
  · exact fun δ hδ => epsMCA_good_below δ hδ
  · exact fun δ hδ => epsMCA_bad_above δ hδ

end ProximityGap.MCAWindowInteriorPin

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.MCAWindowInteriorPin.epsMCA_good_below
#print axioms ProximityGap.MCAWindowInteriorPin.mcaDeltaStar_window_interior_eq
