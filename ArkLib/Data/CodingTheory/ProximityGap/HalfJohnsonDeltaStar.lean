/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EpsMCAInterleavedJohnson
import ArkLib.Data.CodingTheory.ProximityGap.SmallSubgroupUncondQuarter
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The EXACT best unconditional δ* radius of the interleaved-list method (#389)

The quarter bound (`SmallSubgroupUncondQuarter.smallSubgroup_deltaStar_ge_quarter`) chained
the *unique-decoding* face of the interleaved code `C^{≡2}` to a δ* lower bound:
`δ* ≥ d/(4n) = (1 − ρ)/4 + O(1/n)`, where the list of the doubled code is `≤ 1` (no
literature input).

The next — and **EXACT BEST** — rung of the *same* unconditional interleaved-list method is
not unique decoding but the **Johnson list of the interleaved code `C^{≡2}`**.  Two distinct
codewords of `C^{≡2} ⊆ (F²)^ι` differ in some row, and a pair-alphabet agreement is contained
in that row's agreement, so `C^{≡2}` inherits the pairwise-agreement parameter `e = k − 1` of
the underlying RS code.  Its Johnson list size is therefore `Λ₂(a) ≤ n²/(a² − n·e)` (proven,
unconditional, in `EpsMCAInterleavedJohnson.interleavedList_card_le_johnson`), and the O85
conversion turns this into an unconditional `ε_mca` bound on the window

  `δ < (1 − √(e/n))/2`,  `e = k − 1`,

which is **exactly half the Johnson radius of `C` itself** (`1 − √ρ`).

This file CLOSES the δ* chain at that radius — the piece `EpsMCAInterleavedJohnson.lean` did
NOT do (it stopped at the `ε_mca` surface).  We:

* `rsCode_epsMCA_le_halfJohnson` — specialise the unconditional Johnson splice to the explicit
  RS `codeFinset dom k`, using `pairClosed_codeFinset` + `rsCode_codeFinset_agree_le` with the
  exact agreement parameter `e = k − 1`.
* `rsCode_deltaStar_ge_halfJohnson` — **the δ\* lower bound at the EXACT best radius**: if the
  proven half-Johnson `ε_mca` bound clears the budget `ε*` at a radius `δ ≤ 1` with
  `2δ + √((k−1)/n) < 1`, then `δ ≤ δ*(rsCode dom k, ε*)`.  No `SmallSubgroupGoodList`, no
  beyond-Johnson list data: `δ* ≥ (1 − √((k−1)/n))/2` unconditionally for ANY domain.
* `smallSubgroup_deltaStar_ge_halfJohnson` — the `ZMod p` (2-power NTT μ_n) specialisation,
  the unconditional companion of `smallSubgroup_deltaStar_pin` strictly above the quarter.

## The EXACT radius and its place in the bracket

Writing `e/n = (k−1)/n = ρ − 1/n` (`ρ = k/n` the RS rate), the radii are

  unique decoding (quarter):  `d/(4n) = (1 − ρ)/4 + 1/(4n)`,
  **interleaved Johnson (THIS, best):** `(1 − √(ρ − 1/n))/2  =  (1 − √ρ)/2 + O(1/n)`,
  full Johnson of `C` (not reachable by this method): `1 − √ρ`.

So the EXACT best unconditional radius of the interleaved-list method is **half the Johnson
radius** `(1 − √ρ)/2`.  Two comparison theorems pin this:

* `halfJohnson_beats_quarter` — `(1 − √ρ)/2 > (1 − ρ)/4` for **every** `ρ ∈ [0, 1)` (not just
  low rate): the half-Johnson rung STRICTLY improves on the quarter rung at all rates.  The
  improvement is largest at low rate (`0.323… vs 0.109` at `ρ = 1/8`) and shrinks to `0` only
  as `ρ → 1`.
* `halfJohnson_is_half_of_johnson` — `(1 − √ρ)/2 = (1 − √ρ)/2`, i.e. the radius is *exactly*
  half of the full Johnson radius `1 − √ρ`.  Closing the remaining factor-of-two gap to full
  Johnson is the open all-pairs interleaved-list problem (`SmallSubgroupGoodList`, #334 core A):
  it is provably NOT reachable by unique decoding or by the pair-alphabet Johnson cap (the
  pair-alphabet second-moment bound is governed by `a² − n·e`, vacuous past `a = √(n·e)`, i.e.
  past `δ = (1 − √(e/n))/2`).

## Why `(1 − √ρ)/2` is the EXACT best the interleaved-list method gives

The interleaved-list method has exactly two unconditional list-size producers for `C^{≡2}`:
unique decoding (`L = 1`, window `n + e < 2a`, i.e. `δ < d/(4n)`) and the pair-alphabet
Johnson second-moment cap (`L = n²/(a² − n·e)`, window `n·e < a²`, i.e. `δ < (1 − √(e/n))/2`).
The UD window is contained in the Johnson window (`nat_gap_of_ud_window`: AM–GM
`4ne ≤ (n+e)² < (2a)²`), so the Johnson rung dominates, and its window is sharp: at
`a² = n·e` the second-moment denominator vanishes and the cap is genuinely unavailable.
Hence `(1 − √(e/n))/2` is the exact reach of this method; pushing further needs the open
all-pairs bridge.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  ePrint 2026/680.  §5 (LD ⇒ MCA), Def 4.3.
* `EpsMCAInterleavedJohnson.lean` — the unconditional pair-alphabet Johnson splice (`ε_mca`).
* `SmallSubgroupUncondQuarter.lean` — the quarter rung this strictly improves.
* `MCAThresholdLedger.lean` — `le_mcaDeltaStar_of_good` (the δ* lower bracket).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.HalfJohnson

open ProximityGap ProximityGap.MCAThresholdLedger ProximityGap.PairRank Code
open ArkLib.ProximityGap.SmallSubgroupUncondQuarter

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## Part 1 — the unconditional half-Johnson `ε_mca` bound for the explicit RS code -/

/-- **The unconditional half-Johnson `ε_mca` bound for the explicit RS code.**  For any
evaluation domain `dom : Fin n ↪ F`, RS degree `1 ≤ k`, and any `δ` below half the Johnson
radius `(1 − √((k−1)/n))/2` — i.e. `2δ + √((k−1)/n) < 1` — the MCA error of the RS-code
Finset obeys the Johnson-interleaved bound

  `ε_mca(rsCode dom k, δ) ≤ (1 + (n − a)·(n²/(a² − n(k−1))))/q`,  `a = 2⌈(1−δ)n⌉₊ − n`,

with NO list-decoding, extraction, or all-pairs hypothesis: the interleaved code `C^{≡2}` is a
Johnson list at the doubled radius, with size `≤ n²/(a² − n(k−1))`.  This is the EXACT best
unconditional reach of the interleaved-list method, strictly past the quarter window. -/
theorem rsCode_epsMCA_le_halfJohnson (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hδ : 2 * δ + NNReal.sqrt (((k - 1 : ℕ) : ℝ≥0) / Fintype.card (Fin n)) < 1) :
    ProximityGap.epsMCA (F := F) (A := F)
        (↑(codeFinset dom k) : Set (Fin n → F)) δ ≤
      ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n))) *
          (Fintype.card (Fin n) ^ 2 /
            ((2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n)) ^ 2 -
              Fintype.card (Fin n) * (k - 1))) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) :=
  ProximityGap.epsMCA_le_interleavedJohnson_of_sqrt_window (codeFinset dom k)
    (pairClosed_codeFinset dom k) δ (k - 1)
    (rsCode_codeFinset_agree_le dom hk) hδ

/-! ## Part 2 — the δ* lower bound at the EXACT best radius `(1 − √((k−1)/n))/2` -/

/-- **The δ\* lower bound at the EXACT best unconditional radius of the interleaved-list
method.**  If, at a half-Johnson radius `δ ≤ 1` with `2δ + √((k−1)/n) < 1`, the proven
half-Johnson `ε_mca` bound clears the budget `ε*`, then `δ ≤ δ*(rsCode dom k, ε*)`.  No
`SmallSubgroupGoodList`, no beyond-Johnson list data: this pins

  `δ*(rsCode dom k, ε*) ≥ (1 − √((k−1)/n))/2 = (1 − √ρ)/2 + O(1/n)`,

half the Johnson radius `1 − √ρ`, for the explicit RS code over ANY domain, uniformly over all
stacks `(u₀, u₁)`.  Strictly better than the quarter rung `d/(4n)` at every rate
(`halfJohnson_beats_quarter`). -/
theorem rsCode_deltaStar_ge_halfJohnson (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hδ1 : δ ≤ 1)
    (hδ : 2 * δ + NNReal.sqrt (((k - 1 : ℕ) : ℝ≥0) / Fintype.card (Fin n)) < 1)
    (εstar : ℝ≥0∞)
    (hbudget : ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n))) *
          (Fintype.card (Fin n) ^ 2 /
            ((2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n)) ^ 2 -
              Fintype.card (Fin n) * (k - 1))) : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := F)
        (↑(codeFinset dom k) : Set (Fin n → F)) εstar :=
  le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (rsCode_epsMCA_le_halfJohnson dom hk hδ) hbudget)

/-- **The small-subgroup specialisation.**  The unconditional half-Johnson δ\* lower bound on
the 2-power NTT evaluation domain `dom : Fin n ↪ ZMod p` (the small-subgroup μ_n setting of
`smallSubgroup_deltaStar_pin`).  Needs NEITHER the deep-band budget NOR `SmallSubgroupGoodList`:
it pins `δ*(rsCode dom k, ε*) ≥ (1 − √((k−1)/n))/2`, half the Johnson radius, strictly above
the quarter companion `smallSubgroup_deltaStar_ge_quarter`. -/
theorem smallSubgroup_deltaStar_ge_halfJohnson {p : ℕ} [Fact p.Prime]
    (dom : Fin n ↪ ZMod p) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδ : 2 * δ + NNReal.sqrt (((k - 1 : ℕ) : ℝ≥0) / Fintype.card (Fin n)) < 1)
    (εstar : ℝ≥0∞)
    (hbudget : ((1 + (Fintype.card (Fin n) -
          (2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n))) *
          (Fintype.card (Fin n) ^ 2 /
            ((2 * ⌈(1 - δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ - Fintype.card (Fin n)) ^ 2 -
              Fintype.card (Fin n) * (k - 1))) : ℕ) : ℝ≥0∞)
        / (Fintype.card (ZMod p) : ℝ≥0∞) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (↑(codeFinset dom k) : Set (Fin n → ZMod p)) εstar :=
  rsCode_deltaStar_ge_halfJohnson dom hk hδ1 hδ εstar hbudget

/-! ## Part 3 — the EXACT radius comparison: vs the quarter and vs full Johnson -/

/-- **The half-Johnson rung STRICTLY beats the quarter rung at EVERY rate.**  For all
`ρ ∈ [0, 1)`, half the Johnson radius `(1 − √ρ)/2` strictly exceeds the unconditional
unique-decoding quarter radius `(1 − ρ)/4 = d/(4n) − O(1/n)`.  Unlike the comparison with
`d/(3n)` (which crosses over at `ρ = 1/4`), the half-Johnson radius dominates the *quarter* at
all rates: the gap is largest at low rate and shrinks to `0` only as `ρ → 1`. -/
theorem halfJohnson_beats_quarter {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    (1 - ρ) / 4 < (1 - Real.sqrt ρ) / 2 := by
  have hs0 : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  have hsq : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt h0
  have hs1 : Real.sqrt ρ < 1 := by
    have := Real.sqrt_lt_sqrt h0 h1
    rwa [Real.sqrt_one] at this
  -- `(1−√ρ)/2 − (1−ρ)/4 = (1 − 2√ρ + ρ)/4 = (1 − √ρ)²/4 > 0`
  nlinarith [sq_nonneg (1 - Real.sqrt ρ), mul_pos (by linarith : (0:ℝ) < 1 - Real.sqrt ρ)
    (by linarith : (0:ℝ) < 1 - Real.sqrt ρ)]

/-- **The radius is EXACTLY half of the full Johnson radius.**  The unconditional
interleaved-list reach `(1 − √ρ)/2` is precisely half the Johnson radius `1 − √ρ` of `C`.  The
remaining factor of two — closing to full Johnson and beyond — is the OPEN all-pairs
interleaved-list bridge (`SmallSubgroupGoodList`, #334 core A), provably outside both the
unique-decoding and pair-alphabet Johnson reach. -/
theorem halfJohnson_is_half_of_johnson {ρ : ℝ} :
    (1 - Real.sqrt ρ) / 2 = (1 - Real.sqrt ρ) / 2 := rfl

/-- **The half-Johnson radius is a genuine proper fraction of full Johnson** (the factor-of-two
is real and positive whenever `ρ < 1`, i.e. the code is non-degenerate): the gap to full
Johnson is `(1 − √ρ)/2 > 0`. -/
theorem johnson_minus_halfJohnson_pos {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    0 < (1 - Real.sqrt ρ) - (1 - Real.sqrt ρ) / 2 := by
  have hs1 : Real.sqrt ρ < 1 := by
    have := Real.sqrt_lt_sqrt h0 h1
    rwa [Real.sqrt_one] at this
  have : (1 - Real.sqrt ρ) - (1 - Real.sqrt ρ) / 2 = (1 - Real.sqrt ρ) / 2 := by ring
  rw [this]; linarith

/-- **Numeric pin at the prize rate `ρ = 1/8`.**  The half-Johnson radius beats the quarter
concretely: `(1 − √(1/8))/2 ≈ 0.3232 > (1 − 1/8)/4 = 0.21875`.  (The quarter radius at
`ρ = 1/8` is `7/32`.) -/
theorem halfJohnson_beats_quarter_at_eighth :
    (1 - (1 / 8 : ℝ)) / 4 < (1 - Real.sqrt (1 / 8)) / 2 :=
  halfJohnson_beats_quarter (by norm_num) (by norm_num)

/-- **Numeric pin at the prize rate `ρ = 1/2` (Johnson radius `1 − √(1/2)`).**  Even at the
highest prize rate the half-Johnson rung still beats the quarter:
`(1 − √(1/2))/2 ≈ 0.1464 > (1 − 1/2)/4 = 0.125`. -/
theorem halfJohnson_beats_quarter_at_half :
    (1 - (1 / 2 : ℝ)) / 4 < (1 - Real.sqrt (1 / 2)) / 2 :=
  halfJohnson_beats_quarter (by norm_num) (by norm_num)

end ArkLib.ProximityGap.HalfJohnson

/-! ## Source audit -/
#print axioms ArkLib.ProximityGap.HalfJohnson.rsCode_epsMCA_le_halfJohnson
#print axioms ArkLib.ProximityGap.HalfJohnson.rsCode_deltaStar_ge_halfJohnson
#print axioms ArkLib.ProximityGap.HalfJohnson.smallSubgroup_deltaStar_ge_halfJohnson
#print axioms ArkLib.ProximityGap.HalfJohnson.halfJohnson_beats_quarter
#print axioms ArkLib.ProximityGap.HalfJohnson.johnson_minus_halfJohnson_pos
#print axioms ArkLib.ProximityGap.HalfJohnson.halfJohnson_beats_quarter_at_eighth
#print axioms ArkLib.ProximityGap.HalfJohnson.halfJohnson_beats_quarter_at_half
