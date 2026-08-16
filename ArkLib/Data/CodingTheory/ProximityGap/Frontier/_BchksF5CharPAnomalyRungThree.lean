/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergyThreeCharPLowerBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The char-`p` additive-energy anomaly at rung `r = 3`: BOTH-SIDED squeeze (#444)

`_BchksF5_CharPAnomalyExpZero.lean` proved the "exponent-0" anomaly bound
`W_r = E_r(F_p) − E_r^{char0} ≤ Wick_r − E_r^{char0}` (a degree-`(r−1)` gap, leading `n^r`
coefficient cancelled, so the anomaly never moves the leading energy) for `r = 4, 5, 6, 7`, GIVEN
the below-Wick char-`p` input `E_r(F_p) ≤ Wick_r`. It does NOT cover `r = 3`, and for `r = 4..7`
it can prove only the UPPER half of the squeeze (`W_r ≤ gap`); the LOWER half `0 ≤ W_r` is asserted
in prose but left unproven there (the char-0 closed forms `E0 4..7` are stated as `def`s, not
proven additive energies).

**This file lands the `r = 3` rung, BOTH-SIDED and fully discharged on the lower side.** For
`r = 3` the char-0 energy is the genuinely *proven* combinatorial value
`E_3^{char0}(μ_n) = 15n³ − 45n² + 40n` (the negation-symmetric strata producer
`negSymCount_six_closed`, kernel-checked), and the char-`p` LOWER bound
`rEnergy(μ_n) 3 ≥ 15n³ − 45n² + 40n` is ALSO proven char-`p`-universally
(`muN_rEnergy_three_ge_closed`). So at `r = 3`:

* **lower half `0 ≤ W_3`**  — UNCONDITIONAL (proven, not a hypothesis): the char-`p` energy is at
  least the char-0 value (`anomaly_three_nonneg`);
* **upper half `W_3 ≤ Wick_3 − E_3^{char0} = 45n² − 40n`**  — GIVEN the below-Wick input
  `rEnergy 3 ≤ 15n³ = Wick_3` (the open deep-`r` wall, named explicitly): the gap is degree
  `2 = r−1`, leading `n³` cancelled (`gap_three`), so the anomaly is strictly sub-leading
  (`anomaly_three_le_gap`).

The two combine into the both-sided squeeze `0 ≤ W_3 ≤ 45n² − 40n` (`anomaly_three_squeeze`), with
ONLY the upper side conditional on the open Wick wall. This is the `r = 3` analogue of `_BchksF5`,
sharper because the lower half is proven rather than asserted.

## Honest scope
The genuine open input is the below-Wick char-`p` bound `rEnergy(μ_n) 3 ≤ 15n³` (the W1/DC-Wick
deep-`r` wall, the BGK/Burgess √-cancellation core of #444). This file proves NO upper Wick bound,
NO CORE/cancellation, NO completion, NO capacity, NO beyond-Johnson/δ* claim. It records the exact
exponent-0 squeeze at rung 3, with the lower half unconditional. Issue #444.
-/

open ArkLib.ProximityGap.Frontier.REnergyThreeCharPLowerBound
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.EnergyEqualitySidonModNeg (muN)

namespace ArkLib.ProximityGap.Frontier.BchksF5CharPAnomalyRungThree

/-- `Wick_3 n = (2·3−1)‼ · n³ = 5‼ · n³ = 15 n³`. -/
def Wick3 (n : ℕ) : ℤ := 15 * (n : ℤ) ^ 3

/-- `E_3^{char0}(n) = 15 n³ − 45 n² + 40 n` (the proven negation-symmetric strata value). -/
def E0Three (n : ℕ) : ℤ := 15 * (n : ℤ) ^ 3 - 45 * (n : ℤ) ^ 2 + 40 * (n : ℤ)

/-- **The Wick−char0 gap at `r = 3` has the leading coefficient cancelled.** `Wick_3 − E_3^{char0}
= 45 n² − 40 n`, a degree-`2 = r−1` polynomial: the `n³` term vanishes (`15 − 15 = 0`). So the
anomaly bound is strictly sub-leading — it cannot move the leading-order `(2r−1)‼·n^r` energy,
hence not the leading `δ*`. -/
theorem gap_three (n : ℕ) : Wick3 n - E0Three n = 45 * (n : ℤ) ^ 2 - 40 * (n : ℤ) := by
  unfold Wick3 E0Three; ring

/-- **Lower half (UNCONDITIONAL): `0 ≤ W_3` for `μ_n`.** The char-`p` depth-3 relation energy is at
least the char-0 closed form (`muN_rEnergy_three_ge_closed`), so the anomaly
`W_3 = rEnergy(μ_n) 3 − E_3^{char0}` is non-negative. NO Wick hypothesis needed — the extra mod-`p`
coincidences only ADD zero-sum tuples, never remove the genuine ℂ-coincidences. -/
theorem anomaly_three_nonneg {p : ℕ} [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) {n m : ℕ}
    (hn2 : n = 2 ^ m) (hm : 1 ≤ m) {ω : ZMod p} (hω : IsPrimitiveRoot ω n) :
    0 ≤ (rEnergy (muN p n) 3 : ℤ) - E0Three n := by
  have hge := muN_rEnergy_three_ge_closed hp2 hn2 hm hω
  unfold E0Three
  linarith [hge]

/-- **Upper half (GIVEN the open below-Wick input): `W_3 ≤ 45 n² − 40 n`.** From the deep-`r` wall
hypothesis `rEnergy(μ_n) 3 ≤ Wick_3 = 15 n³`, the anomaly is bounded by the degree-`2` gap. The
hypothesis `hWick` is the genuine open core (the BGK/Burgess √-cancellation wall); everything else
is the exact char-0/Wick arithmetic. -/
theorem anomaly_three_le_gap {p : ℕ} [Fact p.Prime] {n : ℕ}
    (hWick : (rEnergy (muN p n) 3 : ℤ) ≤ Wick3 n) :
    (rEnergy (muN p n) 3 : ℤ) - E0Three n ≤ 45 * (n : ℤ) ^ 2 - 40 * (n : ℤ) := by
  have h := sub_le_sub_right hWick (E0Three n)
  rwa [gap_three] at h

/-- **The both-sided exponent-0 squeeze at `r = 3`.** Combining the unconditional lower half and the
Wick-conditional upper half: `0 ≤ W_3 ≤ 45 n² − 40 n`. The lower bound is PROVEN (not assumed); only
the upper bound is conditional on the open below-Wick wall `rEnergy(μ_n) 3 ≤ 15 n³`. The anomaly is
pinned to a degree-`2` band, one power below the leading `n³` energy — exponent-0, as `_BchksF5`
states for `r = 4..7`, but here with the lower half discharged. -/
theorem anomaly_three_squeeze {p : ℕ} [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) {n m : ℕ}
    (hn2 : n = 2 ^ m) (hm : 1 ≤ m) {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    (hWick : (rEnergy (muN p n) 3 : ℤ) ≤ Wick3 n) :
    0 ≤ (rEnergy (muN p n) 3 : ℤ) - E0Three n
      ∧ (rEnergy (muN p n) 3 : ℤ) - E0Three n ≤ 45 * (n : ℤ) ^ 2 - 40 * (n : ℤ) :=
  ⟨anomaly_three_nonneg hp2 hn2 hm hω, anomaly_three_le_gap hWick⟩

end ArkLib.ProximityGap.Frontier.BchksF5CharPAnomalyRungThree

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.BchksF5CharPAnomalyRungThree.gap_three
#print axioms ArkLib.ProximityGap.Frontier.BchksF5CharPAnomalyRungThree.anomaly_three_nonneg
#print axioms ArkLib.ProximityGap.Frontier.BchksF5CharPAnomalyRungThree.anomaly_three_le_gap
#print axioms ArkLib.ProximityGap.Frontier.BchksF5CharPAnomalyRungThree.anomaly_three_squeeze
