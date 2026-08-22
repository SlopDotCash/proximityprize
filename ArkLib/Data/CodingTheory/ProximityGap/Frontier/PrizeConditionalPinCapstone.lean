/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26AsymptoticCeiling
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# The prize δ* conditional pin — capstone (the whole prize = ONE explicit inequality)

This file is the **honest assembly point** for the Reed–Solomon proximity-gap prize (issue #444):
it pins the MCA threshold `δ*` to an *explicit closed value* for the concrete smooth-domain RS code
`evalCode g n ((r−2)·m)` in the prize regime, resting on **exactly one open hypothesis**.

## The two directions

* **CEILING (PROVEN).** `kkh26_mcaDeltaStar_le_capacity_sub_log` proves, axiom-clean,
  `δ*(evalCode …, ε*) ≤ (1 − ρ) − 1/(C·L)` — the Kambiré/KKH26 bad-line family forces correlated
  agreement to *fail* above the window edge. Its hypotheses (`hp` the height condition, `hεstar` the
  budget, `hregime`/`hgap` the thin-regime transport) hold at the concrete prize primes; this
  direction needs only the existence of one bad family (the Thorner–Zaman supply).

* **FLOOR (the SINGLE OPEN INPUT).** `hfloor : epsMCA (evalCode …) edge ≤ ε*` — that the edge radius
  is *good*, i.e. the **realized worst-case bad-scalar count** at the edge stays within the prize
  budget. This is the genuine open core of the prize.

`prize_deltaStar_eq_edge` combines them: **`δ* = (1 − ρ) − 1/(C·L)` GIVEN the one floor inequality.**

## ⚠️ The floor is FINER than the L∞ char-sum bound `M(n) ≤ C·√(n·log m)` (honest correction)

A natural hope is to discharge `hfloor` from the BGK/Paley square-root-cancellation bound
`M(n) = max_{b≠0}|η_b| ≤ C·√(n·log m)`. **This does not work**: `M` is *necessary but insufficient*.
The only `M → epsMCA` route currently available
(`CharSumDeltaStarBridge.le_mcaDeltaStar_of_charSumBound`) goes through the **naive** per-line incidence
budget `|G| + q·B`, which at the prize budget `q·ε* ≈ n ≈ |G|` forces `B ≈ 0` — it is **vacuous** for
any nonzero char-sum bound (overshoots by the index factor `√m`). So `hfloor` (the realized worst-case
incidence) is a *strictly finer* object than `M`; closing it is the actual open problem, NOT the L∞
bound.

So: the prize is **pinned modulo the single realized-incidence floor `hfloor`** — not modulo `M`.

All results `sorry`-free; axiom audit at the bottom.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026 (#444).
- `KKH26AsymptoticCeiling.lean` (proven ceiling), `MCAThresholdLedger.lean` (the δ* ledger),
  `Frontier/DeltaStarEqEdge.lean` (`mcaDeltaStar_eq_of_good_above_bad`, the abstract pin).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.KKH26

/-- The explicit prize δ* edge value: `capacity − 1/(C·L)` at granularity `1/n`, i.e.
`(1 − ((r−2)·m+1)/n) − 1/(C·L)` — one window rung below capacity `1 − ρ`. -/
noncomputable def prizeEdge (n m r : ℕ) (C L : ℝ≥0) : ℝ≥0 :=
  (1 - ((r - 2 : ℕ) * m + 1 : ℕ) / (n : ℝ≥0)) - 1 / (C * L)

theorem prizeEdge_le_one (n m r : ℕ) (C L : ℝ≥0) : prizeEdge n m r C L ≤ 1 :=
  le_trans tsub_le_self tsub_le_self

/-- **CAPSTONE — the prize δ* is pinned to the explicit value `capacity − 1/(C·L)` by exactly ONE
open input.** For the concrete smooth-domain RS code `evalCode g n ((r−2)·m)` in the prize regime:
the CEILING is proven (`kkh26_mcaDeltaStar_le_capacity_sub_log`); the FLOOR `hfloor` — that the
realized worst-case bad-scalar count at the edge stays within budget — is the single remaining open
hypothesis. Together they pin `δ* = prizeEdge`. -/
theorem prize_deltaStar_eq_edge {p n : ℕ} [Fact p.Prime] [NeZero n]
    {μ m r : ℕ} (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
    {C L : ℝ≥0} (hC : 0 < C) (hL : 0 < L)
    (hregime : ((2 : ℝ≥0) ^ μ) ≤ C * L)
    (hgap : (1 : ℝ≥0) - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ)
      ≤ (1 - ((r - 2 : ℕ) * m + 1 : ℕ) / (n : ℝ≥0)) - 1 / (C * L))
    (hfloor : ProximityGap.epsMCA (F := ZMod p)
        (evalCode g n ((r - 2) * m)) (prizeEdge n m r C L) ≤ εstar) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
        (evalCode g n ((r - 2) * m)) εstar
      = prizeEdge n m r C L := by
  refine le_antisymm ?_ ?_
  · exact kkh26_mcaDeltaStar_le_capacity_sub_log hμ hm hn hg hp hr2 hr εstar hεstar hC hL hregime hgap
  · exact ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good
      (evalCode g n ((r - 2) * m)) εstar (prizeEdge_le_one n m r C L) hfloor

/-! ## Source audit -/

#print axioms prizeEdge_le_one
#print axioms prize_deltaStar_eq_edge

end ArkLib.ProximityGap.KKH26
