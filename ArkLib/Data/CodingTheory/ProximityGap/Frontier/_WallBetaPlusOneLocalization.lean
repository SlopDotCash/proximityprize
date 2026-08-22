/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection

/-!
# The first unproven rung `r = β+1`: the char-0 / wraparound split of `DCEnergyBound` (#466, W1)

`DCEnergyCorrection.DCEnergyBound G r` (`A_r ≤ Wick`, i.e. `q·E_r − n^{2r} ≤ q·(2r−1)‼·n^r`) is the
single open per-rung prize hypothesis.  It is proven for `r ≤ β` (DC-crossover / moment-exponent /
TPS-boundary all agree); the prize needs it to `r ≈ ln q`, and `r = β+1` is the **first unproven
rung**.  This file records the EXACT, axiom-clean algebraic localization of that rung, matching the
probe `scripts/probes/probe_466_wall_betaP1.py` (`_out_466_wall_betaP1.txt`).

Write the char-p energy count as `E_r = E_∞ + W_r`, where `E_∞` is the **char-0** energy (the
`p`-independent ladder `E₂ = 3n²−3n, …`; for the dyadic subgroup an exact closed form
`E_∞ = Σ_{c₁+…+c_{n/2}=r}(2r)!/∏(c_t!)²`) and `W_r ≥ 0` is the **wraparound / anomaly**.  Then
exactly `A_r = E_∞ + (W_r − n^{2r}/q)`, so with `D_r := W_r − n^{2r}/q` (the DC-deviation):

* **`CharZeroWick`** `E_∞ ≤ (2r−1)‼·n^r` — the char-0 half.  **PROVEN** (Lam–Leung; in-tree
  `NegationClosedWalk.zeroSumCount_le_doubleFactorial_dyadic` for `μ_{2^k}`).
* **`WraparoundBelowDC`** `q·W_r ≤ n^{2r}` (i.e. `D_r ≤ 0`, the wraparound at/below its DC mean) —
  the **open** residual (= the "Anomaly-Suppression inequality" of `DCEnergyCorrection`).

The two together give `DCEnergyBound` (`dcEnergyBound_of_charZero_of_wraparoundBelowDC`), and under
`WraparoundBelowDC` one even gets the *double margin* `A_r ≤ E_∞ ≤ Wick`
(`dcSubtracted_le_charZero_of_wraparoundBelowDC`) — matching the probe, where `A_r < E_∞ ≤ Wick`
at **every** measured `(n, p, r)` (`D_r < 0` robustly, generic *and* generalized-Fermat).

**The W1 verdict (honest, non-overclaimed).** This SPLIT discharges the char-0 half unconditionally
and pins the entire open content of the `r = β+1` rung to the single scalar inequality
`WraparoundBelowDC`.  That inequality is NOT a signed cancellation (`W_r` is a nonnegative count;
there is nothing to cancel — cf. the round-4 "signed levels" kill): it is the *unsigned*
concentration statement "the arithmetic wraparound count does not exceed its DC mean".  At the prize
(`n = 2^30`, `β = 4`, `r = 5`) it demands `W_r = n^{2r}/p·(1 + O(2^{−47}))` — a genuine
square-root-cancellation statement, no exact formula (the char-0 ladder is `p`-independent and sees
only the diagonal-adjacent part).  So `r = β+1` is *already the wall*, now sharpened from
"`r ≈ log q`" to the exact object `WraparoundBelowDC` at the first past-crossover rung.

Issue #466 (lane W1).
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyCorrection

namespace ArkLib.ProximityGap.WallBetaPlusOne

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The Wick reference value `(2r−1)‼·n^r` as a real. -/
noncomputable def wick (G : Finset F) (r : ℕ) : ℝ :=
  (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r

/-- The char-0 (Lam–Leung) half, on the abstract char-0 energy `Einf`:  `E_∞ ≤ (2r−1)‼·n^r`.
For the dyadic subgroup this is discharged by
`NegationClosedWalk.zeroSumCount_le_doubleFactorial_dyadic`. -/
def CharZeroWick (G : Finset F) (r : ℕ) (Einf : ℝ) : Prop :=
  Einf ≤ wick G r

/-- The open residual: the **wraparound at/below its DC mean**, `q·(E_r − E_∞) ≤ n^{2r}`
(equivalently `D_r = W_r − n^{2r}/q ≤ 0`).  This is the "Anomaly-Suppression inequality"; the
probe measures it TRUE (strictly, `D_r < 0`) at every prize prime but it is the open concentration
statement, not an algebraic identity. -/
def WraparoundBelowDC (G : Finset F) (r : ℕ) (Einf : ℝ) : Prop :=
  (Fintype.card F : ℝ) * ((rEnergy G r : ℝ) - Einf) ≤ (G.card : ℝ) ^ (2 * r)

/-- **The split (sufficiency).** The proven char-0 half `CharZeroWick` together with the open
residual `WraparoundBelowDC` gives the per-rung prize bound `DCEnergyBound` (`A_r ≤ Wick`). This is
the exact localization of `r = β+1`: given char-0 (proven), the whole open content is
`WraparoundBelowDC`. -/
theorem dcEnergyBound_of_charZero_of_wraparoundBelowDC {G : Finset F} {r : ℕ} {Einf : ℝ}
    (hc0 : CharZeroWick G r Einf) (hw : WraparoundBelowDC G r Einf) :
    DCEnergyBound G r := by
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hprod : (Fintype.card F : ℝ) * Einf ≤ (Fintype.card F : ℝ) * wick G r :=
    mul_le_mul_of_nonneg_left hc0 hq
  unfold DCEnergyBound WraparoundBelowDC CharZeroWick wick at *
  nlinarith [hw, hprod]

/-- **The double margin.** Under `WraparoundBelowDC`, the DC-subtracted energy is bounded by the
char-0 energy itself:  `A_r ≤ E_∞`  (cleared of division: `q·E_r − n^{2r} ≤ q·E_∞`).  Hence
`A_r ≤ E_∞ ≤ Wick` whenever char-0 also holds — the `A_r < E_∞ ≤ Wick` seen at every probe point. -/
theorem dcSubtracted_le_charZero_of_wraparoundBelowDC {G : Finset F} {r : ℕ} {Einf : ℝ}
    (hw : WraparoundBelowDC G r Einf) :
    (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * Einf := by
  unfold WraparoundBelowDC at hw
  nlinarith [hw]

/-- **The exact reduction (iff).** `DCEnergyBound G r` holds **iff** the wraparound stays within the
combined DC-plus-char-0-budget `n^{2r} + q·(Wick − E_∞)`.  Since the char-0 budget `Wick − E_∞` is a
`Θ(Wick/n)` (leading `C(r,2)/n`) correction, `A_r ≤ Wick` is — at every rung, exactly — the
statement that the wraparound count exceeds its DC mean by at most `O(Wick/n)`; a two-sided
concentration.  (`Einf` cancels — this is a genuine identity, independent of the value of `E_∞`.) -/
theorem dcEnergyBound_iff_wraparound_within_budget {G : Finset F} {r : ℕ} (Einf : ℝ) :
    DCEnergyBound G r ↔
      (Fintype.card F : ℝ) * ((rEnergy G r : ℝ) - Einf)
        ≤ (G.card : ℝ) ^ (2 * r) + (Fintype.card F : ℝ) * (wick G r - Einf) := by
  unfold DCEnergyBound wick
  constructor <;> intro h <;> nlinarith [h]

end ArkLib.ProximityGap.WallBetaPlusOne

#print axioms ArkLib.ProximityGap.WallBetaPlusOne.dcEnergyBound_of_charZero_of_wraparoundBelowDC
#print axioms ArkLib.ProximityGap.WallBetaPlusOne.dcSubtracted_le_charZero_of_wraparoundBelowDC
#print axioms ArkLib.ProximityGap.WallBetaPlusOne.dcEnergyBound_iff_wraparound_within_budget
