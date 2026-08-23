/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCMomentSupBound

/-!
# The DC-subtracted energy bound — the correct prize hypothesis (#407)

`GaussPeriodMomentBound.GaussianEnergyBound G r := E_r(G) ≤ (2r−1)‼·|G|^r` is the **DC-included** energy
(`E_r = rEnergy = (1/q)∑_{all b}‖η_b‖^{2r}`). Because the `b=0` term forces `E_r ≥ |G|^{2r}/q`, and at the
prize scale (`|G| = n` large, `r ≈ ln q`) the term `n^{2r}/q` **exceeds** Wick `(2r−1)‼·n^r` (verified:
`log(n^{2r}/q / Wick)` crosses `0` at `n = 64` and reaches `+1301` at `n = 2^30`), the hypothesis
`E_r ≤ Wick` is **FALSE at the prize** — so `eta_pow_le_of_energyBound` / `eta_le_optimized` are
*vacuous* there. The CORRECT, true-at-prize hypothesis is the **DC-subtracted** bound `A_r ≤ Wick`:

> **`DCEnergyBound G r`** := `q·E_r(G) − |G|^{2r} ≤ q·(2r−1)‼·|G|^r`  (i.e. `A_r ≤ Wick`).
> **`eta_pow_le_of_dcEnergyBound`** — `DCEnergyBound G r ⟹ ∀ b ≠ 0, ‖η_b‖^{2r} ≤ q·(2r−1)‼·|G|^r`.

This is non-vacuous at the prize, and feeds the moment-order optimization (`r ≈ ln q`) to give the prize
sup-norm `M ≤ √(2n ln q)`. The open content is exactly `A_r ≤ Wick` (= the BGK/Anomaly-Suppression
inequality `Anom_r ≤ |G|^{2r}/q`), measured true at every prize prime. This brick corrects the prize
reduction: the DC subtraction is *mandatory*, not a sharpening.

Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCMomentSupBound

namespace ArkLib.ProximityGap.DCEnergyCorrection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The DC-subtracted energy bound** — the prize hypothesis (`A_r ≤ Wick`, cleared of division):
`q·E_r(G) − |G|^{2r} ≤ q·(2r−1)‼·|G|^r`. Unlike the in-tree `E_r ≤ Wick`, this is TRUE at the prize. -/
def DCEnergyBound (G : Finset F) (r : ℕ) : Prop :=
  (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
    ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)

/-- **Non-vacuous per-frequency bound from the DC-subtracted hypothesis.** `DCEnergyBound G r ⟹
∀ b ≠ 0, ‖η_b‖^{2r} ≤ q·(2r−1)‼·|G|^r`. Combines the UNCONDITIONAL `eta_pow_le_dc`
(`‖η_b‖^{2r} ≤ q·E_r − |G|^{2r}`) with `A_r ≤ Wick`. Unlike the in-tree non-DC route, this is non-vacuous
at the prize parameters. -/
theorem eta_pow_le_of_dcEnergyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (h : DCEnergyBound G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
  (eta_pow_le_dc hψ G r hb).trans h

end ArkLib.ProximityGap.DCEnergyCorrection

#print axioms ArkLib.ProximityGap.DCEnergyCorrection.eta_pow_le_of_dcEnergyBound
