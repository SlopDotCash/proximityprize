/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Data.CodingTheory.ProximityGap.GeneralizedPaleyRamanujan

/-!
# Prize-regime bridge from DC-subtracted moments to the Paley target

The prize-depth moment route cannot use the raw Gaussian energy bound: the DC frequency makes that
statement false near `r ~= log q`.  The surviving spectral route is the DC-subtracted hypothesis
`DCEnergyCorrection.DCEnergyBound`.

This file records the direct consumer that was missing from the prize-regime lane:

* a DC-subtracted `2r`-moment bound gives the usual nonzero-frequency `r`-th-root sup bound;
* if that explicit moment scale fits `C * |G| * log(|F| / |G|)`, then the named
  `GeneralizedPaleyNearRamanujan` target follows;
* hence the existing additive-energy consumer can use the DC-subtracted route without passing
  through the false raw-energy hypothesis.

No theorem here proves the DC-subtracted moment estimate or the real optimization `r ~= log q`.
Those are exactly the remaining prize-regime analytic inputs.
-/

open ArkLib.ProximityGap.DCEnergyCorrection
open ArkLib.ProximityGap.GeneralizedPaleyRamanujan
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

namespace ArkLib.ProximityGap.Frontier.PrizeRegimeDCEnergyBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The explicit squared sup-norm scale produced by a DC-subtracted moment estimate at order `r`.

It is

`( |F| * (2r - 1)!! * |G|^r )^(1/r)`,

the same moment scale as the raw-energy route, but now obtained only for nonzero frequencies from
the DC-subtracted hypothesis. -/
noncomputable def dcMomentScale (G : Finset F) (r : ℕ) : ℝ :=
  ((Fintype.card F : ℝ) *
      ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) ^ ((r : ℝ)⁻¹)

/-- **DC-subtracted moment to worst-case incomplete-sum bound.**

For `r >= 1`, `DCEnergyBound G r` gives the nonzero-frequency bound
`|eta_b|^2 <= dcMomentScale G r`.  This is the prize-depth replacement for the raw
`GaussianEnergyBound` consumer in `GaussPeriodMomentBound`. -/
theorem worstCaseIncompleteSumBound_of_dcEnergyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} (hr : 1 ≤ r)
    (h : DCEnergyBound G r) :
    WorstCaseIncompleteSumBound ψ G (dcMomentScale G r) := by
  intro b hb
  unfold dcMomentScale
  set X : ℝ :=
    (Fintype.card F : ℝ) *
      ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) with hX
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r ≤ X := by
    rw [← pow_mul]
    exact eta_pow_le_of_dcEnergyBound hψ h hb
  calc ‖eta ψ G b‖ ^ 2
      = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (sq_nonneg _) (Nat.one_le_iff_ne_zero.mp hr)).symm
    _ ≤ X ^ ((r : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)

/-- **DC-subtracted moment to near-Ramanujan/Paley target.**

If the explicit DC-moment scale at order `r` is no larger than
`C * |G| * log(|F| / |G|)`, then the named prize-regime generalized-Paley target follows.

This separates the formal bridge from the open real optimization: a future proof only has to supply
`DCEnergyBound G r` and the displayed scale inequality for a prize-depth order `r`. -/
theorem nearRamanujan_of_dcEnergyBound_and_scale {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} {C : ℝ}
    (hr : 1 ≤ r)
    (henergy : DCEnergyBound G r)
    (hscale : dcMomentScale G r ≤
      C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))) :
    GeneralizedPaleyNearRamanujan C ψ G := by
  intro b hb
  exact le_trans (worstCaseIncompleteSumBound_of_dcEnergyBound hψ hr henergy b hb) hscale

/-- **DC-subtracted moment to the existing additive-energy consumer.**

This is the same downstream API as `GeneralizedPaleyRamanujan.addEnergy_le_of_nearRamanujan`, but
the input is the prize-correct DC-subtracted moment hypothesis plus an explicit scale fit. -/
theorem addEnergy_le_of_dcEnergyBound_and_scale {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} {C : ℝ}
    (hr : 1 ≤ r)
    (hcard : (G.card : ℝ) ≤ Fintype.card F)
    (hC : 0 ≤ C)
    (henergy : DCEnergyBound G r)
    (hscale : dcMomentScale G r ≤
      C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ))) :
    (Fintype.card F : ℝ) * (addEnergy G : ℝ)
      ≤ (G.card : ℝ) ^ 4
        + (C * (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / (G.card : ℝ)))
          * ((Fintype.card F : ℝ) * G.card) :=
  addEnergy_le_of_nearRamanujan hψ hcard hC
    (nearRamanujan_of_dcEnergyBound_and_scale hψ hr henergy hscale)

/-! ## Axiom audit -/
#print axioms worstCaseIncompleteSumBound_of_dcEnergyBound
#print axioms nearRamanujan_of_dcEnergyBound_and_scale
#print axioms addEnergy_le_of_dcEnergyBound_and_scale

end ArkLib.ProximityGap.Frontier.PrizeRegimeDCEnergyBridge
