/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS11GenericDepthDecomposition
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS13PairingInductionWick
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FS5TrivialCountClosedForm

/-!
# Depth-seven wraparound-balance residual

The DC correction shows that excluding all finite-characteristic accidents is both unnecessary
and, at larger depths, impossible.  FS11 splits the standard depth-seven energy exactly as

`E₇ = trivialCountG + wraparoundExcessG`,

while FS13 bounds the characteristic-zero term by `13!! n^7 = 135135 n^7`.  The repaired BGK
consumer allows coefficient `2^18 = 262144`, leaving exactly

`262144 - 135135 = 127009`

units of `n^7` slack above the Wick term.  This file isolates the finite-characteristic obligation:

`q * wraparoundExcessG ≤ n^14 + q * 127009 * n^7`.

The leading `n^14` is the mandatory DC collision supply; the second term is the allowed excess.
The theorem below proves that this balance residual implies the standard form of the corrected
coefficient-`2^18` depth-seven inequality.  `_BGKRenergyRepresentationBridge` then transports it
to the BGK lane-local energy.  This is a residual reduction, not a proof of wraparound balance.
Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1024

open Finset Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.Frontier.BGKDepthSevenWraparoundBalance

open ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
open ArkLib.ProximityGap.Frontier.FS5TrivialCountClosedForm
open ArkLib.ProximityGap.Frontier.FS11GenericDepthDecomposition
open ArkLib.ProximityGap.Frontier.FS13PairingInductionWick

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The exact finite-characteristic balance required after paying the DC collision main term and
the characteristic-zero Wick census. -/
def DepthSevenWraparoundBalance (zeta : F) (m : ℕ) : Prop :=
  (Fintype.card F : ℝ) * (wraparoundExcessG zeta m 7 : ℝ)
    ≤ ((2 * m : ℕ) : ℝ) ^ 14 +
      (Fintype.card F : ℝ) * (127009 * ((2 * m : ℕ) : ℝ) ^ 7)

/-- FS11 + FS13 turn the wraparound-balance residual into the repaired standard depth-seven
DC-excess bound with coefficient `2^18`. -/
theorem standard_depthSeven_relaxed_of_wraparoundBalance
    {zeta : F} {m : ℕ} (hm : 0 < m) (hprim : IsPrimitiveRoot zeta (2 * m))
    (hbal : DepthSevenWraparoundBalance zeta m) :
    let G := (Finset.range (2 * m)).image (zeta ^ ·)
    (Fintype.card F : ℝ) * (rEnergy G 7 : ℝ) - (G.card : ℝ) ^ 14
      ≤ (Fintype.card F : ℝ) * ((2 : ℝ) ^ 18 * (G.card : ℝ) ^ 7) := by
  dsimp only
  let G : Finset F := (Finset.range (2 * m)).image (zeta ^ ·)
  have hdec := rEnergy_eq_trivial_add_excess (F := F) hm hprim 7
  have htriv := trivialCountG_le_wick m 7 hm
  have hcard : G.card = 2 * m := by
    exact Gset_card hm hprim
  have hdecR : (rEnergy G 7 : ℝ) =
      (trivialCountG m 7 : ℝ) + (wraparoundExcessG zeta m 7 : ℝ) := by
    exact_mod_cast hdec
  have htrivR : (trivialCountG m 7 : ℝ) ≤
      135135 * (((2 * m : ℕ) : ℝ) ^ 7) := by
    norm_num [Nat.doubleFactorial] at htriv
    exact_mod_cast htriv
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have htrivScaled :
      (Fintype.card F : ℝ) * (trivialCountG m 7 : ℝ) ≤
        (Fintype.card F : ℝ) * (135135 * (((2 * m : ℕ) : ℝ) ^ 7)) :=
    mul_le_mul_of_nonneg_left htrivR hq
  have hwrapCentered :
      (Fintype.card F : ℝ) * (wraparoundExcessG zeta m 7 : ℝ) -
          (((2 * m : ℕ) : ℝ) ^ 14)
        ≤ (Fintype.card F : ℝ) * (127009 * (((2 * m : ℕ) : ℝ) ^ 7)) := by
    unfold DepthSevenWraparoundBalance at hbal
    linarith
  rw [hdecR, hcard]
  calc
    (Fintype.card F : ℝ) *
          ((trivialCountG m 7 : ℝ) + (wraparoundExcessG zeta m 7 : ℝ)) -
        (((2 * m : ℕ) : ℝ) ^ 14)
        = (Fintype.card F : ℝ) * (trivialCountG m 7 : ℝ) +
          ((Fintype.card F : ℝ) * (wraparoundExcessG zeta m 7 : ℝ) -
            (((2 * m : ℕ) : ℝ) ^ 14)) := by ring
    _ ≤ (Fintype.card F : ℝ) * (135135 * (((2 * m : ℕ) : ℝ) ^ 7)) +
          (Fintype.card F : ℝ) * (127009 * (((2 * m : ℕ) : ℝ) ^ 7)) :=
      add_le_add htrivScaled hwrapCentered
    _ = (Fintype.card F : ℝ) *
          ((2 : ℝ) ^ 18 * (((2 * m : ℕ) : ℝ) ^ 7)) := by ring

end ArkLib.ProximityGap.Frontier.BGKDepthSevenWraparoundBalance

#print axioms
  ArkLib.ProximityGap.Frontier.BGKDepthSevenWraparoundBalance.standard_depthSeven_relaxed_of_wraparoundBalance
