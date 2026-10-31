/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier._R151OcticChiFamilyExactRung

/-!
# LANE B2 (#466 round 153): residual target for the octic thinned-family route

R151 exposes the octic exact-rung route for a proper subfamily `Y ⊆ chiFamily χ`, but it asks
directly for `ChiDecompositionOff` on that thinned family.  R19 identifies that hypothesis with
vanishing of the omitted-character residual.

This file packages the R151 consumer in the residual language.  It does not prove the residual
vanishes; it makes the live target explicit and prevents the remaining task from being hidden
inside a decomposition hypothesis.  The octic Stepanov hypotheses are bundled as an
`OcticFamilyCertificate Y Cmax` over the retained subfamily `Y` only.

The endpoints stop at the depth-`2` Wick certificate (and its raw-fourth-moment form).  Direct
incidence / approximate-`B` corollaries would need the R15 depth link `2 = ⌈log q⌉`, which is
incompatible with the octic hypothesis `8 ∣ q - 1`
(`R151OcticChiFamilyExactRung.two_ne_ceil_log_card_of_eight_dvd`), so they are deliberately not
stated (audit CW-B09-01).
-/

namespace ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget

open Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.ConstantIndexGaussSum
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R19ChiDecomposition
open ArkLib.ProximityGap.Frontier.R19ExplicitCharacterRung
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly
open ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter
open ArkLib.ProximityGap.Frontier.R148OcticDStepanovAdapter
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable local instance localInstance_R153OcticThinnedResidualTarget_1 : DecidableEq (MulChar F ℂ) := Classical.decEq _

/-- The R151 thinned-octic exact-rung consumer with the live decomposition hypothesis phrased
as vanishing of the omitted-character residual. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * (Y.card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) Dset 2 :=
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_constant_le_one
    ψ hψ χ G Dset hY cert hmord hn hCw0 hC
    ((chiSubfamily_chiDecompositionOff_iff_residual_vanishes χ hψ hGD hY).2 hres) hq1 hnq hn4q hreg

/-- Raw-fourth-moment companion to `wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * (Y.card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) Dset :=
  (wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal G (Gchi χ) Dset).mp
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
      ψ hψ χ G Dset hY cert hmord hn hGD hCw0 hC hres hq1 hnq hn4q hreg)

/-- Size-gated residual form of the thinned-octic route.  The remaining live
decomposition target is exactly residual vanishing; the normalized constant gate is discharged
from `Cmax ≤ 2`, nonempty `Y`, and `15 * |Y|² ≤ orderOf χ`. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) Dset 2 :=
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_Cmax_le_two
    ψ hψ χ G Dset hY cert hmord hn hCw0 hCmax2 hYnonempty horder
    ((chiSubfamily_chiDecompositionOff_iff_residual_vanishes χ hψ hGD hY).2 hres) hq1 hnq hn4q hreg

/-- Raw-fourth-moment companion to `wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (hres : ChiSubfamilyResidualVanishesOff χ ψ G Dset Y)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) Dset :=
  (wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal G (Gchi χ) Dset).mp
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
      ψ hψ χ G Dset hY cert hmord hn hGD hCw0 hCmax2 hYnonempty horder hres hq1 hnq hn4q hreg)

/-- Character-by-character sufficient condition for the R153 residual target: if every omitted
twisted thin sum vanishes off `Dset`, then the omitted-character residual vanishes off `Dset`.

This is deliberately stronger than cancellation of the omitted sum, but it isolates an exact
per-character target for attempts that choose `Y` by deleting characters with forced shifted
vanishing. -/
theorem chiSubfamilyResidualVanishesOff_of_omitted_twistedThinSum_zero
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G Dset : Finset F)
    (Y : Finset (MulChar F ℂ))
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y → twistedThinSum χ' G s₀ = 0) :
    ChiSubfamilyResidualVanishesOff χ ψ G Dset Y := by
  classical
  intro s₀ hs₀
  unfold chiSubfamilyResidual
  exact Finset.sum_eq_zero fun χ' hχ' => by
    have hmem : χ' ∈ chiFamily χ ∧ χ' ∉ Y := by
      simpa [Finset.mem_sdiff] using hχ'
    rw [homit s₀ hs₀ χ' hmem.1 hmem.2, mul_zero]

/-- Shifted-character-sum version of the omitted-zero sufficient condition.  This is the same
target as `chiSubfamilyResidualVanishesOff_of_omitted_twistedThinSum_zero`, but phrased in the
`shiftedCharSum` API used by the Tχ moment files. -/
theorem chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G Dset : Finset F)
    (Y : Finset (MulChar F ℂ))
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0) :
    ChiSubfamilyResidualVanishesOff χ ψ G Dset Y := by
  refine chiSubfamilyResidualVanishesOff_of_omitted_twistedThinSum_zero χ ψ G Dset Y ?_
  intro s₀ hs₀ χ' hχ' hχ'Y
  simp [twistedThinSum_eq_star_shiftedCharSum, homit s₀ hs₀ χ' hχ' hχ'Y]

/-- Boundary case for the thinned residual: if the retained subfamily covers all of
`chiFamily χ`, then there are no omitted characters and the residual vanishes identically. -/
theorem chiSubfamilyResidualVanishesOff_of_chiFamily_subset
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G Dset : Finset F)
    (Y : Finset (MulChar F ℂ)) (hcover : chiFamily χ ⊆ Y) :
    ChiSubfamilyResidualVanishesOff χ ψ G Dset Y := by
  classical
  intro s₀ _hs₀
  unfold chiSubfamilyResidual
  exact Finset.sum_eq_zero fun χ' hχ' => by
    have hmem : χ' ∈ chiFamily χ ∧ χ' ∉ Y := by
      simpa [Finset.mem_sdiff] using hχ'
    exact False.elim (hmem.2 (hcover hmem.1))

/-- Self-boundary case for the thinned residual: omitting nothing from `chiFamily χ` makes the
residual vanish.  This is not a usable prize route: for the full family both the normalized
constant gate and the `15 * |Y|^2 ≤ m` size gate fail for every order `m ≥ 2`
(`not_full_chiFamily_octic_constant_gate`, `not_full_chiFamily_octic_size_gate`). -/
theorem chiSubfamilyResidualVanishesOff_self
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G Dset : Finset F) :
    ChiSubfamilyResidualVanishesOff χ ψ G Dset (chiFamily χ) :=
  chiSubfamilyResidualVanishesOff_of_chiFamily_subset χ ψ G Dset (chiFamily χ) fun _ hχ => hχ

/-- Size-gated thinned-octic endpoint with the residual target discharged by pointwise
vanishing of every omitted twisted thin sum. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y → twistedThinSum χ' G s₀ = 0)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) Dset 2 :=
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    ψ hψ χ G Dset hY cert hmord hn hGD hCw0 hCmax2 hYnonempty horder
    (chiSubfamilyResidualVanishesOff_of_omitted_twistedThinSum_zero χ ψ G Dset Y homit) hq1 hnq hn4q hreg

/-- Raw-fourth-moment companion to `wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y → twistedThinSum χ' G s₀ = 0)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) Dset :=
  (wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal G (Gchi χ) Dset).mp
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
      ψ hψ χ G Dset hY cert hmord hn hGD hCw0 hCmax2 hYnonempty horder homit hq1 hnq hn4q hreg)

/-- Size-gated thinned-octic endpoint with the residual target discharged by pointwise
vanishing of every omitted shifted character sum. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) Dset 2 :=
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
    ψ hψ χ G Dset hY cert hmord hn hGD hCw0 hCmax2 hYnonempty horder
    (chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero χ ψ G Dset Y homit) hq1 hnq hn4q hreg

/-- Raw-fourth-moment companion to `wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) Dset :=
  (wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal G (Gchi χ) Dset).mp
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
      ψ hψ χ G Dset hY cert hmord hn hGD hCw0 hCmax2 hYnonempty horder homit hq1 hnq hn4q hreg)

/-- Explicit-constant thinned-octic endpoint with the residual target discharged by pointwise
vanishing of every omitted shifted character sum. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * (Y.card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) Dset 2 :=
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
    ψ hψ χ G Dset hY cert hmord hn hGD hCw0 hC
    (chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero χ ψ G Dset Y homit) hq1 hnq hn4q hreg

/-- Raw-fourth-moment companion to `wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_shifted_zero
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card) (hGD : G ⊆ Dset)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * (Y.card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (homit :
      ∀ s₀ : F, s₀ ∉ Dset →
        ∀ χ' ∈ chiFamily χ, χ' ∉ Y →
          ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum χ' G s₀ = 0)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) Dset :=
  (wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal G (Gchi χ) Dset).mp
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero
      ψ hψ χ G Dset hY cert hmord hn hGD hCw0 hC homit hq1 hnq hn4q hreg)

end ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_residual_vanishes
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_residual_vanishes_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  chiSubfamilyResidualVanishesOff_of_omitted_twistedThinSum_zero
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  chiSubfamilyResidualVanishesOff_of_omitted_shiftedCharSum_zero
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  chiSubfamilyResidualVanishesOff_of_chiFamily_subset
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  chiSubfamilyResidualVanishesOff_self
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_omitted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_shifted_zero_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_shifted_zero
open ArkLib.ProximityGap.Frontier.R153OcticThinnedResidualTarget in
#print axioms
  rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_shifted_zero
