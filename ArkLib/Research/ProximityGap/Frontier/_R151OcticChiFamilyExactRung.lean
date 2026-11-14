/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._R19ExplicitCharacterRung
import ArkLib.Research.ProximityGap.Frontier._R149OcticFullRungPipeline

/-!
# LANE B2 (#466 round 151): octic pipeline feeds the explicit `chiFamily` exact rung

R149 packages the order-8 superelliptic/Stepanov route as a producer of
`FourthMomentTwistBound`.  R19 packages the explicit-character decomposition for
`chiFamily χ` and its thinned subfamilies, with only the normalized size gate and
fourth-moment input left to callers.

This file composes those two public APIs.

* `OcticFamilyCertificate X Cmax` bundles the per-character octic superelliptic/Stepanov
  hypotheses of R149 over a character family `X`; `OcticFamilyCertificate.fourthMomentTwistBound`
  turns it into the R17 fourth-moment input.  Thinned consumers ask for a certificate over the
  retained subfamily `Y` only (not over all of `chiFamily χ`).
* The thinned-family consumers produce the depth-`2` Wick certificate
  `WickForIncidenceAwayAt ψ G (Gchi χ) Dset 2` and its raw-fourth-moment form.

## Honesty notes (audit CW-B09-01 / CW-B09-02)

* **No depth-2 incidence endpoints.**  The R15 incidence/approximate-`B` consumers require the
  Wick depth to equal `⌈log q⌉`.  Every octic certificate carries `8 ∣ q - 1`, which forces
  `q ≥ 9` and hence `⌈log q⌉ ≥ 3` (`two_ne_ceil_log_card_of_eight_dvd`).  Composing the depth-2
  Wick certificate with those consumers would therefore only produce vacuous theorems, and they
  have been removed.  A non-vacuous incidence endpoint needs a Wick certificate at depth
  `⌈log q⌉`, which this lane does not provide.
* **No full-`chiFamily` consumers.**  For the full family the normalized constant gate
  `32 * ((4 + Cmax) * |chiFamily χ|^4 + 1) / m^2 / 3 ≤ 1` fails for *every* order `m ≥ 2` once
  `Cmax ≥ 0` (which any certificate over the nonempty full family forces):
  `not_full_chiFamily_octic_constant_gate`, `OcticFamilyCertificate.not_full_chiFamily_gate`.
  The full-family size gate `15 * |chiFamily χ|^2 ≤ m` fails likewise
  (`not_full_chiFamily_octic_size_gate`).  Only genuinely thinned subfamilies can be used.

No prize closure is claimed.
-/

namespace ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung

open Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.ConstantIndexGaussSum
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R16IncidenceR2Rung
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R18SigmaEquidistribution
open ArkLib.ProximityGap.Frontier.R19ChiDecomposition
open ArkLib.ProximityGap.Frontier.R19ExplicitCharacterRung
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly
open ArkLib.ProximityGap.Frontier.R59DStepanovSuperellipticAdapter
open ArkLib.ProximityGap.Frontier.R148OcticDStepanovAdapter
open ArkLib.ProximityGap.Frontier.R149OcticFullRungPipeline
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Bundled per-character hypotheses of the R149 octic superelliptic/Stepanov pipeline over a
character family `X`, with uniform Stepanov constant bound `Cmax`. -/
structure OcticFamilyCertificate (X : Finset (MulChar F ℂ)) (Cmax : ℝ) where
  /-- Value sets of the triple products. -/
  T : MulChar F ℂ → Finset ℂ
  /-- Stepanov step counts. -/
  msteps : MulChar F ℂ → ℕ
  /-- Class-fibre exponents. -/
  e : MulChar F ℂ → ℕ
  /-- Stepanov multiplicities. -/
  J : MulChar F ℂ → ℕ
  /-- Auxiliary-polynomial degrees. -/
  D : MulChar F ℂ → ℕ
  /-- Total degree budgets. -/
  Dtot : MulChar F ℂ → ℕ
  /-- Per-character Stepanov constants. -/
  Cd : MulChar F ℂ → ℝ
  /-- Model polynomials. -/
  gOf : MulChar F ℂ → F → F → F → ℂ → F[X]
  /-- Model scalars. -/
  ζOf : MulChar F ℂ → F → F → F → ℂ → F
  h8 : 8 ∣ (Fintype.card F - 1)
  hm : ∀ χ' ∈ X, 0 < msteps χ'
  hJ : ∀ χ' ∈ X, 0 < J χ'
  hT1 : ∀ χ' ∈ X, ∀ c ∈ T χ', ‖c‖ = 1
  hT0 : ∀ χ' ∈ X, (∑ c ∈ T χ', c) = 0
  hvals : ∀ χ' ∈ X, ∀ u v w s : F,
    tripleVal χ' u v w s = 0 ∨ tripleVal χ' u v w s ∈ T χ'
  hmodel : ∀ χ' ∈ X, ClassFiberPowerModel χ' (T χ') (e χ') (gOf χ') (ζOf χ')
  hpoly : ∀ χ' ∈ X, OcticModelPolynomialHypotheses (F := F) (T χ') (gOf χ')
  he : ∀ χ' ∈ X, e χ' = (Fintype.card F - 1) / 8
  hmq : ∀ χ' ∈ X, msteps χ' < Fintype.card F
  hD : ∀ χ' ∈ X, ∀ u v w : F, ∀ c ∈ T χ',
    8 * D χ' + 7 * (gOf χ' u v w c).natDegree < Fintype.card F
  hcount : ∀ χ' ∈ X, ∀ u v w : F, ∀ c ∈ T χ',
    msteps χ' * (D χ' + ((gOf χ' u v w c).natDegree - 1) * msteps χ' + J χ')
      < 8 * (J χ' * (D χ' + 1))
  hDtot : ∀ χ' ∈ X, ∀ u v w : F, ∀ c ∈ T χ',
    (gOf χ' u v w c).natDegree * (msteps χ' + (8 - 1) * e χ') + D χ'
        + Fintype.card F * (J χ' - 1) ≤ Dtot χ'
  harith : ∀ χ' ∈ X,
    ((T χ').card : ℝ) * ((Dtot χ' : ℝ) / (msteps χ' : ℝ)) - (Fintype.card F : ℝ) + 3
      ≤ Cd χ' * Real.sqrt (Fintype.card F)
  hCd0 : ∀ χ' ∈ X, 0 ≤ Cd χ'
  hCdmax : ∀ χ' ∈ X, Cd χ' ≤ Cmax

namespace OcticFamilyCertificate

variable {X Y : Finset (MulChar F ℂ)} {Cmax : ℝ}

/-- An octic certificate over `X` restricts to any subfamily `Y ⊆ X`. -/
def mono (c : OcticFamilyCertificate X Cmax) (hYX : Y ⊆ X) : OcticFamilyCertificate Y Cmax where
  T := c.T
  msteps := c.msteps
  e := c.e
  J := c.J
  D := c.D
  Dtot := c.Dtot
  Cd := c.Cd
  gOf := c.gOf
  ζOf := c.ζOf
  h8 := c.h8
  hm := fun χ' h => c.hm χ' (hYX h)
  hJ := fun χ' h => c.hJ χ' (hYX h)
  hT1 := fun χ' h => c.hT1 χ' (hYX h)
  hT0 := fun χ' h => c.hT0 χ' (hYX h)
  hvals := fun χ' h => c.hvals χ' (hYX h)
  hmodel := fun χ' h => c.hmodel χ' (hYX h)
  hpoly := fun χ' h => c.hpoly χ' (hYX h)
  he := fun χ' h => c.he χ' (hYX h)
  hmq := fun χ' h => c.hmq χ' (hYX h)
  hD := fun χ' h => c.hD χ' (hYX h)
  hcount := fun χ' h => c.hcount χ' (hYX h)
  hDtot := fun χ' h => c.hDtot χ' (hYX h)
  harith := fun χ' h => c.harith χ' (hYX h)
  hCd0 := fun χ' h => c.hCd0 χ' (hYX h)
  hCdmax := fun χ' h => c.hCdmax χ' (hYX h)

/-- The octic superelliptic pipeline (R149) turns a certificate over `X` into the R17
fourth-moment input for `X`. -/
theorem fourthMomentTwistBound (c : OcticFamilyCertificate X Cmax) (G : Finset F)
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    FourthMomentTwistBound G X (4 + Cmax) :=
  fourthMomentTwistBound_of_octic_superelliptic_pipeline G X c.T c.msteps c.e c.J c.D
    c.Dtot c.Cd c.gOf c.ζOf c.h8 c.hm c.hJ c.hT1 c.hT0 c.hvals c.hmodel c.hpoly c.he
    c.hmq c.hD c.hcount c.hDtot c.harith c.hCd0 c.hCdmax hn4q

/-- A certificate over a nonempty family forces `0 ≤ Cmax`. -/
theorem cmax_nonneg (c : OcticFamilyCertificate X Cmax) (hX : X.Nonempty) : 0 ≤ Cmax := by
  obtain ⟨χ', hχ'⟩ := hX
  exact (c.hCd0 χ' hχ').trans (c.hCdmax χ' hχ')

end OcticFamilyCertificate

/-! ### Thinned-family exact-rung consumers -/

/-- Thinned-family exact-rung consumer with the fourth-moment input supplied by the octic
superelliptic pipeline on the retained subfamily `Y`.  The remaining nontrivial thinning input is
the exact `ChiDecompositionOff` identity for `Y`. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_constant_le_one
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * (Y.card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hdec : ChiDecompositionOff ψ G (Gchi χ) Dset Y (fun χ' => gaussSum χ' ψ) (orderOf χ))
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) Dset 2 :=
  wickForIncidenceAwayAt_two_of_gchi_of_constant_le_one ψ hψ G Dset Y
    (fun χ' => gaussSum χ' ψ) χ hmord hn hCw0 hC hdec
    (gaussSumSizeBound_chiSubfamily χ hψ hY) (cert.fourthMomentTwistBound G hn4q) hq1 hnq hreg

/-- Raw-fourth-moment companion to
`wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_constant_le_one`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_constant_le_one
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hCw0 : 0 ≤ 4 + Cmax)
    (hC :
      32 * ((4 + Cmax) * (Y.card : ℝ) ^ 4 + 1)
          / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1)
    (hdec : ChiDecompositionOff ψ G (Gchi χ) Dset Y (fun χ' => gaussSum χ' ψ) (orderOf χ))
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) Dset :=
  (wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal G (Gchi χ) Dset).mp
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_constant_le_one
      ψ hψ χ G Dset hY cert hmord hn hCw0 hC hdec hq1 hnq hn4q hreg)

/-- Size-gated thinned-family exact-rung consumer for the octic route.  Instead of asking callers
to prove the normalized `hC` gate directly, this version uses the standard R18 arithmetic adapter:
if the octic constant satisfies `4 + Cmax ≤ 6` and `15 * |Y|² ≤ orderOf χ`, the gate fires. -/
theorem wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (hdec : ChiDecompositionOff ψ G (Gchi χ) Dset Y (fun χ' => gaussSum χ' ψ) (orderOf χ))
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) Dset 2 := by
  have hCw6 : 4 + Cmax ≤ 6 := by linarith
  exact wickForIncidenceAwayAt_two_of_gchi_of_Cw_le_six_nonempty_fifteen_card_sq_le_order_nat
    ψ hψ G Dset Y (fun χ' => gaussSum χ' ψ) χ hmord hn hCw0 hCw6 hYnonempty horder
    hdec (gaussSumSizeBound_chiSubfamily χ hψ hY) (cert.fourthMomentTwistBound G hn4q)
    hq1 hnq hreg

/-- Raw-fourth-moment companion to
`wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_Cmax_le_two`. -/
theorem rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_Cmax_le_two
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ)
    (G Dset : Finset F) {Y : Finset (MulChar F ℂ)} (hY : Y ⊆ chiFamily χ) {Cmax : ℝ}
    (cert : OcticFamilyCertificate Y Cmax)
    (hmord : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hCw0 : 0 ≤ 4 + Cmax) (hCmax2 : Cmax ≤ 2)
    (hYnonempty : Y.Nonempty)
    (horder : 15 * Y.card ^ 2 ≤ orderOf χ)
    (hdec : ChiDecompositionOff ψ G (Gchi χ) Dset Y (fun χ' => gaussSum χ' ψ) (orderOf χ))
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    RawFourthMomentWithDiagonal ψ G (Gchi χ) Dset :=
  (wickForIncidenceAwayAt_two_iff_rawFourthMomentWithDiagonal G (Gchi χ) Dset).mp
    (wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_Cmax_le_two
      ψ hψ χ G Dset hY cert hmord hn hCw0 hCmax2 hYnonempty horder hdec hq1 hnq hn4q hreg)

/-! ### No-go facts recording why the removed endpoints were vacuous -/

/-- Every octic certificate carries `8 ∣ q - 1`, which forces `q ≥ 9`, so
`⌈log q⌉ ≥ 3`.  Hence the depth-`2` Wick certificate produced here can never be fed to the R15
incidence/approximate-`B` consumers, which require the depth to be `⌈log q⌉`. -/
theorem two_ne_ceil_log_card_of_eight_dvd (h8 : 8 ∣ (Fintype.card F - 1)) :
    2 ≠ ⌈Real.log (Fintype.card F : ℝ)⌉₊ := by
  have hq2 : 1 < Fintype.card F := Fintype.one_lt_card
  have hq9 : 9 ≤ Fintype.card F := by
    obtain ⟨k, hk⟩ := h8
    omega
  have hq9R : (9 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hq9
  have hexp : Real.exp 2 < 9 := by
    have he1 := Real.exp_one_lt_d9
    have he0 := Real.exp_pos 1
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hlog : (2 : ℝ) < Real.log (Fintype.card F : ℝ) :=
    (Real.lt_log_iff_exp_lt (by linarith)).2 (by linarith)
  have hceil : 2 < ⌈Real.log (Fintype.card F : ℝ)⌉₊ :=
    Nat.lt_ceil.2 (by exact_mod_cast hlog)
  omega

/-- The normalized constant gate cannot be closed by the full explicit `chiFamily χ`: for every
order `m ≥ 2` and every `Cmax ≥ 0`,
`32 * ((4 + Cmax) * (m - 1)^4 + 1) / m^2 / 3 > 1`. -/
theorem not_full_chiFamily_octic_constant_gate (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ)
    {Cmax : ℝ} (hCmax : 0 ≤ Cmax) :
    ¬ 32 * ((4 + Cmax) * ((chiFamily χ).card : ℝ) ^ 4 + 1)
        / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1 := by
  intro h
  rw [chiFamily_card, Nat.cast_sub (by omega : 1 ≤ orderOf χ), Nat.cast_one] at h
  have hmR : (2 : ℝ) ≤ (orderOf χ : ℝ) := by exact_mod_cast hm
  set m : ℝ := (orderOf χ : ℝ) with hmdef
  have hpos : 0 < m ^ 2 * 3 := by positivity
  rw [div_div, div_le_one hpos] at h
  have ha : (1 : ℝ) ≤ m - 1 := by linarith
  have ha2 : (1 : ℝ) ≤ (m - 1) ^ 2 := by nlinarith
  have ha4 : (m - 1) ^ 2 ≤ (m - 1) ^ 4 := by nlinarith
  have hsq : m ^ 2 ≤ 4 * (m - 1) ^ 2 := by nlinarith
  have hA : 4 * (m - 1) ^ 4 ≤ (4 + Cmax) * (m - 1) ^ 4 := by nlinarith
  nlinarith

/-- Certificate form of `not_full_chiFamily_octic_constant_gate`: an octic certificate over the
full (nonempty) `chiFamily χ` forces `Cmax ≥ 0`, so its normalized constant gate always fails. -/
theorem OcticFamilyCertificate.not_full_chiFamily_gate (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ)
    {Cmax : ℝ} (cert : OcticFamilyCertificate (chiFamily χ) Cmax) :
    ¬ 32 * ((4 + Cmax) * ((chiFamily χ).card : ℝ) ^ 4 + 1)
        / ((orderOf χ : ℝ)) ^ 2 / 3 ≤ 1 := by
  have hne : (chiFamily χ).Nonempty := by
    rw [← Finset.card_pos, chiFamily_card]
    omega
  exact not_full_chiFamily_octic_constant_gate χ hm (cert.cmax_nonneg hne)

/-- The size gate used by the `Cmax ≤ 2` octic thinned-family consumer cannot be closed by
taking the full explicit `chiFamily χ`.  The octic route therefore genuinely needs a thinned
subfamily, a different decomposition, or a stronger constant gate. -/
theorem not_full_chiFamily_octic_size_gate (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) :
    ¬ 15 * (chiFamily χ).card ^ 2 ≤ orderOf χ :=
  not_fifteen_chiFamily_card_sq_le_order χ hm

/-- Real-valued companion to `not_full_chiFamily_octic_size_gate`, matching the normalized
constant-gate arithmetic used by downstream analytic consumers. -/
theorem not_full_chiFamily_octic_size_gate_real (χ : MulChar F ℂ) (hm : 2 ≤ orderOf χ) :
    ¬ 15 * (((chiFamily χ).card : ℝ) ^ 2) ≤ (orderOf χ : ℝ) :=
  not_fifteen_chiFamily_card_sq_le_order_real χ hm

end ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms OcticFamilyCertificate.fourthMomentTwistBound
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_constant_le_one
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_constant_le_one
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms wickForIncidenceAwayAt_two_of_chiSubfamily_octic_superelliptic_of_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms rawFourthMomentWithDiagonal_of_chiSubfamily_octic_superelliptic_of_Cmax_le_two
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms two_ne_ceil_log_card_of_eight_dvd
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms not_full_chiFamily_octic_constant_gate
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms OcticFamilyCertificate.not_full_chiFamily_gate
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms not_full_chiFamily_octic_size_gate
open ArkLib.ProximityGap.Frontier.R151OcticChiFamilyExactRung in
#print axioms not_full_chiFamily_octic_size_gate_real
