/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R29FMixedMomentCalibrated

/-!
# R30F (#466): a CS-deficit route into the Main--Res mixed socket

R27F isolated the active Main--Res obstruction as the improved mixed estimate
`MixedMainResHalfCS S A B κ`.  R29F then packaged how any strict `κ < 1` saving is
spent by the quartic rung.

This file records a first reusable route for proving that strict saving.  For
`X_s = A_s^2` and `Y_s = B_s^2`, the Cauchy--Schwarz baseline is

`M := ∑ X_s Y_s ≤ P := sqrt ((∑ X_s^2) * (∑ Y_s^2))`.

Thus a lower bound on the Cauchy--Schwarz deficit

`2(1 - κ) P^2 ≤ 2P^2 - 2PM`

immediately yields the desired `M ≤ κ P`.  Analytically, this is the normalized
square-profile separation between the Main and Residual fourth-power profiles; it is
the algebraic shape behind the measured `κ ≈ 0.33..0.49` in the probes.

No separation is proved here.  The point is to turn the next concrete profile
decorrelation theorem into the existing R29 consumers with no additional bookkeeping.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit

open ArkLib.ProximityGap.Frontier.R27FMixedMoment
open ArkLib.ProximityGap.Frontier.R28FMixedMomentGuards
open ArkLib.ProximityGap.Frontier.R29FMixedMomentCalibrated

section RealLayer

variable {ι : Type*}

/-- Fourth-power mass of a real profile. -/
noncomputable abbrev quarticMass (S : Finset ι) (A : ι → ℝ) : ℝ :=
  ∑ s ∈ S, (A s) ^ 4

/-- The mixed square mass `∑ A²B²`. -/
noncomputable abbrev mixedSquareMass (S : Finset ι) (A B : ι → ℝ) : ℝ :=
  ∑ s ∈ S, (A s) ^ 2 * (B s) ^ 2

/-- Pairwise wedge energy of the two square profiles `A²` and `B²`.

This is the Lagrange-identity face
`∑_{s,t} (A_s²B_t² - A_t²B_s²)²`, a manifestly nonnegative target for proving
strict separation of the fourth-power profiles. -/
noncomputable abbrev mixedWedgeEnergy (S : Finset ι) (A B : ι → ℝ) : ℝ :=
  ∑ s ∈ S, ∑ t ∈ S,
    ((A s) ^ 2 * (B t) ^ 2 - (A t) ^ 2 * (B s) ^ 2) ^ 2

/-- The exact Lagrange identity for the square profiles:
`∑_{s,t}(A_s²B_t² - A_t²B_s²)² = 2((∑A⁴)(∑B⁴) - (∑A²B²)²)`. -/
theorem mixedWedgeEnergy_eq_two_mul_deficit (S : Finset ι) (A B : ι → ℝ) :
    mixedWedgeEnergy S A B =
      2 * (quarticMass S A * quarticMass S B - mixedSquareMass S A B ^ 2) := by
  unfold mixedWedgeEnergy quarticMass mixedSquareMass
  have hdiag :
      (∑ s ∈ S, ∑ t ∈ S,
          ((A s) ^ 2 * (B t) ^ 2 * ((A t) ^ 2 * (B s) ^ 2))) =
        (∑ s ∈ S, (A s) ^ 2 * (B s) ^ 2) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun t ht => ?_
    ring
  have hleft :
      (∑ s ∈ S, ∑ t ∈ S, (A s) ^ 4 * (B t) ^ 4) =
        (∑ s ∈ S, (A s) ^ 4) * (∑ t ∈ S, (B t) ^ 4) := by
    rw [Finset.sum_mul_sum]
  have hright :
      (∑ s ∈ S, ∑ t ∈ S, (A t) ^ 4 * (B s) ^ 4) =
        (∑ s ∈ S, (A s) ^ 4) * (∑ t ∈ S, (B t) ^ 4) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_mul_sum]
  calc
    ∑ s ∈ S, ∑ t ∈ S,
        ((A s) ^ 2 * (B t) ^ 2 - (A t) ^ 2 * (B s) ^ 2) ^ 2
        = ∑ s ∈ S, ∑ t ∈ S,
            ((A s) ^ 4 * (B t) ^ 4 + (A t) ^ 4 * (B s) ^ 4
              - 2 * ((A s) ^ 2 * (B t) ^ 2 * ((A t) ^ 2 * (B s) ^ 2))) := by
          refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun t ht => ?_
          ring
    _ = (∑ s ∈ S, ∑ t ∈ S, (A s) ^ 4 * (B t) ^ 4)
          + (∑ s ∈ S, ∑ t ∈ S, (A t) ^ 4 * (B s) ^ 4)
          - 2 * (∑ s ∈ S, ∑ t ∈ S,
            ((A s) ^ 2 * (B t) ^ 2 * ((A t) ^ 2 * (B s) ^ 2))) := by
          simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * ((∑ s ∈ S, (A s) ^ 4) * (∑ t ∈ S, (B t) ^ 4)
          - (∑ s ∈ S, (A s) ^ 2 * (B s) ^ 2) ^ 2) := by
          rw [hleft, hright, hdiag]
          ring

/-- A normalized Cauchy--Schwarz deficit certificate strong enough to imply
`MixedMainResHalfCS S A B κ`.

The right side is `2P² - 2P M`, where
`P = sqrt ((∑A⁴) * (∑B⁴))` and `M = ∑A²B²`.  Proving this at `κ = 1 / 2`, for the
concrete Main--Res profiles, is exactly the half-CS target consumed by R29F. -/
def MixedCSDeficitAtLeast (S : Finset ι) (A B : ι → ℝ) (κ : ℝ) : Prop :=
  2 * (1 - κ) * (quarticMass S A * quarticMass S B) ≤
    2 * (quarticMass S A * quarticMass S B)
      - 2 * Real.sqrt (quarticMass S A * quarticMass S B) * mixedSquareMass S A B

/-- A squared mixed-mass certificate.  This is often the natural output of an
8-character expansion: prove the square of `∑A²B²` is at most `κ²` times the product
of the two quartic faces. -/
def MixedSquareMassSqBound (S : Finset ι) (A B : ι → ℝ) (κ : ℝ) : Prop :=
  mixedSquareMass S A B ^ 2 ≤ κ ^ 2 * (quarticMass S A * quarticMass S B)

/-- A pairwise wedge-energy certificate.  By the Lagrange identity, this is exactly
the squared mixed-mass saving written as a manifestly nonnegative decorrelation target. -/
def MixedWedgeEnergyAtLeast (S : Finset ι) (A B : ι → ℝ) (κ : ℝ) : Prop :=
  2 * (1 - κ ^ 2) * (quarticMass S A * quarticMass S B) ≤ mixedWedgeEnergy S A B

/-- The squared mixed-mass certificate is monotone in the nonnegative constant `κ`. -/
theorem mixedSquareMassSqBound_mono (S : Finset ι) (A B : ι → ℝ) {κ κ' : ℝ}
    (hκ0 : 0 ≤ κ) (hκκ' : κ ≤ κ')
    (h : MixedSquareMassSqBound S A B κ) :
    MixedSquareMassSqBound S A B κ' := by
  unfold MixedSquareMassSqBound at *
  have hprod0 : (0 : ℝ) ≤ quarticMass S A * quarticMass S B := by
    refine mul_nonneg ?_ ?_
    · unfold quarticMass
      exact Finset.sum_nonneg fun s _ => by positivity
    · unfold quarticMass
      exact Finset.sum_nonneg fun s _ => by positivity
  have hsq : κ ^ 2 ≤ κ' ^ 2 :=
    pow_le_pow_left₀ hκ0 hκκ' 2
  exact h.trans (mul_le_mul_of_nonneg_right hsq hprod0)

/-- A wedge-energy lower bound implies the squared mixed-mass certificate. -/
theorem mixedSquareMassSqBound_of_wedge (S : Finset ι) (A B : ι → ℝ) {κ : ℝ}
    (hwedge : MixedWedgeEnergyAtLeast S A B κ) :
    MixedSquareMassSqBound S A B κ := by
  unfold MixedWedgeEnergyAtLeast at hwedge
  unfold MixedSquareMassSqBound
  have hlag := mixedWedgeEnergy_eq_two_mul_deficit S A B
  nlinarith [hwedge, hlag]

/-- The squared mixed-mass certificate implies the corresponding wedge-energy lower bound.
Thus the wedge certificate is not a stronger assumption; it is the same saving in Lagrange form. -/
theorem wedge_of_mixedSquareMassSqBound (S : Finset ι) (A B : ι → ℝ) {κ : ℝ}
    (hsq : MixedSquareMassSqBound S A B κ) :
    MixedWedgeEnergyAtLeast S A B κ := by
  unfold MixedWedgeEnergyAtLeast
  unfold MixedSquareMassSqBound at hsq
  have hlag := mixedWedgeEnergy_eq_two_mul_deficit S A B
  nlinarith [hsq, hlag]

/-- The wedge-energy certificate and squared mixed-mass certificate are equivalent
presentations of the same Lagrange deficit. -/
theorem mixedWedgeEnergyAtLeast_iff_mixedSquareMassSqBound
    (S : Finset ι) (A B : ι → ℝ) {κ : ℝ} :
    MixedWedgeEnergyAtLeast S A B κ ↔ MixedSquareMassSqBound S A B κ :=
  ⟨mixedSquareMassSqBound_of_wedge S A B,
    wedge_of_mixedSquareMassSqBound S A B⟩

/-- The wedge-energy certificate is monotone in the nonnegative constant `κ`: proving
a sharper saving at `κ` lets later consumers spend it at any looser `κ' ≥ κ`. -/
theorem mixedWedgeEnergyAtLeast_mono (S : Finset ι) (A B : ι → ℝ) {κ κ' : ℝ}
    (hκ0 : 0 ≤ κ) (hκκ' : κ ≤ κ')
    (hwedge : MixedWedgeEnergyAtLeast S A B κ) :
    MixedWedgeEnergyAtLeast S A B κ' :=
  wedge_of_mixedSquareMassSqBound S A B
    (mixedSquareMassSqBound_mono S A B hκ0 hκκ'
      (mixedSquareMassSqBound_of_wedge S A B hwedge))

/-- A CS-deficit certificate implies the `κ`-improved mixed Main--Res bound. -/
theorem mixedMainResHalfCS_of_deficit (S : Finset ι) (A B : ι → ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ) (hdef : MixedCSDeficitAtLeast S A B κ) :
    MixedMainResHalfCS S A B κ := by
  unfold MixedMainResHalfCS
  let SA := quarticMass S A
  let SB := quarticMass S B
  let M := mixedSquareMass S A B
  let P := Real.sqrt (SA * SB)
  have hSA0 : (0 : ℝ) ≤ SA := by
    unfold SA quarticMass
    exact Finset.sum_nonneg fun s _ => by positivity
  have hSB0 : (0 : ℝ) ≤ SB := by
    unfold SB quarticMass
    exact Finset.sum_nonneg fun s _ => by positivity
  have hprod0 : (0 : ℝ) ≤ SA * SB := mul_nonneg hSA0 hSB0
  have hP2 : P ^ 2 = SA * SB := by
    unfold P
    exact Real.sq_sqrt hprod0
  have hMcs : M ≤ P := by
    unfold M P SA SB quarticMass mixedSquareMass
    rw [Real.sqrt_mul hSA0]
    exact mixed_sq_le_sqrt_quartics S A B
  by_cases hP0 : P = 0
  · have hM0 : M ≤ 0 := by
      simpa [hP0] using hMcs
    have htarget : M ≤ κ * P := by
      nlinarith [hM0, hP0]
    simpa [M, P, SA, SB, quarticMass, mixedSquareMass, Real.sqrt_mul hSA0] using htarget
  · have hPpos : 0 < P := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hP0)
    have hdef' : 2 * (1 - κ) * (SA * SB) ≤ 2 * (SA * SB) - 2 * P * M := by
      simpa [MixedCSDeficitAtLeast, SA, SB, M, P, quarticMass, mixedSquareMass] using hdef
    have htarget : M ≤ κ * P := by
      nlinarith [hdef', hP2, hPpos]
    simpa [M, P, SA, SB, quarticMass, mixedSquareMass, Real.sqrt_mul hSA0] using htarget

/-- The original mixed socket implies the normalized Cauchy--Schwarz deficit
certificate. -/
theorem deficit_of_mixedMainResHalfCS (S : Finset ι) (A B : ι → ℝ) {κ : ℝ}
    (h : MixedMainResHalfCS S A B κ) :
    MixedCSDeficitAtLeast S A B κ := by
  unfold MixedMainResHalfCS at h
  unfold MixedCSDeficitAtLeast
  let SA := quarticMass S A
  let SB := quarticMass S B
  let M := mixedSquareMass S A B
  let P := Real.sqrt (SA * SB)
  have hSA0 : (0 : ℝ) ≤ SA := by
    unfold SA quarticMass
    exact Finset.sum_nonneg fun s _ => by positivity
  have hSB0 : (0 : ℝ) ≤ SB := by
    unfold SB quarticMass
    exact Finset.sum_nonneg fun s _ => by positivity
  have hprod0 : (0 : ℝ) ≤ SA * SB := mul_nonneg hSA0 hSB0
  have hP0 : (0 : ℝ) ≤ P := Real.sqrt_nonneg _
  have hP2 : P ^ 2 = SA * SB := by
    unfold P
    exact Real.sq_sqrt hprod0
  have h' : M ≤ κ * P := by
    simpa [SA, SB, M, P, quarticMass, mixedSquareMass, Real.sqrt_mul hSA0] using h
  have hmul : P * M ≤ P * (κ * P) :=
    mul_le_mul_of_nonneg_left h' hP0
  have hmul_eq : P * (κ * P) = κ * (SA * SB) := by
    calc P * (κ * P) = κ * P ^ 2 := by ring
      _ = κ * (SA * SB) := by rw [hP2]
  have hPM : P * M ≤ κ * (SA * SB) :=
    hmul.trans_eq hmul_eq
  have hgoal : 2 * (1 - κ) * (SA * SB) ≤ 2 * (SA * SB) - 2 * P * M := by
    linarith [hPM]
  simpa [SA, SB, M, P, quarticMass, mixedSquareMass] using hgoal

/-- For nonnegative `κ`, the CS-deficit certificate and the original
`MixedMainResHalfCS` socket are equivalent. -/
theorem mixedCSDeficitAtLeast_iff_mixedMainResHalfCS
    (S : Finset ι) (A B : ι → ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    MixedCSDeficitAtLeast S A B κ ↔ MixedMainResHalfCS S A B κ :=
  ⟨mixedMainResHalfCS_of_deficit S A B hκ,
    deficit_of_mixedMainResHalfCS S A B⟩

/-- The baseline Cauchy--Schwarz deficit certificate at `κ = 1` is automatic. -/
theorem mixedCSDeficitAtLeast_one (S : Finset ι) (A B : ι → ℝ) :
    MixedCSDeficitAtLeast S A B 1 :=
  deficit_of_mixedMainResHalfCS S A B (mixedMainResHalfCS_one S A B)

/-- A squared mixed-mass certificate implies the `κ`-improved mixed Main--Res bound.
This gives the next analytic lane a division-free target. -/
theorem mixedMainResHalfCS_of_sq_bound (S : Finset ι) (A B : ι → ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ) (h : MixedSquareMassSqBound S A B κ) :
    MixedMainResHalfCS S A B κ := by
  unfold MixedMainResHalfCS
  have hM0 : (0 : ℝ) ≤ mixedSquareMass S A B := by
    unfold mixedSquareMass
    exact Finset.sum_nonneg fun s _ => by positivity
  have hA0 : (0 : ℝ) ≤ quarticMass S A := by
    unfold quarticMass
    exact Finset.sum_nonneg fun s _ => by positivity
  have hB0 : (0 : ℝ) ≤ quarticMass S B := by
    unfold quarticMass
    exact Finset.sum_nonneg fun s _ => by positivity
  have hP0 : (0 : ℝ) ≤ Real.sqrt (quarticMass S A * quarticMass S B) :=
    Real.sqrt_nonneg _
  have hR0 : (0 : ℝ) ≤ κ * Real.sqrt (quarticMass S A * quarticMass S B) :=
    mul_nonneg hκ hP0
  have hsq : mixedSquareMass S A B ^ 2 ≤
      (κ * Real.sqrt (quarticMass S A * quarticMass S B)) ^ 2 := by
    rw [mul_pow]
    rw [Real.sq_sqrt (mul_nonneg hA0 hB0)]
    simpa [MixedSquareMassSqBound, pow_two] using h
  have hle := sq_le_sq.mp hsq
  have hle' : mixedSquareMass S A B ≤
      κ * Real.sqrt (quarticMass S A * quarticMass S B) := by
    simpa [abs_of_nonneg hM0, abs_of_nonneg hR0] using hle
  rw [Real.sqrt_mul hA0] at hle'
  simpa [quarticMass, mixedSquareMass] using hle'

/-- The original mixed socket implies the squared mixed-mass certificate. -/
theorem sq_bound_of_mixedMainResHalfCS (S : Finset ι) (A B : ι → ℝ) {κ : ℝ}
    (h : MixedMainResHalfCS S A B κ) :
    MixedSquareMassSqBound S A B κ := by
  unfold MixedMainResHalfCS at h
  unfold MixedSquareMassSqBound
  have hM0 : (0 : ℝ) ≤ mixedSquareMass S A B := by
    unfold mixedSquareMass
    exact Finset.sum_nonneg fun s _ => by positivity
  have hA0 : (0 : ℝ) ≤ quarticMass S A := by
    unfold quarticMass
    exact Finset.sum_nonneg fun s _ => by positivity
  have hB0 : (0 : ℝ) ≤ quarticMass S B := by
    unfold quarticMass
    exact Finset.sum_nonneg fun s _ => by positivity
  have hsq := pow_le_pow_left₀ hM0 h 2
  rw [mul_pow] at hsq
  rw [mul_pow] at hsq
  rw [Real.sq_sqrt hA0, Real.sq_sqrt hB0] at hsq
  simpa [quarticMass, mixedSquareMass, pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq

/-- The un-improved Cauchy--Schwarz face is exactly the squared certificate at
`κ = 1`. -/
theorem mixedSquareMassSqBound_one (S : Finset ι) (A B : ι → ℝ) :
    MixedSquareMassSqBound S A B 1 :=
  sq_bound_of_mixedMainResHalfCS S A B (mixedMainResHalfCS_one S A B)

/-- Any `κ ≥ 1` squared certificate is automatic from ordinary Cauchy--Schwarz. -/
theorem mixedSquareMassSqBound_of_one_le (S : Finset ι) (A B : ι → ℝ) {κ : ℝ}
    (hκ : 1 ≤ κ) :
    MixedSquareMassSqBound S A B κ :=
  mixedSquareMassSqBound_mono S A B (by norm_num) hκ (mixedSquareMassSqBound_one S A B)

/-- The un-improved Cauchy--Schwarz face is exactly the wedge certificate at `κ = 1`.
The lower bound is then vacuous because the requested wedge energy is `0`. -/
theorem mixedWedgeEnergyAtLeast_one (S : Finset ι) (A B : ι → ℝ) :
    MixedWedgeEnergyAtLeast S A B 1 :=
  wedge_of_mixedSquareMassSqBound S A B (mixedSquareMassSqBound_one S A B)

/-- Any `κ ≥ 1` wedge certificate is automatic from ordinary Cauchy--Schwarz. -/
theorem mixedWedgeEnergyAtLeast_of_one_le (S : Finset ι) (A B : ι → ℝ) {κ : ℝ}
    (hκ : 1 ≤ κ) :
    MixedWedgeEnergyAtLeast S A B κ :=
  mixedWedgeEnergyAtLeast_mono S A B (by norm_num) hκ (mixedWedgeEnergyAtLeast_one S A B)

/-- A concrete wedge lower bound at the exact coefficient `2(1-κ²)` supplies the
wedge certificate.  This is mostly a readability bridge for analytic lanes, where the
target is naturally stated as a lower bound on the pairwise wedge energy itself. -/
theorem mixedWedgeEnergyAtLeast_of_lower_bound (S : Finset ι) (A B : ι → ℝ) {κ : ℝ}
    (h :
      2 * (1 - κ ^ 2) * (quarticMass S A * quarticMass S B) ≤ mixedWedgeEnergy S A B) :
    MixedWedgeEnergyAtLeast S A B κ :=
  h

/-- A raw lower bound at the coefficient `2(1-κ²)` is equivalent to the squared
mixed-mass certificate. -/
theorem wedge_lower_bound_iff_mixedSquareMassSqBound (S : Finset ι) (A B : ι → ℝ)
    {κ : ℝ} :
    2 * (1 - κ ^ 2) * (quarticMass S A * quarticMass S B) ≤ mixedWedgeEnergy S A B ↔
      MixedSquareMassSqBound S A B κ := by
  exact mixedWedgeEnergyAtLeast_iff_mixedSquareMassSqBound S A B

/-- The squared mixed-mass certificate re-expressed as its raw wedge-energy lower bound. -/
theorem wedge_lower_bound_of_mixedSquareMassSqBound (S : Finset ι) (A B : ι → ℝ)
    {κ : ℝ} (hsq : MixedSquareMassSqBound S A B κ) :
    2 * (1 - κ ^ 2) * (quarticMass S A * quarticMass S B) ≤ mixedWedgeEnergy S A B :=
  (wedge_lower_bound_iff_mixedSquareMassSqBound S A B).2 hsq

/-- The calibrated half-CS wedge target: proving
`(3/2)·(∑A⁴)(∑B⁴) ≤ wedge(A,B)` is exactly enough for `κ = 1/2`. -/
theorem mixedWedgeEnergyAtLeast_half_of_three_halves (S : Finset ι) (A B : ι → ℝ)
    (h : (3 / 2 : ℝ) * (quarticMass S A * quarticMass S B) ≤ mixedWedgeEnergy S A B) :
    MixedWedgeEnergyAtLeast S A B (1 / 2) := by
  refine mixedWedgeEnergyAtLeast_of_lower_bound S A B ?_
  norm_num
  exact h

/-- The concrete `3/2` wedge target is exactly the half squared-mass target. -/
theorem three_halves_wedge_iff_mixedSquareMassSqBound_half (S : Finset ι) (A B : ι → ℝ) :
    (3 / 2 : ℝ) * (quarticMass S A * quarticMass S B) ≤ mixedWedgeEnergy S A B ↔
      MixedSquareMassSqBound S A B (1 / 2) := by
  constructor
  · intro hwedge
    exact mixedSquareMassSqBound_of_wedge S A B
      (mixedWedgeEnergyAtLeast_half_of_three_halves S A B hwedge)
  · intro hsq
    have hwedge : MixedWedgeEnergyAtLeast S A B (1 / 2) :=
      wedge_of_mixedSquareMassSqBound S A B hsq
    unfold MixedWedgeEnergyAtLeast at hwedge
    norm_num at hwedge ⊢
    exact hwedge

/-- Half squared-mass decorrelation re-expressed as the concrete `3/2` wedge lower bound. -/
theorem three_halves_wedge_of_mixedSquareMassSqBound_half (S : Finset ι) (A B : ι → ℝ)
    (hsq : MixedSquareMassSqBound S A B (1 / 2)) :
    (3 / 2 : ℝ) * (quarticMass S A * quarticMass S B) ≤ mixedWedgeEnergy S A B :=
  (three_halves_wedge_iff_mixedSquareMassSqBound_half S A B).2 hsq

/-- For nonnegative `κ`, the squared mixed-mass certificate and the original
`MixedMainResHalfCS` socket are equivalent. -/
theorem mixedSquareMassSqBound_iff_mixedMainResHalfCS
    (S : Finset ι) (A B : ι → ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    MixedSquareMassSqBound S A B κ ↔ MixedMainResHalfCS S A B κ :=
  ⟨mixedMainResHalfCS_of_sq_bound S A B hκ,
    sq_bound_of_mixedMainResHalfCS S A B⟩

/-- For nonnegative `κ`, the CS-deficit and squared mixed-mass certificates are
equivalent presentations of the same mixed improvement. -/
theorem mixedCSDeficitAtLeast_iff_mixedSquareMassSqBound
    (S : Finset ι) (A B : ι → ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    MixedCSDeficitAtLeast S A B κ ↔ MixedSquareMassSqBound S A B κ := by
  rw [mixedCSDeficitAtLeast_iff_mixedMainResHalfCS S A B hκ,
    ← mixedSquareMassSqBound_iff_mixedMainResHalfCS S A B hκ]

/-- Direct real quartic consumer from a CS-deficit certificate plus a signed odd
nonpositive input.  This is the R29 signed-odd branch with the mixed socket discharged
by the deficit certificate. -/
theorem sum_quartic_le_of_deficit_and_signed_odd_nonpos (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb κ Budget : ℝ} (hκ : 0 ≤ κ)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hdef : MixedCSDeficitAtLeast S A B κ)
    (hOdd : ∑ s ∈ S, ((A s) ^ 3 * B s + A s * (B s) ^ 3) ≤ 0)
    (hfit : Ea + Eb + 6 * κ * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget :=
  sum_quartic_le_of_mixed_signed_odd_nonpos S A B hκ hA hB
    (mixedMainResHalfCS_of_deficit S A B hκ hdef) hOdd hfit

/-- Direct real quartic consumer from a squared mixed-mass certificate plus a signed
odd nonpositive input. -/
theorem sum_quartic_le_of_sq_bound_and_signed_odd_nonpos (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb κ Budget : ℝ} (hκ : 0 ≤ κ)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hsq : MixedSquareMassSqBound S A B κ)
    (hOdd : ∑ s ∈ S, ((A s) ^ 3 * B s + A s * (B s) ^ 3) ≤ 0)
    (hfit : Ea + Eb + 6 * κ * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget :=
  sum_quartic_le_of_mixed_signed_odd_nonpos S A B hκ hA hB
    (mixedMainResHalfCS_of_sq_bound S A B hκ hsq) hOdd hfit

/-- Direct real quartic consumer from a pairwise wedge-energy certificate plus a signed
odd nonpositive input. -/
theorem sum_quartic_le_of_wedge_and_signed_odd_nonpos (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb κ Budget : ℝ} (hκ : 0 ≤ κ)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hwedge : MixedWedgeEnergyAtLeast S A B κ)
    (hOdd : ∑ s ∈ S, ((A s) ^ 3 * B s + A s * (B s) ^ 3) ≤ 0)
    (hfit : Ea + Eb + 6 * κ * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget :=
  sum_quartic_le_of_sq_bound_and_signed_odd_nonpos S A B hκ hA hB
    (mixedSquareMassSqBound_of_wedge S A B hwedge) hOdd hfit

/-- Direct real quartic consumer from a raw wedge-energy lower bound plus a signed
odd nonpositive input. -/
theorem sum_quartic_le_of_wedge_lower_bound_and_signed_odd_nonpos
    (S : Finset ι) (A B : ι → ℝ) {Ea Eb κ Budget : ℝ} (hκ : 0 ≤ κ)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hwedge :
      2 * (1 - κ ^ 2) * (quarticMass S A * quarticMass S B) ≤ mixedWedgeEnergy S A B)
    (hOdd : ∑ s ∈ S, ((A s) ^ 3 * B s + A s * (B s) ^ 3) ≤ 0)
    (hfit : Ea + Eb + 6 * κ * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget :=
  sum_quartic_le_of_sq_bound_and_signed_odd_nonpos S A B hκ hA hB
    ((wedge_lower_bound_iff_mixedSquareMassSqBound S A B).1 hwedge) hOdd hfit

/-- Half-target real consumer from the squared mixed-mass certificate and the usual
absolute odd allowance. -/
theorem sum_quartic_le_of_sq_bound_half_target (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hsq : MixedSquareMassSqBound S A B κ) (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget :=
  sum_quartic_le_of_mixed_half_target S A B hκ hΘΘ₀ hA hB
    (mixedMainResHalfCS_of_sq_bound S A B hκ0 hsq) hO hfit

/-- Half-target real consumer from a pairwise wedge-energy certificate and the usual
absolute odd allowance. -/
theorem sum_quartic_le_of_wedge_half_target (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hwedge : MixedWedgeEnergyAtLeast S A B κ) (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget :=
  sum_quartic_le_of_sq_bound_half_target S A B hκ0 hκ hΘΘ₀ hA hB
    (mixedSquareMassSqBound_of_wedge S A B hwedge) hO hfit

/-- Half-target real consumer from the concrete `3/2` pairwise wedge lower bound. -/
theorem sum_quartic_le_of_three_halves_wedge_half_target (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ Budget : ℝ}
    (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hwedge :
      (3 / 2 : ℝ) * (quarticMass S A * quarticMass S B) ≤ mixedWedgeEnergy S A B)
    (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget :=
  sum_quartic_le_of_wedge_half_target S A B (by norm_num) (by norm_num) hΘΘ₀ hA hB
    (mixedWedgeEnergyAtLeast_half_of_three_halves S A B hwedge) hO hfit

/-- Calibrated real quartic consumer from the squared mixed-mass certificate: a
sharper squared estimate at `κ` may be spent at the looser target constant `κ₀`. -/
theorem sum_quartic_le_of_sq_bound_calibrated (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ κ κ₀ Budget : ℝ}
    (hκ0_nonneg : 0 ≤ κ) (hκ₀_nonneg : 0 ≤ κ₀) (hκκ₀ : κ ≤ κ₀) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hsq : MixedSquareMassSqBound S A B κ) (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 6 * κ₀ * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget :=
  sum_quartic_le_of_mixed_half_cs_calibrated S A B hκ₀_nonneg hκκ₀ hΘΘ₀ hA hB
    (mixedMainResHalfCS_of_sq_bound S A B hκ0_nonneg hsq) hO hfit

/-- Calibrated real quartic consumer from a pairwise wedge-energy certificate. -/
theorem sum_quartic_le_of_wedge_calibrated (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ κ κ₀ Budget : ℝ}
    (hκ0_nonneg : 0 ≤ κ) (hκ₀_nonneg : 0 ≤ κ₀) (hκκ₀ : κ ≤ κ₀) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hwedge : MixedWedgeEnergyAtLeast S A B κ) (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 6 * κ₀ * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget :=
  sum_quartic_le_of_sq_bound_calibrated S A B hκ0_nonneg hκ₀_nonneg hκκ₀ hΘΘ₀ hA hB
    (mixedSquareMassSqBound_of_wedge S A B hwedge) hO hfit

/-- Calibrated real quartic consumer from a raw wedge-energy lower bound. -/
theorem sum_quartic_le_of_wedge_lower_bound_calibrated (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ κ κ₀ Budget : ℝ}
    (hκ0_nonneg : 0 ≤ κ) (hκ₀_nonneg : 0 ≤ κ₀) (hκκ₀ : κ ≤ κ₀) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hwedge :
      2 * (1 - κ ^ 2) * (quarticMass S A * quarticMass S B) ≤ mixedWedgeEnergy S A B)
    (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 6 * κ₀ * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget :=
  sum_quartic_le_of_sq_bound_calibrated S A B hκ0_nonneg hκ₀_nonneg hκκ₀ hΘΘ₀ hA hB
    ((wedge_lower_bound_iff_mixedSquareMassSqBound S A B).1 hwedge) hO hfit

/-- Half-target real consumer from a sharper squared estimate. -/
theorem sum_quartic_le_of_sq_bound_half_target_of_le (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hsq : MixedSquareMassSqBound S A B κ) (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget :=
  sum_quartic_le_of_sq_bound_calibrated S A B hκ0 (by norm_num) hκ hΘΘ₀ hA hB hsq hO
    (by nlinarith [hfit])

/-- Half-target real consumer from a sharper wedge-energy estimate. -/
theorem sum_quartic_le_of_wedge_half_target_of_le (S : Finset ι) (A B : ι → ℝ)
    {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hwedge : MixedWedgeEnergyAtLeast S A B κ) (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget :=
  sum_quartic_le_of_wedge_calibrated S A B hκ0 (by norm_num) hκ hΘΘ₀ hA hB hwedge hO
    (by nlinarith [hfit])

/-- Half-target real consumer from a raw wedge-energy lower bound at any `κ ≤ 1/2`. -/
theorem sum_quartic_le_of_wedge_lower_bound_half_target_of_le
    (S : Finset ι) (A B : ι → ℝ) {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, (A s) ^ 4 ≤ Ea) (hB : ∑ s ∈ S, (B s) ^ 4 ≤ Eb)
    (hwedge :
      2 * (1 - κ ^ 2) * (quarticMass S A * quarticMass S B) ≤ mixedWedgeEnergy S A B)
    (hO : OddMainResBound S A B Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, (A s + B s) ^ 4 ≤ Budget :=
  sum_quartic_le_of_sq_bound_half_target S A B hκ0 hκ hΘΘ₀ hA hB
    ((wedge_lower_bound_iff_mixedSquareMassSqBound S A B).1 hwedge) hO hfit

end RealLayer

section ComplexBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Complex Main--Res consumer from a real-profile CS-deficit certificate and a
nonpositive signed odd term. -/
theorem sum_norm_quartic_le_of_deficit_and_signed_odd_nonpos
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb κ Budget : ℝ} (hκ : 0 ≤ κ)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hdef : MixedCSDeficitAtLeast S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hOdd : ∑ s ∈ S,
      (((Mp s).re) ^ 3 * (Rv s).re + (Mp s).re * ((Rv s).re) ^ 3) ≤ 0)
    (hfit : Ea + Eb + 6 * κ * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget :=
  sum_norm_quartic_le_of_mixed_signed_odd_nonpos S Mp Rv hMim hRim hκ hA hB
    (mixedMainResHalfCS_of_deficit S (fun s => (Mp s).re) (fun s => (Rv s).re) hκ hdef)
    hOdd hfit

/-- Complex Main--Res consumer from a squared real-profile mixed-mass certificate and
a nonpositive signed odd term. -/
theorem sum_norm_quartic_le_of_sq_bound_and_signed_odd_nonpos
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb κ Budget : ℝ} (hκ : 0 ≤ κ)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hsq : MixedSquareMassSqBound S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hOdd : ∑ s ∈ S,
      (((Mp s).re) ^ 3 * (Rv s).re + (Mp s).re * ((Rv s).re) ^ 3) ≤ 0)
    (hfit : Ea + Eb + 6 * κ * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget :=
  sum_norm_quartic_le_of_mixed_signed_odd_nonpos S Mp Rv hMim hRim hκ hA hB
    (mixedMainResHalfCS_of_sq_bound S (fun s => (Mp s).re) (fun s => (Rv s).re) hκ hsq)
    hOdd hfit

/-- Complex Main--Res consumer from a pairwise wedge-energy certificate and a nonpositive
signed odd term. -/
theorem sum_norm_quartic_le_of_wedge_and_signed_odd_nonpos
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb κ Budget : ℝ} (hκ : 0 ≤ κ)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hwedge : MixedWedgeEnergyAtLeast S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hOdd : ∑ s ∈ S,
      (((Mp s).re) ^ 3 * (Rv s).re + (Mp s).re * ((Rv s).re) ^ 3) ≤ 0)
    (hfit : Ea + Eb + 6 * κ * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget :=
  sum_norm_quartic_le_of_sq_bound_and_signed_odd_nonpos S Mp Rv hMim hRim hκ hA hB
    (mixedSquareMassSqBound_of_wedge S (fun s => (Mp s).re) (fun s => (Rv s).re) hwedge)
    hOdd hfit

/-- Complex Main--Res consumer from a raw real-profile wedge lower bound and a nonpositive
signed odd term. -/
theorem sum_norm_quartic_le_of_wedge_lower_bound_and_signed_odd_nonpos
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb κ Budget : ℝ} (hκ : 0 ≤ κ)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hwedge :
      2 * (1 - κ ^ 2)
          * (quarticMass S (fun s => (Mp s).re) * quarticMass S (fun s => (Rv s).re))
        ≤ mixedWedgeEnergy S (fun s => (Mp s).re) (fun s => (Rv s).re))
    (hOdd : ∑ s ∈ S,
      (((Mp s).re) ^ 3 * (Rv s).re + (Mp s).re * ((Rv s).re) ^ 3) ≤ 0)
    (hfit : Ea + Eb + 6 * κ * Real.sqrt (Ea * Eb) ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget :=
  sum_norm_quartic_le_of_sq_bound_and_signed_odd_nonpos S Mp Rv hMim hRim hκ hA hB
    ((wedge_lower_bound_iff_mixedSquareMassSqBound S
      (fun s => (Mp s).re) (fun s => (Rv s).re)).1 hwedge) hOdd hfit

/-- Half-target complex consumer from the squared real-profile mixed-mass certificate
and the usual absolute odd allowance. -/
theorem sum_norm_quartic_le_of_sq_bound_half_target
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hsq : MixedSquareMassSqBound S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget :=
  sum_norm_quartic_le_of_mixed_half_target S Mp Rv hMim hRim hκ hΘΘ₀ hA hB
    (mixedMainResHalfCS_of_sq_bound S (fun s => (Mp s).re) (fun s => (Rv s).re) hκ0 hsq)
    hO hfit

/-- Half-target complex consumer from a pairwise wedge-energy certificate and the usual
absolute odd allowance. -/
theorem sum_norm_quartic_le_of_wedge_half_target
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hwedge : MixedWedgeEnergyAtLeast S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget :=
  sum_norm_quartic_le_of_sq_bound_half_target S Mp Rv hMim hRim hκ0 hκ hΘΘ₀ hA hB
    (mixedSquareMassSqBound_of_wedge S (fun s => (Mp s).re) (fun s => (Rv s).re) hwedge)
    hO hfit

/-- Half-target complex consumer from the concrete `3/2` pairwise wedge lower bound. -/
theorem sum_norm_quartic_le_of_three_halves_wedge_half_target
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ Budget : ℝ}
    (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hwedge :
      (3 / 2 : ℝ)
          * (quarticMass S (fun s => (Mp s).re) * quarticMass S (fun s => (Rv s).re))
        ≤ mixedWedgeEnergy S (fun s => (Mp s).re) (fun s => (Rv s).re))
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget :=
  sum_norm_quartic_le_of_wedge_half_target S Mp Rv hMim hRim (by norm_num) (by norm_num)
    hΘΘ₀ hA hB
    (mixedWedgeEnergyAtLeast_half_of_three_halves S
      (fun s => (Mp s).re) (fun s => (Rv s).re) hwedge)
    hO hfit

/-- Calibrated complex Main--Res consumer from a sharper squared real-profile
mixed-mass certificate. -/
theorem sum_norm_quartic_le_of_sq_bound_calibrated
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ κ₀ Budget : ℝ}
    (hκ0_nonneg : 0 ≤ κ) (hκ₀_nonneg : 0 ≤ κ₀) (hκκ₀ : κ ≤ κ₀) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hsq : MixedSquareMassSqBound S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 6 * κ₀ * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget :=
  sum_norm_quartic_le_of_mixed_faces_calibrated S Mp Rv hMim hRim hκ₀_nonneg hκκ₀ hΘΘ₀ hA hB
    (mixedMainResHalfCS_of_sq_bound S (fun s => (Mp s).re) (fun s => (Rv s).re)
      hκ0_nonneg hsq)
    hO hfit

/-- Calibrated complex Main--Res consumer from a pairwise wedge-energy certificate. -/
theorem sum_norm_quartic_le_of_wedge_calibrated
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ κ₀ Budget : ℝ}
    (hκ0_nonneg : 0 ≤ κ) (hκ₀_nonneg : 0 ≤ κ₀) (hκκ₀ : κ ≤ κ₀) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hwedge : MixedWedgeEnergyAtLeast S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 6 * κ₀ * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget :=
  sum_norm_quartic_le_of_sq_bound_calibrated S Mp Rv hMim hRim hκ0_nonneg hκ₀_nonneg
    hκκ₀ hΘΘ₀ hA hB
    (mixedSquareMassSqBound_of_wedge S (fun s => (Mp s).re) (fun s => (Rv s).re) hwedge)
    hO hfit

/-- Calibrated complex Main--Res consumer from a raw real-profile wedge lower bound. -/
theorem sum_norm_quartic_le_of_wedge_lower_bound_calibrated
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ κ₀ Budget : ℝ}
    (hκ0_nonneg : 0 ≤ κ) (hκ₀_nonneg : 0 ≤ κ₀) (hκκ₀ : κ ≤ κ₀) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hwedge :
      2 * (1 - κ ^ 2)
          * (quarticMass S (fun s => (Mp s).re) * quarticMass S (fun s => (Rv s).re))
        ≤ mixedWedgeEnergy S (fun s => (Mp s).re) (fun s => (Rv s).re))
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 6 * κ₀ * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget :=
  sum_norm_quartic_le_of_sq_bound_calibrated S Mp Rv hMim hRim hκ0_nonneg hκ₀_nonneg
    hκκ₀ hΘΘ₀ hA hB
    ((wedge_lower_bound_iff_mixedSquareMassSqBound S
      (fun s => (Mp s).re) (fun s => (Rv s).re)).1 hwedge) hO hfit

/-- Half-target complex consumer from a sharper squared real-profile estimate. -/
theorem sum_norm_quartic_le_of_sq_bound_half_target_of_le
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hsq : MixedSquareMassSqBound S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget :=
  sum_norm_quartic_le_of_sq_bound_calibrated S Mp Rv hMim hRim hκ0 (by norm_num) hκ hΘΘ₀
    hA hB hsq hO (by nlinarith [hfit])

/-- Half-target complex consumer from a sharper wedge-energy estimate. -/
theorem sum_norm_quartic_le_of_wedge_half_target_of_le
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hwedge : MixedWedgeEnergyAtLeast S (fun s => (Mp s).re) (fun s => (Rv s).re) κ)
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget :=
  sum_norm_quartic_le_of_wedge_calibrated S Mp Rv hMim hRim hκ0 (by norm_num) hκ hΘΘ₀
    hA hB hwedge hO (by nlinarith [hfit])

/-- Half-target complex consumer from a raw real-profile wedge lower bound at any
`κ ≤ 1/2`. -/
theorem sum_norm_quartic_le_of_wedge_lower_bound_half_target_of_le
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ Θ₀ κ Budget : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ (1 / 2 : ℝ)) (hΘΘ₀ : Θ ≤ Θ₀)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hwedge :
      2 * (1 - κ ^ 2)
          * (quarticMass S (fun s => (Mp s).re) * quarticMass S (fun s => (Rv s).re))
        ≤ mixedWedgeEnergy S (fun s => (Mp s).re) (fun s => (Rv s).re))
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ)
    (hfit : Ea + Eb + 3 * Real.sqrt (Ea * Eb) + 4 * Θ₀ ≤ Budget) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ Budget :=
  sum_norm_quartic_le_of_sq_bound_half_target S Mp Rv hMim hRim hκ0 hκ hΘΘ₀ hA hB
    ((wedge_lower_bound_iff_mixedSquareMassSqBound S
      (fun s => (Mp s).re) (fun s => (Rv s).re)).1 hwedge) hO hfit

end ComplexBridge

end ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedWedgeEnergy_eq_two_mul_deficit
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedMainResHalfCS_of_deficit
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.deficit_of_mixedMainResHalfCS
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedCSDeficitAtLeast_iff_mixedMainResHalfCS
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedSquareMassSqBound_mono
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedSquareMassSqBound_of_wedge
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.wedge_of_mixedSquareMassSqBound
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedWedgeEnergyAtLeast_iff_mixedSquareMassSqBound
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedWedgeEnergyAtLeast_mono
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedSquareMassSqBound_one
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedSquareMassSqBound_of_one_le
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedWedgeEnergyAtLeast_one
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedWedgeEnergyAtLeast_of_one_le
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedWedgeEnergyAtLeast_of_lower_bound
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.wedge_lower_bound_iff_mixedSquareMassSqBound
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.wedge_lower_bound_of_mixedSquareMassSqBound
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedWedgeEnergyAtLeast_half_of_three_halves
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.three_halves_wedge_iff_mixedSquareMassSqBound_half
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.three_halves_wedge_of_mixedSquareMassSqBound_half
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedMainResHalfCS_of_sq_bound
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sq_bound_of_mixedMainResHalfCS
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedSquareMassSqBound_iff_mixedMainResHalfCS
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedCSDeficitAtLeast_iff_mixedSquareMassSqBound
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.mixedCSDeficitAtLeast_one
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_quartic_le_of_deficit_and_signed_odd_nonpos
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_quartic_le_of_sq_bound_and_signed_odd_nonpos
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_quartic_le_of_wedge_and_signed_odd_nonpos
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_quartic_le_of_wedge_lower_bound_and_signed_odd_nonpos
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_quartic_le_of_sq_bound_half_target
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_quartic_le_of_wedge_half_target
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_quartic_le_of_three_halves_wedge_half_target
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_quartic_le_of_sq_bound_calibrated
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_quartic_le_of_wedge_calibrated
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_quartic_le_of_wedge_lower_bound_calibrated
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_quartic_le_of_sq_bound_half_target_of_le
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_quartic_le_of_wedge_half_target_of_le
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_quartic_le_of_wedge_lower_bound_half_target_of_le
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_norm_quartic_le_of_deficit_and_signed_odd_nonpos
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_norm_quartic_le_of_sq_bound_and_signed_odd_nonpos
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_norm_quartic_le_of_wedge_and_signed_odd_nonpos
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_norm_quartic_le_of_wedge_lower_bound_and_signed_odd_nonpos
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_norm_quartic_le_of_sq_bound_half_target
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_norm_quartic_le_of_wedge_half_target
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_norm_quartic_le_of_three_halves_wedge_half_target
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_norm_quartic_le_of_sq_bound_calibrated
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_norm_quartic_le_of_wedge_calibrated
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_norm_quartic_le_of_wedge_lower_bound_calibrated
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_norm_quartic_le_of_sq_bound_half_target_of_le
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_norm_quartic_le_of_wedge_half_target_of_le
#print axioms ArkLib.ProximityGap.Frontier.R30FMixedMomentDeficit.sum_norm_quartic_le_of_wedge_lower_bound_half_target_of_le
