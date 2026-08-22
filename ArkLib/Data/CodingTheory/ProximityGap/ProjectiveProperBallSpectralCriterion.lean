/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveProperQuotientBall
import ArkLib.Data.CodingTheory.ProximityGap.ProjectiveRankTwoAPI

/-!
# The signed spectral criterion for the proper projective ball

`ProjectiveProperQuotientBall.properAffineBallIncidence_spectral` gives an exact Fourier
expansion but leaves the principal character mixed into the hard frequencies.  This file removes
that character and retains the *signed real part* of the remaining annihilator sum.  The result is
an unconditional exact formula for the full projective MCA census, including the infinity slot.

The distinction between the real part and the norm is essential.  Production only requires an
upper bound on the signed sum.  Replacing it by its norm invokes a triangle or Cauchy--Schwarz
bound and loses precisely the inter-frequency cancellation which is open in the prize regime.

The final theorem reduces `ProjectiveWorstCaseIncidenceBounded` to this signed inequality on
genuine rank-two quotient pencils.  Thus the remaining arithmetic target is a uniform one-sided
bound for a completely explicit, pencil-dependent nonprincipal Fourier sum.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal
open ProximityGap Code

namespace ProximityGap.ProjectiveProperBallSpectralCriterion

open MCAProjectiveEquivariance
open ProjectiveProperQuotientBall
open ProjectiveQuotientSupport
open ProjectiveWorstCaseIncidence

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

attribute [local instance] Classical.propDecidable

/-- Fourier coefficient of the pencil-dependent proper quotient ball.  This is not the ambient
Hamming-shell transform: quotient cosets are deduplicated and support witnesses containing `P`
are removed. -/
noncomputable def properBallFourierCoeff
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (P : Submodule F ((ι → A) ⧸ C))
    (ψ : AddChar ((ι → A) ⧸ C) ℂ) : ℂ := by
  classical
  exact ∑ q ∈ properQuotientBall C δ P, ψ (-q)

/-- Scalar dilation of a quotient additive character, by precomposition with `q ↦ a • q`. -/
def scaleAddChar (C : Submodule F (ι → A)) (a : F)
    (ψ : AddChar ((ι → A) ⧸ C) ℂ) :
    AddChar ((ι → A) ⧸ C) ℂ :=
  ψ.compAddMonoidHom ((smulAddHom F ((ι → A) ⧸ C)) a)

@[simp] theorem scaleAddChar_apply (C : Submodule F (ι → A))
    (a : F) (ψ : AddChar ((ι → A) ⧸ C) ℂ)
    (q : (ι → A) ⧸ C) :
    scaleAddChar (C := C) a ψ q = ψ (a • q) :=
  rfl

@[simp] theorem scaleAddChar_zero (C : Submodule F (ι → A)) (a : F) :
    scaleAddChar C a (0 : AddChar ((ι → A) ⧸ C) ℂ) = 0 := by
  ext q
  simp

@[simp] theorem scaleAddChar_one (C : Submodule F (ι → A))
    (ψ : AddChar ((ι → A) ⧸ C) ℂ) :
    scaleAddChar C 1 ψ = ψ := by
  ext q
  simp

theorem scaleAddChar_scaleAddChar (C : Submodule F (ι → A)) (a b : F)
    (ψ : AddChar ((ι → A) ⧸ C) ℂ) :
    scaleAddChar C a (scaleAddChar C b ψ) = scaleAddChar C (a * b) ψ := by
  ext q
  simp [smul_smul, mul_comm]

theorem scaleAddChar_inv_scaleAddChar (C : Submodule F (ι → A))
    (a : F) (ha : a ≠ 0) (ψ : AddChar ((ι → A) ⧸ C) ℂ) :
    scaleAddChar C a⁻¹ (scaleAddChar C a ψ) = ψ := by
  rw [scaleAddChar_scaleAddChar]
  simp [ha]

theorem scaleAddChar_eq_zero_iff (C : Submodule F (ι → A))
    (a : F) (ha : a ≠ 0) (ψ : AddChar ((ι → A) ⧸ C) ℂ) :
    scaleAddChar C a ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    calc
      ψ = scaleAddChar C a⁻¹ (scaleAddChar C a ψ) :=
        (scaleAddChar_inv_scaleAddChar C a ha ψ).symm
      _ = scaleAddChar C a⁻¹ 0 := congrArg (scaleAddChar C a⁻¹) h
      _ = 0 := scaleAddChar_zero C a⁻¹
  · rintro rfl
    exact scaleAddChar_zero C a

/-- Nonzero scalar dilation preserves whether a character annihilates a fixed quotient point. -/
theorem directionChar_scaleAddChar_eq_zero_iff
    (C : Submodule F (ι → A)) (a : F) (ha : a ≠ 0)
    (ψ : AddChar ((ι → A) ⧸ C) ℂ) (q : (ι → A) ⧸ C) :
    ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F)
        (scaleAddChar C a ψ) q = 0 ↔
      ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ q = 0 := by
  have preserve : ∀ (b : F) (χ : AddChar ((ι → A) ⧸ C) ℂ),
      ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) χ q = 0 →
        ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F)
          (scaleAddChar C b χ) q = 0 := by
    intro b χ hχ
    ext γ
    have hγ := congrArg (fun θ : AddChar F ℂ => θ (b * γ)) hχ
    simpa [ArkLib.ProximityGap.LineIncidenceSpectral.directionChar_apply,
      smul_smul, mul_comm] using hγ
  constructor
  · intro hscaled
    have hback := preserve a⁻¹ (scaleAddChar C a ψ) hscaled
    simpa [scaleAddChar_inv_scaleAddChar C a ha ψ] using hback
  · exact preserve a ψ

/-- The proper quotient ball is a cone: multiplication by a nonzero field scalar preserves
membership in both directions. -/
theorem smul_mem_properQuotientBall_iff
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (P : Submodule F ((ι → A) ⧸ C))
    (a : F) (ha : a ≠ 0) (q : (ι → A) ⧸ C) :
    a • q ∈ properQuotientBall C δ P ↔ q ∈ properQuotientBall C δ P := by
  rw [mem_properQuotientBall_iff, mem_properQuotientBall_iff]
  constructor
  · rintro ⟨S, hS, hmem, hproper⟩
    refine ⟨S, hS, ?_, hproper⟩
    have hinv := (quotientSupportSubmodule C S).smul_mem a⁻¹ hmem
    simpa [smul_smul, ha] using hinv
  · rintro ⟨S, hS, hmem, hproper⟩
    exact ⟨S, hS, (quotientSupportSubmodule C S).smul_mem a hmem, hproper⟩

/-- Proper-ball Fourier coefficients are constant on every nonzero scalar orbit in the dual
quotient.  This projectivizes the frequency variable before any analytic estimate is used. -/
theorem properBallFourierCoeff_scaleAddChar
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (P : Submodule F ((ι → A) ⧸ C))
    (a : F) (ha : a ≠ 0) (ψ : AddChar ((ι → A) ⧸ C) ℂ) :
    properBallFourierCoeff C δ P (scaleAddChar (C := C) a ψ) =
      properBallFourierCoeff C δ P ψ := by
  classical
  unfold properBallFourierCoeff
  refine Finset.sum_bij' (fun q _ => a • q) (fun q _ => a⁻¹ • q) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    exact (smul_mem_properQuotientBall_iff C δ P a ha q).2 hq
  · intro q hq
    exact (smul_mem_properQuotientBall_iff C δ P a⁻¹ (inv_ne_zero ha) q).2 hq
  · intro q _hq
    simp [smul_smul, ha]
  · intro q _hq
    simp [smul_smul, ha]
  · intro q _hq
    change ψ (a • (-q)) = ψ (-(a • q))
    rw [smul_neg]

/-- Summing the phase of one character over a full nonzero scalar orbit is exactly `q - 1` when
the character annihilates the point and `-1` otherwise.  Combined with
`properBallFourierCoeff_scaleAddChar`, this is the algebraic orbit collapse available before the
remaining projective-frequency sum. -/
theorem sum_scaleAddChar_apply_nonzero
    (C : Submodule F (ι → A)) (ψ : AddChar ((ι → A) ⧸ C) ℂ)
    (q : (ι → A) ⧸ C) :
    (∑ a ∈ (Finset.univ.erase (0 : F)), scaleAddChar (C := C) a ψ q) =
      if ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ q = 0 then
        (Fintype.card F : ℂ) - 1
      else -1 := by
  classical
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : F))]
  simp only [scaleAddChar_apply, zero_smul, AddChar.map_zero_eq_one]
  change (∑ a : F,
      ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ q a) - 1 = _
  rw [AddChar.sum_eq_ite]
  split <;> simp_all

/-- The nonzero characters annihilating the affine pencil direction. -/
noncomputable def properDeviationSupport
    (C : Submodule F (ι → A)) (u₁ : ι → A) :
    Finset (AddChar ((ι → A) ⧸ C) ℂ) := by
  classical
  exact (Finset.univ.erase 0).filter fun ψ =>
    ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ
      (Submodule.Quotient.mk (p := C) u₁) = 0

/-- Nonprincipal characters annihilating the entire quotient pencil. -/
noncomputable def properPencilAnnihilatorSupport
    (C : Submodule F (ι → A)) (u₀ u₁ : ι → A) :
    Finset (AddChar ((ι → A) ⧸ C) ℂ) := by
  classical
  exact (properDeviationSupport C u₁).filter fun ψ =>
    ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ
      (Submodule.Quotient.mk (p := C) u₀) = 0

/-- Direction-annihilating characters which do not annihilate the offset row. -/
noncomputable def properTransverseDeviationSupport
    (C : Submodule F (ι → A)) (u₀ u₁ : ι → A) :
    Finset (AddChar ((ι → A) ⧸ C) ℂ) := by
  classical
  exact (properDeviationSupport C u₁).filter fun ψ =>
    ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ
      (Submodule.Quotient.mk (p := C) u₀) ≠ 0

/-- A nonzero scalar dilation permutes the deviation-support hyperplane. -/
theorem scaleAddChar_mem_properDeviationSupport_iff
    (C : Submodule F (ι → A)) (u₁ : ι → A) (a : F) (ha : a ≠ 0)
    (ψ : AddChar ((ι → A) ⧸ C) ℂ) :
    scaleAddChar C a ψ ∈ properDeviationSupport C u₁ ↔
      ψ ∈ properDeviationSupport C u₁ := by
  classical
  simp only [properDeviationSupport, Finset.mem_filter, Finset.mem_erase,
    Finset.mem_univ, and_true]
  constructor
  · rintro ⟨hscaled, hdir⟩
    refine ⟨?_, (directionChar_scaleAddChar_eq_zero_iff C a ha ψ _).1 hdir⟩
    intro hzero
    subst ψ
    exact hscaled (scaleAddChar_zero C a)
  · rintro ⟨hψ, hdir⟩
    refine ⟨?_, (directionChar_scaleAddChar_eq_zero_iff C a ha ψ _).2 hdir⟩
    intro hscaled
    exact hψ ((scaleAddChar_eq_zero_iff C a ha ψ).1 hscaled)

/-- The nonprincipal part of the Fourier sum surviving on the annihilator of the affine pencil
direction.  Unlike a norm envelope, this keeps the phases and therefore the cancellation needed
at the production budget. -/
noncomputable def properDirectionalDeviation
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℂ := by
  classical
  exact ∑ ψ ∈ (Finset.univ.erase (0 : AddChar ((ι → A) ⧸ C) ℂ)),
    if ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ
        (Submodule.Quotient.mk (p := C) u₁) = 0 then
      ∑ q ∈ properQuotientBall C δ (quotientPencil C u₀ u₁),
        ψ (Submodule.Quotient.mk (p := C) u₀ - q)
    else 0

/-- The deviation is a phase-weighted correlation of proper-ball Fourier coefficients over the
nonprincipal annihilator hyperplane.  This is the precise analog of the BCHKS/Paley hyperplane
sum, but its coefficient family is pencil-dependent rather than a bare subgroup Gauss period. -/
theorem properDirectionalDeviation_eq_phase_weighted
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    properDirectionalDeviation C δ u₀ u₁ =
      ∑ ψ ∈ (Finset.univ.erase (0 : AddChar ((ι → A) ⧸ C) ℂ)),
        if ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ
            (Submodule.Quotient.mk (p := C) u₁) = 0 then
          ψ (Submodule.Quotient.mk (p := C) u₀) *
            properBallFourierCoeff C δ (quotientPencil C u₀ u₁) ψ
        else 0 := by
  classical
  unfold properDirectionalDeviation
  apply Finset.sum_congr rfl
  intro ψ _hψ
  by_cases hd : ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ
      (Submodule.Quotient.mk (p := C) u₁) = 0
  · simp only [hd, if_true]
    unfold properBallFourierCoeff
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [← AddChar.map_add_eq_mul]
    congr 1
    abel
  · simp [hd]

/-- Filtered-support form of the phase-weighted deviation. -/
theorem properDirectionalDeviation_eq_support_sum
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    properDirectionalDeviation C δ u₀ u₁ =
      ∑ ψ ∈ properDeviationSupport C u₁,
        ψ (Submodule.Quotient.mk (p := C) u₀) *
          properBallFourierCoeff C δ (quotientPencil C u₀ u₁) ψ := by
  rw [properDirectionalDeviation_eq_phase_weighted]
  simp only [properDeviationSupport, Finset.sum_filter]

/-- **Exact `F*`-orbit projectivization.**  Averaging the deviation over scalar dilations of the
dual characters and using cone-invariance of the proper ball gives

`(q - 1) D = Σ_{ψ ∈ u₁^⊥ \ {0}} Bhat_P(ψ) · ((q - 1) if ψ ⊥ u₀ else -1)`.

Thus the affine offset phases are eliminated exactly.  The remaining open arithmetic content is a
signed sum of proper-ball Fourier coefficients over projective dual frequencies, split according
to whether they annihilate the whole quotient pencil or only its direction. -/
theorem properDirectionalDeviation_orbit_projectivization
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    ((Fintype.card F : ℂ) - 1) * properDirectionalDeviation C δ u₀ u₁ =
      ∑ ψ ∈ properDeviationSupport C u₁,
        properBallFourierCoeff C δ (quotientPencil C u₀ u₁) ψ *
          (if ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ
              (Submodule.Quotient.mk (p := C) u₀) = 0 then
            (Fintype.card F : ℂ) - 1
          else -1) := by
  classical
  let H := properDeviationSupport C u₁
  let K := Finset.univ.erase (0 : F)
  let P := quotientPencil C u₀ u₁
  let q₀ : (ι → A) ⧸ C := Submodule.Quotient.mk (p := C) u₀
  have hinner : ∀ a ∈ K,
      (∑ ψ ∈ H, properBallFourierCoeff C δ P ψ * scaleAddChar C a ψ q₀) =
        ∑ ψ ∈ H, ψ q₀ * properBallFourierCoeff C δ P ψ := by
    intro a haK
    have ha : a ≠ 0 := (Finset.mem_erase.mp haK).1
    refine Finset.sum_bij' (fun ψ _ => scaleAddChar C a ψ)
      (fun ψ _ => scaleAddChar C a⁻¹ ψ) ?_ ?_ ?_ ?_ ?_
    · intro ψ hψ
      exact (scaleAddChar_mem_properDeviationSupport_iff C u₁ a ha ψ).2 hψ
    · intro ψ hψ
      exact (scaleAddChar_mem_properDeviationSupport_iff C u₁ a⁻¹
        (inv_ne_zero ha) ψ).2 hψ
    · intro ψ _hψ
      exact scaleAddChar_inv_scaleAddChar C a ha ψ
    · intro ψ _hψ
      simpa using scaleAddChar_inv_scaleAddChar C a⁻¹ (inv_ne_zero ha) ψ
    · intro ψ _hψ
      rw [properBallFourierCoeff_scaleAddChar C δ P a ha ψ]
      ring
  have hsupport : properDirectionalDeviation C δ u₀ u₁ =
      ∑ ψ ∈ H, ψ q₀ * properBallFourierCoeff C δ P ψ := by
    simpa [H, P, q₀] using properDirectionalDeviation_eq_support_sum C δ u₀ u₁
  have horbit : ∀ ψ : AddChar ((ι → A) ⧸ C) ℂ,
      (∑ a ∈ K, scaleAddChar C a ψ q₀) =
        if ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ q₀ = 0 then
          (Fintype.card F : ℂ) - 1
        else -1 := by
    intro ψ
    simpa [K, q₀] using sum_scaleAddChar_apply_nonzero C ψ q₀
  symm
  calc
    (∑ ψ ∈ H, properBallFourierCoeff C δ P ψ *
        (if ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ q₀ = 0 then
          (Fintype.card F : ℂ) - 1 else -1))
        = ∑ ψ ∈ H, properBallFourierCoeff C δ P ψ *
            ∑ a ∈ K, scaleAddChar C a ψ q₀ := by
              apply Finset.sum_congr rfl
              intro ψ _hψ
              rw [horbit ψ]
    _ = ∑ ψ ∈ H, ∑ a ∈ K,
          properBallFourierCoeff C δ P ψ * scaleAddChar C a ψ q₀ := by
            apply Finset.sum_congr rfl
            intro ψ _hψ
            rw [Finset.mul_sum]
    _ = ∑ a ∈ K, ∑ ψ ∈ H,
          properBallFourierCoeff C δ P ψ * scaleAddChar C a ψ q₀ := by
            rw [Finset.sum_comm]
    _ = ∑ _a ∈ K, ∑ ψ ∈ H,
          ψ q₀ * properBallFourierCoeff C δ P ψ := by
            apply Finset.sum_congr rfl
            intro a ha
            exact hinner a ha
    _ = ∑ _a ∈ K, properDirectionalDeviation C δ u₀ u₁ := by
            apply Finset.sum_congr rfl
            intro _a _ha
            exact hsupport.symm
    _ = (K.card : ℂ) * properDirectionalDeviation C δ u₀ u₁ := by
            rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((Fintype.card F : ℂ) - 1) * properDirectionalDeviation C δ u₀ u₁ := by
            have hcard : 1 ≤ Fintype.card F := by
              have hpos : 0 < Fintype.card F := Fintype.card_pos
              omega
            congr 1
            simp [K, Finset.card_erase_of_mem, hcard]

/-- Split form of the orbit projectivization.  Frequencies annihilating the whole pencil carry
weight `q - 1`; the genuinely transverse projective frequencies carry weight `-1`. -/
theorem properDirectionalDeviation_orbit_projectivization_split
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    ((Fintype.card F : ℂ) - 1) * properDirectionalDeviation C δ u₀ u₁ =
      ((Fintype.card F : ℂ) - 1) *
          ∑ ψ ∈ properPencilAnnihilatorSupport C u₀ u₁,
            properBallFourierCoeff C δ (quotientPencil C u₀ u₁) ψ -
        ∑ ψ ∈ properTransverseDeviationSupport C u₀ u₁,
          properBallFourierCoeff C δ (quotientPencil C u₀ u₁) ψ := by
  classical
  rw [properDirectionalDeviation_orbit_projectivization]
  let H := properDeviationSupport C u₁
  let pred : AddChar ((ι → A) ⧸ C) ℂ → Prop := fun ψ =>
    ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F) ψ
      (Submodule.Quotient.mk (p := C) u₀) = 0
  let coeff : AddChar ((ι → A) ⧸ C) ℂ → ℂ := fun ψ =>
    properBallFourierCoeff C δ (quotientPencil C u₀ u₁) ψ
  let Q : ℂ := (Fintype.card F : ℂ) - 1
  have hsplit := Finset.sum_filter_add_sum_filter_not H pred
    (fun ψ => coeff ψ * (if pred ψ then Q else -1))
  have hyes :
      (∑ ψ ∈ H.filter pred, coeff ψ * (if pred ψ then Q else -1)) =
        ∑ ψ ∈ H.filter pred, coeff ψ * Q := by
    apply Finset.sum_congr rfl
    intro ψ hψ
    simp [(Finset.mem_filter.mp hψ).2]
  have hno :
      (∑ ψ ∈ H.filter (fun ψ => ¬ pred ψ),
          coeff ψ * (if pred ψ then Q else -1)) =
        ∑ ψ ∈ H.filter (fun ψ => ¬ pred ψ), coeff ψ * (-1) := by
    apply Finset.sum_congr rfl
    intro ψ hψ
    simp [(Finset.mem_filter.mp hψ).2]
  have hpos : (∑ ψ ∈ H.filter pred, coeff ψ * Q) =
      Q * ∑ ψ ∈ H.filter pred, coeff ψ := by
    rw [← Finset.sum_mul]
    ring
  have hneg : (∑ ψ ∈ H.filter (fun ψ => ¬ pred ψ), coeff ψ * (-1)) =
      -(∑ ψ ∈ H.filter (fun ψ => ¬ pred ψ), coeff ψ) := by
    rw [← Finset.sum_mul]
    ring
  calc
    (∑ ψ ∈ H, coeff ψ * (if pred ψ then Q else -1))
        = (∑ ψ ∈ H.filter pred, coeff ψ * (if pred ψ then Q else -1)) +
            ∑ ψ ∈ H.filter (fun ψ => ¬ pred ψ),
              coeff ψ * (if pred ψ then Q else -1) := hsplit.symm
    _ = (∑ ψ ∈ H.filter pred, coeff ψ * Q) +
          ∑ ψ ∈ H.filter (fun ψ => ¬ pred ψ), coeff ψ * (-1) := by
            rw [hyes, hno]
    _ = Q * (∑ ψ ∈ H.filter pred, coeff ψ) -
          ∑ ψ ∈ H.filter (fun ψ => ¬ pred ψ), coeff ψ := by
            rw [hpos, hneg]
            ring
    _ = ((Fintype.card F : ℂ) - 1) *
          ∑ ψ ∈ properPencilAnnihilatorSupport C u₀ u₁,
            properBallFourierCoeff C δ (quotientPencil C u₀ u₁) ψ -
        ∑ ψ ∈ properTransverseDeviationSupport C u₀ u₁,
          properBallFourierCoeff C δ (quotientPencil C u₀ u₁) ψ := by
            rfl

/-- The projectivized signed sum left after the exact `F*` orbit collapse. -/
noncomputable def properOrbitSignedSum
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℂ :=
  ((Fintype.card F : ℂ) - 1) *
      ∑ ψ ∈ properPencilAnnihilatorSupport C u₀ u₁,
        properBallFourierCoeff C δ (quotientPencil C u₀ u₁) ψ -
    ∑ ψ ∈ properTransverseDeviationSupport C u₀ u₁,
      properBallFourierCoeff C δ (quotientPencil C u₀ u₁) ψ

/-- The projectivized sum is exactly `(q - 1)` times the original deviation. -/
theorem properOrbitSignedSum_eq_card_sub_one_mul_deviation
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    properOrbitSignedSum C δ u₀ u₁ =
      ((Fintype.card F : ℂ) - 1) * properDirectionalDeviation C δ u₀ u₁ := by
  exact (properDirectionalDeviation_orbit_projectivization_split C δ u₀ u₁).symm

/-- Splitting off the principal character turns the affine spectral formula into the average
term `|F| * |properBall|` plus the signed nonprincipal deviation. -/
theorem properAffineBallIncidence_spectral_split
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    ((properAffineBallIncidence C δ u₀ u₁ : ℕ) : ℂ) *
        (Fintype.card ((ι → A) ⧸ C) : ℂ) =
      (Fintype.card F : ℂ) *
        ((properQuotientBall C δ (quotientPencil C u₀ u₁)).card +
          properDirectionalDeviation C δ u₀ u₁) := by
  classical
  rw [properAffineBallIncidence_spectral]
  have hzero : (0 : AddChar ((ι → A) ⧸ C) ℂ) ∈
      (Finset.univ : Finset (AddChar ((ι → A) ⧸ C) ℂ)) := Finset.mem_univ _
  rw [← Finset.add_sum_erase _ _ hzero]
  have hdirzero :
      ArkLib.ProximityGap.LineIncidenceSpectral.directionChar (F := F)
          (0 : AddChar ((ι → A) ⧸ C) ℂ)
          (Submodule.Quotient.mk (p := C) u₁) = 0 := by
    ext γ
    simp [ArkLib.ProximityGap.LineIncidenceSpectral.directionChar]
  simp [hdirzero, properDirectionalDeviation]

/-- Exact real-valued affine formula.  The imaginary part cancels automatically; the incidence
is governed by the real part of the nonprincipal sum, not by its absolute value. -/
theorem properAffineBallIncidence_mul_card_eq_signed
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    (properAffineBallIncidence C δ u₀ u₁ : ℝ) *
        Fintype.card ((ι → A) ⧸ C) =
      Fintype.card F *
        ((properQuotientBall C δ (quotientPencil C u₀ u₁)).card +
          (properDirectionalDeviation C δ u₀ u₁).re) := by
  have h := congrArg Complex.re
    (properAffineBallIncidence_spectral_split C δ u₀ u₁)
  simpa using h

/-- The infinity-slot indicator appearing in the full projective census. -/
noncomputable def properInfinityIndicator
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : ℕ :=
  if (Submodule.Quotient.mk (p := C) u₁ : (ι → A) ⧸ C) ∈
      properQuotientBall C δ (quotientPencil C u₀ u₁) then 1 else 0

/-- **Unconditional signed spectral census.**  The full MCA bad-slot count is the principal
proper-ball density plus the real part of the nonprincipal annihilator sum, together with the
single projective point at infinity. -/
theorem badSlotCount_mul_card_eq_signed
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    (badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ : ℝ) *
        Fintype.card ((ι → A) ⧸ C) =
      Fintype.card F *
          ((properQuotientBall C δ (quotientPencil C u₀ u₁)).card +
            (properDirectionalDeviation C δ u₀ u₁).re) +
        properInfinityIndicator C δ u₀ u₁ *
          Fintype.card ((ι → A) ⧸ C) := by
  rw [badSlotCount_eq_properProjectiveBallIncidence,
    properProjectiveBallIncidence_eq_affine_add_infty]
  change ((properAffineBallIncidence C δ u₀ u₁ +
      properInfinityIndicator C δ u₀ u₁ : ℕ) : ℝ) *
        Fintype.card ((ι → A) ⧸ C) = _
  rw [Nat.cast_add, add_mul, properAffineBallIncidence_mul_card_eq_signed]

/-- The signed Fourier inequality is exactly the per-pencil production bound.  This formulation
does not pay a triangle or square-root loss: it is an equivalence, not merely a sufficient norm
estimate. -/
theorem badSlotCount_le_iff_signed_spectral
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (E : ℕ) :
    badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ ≤ E ↔
      Fintype.card F *
          ((properQuotientBall C δ (quotientPencil C u₀ u₁)).card +
            (properDirectionalDeviation C δ u₀ u₁).re) +
        properInfinityIndicator C δ u₀ u₁ *
            Fintype.card ((ι → A) ⧸ C) ≤
          E * Fintype.card ((ι → A) ⧸ C) := by
  rw [← badSlotCount_mul_card_eq_signed C δ u₀ u₁]
  have hcard : (0 : ℝ) < Fintype.card ((ι → A) ⧸ C) := by positivity
  constructor
  · intro h
    have hcast :
        (badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ : ℝ) ≤ E := by
      exact_mod_cast h
    nlinarith
  · intro h
    have hcast :
        (badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ : ℝ) ≤ E := by
      nlinarith
    exact_mod_cast hcast

/-- The exact nonprincipal Fourier allowance left after charging the principal proper-ball density
and the possible point at infinity against a projective budget `E`. -/
noncomputable def properDeviationAllowance
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (E : ℕ) : ℝ :=
  (((E : ℝ) - properInfinityIndicator C δ u₀ u₁) *
      Fintype.card ((ι → A) ⧸ C)) / Fintype.card F -
    (properQuotientBall C δ (quotientPencil C u₀ u₁)).card

/-- **Exact one-sided character-sum target.**  A pencil meets budget `E` if and only if the real
part of its nonprincipal annihilator sum is at most `properDeviationAllowance`.  This is the
sharp arithmetic obligation: no modulus, triangle inequality, or Cauchy--Schwarz relaxation is
present. -/
theorem badSlotCount_le_iff_deviation_re_le_allowance
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (E : ℕ) :
    badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ ≤ E ↔
      (properDirectionalDeviation C δ u₀ u₁).re ≤
        properDeviationAllowance C δ u₀ u₁ E := by
  rw [badSlotCount_le_iff_signed_spectral C δ u₀ u₁ E]
  unfold properDeviationAllowance
  have hq : (0 : ℝ) < Fintype.card F := by positivity
  rw [le_sub_iff_add_le, le_div_iff₀ hq]
  constructor <;> intro h <;> nlinarith

/-- **Exact projectivized signed-cancellation criterion.**  After the `F*` orbit collapse, a
pencil meets budget `E` exactly when the real part of `properOrbitSignedSum` is at most
`(q - 1)` times its deviation allowance.  This is the remaining arithmetic statement with all
generic Fourier and projective normalization removed. -/
theorem badSlotCount_le_iff_orbitSignedSum_re_le
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (E : ℕ) :
    badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ ≤ E ↔
      (properOrbitSignedSum C δ u₀ u₁).re ≤
        ((Fintype.card F : ℝ) - 1) * properDeviationAllowance C δ u₀ u₁ E := by
  rw [badSlotCount_le_iff_deviation_re_le_allowance C δ u₀ u₁ E]
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hq1R : (1 : ℝ) < Fintype.card F := by exact_mod_cast hq1
  have hQ : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by
    linarith
  have hsigned := congrArg Complex.re
    (properOrbitSignedSum_eq_card_sub_one_mul_deviation C δ u₀ u₁)
  have hsignedReal : (properOrbitSignedSum C δ u₀ u₁).re =
      ((Fintype.card F : ℝ) - 1) *
        (properDirectionalDeviation C δ u₀ u₁).re := by
    simpa using hsigned
  constructor
  · intro h
    rw [hsignedReal]
    exact mul_le_mul_of_nonneg_left h hQ.le
  · intro h
    rw [hsignedReal] at h
    nlinarith

/-- A norm bound is a sufficient but deliberately stronger substitute for the exact signed
criterion.  This theorem makes the point of loss explicit: the only extra step is
`re z ≤ ‖z‖`. -/
theorem badSlotCount_le_of_deviation_norm_le_allowance
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (E : ℕ)
    (hdev : ‖properDirectionalDeviation C δ u₀ u₁‖ ≤
      properDeviationAllowance C δ u₀ u₁ E) :
    badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ ≤ E := by
  apply (badSlotCount_le_iff_deviation_re_le_allowance C δ u₀ u₁ E).2
  exact le_trans (Complex.re_le_norm _) hdev

/-- The deviation allowance is negative exactly when the principal proper-ball density plus the
infinity slot already exceeds the projective budget. -/
theorem properDeviationAllowance_neg_iff_principal_exceeds
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (E : ℕ) :
    properDeviationAllowance C δ u₀ u₁ E < 0 ↔
      (E : ℝ) * Fintype.card ((ι → A) ⧸ C) <
        Fintype.card F *
            (properQuotientBall C δ (quotientPencil C u₀ u₁)).card +
          properInfinityIndicator C δ u₀ u₁ *
            Fintype.card ((ι → A) ⧸ C) := by
  unfold properDeviationAllowance
  have hq : (0 : ℝ) < Fintype.card F := by positivity
  rw [sub_neg, div_lt_iff₀ hq]
  constructor <;> intro h <;> nlinarith

/-- If the principal density overshoots but the pencil nevertheless meets the production budget,
then the surviving nonprincipal character sum must have strictly negative real part.  Thus in this
regime cancellation is not optional: it must cancel the principal term. -/
theorem deviation_re_neg_of_badSlotCount_le_of_principal_exceeds
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (E : ℕ)
    (hcount : badSlotCount (F := F) (C : Set (ι → A)) δ u₀ u₁ ≤ E)
    (hprincipal :
      (E : ℝ) * Fintype.card ((ι → A) ⧸ C) <
        Fintype.card F *
            (properQuotientBall C δ (quotientPencil C u₀ u₁)).card +
          properInfinityIndicator C δ u₀ u₁ *
            Fintype.card ((ι → A) ⧸ C)) :
    (properDirectionalDeviation C δ u₀ u₁).re < 0 := by
  exact lt_of_le_of_lt
    ((badSlotCount_le_iff_deviation_re_le_allowance C δ u₀ u₁ E).1 hcount)
    ((properDeviationAllowance_neg_iff_principal_exceeds C δ u₀ u₁ E).2 hprincipal)

/-- **Precise norm-route no-go.**  Once the principal density exceeds budget, the exact allowance
is negative, while every norm is nonnegative.  Consequently no certificate of the form
`‖deviation‖ ≤ allowance` can prove production there; a one-sided signed estimate is strictly
necessary. -/
theorem not_deviation_norm_le_allowance_of_principal_exceeds
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (E : ℕ)
    (hprincipal :
      (E : ℝ) * Fintype.card ((ι → A) ⧸ C) <
        Fintype.card F *
            (properQuotientBall C δ (quotientPencil C u₀ u₁)).card +
          properInfinityIndicator C δ u₀ u₁ *
            Fintype.card ((ι → A) ⧸ C)) :
    ¬ ‖properDirectionalDeviation C δ u₀ u₁‖ ≤
      properDeviationAllowance C δ u₀ u₁ E := by
  intro hnorm
  have hneg :=
    (properDeviationAllowance_neg_iff_principal_exceeds C δ u₀ u₁ E).2 hprincipal
  exact (not_lt_of_ge (norm_nonneg _)) (lt_of_le_of_lt hnorm hneg)

/-- **Rank-two signed criterion for production.**  At every nontrivial budget, the complete
worst-case production statement is equivalent to the signed spectral inequality above on genuine
rank-two quotient pencils only. -/
theorem projectiveWorstCaseIncidenceBounded_iff_rankTwo_signed_spectral
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (E : ℕ) (hE : 1 ≤ E) :
    ProjectiveWorstCaseIncidenceBounded C δ E ↔
      ∀ u : WordStack A (Fin 2) ι,
        RowsIndependentModCode C (u 0) (u 1) →
          Fintype.card F *
              ((properQuotientBall C δ (quotientPencil C (u 0) (u 1))).card +
                (properDirectionalDeviation C δ (u 0) (u 1)).re) +
            properInfinityIndicator C δ (u 0) (u 1) *
                Fintype.card ((ι → A) ⧸ C) ≤
              E * Fintype.card ((ι → A) ⧸ C) := by
  rw [projectiveWorstCaseIncidenceBounded_iff_rankTwo C δ E hE]
  constructor
  · intro h u hu
    exact (badSlotCount_le_iff_signed_spectral C δ (u 0) (u 1) E).1 (h u hu)
  · intro h u hu
    exact (badSlotCount_le_iff_signed_spectral C δ (u 0) (u 1) E).2 (h u hu)

/-- Compact allowance form of the rank-two production criterion.  This is the final consumer
surface for arithmetic work: prove one uniform, one-sided estimate for the real nonprincipal
Fourier deviation on every genuine quotient two-plane. -/
theorem projectiveWorstCaseIncidenceBounded_iff_rankTwo_deviation_re_le_allowance
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (E : ℕ) (hE : 1 ≤ E) :
    ProjectiveWorstCaseIncidenceBounded C δ E ↔
      ∀ u : WordStack A (Fin 2) ι,
        RowsIndependentModCode C (u 0) (u 1) →
          (properDirectionalDeviation C δ (u 0) (u 1)).re ≤
            properDeviationAllowance C δ (u 0) (u 1) E := by
  rw [projectiveWorstCaseIncidenceBounded_iff_rankTwo C δ E hE]
  constructor
  · intro h u hu
    exact (badSlotCount_le_iff_deviation_re_le_allowance C δ (u 0) (u 1) E).1 (h u hu)
  · intro h u hu
    exact (badSlotCount_le_iff_deviation_re_le_allowance C δ (u 0) (u 1) E).2 (h u hu)

end ProximityGap.ProjectiveProperBallSpectralCriterion

/-! ## Axiom audit -/
open ProximityGap.ProjectiveProperBallSpectralCriterion
#print axioms smul_mem_properQuotientBall_iff
#print axioms properBallFourierCoeff_scaleAddChar
#print axioms sum_scaleAddChar_apply_nonzero
#print axioms properDirectionalDeviation_eq_phase_weighted
#print axioms properDirectionalDeviation_orbit_projectivization
#print axioms properDirectionalDeviation_orbit_projectivization_split
#print axioms properOrbitSignedSum_eq_card_sub_one_mul_deviation
#print axioms properAffineBallIncidence_spectral_split
#print axioms properAffineBallIncidence_mul_card_eq_signed
#print axioms badSlotCount_mul_card_eq_signed
#print axioms badSlotCount_le_iff_signed_spectral
#print axioms badSlotCount_le_iff_deviation_re_le_allowance
#print axioms badSlotCount_le_iff_orbitSignedSum_re_le
#print axioms badSlotCount_le_of_deviation_norm_le_allowance
#print axioms properDeviationAllowance_neg_iff_principal_exceeds
#print axioms deviation_re_neg_of_badSlotCount_le_of_principal_exceeds
#print axioms not_deviation_norm_le_allowance_of_principal_exceeds
#print axioms projectiveWorstCaseIncidenceBounded_iff_rankTwo_signed_spectral
#print axioms projectiveWorstCaseIncidenceBounded_iff_rankTwo_deviation_re_le_allowance
