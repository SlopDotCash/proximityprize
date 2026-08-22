/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKC12TranslateIntersectionReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKLateNewtonTwoColourPhysicalBridge

/-!
# Additive and spectral coordinates for the late-Newton `C12` alignment

The surviving favourable cross count from the late Newton packet is the physical correlation

`C12(r) = sum_t W_G(t) R_r(t)`.

This file gives both rows their exact additive and Fourier coordinates.  The adjacent subset row
is the cross-correlation

`R_r(t) = sum_s a_r(t+s) a_(r-1)(s)`,

where `a_j` is the `j`-subset-sum histogram.  Its Fourier transform is therefore
`e_r(b) * conj(e_(r-1)(b))`.  The shifted-intersection row has transform

`eta(2b) * conj(eta(b))`.

Cross Parseval then identifies the centered alignment `A_r` exactly with the nonzero-frequency
mixed sum

`sum_(b != 0) eta(2b) conj(eta(b)) conj(e_r(b)) e_(r-1)(b)`.

This is an exact reduction, not an estimate.  In particular, separate bounds for the absolute
values of the two spectra do not determine the sign of their mixed inner product; an abstract
two-frequency countermodel at the end records that obstruction.  A successful analytic input
must control the relative phases of these two actual spectra.  Issue #466.

## Literature boundary

* Zhu--Wan, *An Asymptotic Formula for Counting Subset Sums Over Subgroups of Finite Fields*
  (arXiv:1101.0289), gives strong one-histogram estimates when the subgroup index is small and
  gives its uniform-positivity corollaries only for subset size logarithmic in the field order.
  The production index is `2^128+192` (or `2^129+13`) while `r=5,6`, so that regime does not
  apply.
* Kerr--Macourt, *Multilinear Exponential Sums With A General Class Of Weights*
  (arXiv:1901.00975), and Macourt--Petridis--Shkredov--Shparlinski,
  *Bounds of Trilinear and Trinomial Exponential Sums* (arXiv:2003.03493), supply absolute-value
  upper bounds for multilinear sums.  They do not give the signed lower correlation displayed
  here.
* Cyclotomic association schemes diagonalize the `W_G` factor, but the adjacent distinct-subset
  spectrum is not a single scheme relation.  Intersection-number integrality or separate
  eigenvalue envelopes therefore do not determine this mixed phase alignment.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKC12AdditiveSpectralBridge

open ArkLib.ProximityGap.Frontier.BGKC12TranslateIntersectionReduction
open ArkLib.ProximityGap.Frontier.BGKLateNewtonSignedCovariance
open ArkLib.ProximityGap.Frontier.BGKRepeatedSectorNewtonAbsorption
open ArkLib.ProximityGap.Frontier.BGKCenteredTrajectoryContraction
open ArkLib.ProximityGap.Round4CharacterSum
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

section DifferenceConvolution

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Fibre of a difference phase is the additive cross-correlation of the two source fibres. -/
theorem phaseFiberCount_difference_eq_crossCorrelation
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (phi : X -> F) (chi : Y -> F) (t : F) :
    phaseFiberCount (fun z : X × Y => phi z.1 - chi z.2) t =
      ∑ s : F, phaseFiberCount phi (t + s) * phaseFiberCount chi s := by
  classical
  unfold phaseFiberCount
  calc
    ((Finset.univ.filter fun z : X × Y => phi z.1 - chi z.2 = t).card) =
        (((Finset.univ : Finset X) ×ˢ (Finset.univ : Finset Y)).filter
          fun z : X × Y => phi z.1 - chi z.2 = t).card := by
      simp
    _ = ∑ s : F,
        (((Finset.univ.filter fun x : X => phi x = t + s) ×ˢ
          (Finset.univ.filter fun y : Y => chi y = s)).card) := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext z
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
          Finset.mem_biUnion]
        constructor
        · intro h
          refine ⟨chi z.2, ?_, rfl⟩
          linear_combination h
        · rintro ⟨s, hphi, hchi⟩
          linear_combination hphi - hchi
      · intro a _ha b _hb hab
        apply Finset.disjoint_left.mpr
        intro z hza hzb
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hza hzb
        exact hab (hza.2.symm.trans hzb.2)
    _ = ∑ s : F,
        (Finset.univ.filter fun x : X => phi x = t + s).card *
          (Finset.univ.filter fun y : Y => chi y = s).card := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Finset.card_product]

/-- The adjacent subset-difference row is literally the cross-correlation of consecutive
subset-sum histograms. -/
theorem subsetDifferenceMultiplicity_eq_subsetSumCrossCorrelation
    (G : Finset F) (r : Nat) (t : F) :
    subsetDifferenceMultiplicity G r t =
      ∑ s : F, subsetSumCount G r (t + s) * subsetSumCount G (r - 1) s := by
  let labelSum (d : Nat) : SubsetAt G d -> F :=
    ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge.labelSubsetSum G d
  have hphase : subsetDifferencePhase G r =
      fun z : SubsetAt G r × SubsetAt G (r - 1) => labelSum r z.1 - labelSum (r - 1) z.2 := by
    funext z
    rfl
  unfold subsetDifferenceMultiplicity
  rw [hphase, phaseFiberCount_difference_eq_crossCorrelation]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [show phaseFiberCount (labelSum r) (t + s) = subsetSumCount G r (t + s) by
      simpa [labelSum] using
        (ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge.labelSubsetFiber_eq_valueSubsetFiber
          G r (t + s)).trans
        (ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge.valueSubsetFiber_eq_subsetSumCount
          G r (t + s))]
  rw [show phaseFiberCount (labelSum (r - 1)) s = subsetSumCount G (r - 1) s by
      simpa [labelSum] using
        (ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge.labelSubsetFiber_eq_valueSubsetFiber
          G (r - 1) s).trans
        (ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge.valueSubsetFiber_eq_subsetSumCount
          G (r - 1) s)]

end DifferenceConvolution

section FourierCoordinates

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Fourier transform of the shifted-intersection row, represented by its marked source family. -/
noncomputable def markedDifferenceSpectrum (psi : AddChar F Complex) (G : Finset F)
    (b : F) : Complex :=
  phaseFamilyPeriod psi (markedDifferencePhase G) b

/-- Fourier transform of the adjacent subset-difference row. -/
noncomputable def subsetDifferenceSpectrum (psi : AddChar F Complex) (G : Finset F)
    (r : Nat) (b : F) : Complex :=
  phaseFamilyPeriod psi (subsetDifferencePhase G r) b

/-- Fourier transformation commutes with passing from a finite phase family to its exact fibre
histogram. -/
theorem phaseFamilyPeriod_eq_fiberFourier
    {X : Type*} [Fintype X] [DecidableEq X]
    (psi : AddChar F Complex) (phi : X -> F) (b : F) :
    phaseFamilyPeriod psi phi b =
      ∑ t : F, (phaseFiberCount phi t : Complex) * psi (b * t) := by
  classical
  unfold phaseFamilyPeriod phaseFiberCount
  calc
    (∑ x : X, psi (b * phi x)) =
        ∑ x : X, ∑ t : F, if phi x = t then psi (b * t) else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      simp
    _ = ∑ t : F, ∑ x : X, if phi x = t then psi (b * t) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t : F,
        ((Finset.univ.filter fun x : X => phi x = t).card : Complex) * psi (b * t) := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.card_filter]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases h : phi x = t <;> simp [h]

/-- Literal row-transform statement for `W_G`. -/
theorem sum_markedDifferenceMultiplicity_mul_char_eq_spectrum
    (psi : AddChar F Complex) (G : Finset F) (b : F) :
    (∑ t : F, (markedDifferenceMultiplicity G t : Complex) * psi (b * t)) =
      markedDifferenceSpectrum psi G b := by
  symm
  exact phaseFamilyPeriod_eq_fiberFourier psi (markedDifferencePhase G) b

/-- Literal row-transform statement for `R_r`. -/
theorem sum_subsetDifferenceMultiplicity_mul_char_eq_spectrum
    (psi : AddChar F Complex) (G : Finset F) (r : Nat) (b : F) :
    (∑ t : F, (subsetDifferenceMultiplicity G r t : Complex) * psi (b * t)) =
      subsetDifferenceSpectrum psi G r b := by
  symm
  exact phaseFamilyPeriod_eq_fiberFourier psi (subsetDifferencePhase G r) b

/-- A difference-family Fourier transform factors into one transform times the conjugate of the
other. -/
theorem phaseFamilyPeriod_difference_eq_mul_conj
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (psi : AddChar F Complex) (phi : X -> F) (chi : Y -> F) (b : F) :
    phaseFamilyPeriod psi (fun z : X × Y => phi z.1 - chi z.2) b =
      phaseFamilyPeriod psi phi b *
        (starRingEnd Complex) (phaseFamilyPeriod psi chi b) := by
  classical
  have hchar : (0 : Nat) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : forall a : F, (starRingEnd Complex) (psi a) = psi (-a) := by
    intro a
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  unfold phaseFamilyPeriod
  rw [Fintype.sum_prod_type, map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro y _hy
  rw [hconj, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The Fourier transform of the labelled subset-sum map is the existing ordinary subset-sum
period. -/
theorem phaseFamilyPeriod_labelSubsetSum_eq_subsetSumPeriod
    (psi : AddChar F Complex) (G : Finset F) (d : Nat) (b : F) :
    phaseFamilyPeriod psi
        (ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge.labelSubsetSum G d) b =
      subsetSumPeriod psi G d b := by
  classical
  unfold phaseFamilyPeriod subsetSumPeriod
  apply Fintype.sum_equiv
    (ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge.labelValueSubsetEquiv G d)
  intro S
  rw [ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge.labelValueSubsetEquiv_phase]

/-- **Exact Fourier coordinate of `R_r`.**  The adjacent subset-difference spectrum is the
cross-product of consecutive elementary-symmetric subset periods. -/
theorem subsetDifferenceSpectrum_eq_subsetSumPeriod_mul_conj
    (psi : AddChar F Complex) (G : Finset F) (r : Nat) (b : F) :
    subsetDifferenceSpectrum psi G r b =
      subsetSumPeriod psi G r b *
        (starRingEnd Complex) (subsetSumPeriod psi G (r - 1) b) := by
  let labelSum (d : Nat) : SubsetAt G d -> F :=
    ArkLib.ProximityGap.Frontier.BGKLateNewtonTwoColourPhysicalBridge.labelSubsetSum G d
  have hphase : subsetDifferencePhase G r =
      fun z : SubsetAt G r × SubsetAt G (r - 1) => labelSum r z.1 - labelSum (r - 1) z.2 := by
    funext z
    rfl
  unfold subsetDifferenceSpectrum
  rw [hphase, phaseFamilyPeriod_difference_eq_mul_conj]
  rw [show phaseFamilyPeriod psi (labelSum r) b = subsetSumPeriod psi G r b by
      simpa [labelSum] using phaseFamilyPeriod_labelSubsetSum_eq_subsetSumPeriod psi G r b]
  rw [show phaseFamilyPeriod psi (labelSum (r - 1)) b =
      subsetSumPeriod psi G (r - 1) b by
      simpa [labelSum] using
        phaseFamilyPeriod_labelSubsetSum_eq_subsetSumPeriod psi G (r - 1) b]

/-- **Exact Fourier coordinate of `W_G`.**  The shifted-intersection spectrum is one dilated
Gauss period times the conjugate of the undilated period. -/
theorem markedDifferenceSpectrum_eq_powerSum_two_mul_conj_one
    (psi : AddChar F Complex) (G : Finset F) (b : F) :
    markedDifferenceSpectrum psi G b =
      phasePowerSum (subgroupPhase psi G b) 2 *
        (starRingEnd Complex) (phasePowerSum (subgroupPhase psi G b) 1) := by
  classical
  have hchar : (0 : Nat) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : forall a : F, (starRingEnd Complex) (psi a) = psi (-a) := by
    intro a
    rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  unfold markedDifferenceSpectrum phaseFamilyPeriod markedDifferencePhase phasePowerSum
    subgroupPhase
  rw [Fintype.sum_prod_type, map_sum, Finset.sum_mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _hy
  apply Finset.sum_congr rfl
  intro x _hx
  rw [pow_one, hconj, ← AddChar.map_nsmul_eq_pow,
    ← Nat.cast_smul_eq_nsmul (R := F)]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [smul_eq_mul]
  ring

/-- Period notation for the shifted-intersection spectrum. -/
theorem markedDifferenceSpectrum_eq_eta_two_mul_conj_eta_one
    (psi : AddChar F Complex) (G : Finset F) (b : F) :
    markedDifferenceSpectrum psi G b =
      eta psi G ((2 : F) * b) * (starRingEnd Complex) (eta psi G b) := by
  rw [markedDifferenceSpectrum_eq_powerSum_two_mul_conj_one,
    phasePowerSum_subgroupPhase, phasePowerSum_subgroupPhase]
  simp

/-- Literal shifted-intersection transform, with `W_G(t)=#{y in G : 2*y-t in G}` exposed. -/
theorem sum_doubledTranslateIntersection_mul_char_eq_eta_autocorrelation
    (psi : AddChar F Complex) (G : Finset F) (b : F) :
    (∑ t : F, (doubledTranslateIntersection G t : Complex) * psi (b * t)) =
      eta psi G ((2 : F) * b) * (starRingEnd Complex) (eta psi G b) := by
  calc
    (∑ t : F, (doubledTranslateIntersection G t : Complex) * psi (b * t)) =
        ∑ t : F, (markedDifferenceMultiplicity G t : Complex) * psi (b * t) := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [markedDifferenceMultiplicity_eq_doubledTranslateIntersection]
    _ = markedDifferenceSpectrum psi G b :=
      sum_markedDifferenceMultiplicity_mul_char_eq_spectrum psi G b
    _ = eta psi G ((2 : F) * b) * (starRingEnd Complex) (eta psi G b) :=
      markedDifferenceSpectrum_eq_eta_two_mul_conj_eta_one psi G b

/-- Every finite phase-family transform has source-cardinality mass at frequency zero. -/
theorem phaseFamilyPeriod_zero
    {X : Type*} [Fintype X] [DecidableEq X]
    (psi : AddChar F Complex) (phi : X -> F) :
    phaseFamilyPeriod psi phi 0 = (Fintype.card X : Complex) := by
  unfold phaseFamilyPeriod
  simp

theorem markedDifferenceSpectrum_zero
    (psi : AddChar F Complex) (G : Finset F) :
    markedDifferenceSpectrum psi G 0 = (G.card : Complex) ^ 2 := by
  unfold markedDifferenceSpectrum
  rw [phaseFamilyPeriod_zero]
  simp only [MarkedPair, Fintype.card_prod, Fintype.card_coe]
  push_cast
  ring

theorem subsetDifferenceSpectrum_zero
    (psi : AddChar F Complex) (G : Finset F) (r : Nat) :
    subsetDifferenceSpectrum psi G r 0 =
      (G.card.choose r : Complex) * G.card.choose (r - 1) := by
  unfold subsetDifferenceSpectrum
  rw [phaseFamilyPeriod_zero]
  simp only [AdjacentSubsetPair, SubsetAt, Fintype.card_prod, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ]
  push_cast
  ring

/-- Full cross Parseval for the two actual rows. -/
theorem sum_markedSpectrum_mul_conj_subsetSpectrum_eq_c12
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive)
    (G : Finset F) (r : Nat) :
    (∑ b : F, markedDifferenceSpectrum psi G b *
      (starRingEnd Complex) (subsetDifferenceSpectrum psi G r b)) =
      (Fintype.card F : Complex) * newtonJoinCollisionCount G 1 r 2 (r - 1) := by
  unfold markedDifferenceSpectrum subsetDifferenceSpectrum
  rw [sum_phaseFamilyPeriod_mul_conj_eq_crossCollision hpsi,
    ← newtonJoinCollisionCount_one_two_eq_differenceCrossCollision]

/-- **Exact signed spectral identity for the surviving alignment.**  The zero frequency is
precisely the product of the two row masses; deleting it leaves the integer `A_r`. -/
theorem sum_nonzero_markedSpectrum_mul_conj_subsetSpectrum_eq_centeredAlignment
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive)
    (G : Finset F) (r : Nat) :
    (∑ b ∈ Finset.univ.erase (0 : F), markedDifferenceSpectrum psi G b *
      (starRingEnd Complex) (subsetDifferenceSpectrum psi G r b)) =
      (c12CenteredAlignment G r : Complex) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0),
    sum_markedSpectrum_mul_conj_subsetSpectrum_eq_c12 hpsi,
    markedDifferenceSpectrum_zero, subsetDifferenceSpectrum_zero]
  rw [newtonJoinCollisionCount_one_two_eq_translateCorrelation]
  unfold c12CenteredAlignment
  push_cast
  simp

/-- Expanded mixed-period form of the same exact identity.  This is the analytic target: relative
phase alignment between a dilated Gauss autocorrelation and adjacent subset periods. -/
theorem sum_nonzero_eta_autocorrelation_mul_conj_subsetPeriods_eq_centeredAlignment
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive)
    (G : Finset F) (r : Nat) :
    (∑ b ∈ Finset.univ.erase (0 : F),
      (eta psi G ((2 : F) * b) * (starRingEnd Complex) (eta psi G b)) *
        (starRingEnd Complex)
          (subsetSumPeriod psi G r b *
            (starRingEnd Complex) (subsetSumPeriod psi G (r - 1) b))) =
      (c12CenteredAlignment G r : Complex) := by
  simpa only [markedDifferenceSpectrum_eq_eta_two_mul_conj_eta_one,
    subsetDifferenceSpectrum_eq_subsetSumPeriod_mul_conj] using
      sum_nonzero_markedSpectrum_mul_conj_subsetSpectrum_eq_centeredAlignment hpsi G r

/-- The previous identity with the outer conjugate expanded. -/
theorem sum_nonzero_eta_autocorrelation_mul_conj_er_mul_erPrev_eq_centeredAlignment
    {psi : AddChar F Complex} (hpsi : psi.IsPrimitive)
    (G : Finset F) (r : Nat) :
    (∑ b ∈ Finset.univ.erase (0 : F),
      eta psi G ((2 : F) * b) * (starRingEnd Complex) (eta psi G b) *
        (starRingEnd Complex) (subsetSumPeriod psi G r b) *
          subsetSumPeriod psi G (r - 1) b) =
      (c12CenteredAlignment G r : Complex) := by
  rw [← sum_nonzero_eta_autocorrelation_mul_conj_subsetPeriods_eq_centeredAlignment
    hpsi G r]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [map_mul, starRingEnd_self_apply]
  ring

end FourierCoordinates

/-! ## Refuted shortcut: separate spectral magnitudes do not determine alignment -/

section MagnitudeNoGo

/-- A two-frequency left spectrum. -/
def twoFrequencyLeft (_i : Fin 2) : Int := 1

/-- The aligned right spectrum. -/
def twoFrequencyAligned (_i : Fin 2) : Int := 1

/-- The anti-aligned right spectrum, with exactly the same pointwise square magnitudes. -/
def twoFrequencyAntialigned (_i : Fin 2) : Int := -1

theorem twoFrequency_right_squareMagnitudes_equal (i : Fin 2) :
    twoFrequencyAligned i ^ 2 = twoFrequencyAntialigned i ^ 2 := by
  simp [twoFrequencyAligned, twoFrequencyAntialigned]

theorem twoFrequency_right_totalSquareMass_equal :
    (∑ i : Fin 2, twoFrequencyAligned i ^ 2) =
      ∑ i : Fin 2, twoFrequencyAntialigned i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _hi
  exact twoFrequency_right_squareMagnitudes_equal i

theorem twoFrequency_aligned_inner_positive :
    (∑ i : Fin 2, twoFrequencyLeft i * twoFrequencyAligned i) = 2 := by
  norm_num [twoFrequencyLeft, twoFrequencyAligned, Fin.sum_univ_two]

theorem twoFrequency_antialigned_inner_negative :
    (∑ i : Fin 2, twoFrequencyLeft i * twoFrequencyAntialigned i) = -2 := by
  norm_num [twoFrequencyLeft, twoFrequencyAntialigned, Fin.sum_univ_two]

/-- **Magnitude-only spectral no-go.**  Two right spectra can have identical pointwise square
magnitudes and identical total square mass, but their inner products with the same left spectrum
have opposite signs.  Hence separate Gauss-period and subset-period norm estimates cannot imply a
lower bound for `A_r` without an additional relative-phase theorem. -/
theorem same_spectral_magnitudes_inner_product_has_opposite_signs :
    (forall i : Fin 2,
      twoFrequencyAligned i ^ 2 = twoFrequencyAntialigned i ^ 2) ∧
    (∑ i : Fin 2, twoFrequencyAligned i ^ 2) =
      (∑ i : Fin 2, twoFrequencyAntialigned i ^ 2) ∧
    (∑ i : Fin 2, twoFrequencyLeft i * twoFrequencyAligned i) = 2 ∧
    (∑ i : Fin 2, twoFrequencyLeft i * twoFrequencyAntialigned i) = -2 := by
  exact ⟨twoFrequency_right_squareMagnitudes_equal,
    twoFrequency_right_totalSquareMass_equal,
    twoFrequency_aligned_inner_positive,
    twoFrequency_antialigned_inner_negative⟩

end MagnitudeNoGo

/-! ## Axiom audit -/

#print axioms phaseFiberCount_difference_eq_crossCorrelation
#print axioms subsetDifferenceMultiplicity_eq_subsetSumCrossCorrelation
#print axioms phaseFamilyPeriod_eq_fiberFourier
#print axioms markedDifferenceSpectrum_eq_eta_two_mul_conj_eta_one
#print axioms sum_doubledTranslateIntersection_mul_char_eq_eta_autocorrelation
#print axioms subsetDifferenceSpectrum_eq_subsetSumPeriod_mul_conj
#print axioms sum_nonzero_markedSpectrum_mul_conj_subsetSpectrum_eq_centeredAlignment
#print axioms sum_nonzero_eta_autocorrelation_mul_conj_subsetPeriods_eq_centeredAlignment
#print axioms sum_nonzero_eta_autocorrelation_mul_conj_er_mul_erPrev_eq_centeredAlignment
#print axioms same_spectral_magnitudes_inner_product_has_opposite_signs

end ArkLib.ProximityGap.Frontier.BGKC12AdditiveSpectralBridge
