/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R207 nonzero Gauss-period dilation consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R200ShiftedQuarterPrizeConsumer
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumDilationRecursion

/-!
# R207 (#466): nonzero-frequency Gauss-period dilation consumer

R204--R206 proved the concrete full-frequency shift/dilation chain.  The prize
object is the nonprincipal spectrum, so this file repeats the concrete bridge
on the carrier `Finset.univ.erase 0`.  This removes the DC term from the
quarter-MGF interface and aligns the shifted-quarter route with the existing
DC-subtracted moment files.

The only analytic hypothesis left here is the nonzero one-child quarter-MGF
bound for `b ↦ ‖η_G(b)‖`.
-/

open Finset AddChar
open Real
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer

open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer
open ArkLib.ProximityGap.Frontier.R200ShiftedQuarterPrizeConsumer
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Nonzero frequencies, the carrier of the nonprincipal period spectrum. -/
def nonzeroFreqs : Finset F :=
  Finset.univ.erase (0 : F)

/-- Membership in `nonzeroFreqs` is exactly nonzeroness. -/
theorem mem_nonzeroFreqs (b : F) : b ∈ nonzeroFreqs (F := F) ↔ b ≠ 0 := by
  unfold nonzeroFreqs
  simp

/-- Multiplication by a nonzero scalar preserves the nonzero-frequency carrier. -/
theorem mul_mem_nonzeroFreqs {ζ b : F} (hζ : ζ ≠ 0)
    (hb : b ∈ nonzeroFreqs (F := F)) :
    ζ * b ∈ nonzeroFreqs (F := F) := by
  rw [mem_nonzeroFreqs] at hb ⊢
  exact mul_ne_zero hζ hb

/-- The quarter-MGF sum of a Gauss-period spectrum over nonzero frequencies is
invariant under a nonzero multiplicative frequency shift. -/
theorem nonzero_quarter_sum_eta_shift_eq
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0) :
    (∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * ‖eta ψ G (ζ * b)‖))
      = ∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖) := by
  refine Finset.sum_nbij' (fun b : F => ζ * b) (fun c : F => ζ⁻¹ * c) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    exact mul_mem_nonzeroFreqs hζ hb
  · intro c hc
    exact mul_mem_nonzeroFreqs (inv_ne_zero hζ) hc
  · intro b _
    simp [hζ]
  · intro c _
    field_simp [hζ]
  · intro _ _
    rfl

/-- Inequality form of the nonzero-frequency shift identity. -/
theorem nonzero_quarter_sum_eta_shift_le
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0) :
    (∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * ‖eta ψ G (ζ * b)‖))
      ≤ ∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖) :=
  (nonzero_quarter_sum_eta_shift_eq ψ G hζ).le

/-- Nonzero-frequency dyadic-tail MGF residual for the actual dilation parent. -/
theorem dyadicTailMGF_of_nonzero_gaussPeriod_dilation_quarter
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    (hLeft :
      (∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ)) :
    DyadicTailMGFBound (nonzeroFreqs (F := F))
      (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖) := by
  refine dyadicTailMGF_of_shifted_quarter (nonzeroFreqs (F := F))
    (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖)
    (fun b => ‖eta ψ G b‖)
    (fun b => ‖eta ψ G (ζ * b)‖) ?_ ?_ hLeft
  · intro b _
    exact eta_union_dilate_norm_le ψ G hζ hdisj b
  · exact nonzero_quarter_sum_eta_shift_le ψ G hζ

/-- Prize-square endpoint for the nonprincipal dilation spectrum. -/
theorem prize_sq_of_nonzero_gaussPeriod_dilation_quarter
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    {Mmax n Q : ℝ} {r : ℕ}
    (hLeft :
      (∑ b ∈ nonzeroFreqs (F := F),
        Real.exp ((1 / 4 : ℝ) * ‖eta ψ G b‖))
        ≤ 2 * ((nonzeroFreqs (F := F)).card : ℝ))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < ((nonzeroFreqs (F := F)).card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  refine prize_sq_of_shifted_quarter (nonzeroFreqs (F := F))
    (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖)
    (fun b => ‖eta ψ G b‖)
    (fun b => ‖eta ψ G (ζ * b)‖) ?_ ?_ hLeft
    hMmax hn hQ ?_ hP hr hrQ ?_
  · intro b _
    exact eta_union_dilate_norm_le ψ G hζ hdisj b
  · exact nonzero_quarter_sum_eta_shift_le ψ G hζ
  · intro b _
    exact norm_nonneg _
  · exact hmoment

end ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer.nonzero_quarter_sum_eta_shift_eq
#print axioms ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer.dyadicTailMGF_of_nonzero_gaussPeriod_dilation_quarter
#print axioms ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer.prize_sq_of_nonzero_gaussPeriod_dilation_quarter
