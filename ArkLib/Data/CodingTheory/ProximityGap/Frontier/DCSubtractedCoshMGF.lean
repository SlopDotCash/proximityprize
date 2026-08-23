/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CoshMGFSaddle

/-!
# DC-subtracted cosh-MGF consumer (#407 / #444)

The live #444 reduction warns that the raw energy MGF is the wrong prize object: the `b = 0`
term contributes `|G|^(2r)` and makes raw `E_r ≤ Wick` false at the saddle.  This file ports the
cosh-MGF mechanism to the mandatory nonzero-frequency object:

`∑_{b≠0} cosh(‖η_b‖ y)
  = ∑'_r ((q E_r(G) - |G|^(2r)) y^(2r) / (2r)!)`.

Thus any bound on the **DC-subtracted** MGF gives a root-free period bound by the same elementary
`exp t ≤ 2 cosh t` step used in `_CoshMGFSaddle.lean`.  The open content remains exactly the
DC-subtracted MGF inequality at the saddle; this file is only the consumer.
-/

open scoped BigOperators

namespace ProximityGap.Frontier.DCSubtractedCoshMGF

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ProximityGap.Frontier.CoshMGFSaddle

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **DC-subtracted cosh-MGF identity.**  Summing only over nonzero frequencies removes the
principal character term:
`∑_{b≠0} cosh(‖η_b‖ y) = ∑'_r ((q E_r(G) - |G|^(2r)) y^(2r)/(2r)!)`. -/
theorem nonzeroCoshMGF_eq_dcMoment_tsum {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (y : ℝ) :
    (∑ b ∈ (univ.erase (0 : F)), Real.cosh (‖eta ψ G b‖ * y))
      = ∑' r : ℕ,
          (((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r))
            * y ^ (2 * r) / ((2 * r).factorial : ℝ)) := by
  classical
  have hb : ∀ b : F,
      HasSum (fun r : ℕ => (‖eta ψ G b‖ * y) ^ (2 * r) / ((2 * r).factorial : ℝ))
        (Real.cosh (‖eta ψ G b‖ * y)) := fun b => Real.hasSum_cosh _
  have hsum := hasSum_sum (fun b (_ : b ∈ (univ.erase (0 : F))) => hb b)
  rw [← hsum.tsum_eq]
  refine tsum_congr (fun r => ?_)
  rw [← sum_nonzero_moment hψ G r]
  rw [show ((∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)) * y ^ (2 * r)
          / ((2 * r).factorial : ℝ))
        = ∑ b ∈ univ.erase (0 : F),
            (‖eta ψ G b‖ ^ (2 * r) * y ^ (2 * r) / ((2 * r).factorial : ℝ)) by
      rw [Finset.sum_mul, Finset.sum_div]]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [mul_pow]

/-- **Single nonzero-period domination by the DC-subtracted cosh-MGF.** -/
theorem cosh_period_le_dcMoment_tsum {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (y : ℝ) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    Real.cosh (‖eta ψ G b₀‖ * y)
      ≤ ∑' r : ℕ,
          (((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r))
            * y ^ (2 * r) / ((2 * r).factorial : ℝ)) := by
  have hterm :
      Real.cosh (‖eta ψ G b₀‖ * y)
        ≤ ∑ b ∈ (univ.erase (0 : F)), Real.cosh (‖eta ψ G b‖ * y) := by
    refine Finset.single_le_sum (f := fun b => Real.cosh (‖eta ψ G b‖ * y)) ?_ ?_
    · intro b _; positivity
    · exact Finset.mem_erase.mpr ⟨hb₀, Finset.mem_univ b₀⟩
  exact hterm.trans_eq (nonzeroCoshMGF_eq_dcMoment_tsum hψ G y)

/-- **DC-subtracted cosh-MGF consumer.**  For `b₀ ≠ 0`, any bound
`DC-MGF(y) ≤ B` with `B > 0` implies `‖η_{b₀}‖ ≤ log(2B)/y`.
This is the prize-aligned analogue of `_CoshMGFSaddle.period_le_of_mgfBound`. -/
theorem period_le_of_dcMGFBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y B : ℝ} (hy : 0 < y) (hB : 0 < B) {b₀ : F} (hb₀ : b₀ ≠ 0)
    (hDCMGF : (∑' r : ℕ,
          (((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r))
            * y ^ (2 * r) / ((2 * r).factorial : ℝ))) ≤ B) :
    ‖eta ψ G b₀‖ ≤ Real.log (2 * B) / y := by
  have hcosh : Real.cosh (‖eta ψ G b₀‖ * y) ≤ B :=
    (cosh_period_le_dcMoment_tsum hψ G y hb₀).trans hDCMGF
  have hexp : Real.exp (‖eta ψ G b₀‖ * y) ≤ 2 * B :=
    (exp_le_two_mul_cosh _).trans (by linarith [hcosh])
  have hlog : ‖eta ψ G b₀‖ * y ≤ Real.log (2 * B) := by
    calc ‖eta ψ G b₀‖ * y = Real.log (Real.exp (‖eta ψ G b₀‖ * y)) := (Real.log_exp _).symm
      _ ≤ Real.log (2 * B) := Real.log_le_log (Real.exp_pos _) hexp
  rw [le_div_iff₀ hy]
  exact hlog

/-- **Gaussian-form DC-subtracted cosh-MGF consumer.**  This is the call-site shape for the #444
saddle: if the DC-subtracted MGF is bounded by `q·exp(|G| y²/2)`, then every nonzero period satisfies
`‖η_b‖ ≤ log(2q exp(|G|y²/2))/y`. -/
theorem period_le_of_dcGaussianMGFBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {y : ℝ} (hy : 0 < y) {b₀ : F} (hb₀ : b₀ ≠ 0)
    (hDCMGF : (∑' r : ℕ,
          (((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r))
            * y ^ (2 * r) / ((2 * r).factorial : ℝ)))
        ≤ (Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2)) :
    ‖eta ψ G b₀‖
      ≤ Real.log
          (2 * ((Fintype.card F : ℝ) * Real.exp ((G.card : ℝ) * y ^ 2 / 2))) / y := by
  refine period_le_of_dcMGFBound hψ G hy ?_ hb₀ hDCMGF
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have := Fintype.card_pos (α := F); exact_mod_cast this
  positivity

end ProximityGap.Frontier.DCSubtractedCoshMGF

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.DCSubtractedCoshMGF.nonzeroCoshMGF_eq_dcMoment_tsum
#print axioms ProximityGap.Frontier.DCSubtractedCoshMGF.cosh_period_le_dcMoment_tsum
#print axioms ProximityGap.Frontier.DCSubtractedCoshMGF.period_le_of_dcMGFBound
#print axioms ProximityGap.Frontier.DCSubtractedCoshMGF.period_le_of_dcGaussianMGFBound
