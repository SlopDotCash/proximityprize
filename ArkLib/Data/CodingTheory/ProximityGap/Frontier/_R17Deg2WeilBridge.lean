/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R16DiagonalExactValue
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R16LegendreCosetFace

/-!
# LANE DEG2-WEIL (#466 round 17): consuming the exact quadratic-character bridge

The deg=2 probe found an exact identity, for `H = QR` and `G = μ_n ⊆ QR`,

`I_QR(s) = (q·1_G(s) - n + g(χ)·W(s)) / 2`,

where `W(s) = ∑_{x∈G} χ(s-x)` and `‖g(χ)‖ = √q`.  Off the deleted diagonal
`D ⊇ G`, this gives the deterministic envelope

`‖I_QR(s)‖ ≤ (n + √q · |W(s)|) / 2`.

This file lands the Lean-side consumer: any fourth-moment bound on the Legendre-shift field `W`
immediately yields an r=2 away-incidence moment bound with explicit constants.  The actual Weil /
Jacobi input for `∑ W^4` is left as a named numerical hypothesis; the algebraic bridge is
axiom-clean and ready to plug into `WickAwayAtWithConstant`.

Probe evidence (`scripts/probes/probe_r17_deg2_weil_rung.py`):
`S₂^D/Wick₂ ≈ 0.24–0.25` in beta 4/5 cells, matching the exact bridge's predicted `1/4` face.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R16DiagonalExactValue

namespace ArkLib.ProximityGap.Frontier.R17Deg2WeilBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A real-valued fourth moment of an auxiliary shifted-character field. -/
def AuxFourthMoment (W : F → ℝ) : ℝ :=
  ∑ s : F, |W s| ^ 4

/-- The off-diagonal norm envelope produced by the exact deg=2 Legendre/Gauss bridge:
`‖I(s)‖ ≤ (n + sqrt(q)|W(s)|)/2` for `s ∉ D`.

Here `n` is supplied as a real parameter so the theorem can be used both with `n = |G|`
and with slightly rounded external arithmetic hypotheses. -/
def DegTwoBridgeEnvelope (ψ : AddChar F ℂ) (G H D : Finset F) (W : F → ℝ) (n : ℝ) : Prop :=
  ∀ s : F, s ∉ D →
    ‖incidenceSum ψ G H s‖
      ≤ (n + Real.sqrt (Fintype.card F : ℝ) * |W s|) / 2

/-- Exact algebraic output in the natural `q²·B + q·n⁴` scale.  This version avoids hiding the
extra `q` inside constants and is the preferred consumer for sharp deg=2 work. -/
theorem incidenceMomentAway_two_le_of_degTwoBridge_qsq {ψ : AddChar F ℂ}
    (G H D : Finset F) (W : F → ℝ) {n B : ℝ}
    (hB : AuxFourthMoment W ≤ B)
    (hbridge : DegTwoBridgeEnvelope ψ G H D W n) :
    incidenceMomentAway ψ G H D 2
      ≤ (Fintype.card F : ℝ) ^ 2 * B + (Fintype.card F : ℝ) * n ^ 4 := by
  classical
  -- This is the sharp form obtained before the final optional normalization in the previous proof.
  unfold incidenceMomentAway
  set qR : ℝ := (Fintype.card F : ℝ)
  have hq0 : 0 ≤ qR := by positivity
  have hterm : ∀ s ∈ Finset.univ \ D,
      ‖incidenceSum ψ G H s‖ ^ (2 * 2)
        ≤ (Real.sqrt qR) ^ 4 * |W s| ^ 4 + n ^ 4 := by
    intro s hs
    have hsD : s ∉ D := (Finset.mem_sdiff.mp hs).2
    have hle : ‖incidenceSum ψ G H s‖ ≤ (n + Real.sqrt qR * |W s|) / 2 := by
      simpa [DegTwoBridgeEnvelope, qR] using hbridge s hsD
    have hnonneg : 0 ≤ ‖incidenceSum ψ G H s‖ := norm_nonneg _
    have hpow := pow_le_pow_left₀ hnonneg hle 4
    have hmain :
        ((n + Real.sqrt qR * |W s|) / 2) ^ 4
          ≤ (Real.sqrt qR) ^ 4 * |W s| ^ 4 + n ^ 4 := by
      have hsum :
          (n + Real.sqrt qR * |W s|) ^ 4
            ≤ 8 * (n ^ 4 + (Real.sqrt qR * |W s|) ^ 4) := by
        nlinarith [sq_nonneg (n - Real.sqrt qR * |W s|),
          sq_nonneg (n + Real.sqrt qR * |W s|),
          sq_nonneg (n ^ 2 - (Real.sqrt qR * |W s|) ^ 2)]
      have hdiv :
          ((n + Real.sqrt qR * |W s|) / 2) ^ 4
            = (n + Real.sqrt qR * |W s|) ^ 4 / 16 := by ring
      have hrel :
          ((n + Real.sqrt qR * |W s|) / 2) ^ 4
            ≤ (n ^ 4 + (Real.sqrt qR * |W s|) ^ 4) := by
        have hdiv_le :
            (n + Real.sqrt qR * |W s|) ^ 4 / 16
              ≤ (8 * (n ^ 4 + (Real.sqrt qR * |W s|) ^ 4)) / 16 := by
          exact div_le_div_of_nonneg_right hsum (by norm_num)
        have htarget_nonneg :
            0 ≤ n ^ 4 + (Real.sqrt qR * |W s|) ^ 4 := by positivity
        have hrelax :
            (8 * (n ^ 4 + (Real.sqrt qR * |W s|) ^ 4)) / 16
              ≤ n ^ 4 + (Real.sqrt qR * |W s|) ^ 4 := by
          nlinarith [htarget_nonneg]
        rw [hdiv]
        exact le_trans hdiv_le hrelax
      have hmul : (Real.sqrt qR * |W s|) ^ 4 = (Real.sqrt qR) ^ 4 * |W s| ^ 4 := by ring
      nlinarith
    have hpow' :
        ‖incidenceSum ψ G H s‖ ^ 4
          ≤ (Real.sqrt qR) ^ 4 * |W s| ^ 4 + n ^ 4 := le_trans hpow hmain
    simpa using hpow'
  calc
    ∑ s ∈ Finset.univ \ D, ‖incidenceSum ψ G H s‖ ^ (2 * 2)
        ≤ ∑ s ∈ Finset.univ \ D, ((Real.sqrt qR) ^ 4 * |W s| ^ 4 + n ^ 4) := by
          exact Finset.sum_le_sum hterm
    _ ≤ ∑ s : F, ((Real.sqrt qR) ^ 4 * |W s| ^ 4) + ∑ _s : F, n ^ 4 := by
        rw [Finset.sum_add_distrib]
        have hsub : Finset.univ \ D ⊆ (Finset.univ : Finset F) := by
          intro s hs
          exact (Finset.mem_sdiff.mp hs).1
        apply add_le_add
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (s := Finset.univ \ D) (t := Finset.univ)
            (f := fun s : F => (Real.sqrt qR) ^ 4 * |W s| ^ 4)
            hsub
            (by intro s _ _; positivity)
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (s := Finset.univ \ D) (t := Finset.univ)
            (f := fun _s : F => n ^ 4)
            hsub
            (by intro s _ _; positivity)
    _ = (Real.sqrt qR) ^ 4 * AuxFourthMoment W + qR * n ^ 4 := by
        unfold AuxFourthMoment
        rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        simp [qR]
    _ ≤ qR ^ 2 * B + qR * n ^ 4 := by
        have hsqrt4 : (Real.sqrt qR) ^ 4 = qR ^ 2 := by
          rw [show (Real.sqrt qR) ^ 4 = ((Real.sqrt qR) ^ 2) ^ 2 by ring]
          rw [Real.sq_sqrt hq0]
        rw [hsqrt4]
        have hcoef : 0 ≤ qR ^ 2 := by positivity
        have hmul : qR ^ 2 * AuxFourthMoment W ≤ qR ^ 2 * B :=
          mul_le_mul_of_nonneg_left hB hcoef
        exact add_le_add hmul le_rfl

end ArkLib.ProximityGap.Frontier.R17Deg2WeilBridge

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R17Deg2WeilBridge.incidenceMomentAway_two_le_of_degTwoBridge_qsq
