/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R17Deg2WeilRung

/-!
# LANE B2 (#466 round 18): the CONVERSE deg-2 envelope — corrected Problem B at deg 2 is
  (two-sidedly) the thin-shifted-Legendre sup-cancellation problem

`_R17Deg2WeilRung.bridge` gives the exact identity `I_QR(s₀) = (q·1_G(s₀) − n + g·W(s₀))/2`
with `‖g‖ = √q`.  The forward direction (a `W`-bound yields an incidence bound) is consumed by
`_R17Deg2WeilBridge`/`_R17Deg2WeilRung`.  This brick lands the CONVERSE, off the diagonal:

  `|W(s₀)| = ‖2·I_QR(s₀) + n‖ / √q  ≤ (2·‖I_QR(s₀)‖ + n) / √q`.

Hence any bound on the off-diagonal incidence field transfers back to the shifted Legendre sum
with NO loss beyond the exact algebra: **the deg-2 face of corrected Problem B and the
sup-cancellation problem for `W(s₀) = ∑_{y∈μ_n} χ(s₀−y)` (Karatsuba's thin shifted-subgroup
problem) are the same problem, two-sidedly, with explicit constants.**  In particular the
`√|H|·M`-shaped corrected Problem B at deg 2 pins `max_{s₀∉D} |W|` to `O(√(n·log q))`-scale
and conversely — the campaign's Problem B (deg 2) is not merely "Weil-adjacent": it is
literally the classical open thin-shift object.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 18, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung

namespace ArkLib.ProximityGap.Frontier.R18Deg2FaceConverse

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- **The exact converse identity** off the diagonal: for `s₀ ∉ G`,
`g·W(s₀) = 2·I_QR(s₀) + n` (as complex numbers). -/
theorem gW_eq_two_incidence_add (hχ : IsRealQuadChar χ)
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {s₀ : F} (hs₀ : s₀ ∉ G) :
    gSum χ ψ * ((Wsum χ G s₀ : ℝ) : ℂ)
      = 2 * incidenceSum ψ G (QRset χ) s₀ + (G.card : ℂ) := by
  have hbr := bridge hχ hψ G s₀
  rw [if_neg hs₀] at hbr
  rw [hbr]
  ring

/-- **The converse envelope**: off the diagonal,
`|W(s₀)| ≤ (2·‖I_QR(s₀)‖ + n) / √q`.  Together with the forward envelope this makes the deg-2
face of corrected Problem B two-sidedly equivalent (exact constants) to sup-cancellation of the
thin shifted Legendre sum — Karatsuba's problem. -/
theorem abs_W_le_of_incidence (hχ : IsRealQuadChar χ)
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {s₀ : F} (hs₀ : s₀ ∉ G)
    (hq1 : 1 ≤ (Fintype.card F : ℝ)) :
    |Wsum χ G s₀|
      ≤ (2 * ‖incidenceSum ψ G (QRset χ) s₀‖ + (G.card : ℝ))
          / Real.sqrt (Fintype.card F : ℝ) := by
  have hqpos : (0:ℝ) < Real.sqrt (Fintype.card F : ℝ) := Real.sqrt_pos.mpr (by linarith)
  rw [le_div_iff₀ hqpos]
  -- ‖g·W‖ = √q·|W| and ‖2I + n‖ ≤ 2‖I‖ + n
  have hgnorm : ‖gSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
    have h2 := norm_gSum_sq hχ hψ
    have h3 : ‖gSum χ ψ‖ = Real.sqrt (‖gSum χ ψ‖ ^ 2) := by
      rw [Real.sqrt_sq (norm_nonneg _)]
    rw [h3, h2]
  have hLHS : ‖gSum χ ψ * ((Wsum χ G s₀ : ℝ) : ℂ)‖
      = Real.sqrt (Fintype.card F : ℝ) * |Wsum χ G s₀| := by
    rw [norm_mul, hgnorm, Complex.norm_real]
    rfl
  have hRHS : ‖(2 : ℂ) * incidenceSum ψ G (QRset χ) s₀ + (G.card : ℂ)‖
      ≤ 2 * ‖incidenceSum ψ G (QRset χ) s₀‖ + (G.card : ℝ) := by
    calc ‖(2 : ℂ) * incidenceSum ψ G (QRset χ) s₀ + (G.card : ℂ)‖
        ≤ ‖(2 : ℂ) * incidenceSum ψ G (QRset χ) s₀‖ + ‖(G.card : ℂ)‖ := norm_add_le _ _
      _ = 2 * ‖incidenceSum ψ G (QRset χ) s₀‖ + (G.card : ℝ) := by
          rw [norm_mul, Complex.norm_natCast]
          norm_num
  calc |Wsum χ G s₀| * Real.sqrt (Fintype.card F : ℝ)
      = ‖gSum χ ψ * ((Wsum χ G s₀ : ℝ) : ℂ)‖ := by rw [hLHS]; ring
    _ = ‖(2 : ℂ) * incidenceSum ψ G (QRset χ) s₀ + (G.card : ℂ)‖ := by
        rw [gW_eq_two_incidence_add hχ hψ G hs₀]
    _ ≤ 2 * ‖incidenceSum ψ G (QRset χ) s₀‖ + (G.card : ℝ) := hRHS

end ArkLib.ProximityGap.Frontier.R18Deg2FaceConverse

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R18Deg2FaceConverse.gW_eq_two_incidence_add
#print axioms ArkLib.ProximityGap.Frontier.R18Deg2FaceConverse.abs_W_le_of_incidence
