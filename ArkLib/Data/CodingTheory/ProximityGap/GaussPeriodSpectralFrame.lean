/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralizedPaleyRamanujan
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodParsevalFloor

/-!
# The two-sided spectral frame for the prize per-frequency core `M(n) = λ₂(Cay(F_q, μ_n))` (#407)

The #407 24-connection adversarial ledger (comment 4701053592) found that the in-tree
`GeneralizedPaleyRamanujan` target `‖η_b‖ ≤ 2√|G|` (exact Ramanujan) is the **wrong** ceiling: at
the prize scale `M(n) > 2√n` (the graph is provably NOT Ramanujan), and the *achievable / needed*
bound carries a `√log` factor. The correct lever is **near-Ramanujan up to √log**:

> `NearRamanujanSqrtLog ψ G C : ∀ b≠0, ‖η_b‖ ≤ C·√(|G|·log(q/|G|))`.

This file defines that (correctly-scaled) target and its bridge to the in-tree open residual
`WorstCaseIncompleteSumBound` at scale `C²·|G|·log(q/|G|)` (generalizing the too-strong `4|G|`
bridge), and assembles the **two-sided frame**: the Parseval floor (`GaussPeriodParsevalFloor`,
PROVEN lower half, `M² ≥ n(q−n)/(q−1) ≈ n`) together with `NearRamanujanSqrtLog` (the named-OPEN
upper half) brackets `M²`:  `n(q−n)/(q−1) ≤ M² ≤ C²·n·log(q/n)`.

Lower half proven (Parseval); upper half = the recognized-open BGK / Paley sub-`√q` cancellation
(F4), kept as a named hypothesis. This is the most-promising δ* lever (ledger "lever D"): the floor
scale `√n` is unconditional, the ceiling is the single remaining analytic input.

Axiom-clean. Issue #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.GeneralizedPaleyRamanujan
open ArkLib.ProximityGap.GaussPeriodParsevalFloor

namespace ArkLib.ProximityGap.GaussPeriodSpectralFrame

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Near-Ramanujan up to `√log`** — the correctly-scaled prize per-frequency ceiling:
every nonzero Gauss period has modulus `≤ C·√(|G|·log(q/|G|))`. The `√log` factor over the exact
Ramanujan bound `2√|G|` is unavoidable in the prize regime (`q/|G| = 2¹²⁸`); this is the genuine
open target (BGK / Paley sub-`√q` cancellation). -/
def NearRamanujanSqrtLog (ψ : AddChar F ℂ) (G : Finset F) (C : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 →
    ‖eta ψ G b‖ ≤ C * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))

/-- **Bridge: near-Ramanujan-up-to-√log discharges the in-tree open residual** at the `√log` scale
`M = C²·|G|·log(q/|G|)`. Generalizes `worstCaseIncompleteSumBound_of_ramanujan` (the `C=2`,
`log→1` special case gives `4|G|`). -/
theorem worstCaseIncompleteSumBound_of_nearRamanujan {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ}
    (hq : (G.card : ℝ) ≤ Fintype.card F) (hC : 0 ≤ C)
    (h : NearRamanujanSqrtLog ψ G C) :
    WorstCaseIncompleteSumBound ψ G
      (C ^ 2 * ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))) := by
  intro b hb
  set L : ℝ := (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card) with hL
  have hLnn : 0 ≤ L := by
    rw [hL]
    rcases Nat.eq_zero_or_pos G.card with hG0 | hGpos
    · simp [hG0]
    · have hGposR : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast hGpos
      have h1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) / G.card :=
        (le_div_iff₀ hGposR).mpr (by simpa using hq)
      exact mul_nonneg (le_of_lt hGposR) (Real.log_nonneg h1)
  have hb2 : ‖eta ψ G b‖ ≤ C * Real.sqrt L := h b hb
  have hsqL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLnn
  have h0 : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
  calc ‖eta ψ G b‖ ^ 2 ≤ (C * Real.sqrt L) ^ 2 := by nlinarith [Real.sqrt_nonneg L, h0, hb2]
    _ = C ^ 2 * L := by rw [mul_pow, hsqL]

/-- **The two-sided spectral frame.** Under the (open) near-Ramanujan-up-to-√log ceiling, the
prize per-frequency core `M² = max_{b≠0}‖η_b‖²` is bracketed
`n(q−n)/(q−1) ≤ M² ≤ C²·n·log(q/n)`: there is a frequency realizing the (PROVEN) Parseval floor, and
*every* frequency obeys the (OPEN) ceiling — in particular the floor witness does. The floor scale
`√n` is unconditional; closing the prize = proving the ceiling with `C·√log = O(√(log(1/ε*)))`. -/
theorem spectral_frame {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {C : ℝ}
    (hq : 2 ≤ Fintype.card F) (hcard : (G.card : ℝ) ≤ Fintype.card F) (hC : 0 ≤ C)
    (h : NearRamanujanSqrtLog ψ G C) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ 2
      ∧ ‖eta ψ G b‖ ^ 2
        ≤ C ^ 2 * ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)) := by
  obtain ⟨b, hbne, hfloor⟩ := exists_eta_sq_ge_parseval_floor hψ G hq
  exact ⟨b, hbne, hfloor, worstCaseIncompleteSumBound_of_nearRamanujan hcard hC h b hbne⟩

end ArkLib.ProximityGap.GaussPeriodSpectralFrame

#print axioms ArkLib.ProximityGap.GaussPeriodSpectralFrame.worstCaseIncompleteSumBound_of_nearRamanujan
#print axioms ArkLib.ProximityGap.GaussPeriodSpectralFrame.spectral_frame
