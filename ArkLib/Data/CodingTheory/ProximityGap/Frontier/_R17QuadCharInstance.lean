/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R17Deg2WeilRung
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# LANE B2 (#466 round 17, instantiation): `IsRealQuadChar` holds for Mathlib's `quadraticChar`

`_R17Deg2WeilRung.lean` proved the r = 2 away-Wick rung at deg 2 for an ABSTRACT real
quadratic character (`IsRealQuadChar χ`).  This companion brick instantiates the package at
Mathlib's `quadraticChar F` (composed to `ℝ`) for any finite field of odd characteristic —
so the round-17 theorem `wickAwayAt_two_of_weil` is concretely available at every prize-shaped
prime field, with the named `WeilQuarticPairs` input the ONLY remaining hypothesis.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 17 companion.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R17QuadCharInstance

open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The real-valued quadratic character `a ↦ (quadraticChar F a : ℝ)`. -/
def realQuadChar (F : Type*) [Field F] [Fintype F] [DecidableEq F] : F → ℝ :=
  fun a => ((quadraticChar F a : ℤ) : ℝ)

/-- **Instantiation**: Mathlib's quadratic character satisfies the round-17 abstract package,
for any finite field of odd characteristic. -/
theorem isRealQuadChar_realQuadChar (hF : ringChar F ≠ 2) :
    IsRealQuadChar (realQuadChar F) where
  map_zero := by
    simp [realQuadChar]
  map_mul := by
    intro a b
    simp only [realQuadChar, map_mul]
    push_cast
    ring
  sq_eq_one := by
    intro a ha
    have h := quadraticChar_sq_one (F := F) ha
    simp only [realQuadChar]
    have : ((quadraticChar F a : ℤ) : ℝ) ^ 2 = (((quadraticChar F a ^ 2 : ℤ)) : ℝ) := by
      push_cast; ring
    rw [this]
    norm_cast
  sum_eq_zero := by
    have h := quadraticChar_sum_zero (F := F) hF
    have hcast : ∑ a : F, realQuadChar F a
        = (((∑ a : F, quadraticChar F a : ℤ)) : ℝ) := by
      push_cast [realQuadChar]
      rfl
    rw [hcast]
    norm_cast

/-- **The round-17 theorem at the concrete quadratic character**: for any finite field of odd
characteristic with `√q ≥ 16·n²`, the constant-1 r = 2 diagonal-subtracted Wick rung holds at
`H = QR = {b : quadraticChar F b = 1}`, conditional only on the classical `WeilQuarticPairs`
input. -/
theorem wickAwayAt_two_of_weil_quadraticChar (hF : ringChar F ≠ 2)
    [DecidablePred fun b : F => realQuadChar F b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hweil : WeilQuarticPairs (realQuadChar F))
    (hbig : 16 * (G.card : ℝ) ^ 2 ≤ Real.sqrt (Fintype.card F))
    (hGne : G.Nonempty) :
    ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange.WickForIncidenceAwayAt
      ψ G (QRset (realQuadChar F)) (insert (0:F) G) 2 :=
  wickAwayAt_two_of_weil (isRealQuadChar_realQuadChar hF) hψ G hweil hbig hGne

end ArkLib.ProximityGap.Frontier.R17QuadCharInstance

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R17QuadCharInstance.isRealQuadChar_realQuadChar
#print axioms
  ArkLib.ProximityGap.Frontier.R17QuadCharInstance.wickAwayAt_two_of_weil_quadraticChar
