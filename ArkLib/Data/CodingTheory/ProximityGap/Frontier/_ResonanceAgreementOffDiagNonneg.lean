/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceAgreementReality
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceTowerFloor

/-!
# The agreement off-diagonal is a nonnegative real excess (#407 / #444)

`_ResonanceAgreementReality` identified the agreement off-diagonal as a real quantity and proved

`T r = (m - 1)^r + Re Off`.

`_ResonanceTowerFloor` independently proved the tower floor `(m - 1)^r ≤ T r` from the spectral
power-mean/Chebyshev lower bound. Combining them pins the agreement off-diagonal as a **nonnegative
real excess** above the Wick floor:

`0 ≤ (resonanceOffDiag u r).re`.

Honest scope: this is a floor-side/constraint statement. It does not upper-bound the off-diagonal,
does not prove cancellation, and does not close CORE. The prize remains the missing upper control of
this real excess / the one-step worst-frequency spectrum.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **Agreement off-diagonal nonnegativity.** For unit-modulus phases, the real agreement
off-diagonal is exactly `T r - (m - 1)^r`, hence is nonnegative by the proven tower floor. -/
theorem resonanceOffDiag_re_nonneg (u : ZMod m → ℂ) (r : ℕ)
    (hu : ∀ a : ZMod m, ‖u a‖ = 1) :
    0 ≤ (resonanceOffDiag u r).re := by
  have hdec := resonanceMoment_eq_wick_add_offDiag_re u r (fun a _ha => hu a)
  have hfloor := resonanceMoment_ge_pow u hu r
  have hcast : (((m - 1 : ℕ) : ℝ) ^ r) = (((m : ℝ) - 1) ^ r) := by
    have hm : (1 : ℕ) ≤ m := NeZero.one_le
    rw [Nat.cast_sub hm, Nat.cast_one]
  rw [hcast] at hdec
  linarith

/-- **Floor equality iff zero agreement excess.** The tower sits exactly on the Wick floor iff the
real agreement off-diagonal vanishes. This names the precise zero-slack case; no upper bound is
claimed. -/
theorem resonanceMoment_eq_floor_iff_offDiag_re_eq_zero (u : ZMod m → ℂ) (r : ℕ)
    (hu : ∀ a : ZMod m, ‖u a‖ = 1) :
    resonanceMoment u r = ((m : ℝ) - 1) ^ r ↔ (resonanceOffDiag u r).re = 0 := by
  have hdec := resonanceMoment_eq_wick_add_offDiag_re u r (fun a _ha => hu a)
  have hcast : (((m - 1 : ℕ) : ℝ) ^ r) = (((m : ℝ) - 1) ^ r) := by
    have hm : (1 : ℕ) ≤ m := NeZero.one_le
    rw [Nat.cast_sub hm, Nat.cast_one]
  rw [hcast] at hdec
  constructor <;> intro h <;> linarith

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag_re_nonneg
#print axioms
  ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_eq_floor_iff_offDiag_re_eq_zero
