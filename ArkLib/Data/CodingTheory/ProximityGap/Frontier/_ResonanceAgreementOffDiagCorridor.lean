/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceAgreementOffDiagNonneg
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceMomentGeneralCeiling

/-!
# The agreement off-diagonal corridor between Wick floor and trivial ceiling (#444)

`_ResonanceAgreementOffDiagNonneg` proved that the agreement off-diagonal is the nonnegative
real excess above the Wick floor.  This small Lane-2/3 corridor adds the matching trivial upper
bookkeeping: for `r ≥ 1`, the same exact decomposition and the uniform triangle ceiling imply

`0 ≤ Re Off ≤ m (m - 1)^(2(r-1)) - (m - 1)^r`.

Honest scope: this is only the corridor forced by the already-known floor and triangle ceiling.
It does **not** improve the ceiling, does not prove cancellation, and does not close CORE.  It
names precisely how much room the agreement off-diagonal has before any genuinely new door-(iv)
anti-concentration input is supplied.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- **Agreement off-diagonal is exactly the excess above the Wick floor.**
For unit phases, `Re Off = T r - (m - 1)^r`.  This is the algebraic identity behind the
nonnegativity and corridor statements. -/
theorem resonanceOffDiag_re_eq_moment_sub_floor (u : ZMod m → ℂ) (r : ℕ)
    (hu : ∀ a : ZMod m, ‖u a‖ = 1) :
    (resonanceOffDiag u r).re = resonanceMoment u r - ((m : ℝ) - 1) ^ r := by
  have hdec := resonanceMoment_eq_wick_add_offDiag_re u r (fun a _ha => hu a)
  have hcast : (((m - 1 : ℕ) : ℝ) ^ r) = (((m : ℝ) - 1) ^ r) := by
    have hm : (1 : ℕ) ≤ m := NeZero.one_le
    rw [Nat.cast_sub hm, Nat.cast_one]
  rw [hcast] at hdec
  linarith

/-- **Trivial-ceiling upper room for the agreement off-diagonal.**
For `r ≥ 1`, the off-diagonal excess cannot exceed the gap between the uniform triangle ceiling
`m (m - 1)^(2(r-1))` and the Wick floor `(m - 1)^r`.  This is not cancellation; it is only the
bookkeeping envelope left by the trivial ceiling. -/
theorem resonanceOffDiag_re_le_trivial_ceiling_gap (u : ZMod m → ℂ) (r : ℕ) (hr : 1 ≤ r)
    (hu : ∀ a : ZMod m, ‖u a‖ = 1) :
    (resonanceOffDiag u r).re
      ≤ (m : ℝ) * ((m : ℝ) - 1) ^ (2 * (r - 1)) - ((m : ℝ) - 1) ^ r := by
  have hgap := resonanceOffDiag_re_eq_moment_sub_floor u r hu
  have hceil := resonanceMoment_le_general u hu r hr
  linarith

/-- **The agreement off-diagonal corridor.**
For unit phases and `r ≥ 1`, the named off-diagonal real excess lies between zero and the gap
between the trivial ceiling and the Wick floor.  Any prize-relevant theorem must shrink this
corridor by new phase-distribution input, not by floor/ceiling bookkeeping. -/
theorem resonanceOffDiag_re_corridor (u : ZMod m → ℂ) (r : ℕ) (hr : 1 ≤ r)
    (hu : ∀ a : ZMod m, ‖u a‖ = 1) :
    0 ≤ (resonanceOffDiag u r).re ∧
      (resonanceOffDiag u r).re
        ≤ (m : ℝ) * ((m : ℝ) - 1) ^ (2 * (r - 1)) - ((m : ℝ) - 1) ^ r := by
  exact ⟨resonanceOffDiag_re_nonneg u r hu,
    resonanceOffDiag_re_le_trivial_ceiling_gap u r hr hu⟩

/-- **Upper-corridor equality is exactly trivial-ceiling saturation.**
For `r ≥ 1`, the agreement off-diagonal fills the whole corridor precisely when the resonance
moment itself attains the uniform triangle ceiling.  Thus any proof that the off-diagonal stays
strictly below the corridor top is equivalent to proving genuine slack in the triangle ceiling. -/
theorem resonanceOffDiag_re_eq_trivial_ceiling_gap_iff (u : ZMod m → ℂ) (r : ℕ)
    (hu : ∀ a : ZMod m, ‖u a‖ = 1) :
    (resonanceOffDiag u r).re
        = (m : ℝ) * ((m : ℝ) - 1) ^ (2 * (r - 1)) - ((m : ℝ) - 1) ^ r
      ↔ resonanceMoment u r = (m : ℝ) * ((m : ℝ) - 1) ^ (2 * (r - 1)) := by
  have hgap := resonanceOffDiag_re_eq_moment_sub_floor u r hu
  constructor <;> intro h <;> linarith

/-- **The corridor top is nonnegative whenever unit phases exist.**
This is only a consistency check forced by the already-proven floor and ceiling: the trivial
ceiling sits above the Wick floor in the unit-phase regime. -/
theorem trivial_ceiling_gap_nonneg_of_unit (u : ZMod m → ℂ) (r : ℕ) (hr : 1 ≤ r)
    (hu : ∀ a : ZMod m, ‖u a‖ = 1) :
    0 ≤ (m : ℝ) * ((m : ℝ) - 1) ^ (2 * (r - 1)) - ((m : ℝ) - 1) ^ r := by
  have hcorr := resonanceOffDiag_re_corridor u r hr hu
  exact le_trans hcorr.1 hcorr.2

end ArkLib.ProximityGap.GaussPhaseResonance

#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag_re_eq_moment_sub_floor
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag_re_le_trivial_ceiling_gap
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag_re_corridor
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceOffDiag_re_eq_trivial_ceiling_gap_iff
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.trivial_ceiling_gap_nonneg_of_unit
