/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Door-(iv) phase-blind radial statistics are invariant under unit twists (#444)

Shaw's `probe_bsummation_phaseblind_dichotomy.py` separated two classes of `b`-summed tools:
radial / polynomial-moment statistics, which collapse to integer counts and lose the adversarial
phase, and genuinely phase-coupled statistics, which are outside that polynomial moment class.

This file kernels the exact finite obstruction for the radial side.  Any statistic that sees a
complex period only through `Complex.normSq` is invariant under an arbitrary pointwise unit twist.
Consequently, no such statistic can distinguish two spectra that differ only by phases.  This is a
constraint lemma, not a CORE bound: it proves no cancellation, no anti-concentration, no completion
saving, no moment saving, and no capacity claim.  It only records that radial `b`-summed summaries are
phase-blind and therefore cannot by themselves control the worst-frequency phase alignment object.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.DoorIVPhaseBlindRadialStats

variable {ι : Type*}

/-- Multiplying a complex number by a unit-phase factor preserves squared modulus. -/
theorem normSq_mul_eq_of_unit (u z : ℂ) (hu : Complex.normSq u = 1) :
    Complex.normSq (u * z) = Complex.normSq z := by
  rw [Complex.normSq_mul, hu, one_mul]

/-- Any radial observable `F(normSq z)` is invariant under a unit-phase twist. -/
theorem radialObservable_eq_of_unit (F : ℝ → ℝ) (u z : ℂ) (hu : Complex.normSq u = 1) :
    F (Complex.normSq (u * z)) = F (Complex.normSq z) := by
  rw [normSq_mul_eq_of_unit u z hu]

/-- **Finite radial sums are phase-blind.**  A pointwise unit twist of a complex spectrum leaves every
`normSq`-radial `b`-summed statistic unchanged.  Thus a radial / moment summary cannot see the
adversarial phase alignment that Door (iv) needs. -/
theorem radialSum_invariant_under_unit_twist (s : Finset ι) (F : ℝ → ℝ) (tw A : ι → ℂ)
    (htw : ∀ i ∈ s, Complex.normSq (tw i) = 1) :
    (∑ i ∈ s, F (Complex.normSq (tw i * A i))) =
      ∑ i ∈ s, F (Complex.normSq (A i)) := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact radialObservable_eq_of_unit F (tw i) (A i) (htw i hi)

/-- A max over radial observables is also invariant under pointwise unit twists, because every entry is
unchanged.  This is the max-facing form of the same phase-blindness obstruction. -/
theorem radialEntry_eq_under_unit_twist (F : ℝ → ℝ) (tw A : ι → ℂ) {i : ι}
    (htw : Complex.normSq (tw i) = 1) :
    F (Complex.normSq (tw i * A i)) = F (Complex.normSq (A i)) := by
  exact radialObservable_eq_of_unit F (tw i) (A i) htw

end ArkLib.ProximityGap.Frontier.DoorIVPhaseBlindRadialStats

#print axioms ArkLib.ProximityGap.Frontier.DoorIVPhaseBlindRadialStats.normSq_mul_eq_of_unit
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPhaseBlindRadialStats.radialObservable_eq_of_unit
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPhaseBlindRadialStats.radialSum_invariant_under_unit_twist
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPhaseBlindRadialStats.radialEntry_eq_under_unit_twist
