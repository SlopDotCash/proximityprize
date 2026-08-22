/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic

/-!
# Door-IV eighth-cumulant sign instability

Probe context: `scripts/probes/probe_dooriv_eighth_cumulant_multiprime.py` measures the normalized
8th connected marginal cumulant across proper dyadic prize subgroups and finds both signs at the same
`n` across admissible primes (for example `n=32`: `+0.257, -0.358, -0.358`; `n=64`: `+0.415,
-0.056, +1.540`).

This file packages the formal constraint behind that measurement: once a candidate cumulant statistic
has two admissible instances with opposite signs, no universal fixed-sign certificate can be the missing
door-(iv) anti-concentration lever.  It does not claim the probe values as Lean data;
it records the kernel-checked implication any such mixed-sign data supplies.

No CORE/cancellation/completion/moment/capacity claim is made.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable

/-- A statistic is universally nonnegative over the sampled/admissible index set. -/
def UniversalNonnegative {ι : Type*} (κ : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ κ i

/-- A statistic is universally nonpositive over the sampled/admissible index set. -/
def UniversalNonpositive {ι : Type*} (κ : ι → ℝ) : Prop :=
  ∀ i, κ i ≤ 0

/-- One negative sample refutes a universal nonnegative-sign certificate. -/
theorem not_universalNonnegative_of_negative_sample {ι : Type*} {κ : ι → ℝ} {i : ι}
    (hi : κ i < 0) :
    ¬ UniversalNonnegative κ := by
  intro h
  exact (not_le_of_gt hi) (h i)

/-- One positive sample refutes a universal nonpositive-sign certificate. -/
theorem not_universalNonpositive_of_positive_sample {ι : Type*} {κ : ι → ℝ} {i : ι}
    (hi : 0 < κ i) :
    ¬ UniversalNonpositive κ := by
  intro h
  exact (not_le_of_gt hi) (h i)

/--
**Mixed eighth-cumulant signs forbid any universal fixed-sign route.**  If two admissible instances
of the candidate statistic have opposite signs, then neither a universal `κ ≥ 0` nor a universal
`κ ≤ 0` certificate can hold.
-/
theorem mixed_sign_forbids_universal_fixed_sign {ι : Type*} {κ : ι → ℝ} {i j : ι}
    (hpos : 0 < κ i) (hneg : κ j < 0) :
    ¬ UniversalNonnegative κ ∧ ¬ UniversalNonpositive κ := by
  exact ⟨not_universalNonnegative_of_negative_sample hneg,
    not_universalNonpositive_of_positive_sample hpos⟩

/-- Contradiction form for a proposed fixed-sign certificate. -/
theorem no_fixedSignCertificate_of_mixed_sign {ι : Type*} {κ : ι → ℝ} {i j : ι}
    (hpos : 0 < κ i) (hneg : κ j < 0) :
    ¬ (UniversalNonnegative κ ∨ UniversalNonpositive κ) := by
  intro h
  rcases h with hnonneg | hnonpos
  · exact (not_universalNonnegative_of_negative_sample hneg) hnonneg
  · exact (not_universalNonpositive_of_positive_sample hpos) hnonpos

#print axioms not_universalNonnegative_of_negative_sample
#print axioms not_universalNonpositive_of_positive_sample
#print axioms mixed_sign_forbids_universal_fixed_sign
#print axioms no_fixedSignCertificate_of_mixed_sign

end ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable
