/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Burgess shift-Hölder exponent gate at the beta-four wall

The classical Burgess estimate for a length-`H` character sum has the schematic exponent

`H^(1 - 1/r) * p^((r + 1) / (4r^2))`.

If `p = H^beta`, this is a pure `H`-power

`H^(1 - 1/r + beta * (r + 1) / (4r^2))`.

This file records the elementary exponent barrier:

* the bound is nontrivial relative to the trivial `H` bound only when
  `beta < 4r / (r + 1)`;
* the threshold `4r / (r + 1)` is always strictly below `4`;
* at the prize/Burgess wall `beta = 4`, every finite Burgess parameter gives exponent
  `1 + 1/r^2`, strictly worse than trivial.

This is not an analytic theorem and does not assert Burgess for the subgroup period.  It is the
consumer-side arithmetic behind the KB verdict that Burgess shift-Hölder amplification dies at
`p = H^4`.
-/

namespace ArkLib.ProximityGap.Frontier.BurgessShiftHolderExponentGate

/-! ## The Burgess exponent as a pure `H`-power -/

/-- The `H`-exponent of the schematic Burgess bound
`H^(1 - 1/r) * p^((r+1)/(4r^2))` after substituting `p = H^beta`. -/
noncomputable def burgessHExponent (beta r : ℝ) : ℝ :=
  1 - 1 / r + beta * (r + 1) / (4 * r ^ 2)

/-- A rearranged form that exposes the nontriviality numerator. -/
theorem burgessHExponent_eq_one_plus {beta r : ℝ} (hr : r ≠ 0) :
    burgessHExponent beta r =
      1 + (beta * (r + 1) - 4 * r) / (4 * r ^ 2) := by
  unfold burgessHExponent
  field_simp [hr]
  ring

/-- Exact beta-four specialization: every finite Burgess parameter gives exponent
`1 + 1/r^2`. -/
theorem burgessHExponent_beta_four_eq {r : ℝ} (hr : r ≠ 0) :
    burgessHExponent 4 r = 1 + 1 / r ^ 2 := by
  rw [burgessHExponent_eq_one_plus (beta := 4) hr]
  field_simp [hr]
  ring

/-- At beta four, Burgess is strictly worse than the trivial `H` bound. -/
theorem one_lt_burgessHExponent_beta_four {r : ℝ} (hr : 0 < r) :
    1 < burgessHExponent 4 r := by
  rw [burgessHExponent_beta_four_eq (r := r) (ne_of_gt hr)]
  have hsq : 0 < r ^ 2 := sq_pos_of_ne_zero (ne_of_gt hr)
  have hfrac : 0 < 1 / r ^ 2 := by positivity
  linarith

/-- Consequently beta-four Burgess cannot even prove a nontrivial `H^{<1}` bound. -/
theorem not_burgess_nontrivial_beta_four {r : ℝ} (hr : 0 < r) :
    ¬ burgessHExponent 4 r < 1 := by
  exact not_lt_of_ge (le_of_lt (one_lt_burgessHExponent_beta_four hr))

/-! ## The exact nontriviality threshold -/

/-- Burgess beats the trivial exponent `1` exactly below the threshold `4r/(r+1)`. -/
theorem burgessHExponent_lt_one_iff {beta r : ℝ} (hr : 0 < r) :
    burgessHExponent beta r < 1 ↔ beta < 4 * r / (r + 1) := by
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hden : 0 < 4 * r ^ 2 := by positivity
  have hr1 : 0 < r + 1 := by linarith
  rw [burgessHExponent_eq_one_plus (beta := beta) (r := r) hr_ne]
  constructor
  · intro h
    have hfrac : (beta * (r + 1) - 4 * r) / (4 * r ^ 2) < 0 := by
      linarith
    have hnum : beta * (r + 1) - 4 * r < 0 := by
      rw [div_lt_iff₀ hden] at hfrac
      simpa using hfrac
    rw [lt_div_iff₀ hr1]
    linarith
  · intro h
    have hmul : beta * (r + 1) < 4 * r := by
      rw [lt_div_iff₀ hr1] at h
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hnum : beta * (r + 1) - 4 * r < 0 := by linarith
    have hfrac : (beta * (r + 1) - 4 * r) / (4 * r ^ 2) < 0 := by
      rw [div_lt_iff₀ hden]
      simpa using hnum
    linarith

/-- The Burgess nontriviality threshold is always strictly below beta four. -/
theorem burgess_threshold_lt_four {r : ℝ} (hr : 0 < r) :
    4 * r / (r + 1) < 4 := by
  have hr1 : 0 < r + 1 := by linarith
  rw [div_lt_iff₀ hr1]
  nlinarith

/-- Any Burgess nontriviality claim automatically requires `beta < 4`. -/
theorem beta_lt_four_of_burgess_nontrivial {beta r : ℝ} (hr : 0 < r)
    (h : burgessHExponent beta r < 1) :
    beta < 4 := by
  exact lt_trans ((burgessHExponent_lt_one_iff (beta := beta) hr).mp h)
    (burgess_threshold_lt_four hr)

/-- At beta four, the Burgess exponent is also strictly above the prize exponent `1/2`. -/
theorem half_lt_burgessHExponent_beta_four {r : ℝ} (hr : 0 < r) :
    (1 / 2 : ℝ) < burgessHExponent 4 r := by
  have h := one_lt_burgessHExponent_beta_four hr
  linarith

/-- Natural-parameter form used in notes: for every Burgess parameter `r >= 1`, beta-four is
worse than trivial. -/
theorem nat_one_lt_burgessHExponent_beta_four (r : ℕ) (hr : 1 ≤ r) :
    1 < burgessHExponent 4 (r : ℝ) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (Nat.pos_of_ne_zero (by omega : r ≠ 0))
  exact one_lt_burgessHExponent_beta_four hrpos

/-- Bundled verdict: finite Burgess shift-Hölder amplification is not a beta-four proof. -/
theorem burgess_beta_four_gate {r : ℝ} (hr : 0 < r) :
    burgessHExponent 4 r = 1 + 1 / r ^ 2 ∧
      1 < burgessHExponent 4 r ∧
      ¬ burgessHExponent 4 r < 1 ∧
      (1 / 2 : ℝ) < burgessHExponent 4 r := by
  exact ⟨burgessHExponent_beta_four_eq (ne_of_gt hr),
    one_lt_burgessHExponent_beta_four hr,
    not_burgess_nontrivial_beta_four hr,
    half_lt_burgessHExponent_beta_four hr⟩

end ArkLib.ProximityGap.Frontier.BurgessShiftHolderExponentGate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.BurgessShiftHolderExponentGate.burgessHExponent_eq_one_plus
#print axioms ArkLib.ProximityGap.Frontier.BurgessShiftHolderExponentGate.burgessHExponent_beta_four_eq
#print axioms ArkLib.ProximityGap.Frontier.BurgessShiftHolderExponentGate.one_lt_burgessHExponent_beta_four
#print axioms ArkLib.ProximityGap.Frontier.BurgessShiftHolderExponentGate.burgessHExponent_lt_one_iff
#print axioms ArkLib.ProximityGap.Frontier.BurgessShiftHolderExponentGate.burgess_threshold_lt_four
#print axioms ArkLib.ProximityGap.Frontier.BurgessShiftHolderExponentGate.beta_lt_four_of_burgess_nontrivial
#print axioms ArkLib.ProximityGap.Frontier.BurgessShiftHolderExponentGate.burgess_beta_four_gate
