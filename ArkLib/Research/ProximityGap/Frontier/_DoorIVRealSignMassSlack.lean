/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Door IV real sign-mass slack

This is a second small constraint brick for Shaw's door-(iv) coherence object.  Once a coset
refinement is negation-stable, every piece-period is real.  The only way the normalized coherence
can drop below `1` is then literal cancellation between the positive and negative real mass.

If `P` is the total positive mass and `N` is the total negative mass (recorded as a nonnegative
number), the real coherence is

`|P - N| / (P + N)`.

The exact formulas below say that the slack from `1` is precisely twice the minority sign mass
divided by the total mass.  Thus any door-(iv) theorem based on a real, negation-stable
refinement must prove a lower bound on the minority sign mass.  Merely naming a finer
decomposition does not supply phase
anti-concentration; it has to force a balanced sign split.

This is not CORE and not a moment/completion bound.  It is a constraint lemma for the
surviving door-(iv) lane.
-/

namespace ProximityGap.Frontier.DoorIVRealSignMassSlack

/-- Coherence after compressing real pieces to positive mass `P` and negative mass `N`. -/
noncomputable def signMassCoherence (P N : ℝ) : ℝ := |P - N| / (P + N)

/-- If negative mass is the minority, coherence is `1 - 2N/(P+N)`. -/
theorem signMassCoherence_eq_one_sub_twice_neg {P N : ℝ}
    (hle : N ≤ P) (hden : 0 < P + N) :
    signMassCoherence P N = 1 - 2 * N / (P + N) := by
  unfold signMassCoherence
  have hsub : 0 ≤ P - N := sub_nonneg.mpr hle
  rw [abs_of_nonneg hsub]
  field_simp [ne_of_gt hden]
  ring

/-- If positive mass is the minority, coherence is `1 - 2P/(P+N)`. -/
theorem signMassCoherence_eq_one_sub_twice_pos {P N : ℝ}
    (hle : P ≤ N) (hden : 0 < P + N) :
    signMassCoherence P N = 1 - 2 * P / (P + N) := by
  unfold signMassCoherence
  have hsub : P - N ≤ 0 := sub_nonpos.mpr hle
  rw [abs_of_nonpos hsub]
  field_simp [ne_of_gt hden]
  ring

/-- Real sign-mass coherence is always at most `1` for nonnegative sign masses. -/
theorem signMassCoherence_le_one {P N : ℝ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) (hden : 0 < P + N) :
    signMassCoherence P N ≤ 1 := by
  unfold signMassCoherence
  have h_abs : |P - N| ≤ P + N := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  exact (div_le_one hden).mpr h_abs

/-- Threshold form of the sign-mass constraint.  To force real-piece coherence below
`1 - eps`, the minority sign mass must be at least an `eps/2` fraction of the total
mass.  Thus a real, negation-stable door-(iv) refinement only helps after proving a
quantitative lower bound on minority sign mass. -/
theorem minority_mass_ge_of_coherence_le_one_sub {P N eps : ℝ}
    (hden : 0 < P + N) (hcoh : signMassCoherence P N ≤ 1 - eps) :
    eps * (P + N) / 2 ≤ min P N := by
  rcases le_total N P with hNP | hPN
  · have hform := signMassCoherence_eq_one_sub_twice_neg hNP hden
    have hineq : 1 - 2 * N / (P + N) ≤ 1 - eps := by
      simpa [hform] using hcoh
    have heps_le : eps ≤ 2 * N / (P + N) := by linarith
    have hmul : eps * (P + N) ≤ 2 * N := by
      exact (le_div_iff₀ hden).mp heps_le
    have hhalf : eps * (P + N) / 2 ≤ N := by linarith
    simpa [min_eq_right hNP] using hhalf
  · have hform := signMassCoherence_eq_one_sub_twice_pos hPN hden
    have hineq : 1 - 2 * P / (P + N) ≤ 1 - eps := by
      simpa [hform] using hcoh
    have heps_le : eps ≤ 2 * P / (P + N) := by linarith
    have hmul : eps * (P + N) ≤ 2 * P := by
      exact (le_div_iff₀ hden).mp heps_le
    have hhalf : eps * (P + N) / 2 ≤ P := by linarith
    simpa [min_eq_left hPN] using hhalf

/-- Exact one-line sign-mass formula: real-piece coherence is one minus twice the
minority sign mass divided by total mass. -/
theorem signMassCoherence_eq_one_sub_twice_min {P N : ℝ} (hden : 0 < P + N) :
    signMassCoherence P N = 1 - 2 * min P N / (P + N) := by
  rcases le_total N P with hNP | hPN
  · simpa [min_eq_right hNP] using signMassCoherence_eq_one_sub_twice_neg hNP hden
  · simpa [min_eq_left hPN] using signMassCoherence_eq_one_sub_twice_pos hPN hden

/-- Exact threshold equivalence for real-piece coherence.  Achieving a target `theta`
is equivalent to proving that the minority sign mass is at least `(1-theta)/2` of the
total mass. -/
theorem signMassCoherence_le_iff_minority_mass_ge {P N theta : ℝ}
    (hden : 0 < P + N) :
    signMassCoherence P N ≤ theta ↔ (1 - theta) * (P + N) / 2 ≤ min P N := by
  rw [signMassCoherence_eq_one_sub_twice_min hden]
  constructor
  · intro hcoh
    have hle : 1 - theta ≤ 2 * min P N / (P + N) := by linarith
    have hmul : (1 - theta) * (P + N) ≤ 2 * min P N := by
      exact (le_div_iff₀ hden).mp hle
    linarith
  · intro hminor
    have hmul : (1 - theta) * (P + N) ≤ 2 * min P N := by linarith
    have hle : 1 - theta ≤ 2 * min P N / (P + N) := by
      exact (le_div_iff₀ hden).mpr hmul
    linarith

/-- Equivalent operational corollary: if the minority sign mass is below an `eps/2`
fraction of total mass, then a real-piece coherence drop of size `eps` is impossible. -/
theorem not_coherence_le_one_sub_of_minority_mass_lt {P N eps : ℝ}
    (hden : 0 < P + N) (hminor : min P N < eps * (P + N) / 2) :
    ¬ signMassCoherence P N ≤ 1 - eps := by
  intro hcoh
  have hge := minority_mass_ge_of_coherence_le_one_sub hden hcoh
  linarith


/-- Exact strict-slack criterion for the real sign-mass compression: with nonnegative
sign masses and positive total mass, real coherence is strictly below `1` if and only if
the minority sign mass is positive. -/
theorem signMassCoherence_lt_one_iff_min_pos {P N : ℝ} (hden : 0 < P + N) :
    signMassCoherence P N < 1 ↔ 0 < min P N := by
  rw [signMassCoherence_eq_one_sub_twice_min hden]
  constructor
  · intro hlt
    have hpos : 0 < 2 * min P N / (P + N) := by linarith
    have hmul : 0 < 2 * min P N := by
      exact (div_pos_iff_of_pos_right hden).mp hpos
    have htwo : (0 : ℝ) < 2 := by norm_num
    exact (mul_pos_iff_of_pos_left htwo).mp hmul
  · intro hmin
    have hterm : 0 < 2 * min P N / (P + N) := by
      exact div_pos (mul_pos (by norm_num) hmin) hden
    linarith

/-- Zero minority sign mass is exactly the no-slack real Door-IV case. -/
theorem signMassCoherence_eq_one_of_min_eq_zero {P N : ℝ}
    (hden : 0 < P + N) (hmin : min P N = 0) :
    signMassCoherence P N = 1 := by
  rw [signMassCoherence_eq_one_sub_twice_min hden, hmin]
  ring

/-- Strict real sign-mass improvement below `1` forces both signs to be present with positive
mass.  In particular, any real/collinear Door-IV refinement with zero minority sign mass is
incapable of proving a threshold `theta < 1`. -/
theorem positive_sign_masses_of_coherence_lt_one_threshold {P N theta : ℝ}
    (hden : 0 < P + N) (htheta : theta < 1) (hcoh : signMassCoherence P N ≤ theta) :
    0 < P ∧ 0 < N := by
  have hminor_ge : (1 - theta) * (P + N) / 2 ≤ min P N :=
    (signMassCoherence_le_iff_minority_mass_ge (P := P) (N := N) (theta := theta) hden).1 hcoh
  have hminor_pos : 0 < min P N := by
    have htheta_pos : 0 < 1 - theta := by linarith
    have hleft : 0 < (1 - theta) * (P + N) / 2 := by
      exact div_pos (mul_pos htheta_pos hden) two_pos
    exact lt_of_lt_of_le hleft hminor_ge
  exact ⟨lt_of_lt_of_le hminor_pos (min_le_left P N),
    lt_of_lt_of_le hminor_pos (min_le_right P N)⟩

end ProximityGap.Frontier.DoorIVRealSignMassSlack

open ProximityGap.Frontier.DoorIVRealSignMassSlack

#print axioms signMassCoherence_eq_one_sub_twice_neg
#print axioms signMassCoherence_eq_one_sub_twice_pos
#print axioms signMassCoherence_le_one
#print axioms minority_mass_ge_of_coherence_le_one_sub
#print axioms signMassCoherence_eq_one_sub_twice_min
#print axioms signMassCoherence_le_iff_minority_mass_ge
#print axioms not_coherence_le_one_sub_of_minority_mass_lt
#print axioms signMassCoherence_lt_one_iff_min_pos
#print axioms signMassCoherence_eq_one_of_min_eq_zero
#print axioms positive_sign_masses_of_coherence_lt_one_threshold
