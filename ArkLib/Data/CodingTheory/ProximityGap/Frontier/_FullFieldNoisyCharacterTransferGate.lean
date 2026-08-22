/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Full-field noisy-character transfer gate

Recent noisy-character/polynomial-recovery results work over the whole field: their hypotheses are
global agreement or sample-density statements over `F_q`.  The #464 object is different.  It gives
values only on the thin subgroup `mu_n`, whose field density is `n/q`.

At the prize/Burgess scale `q >= n^4`, that density is at most `n^-3`.  Thus a full-field theorem
whose consumer requires agreement density `tau` cannot be triggered from perfect information on
`mu_n` unless `tau <= n/q <= n^-3`.  The degree side may be fine (`d <= n <= sqrt q`), but the
global-density side is the transfer failure.

This file proves only that arithmetic gate.  It does not assume any recovery theorem and it does
not prove any character-sum cancellation.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.FullFieldNoisyCharacterTransferGate

/-- Density of an `n`-point subgroup inside a field of size `q`. -/
noncomputable def subgroupDensity (n q : ℝ) : ℝ :=
  n / q

/-- The degree condition of a full-field theorem can be harmless at prize scale: if the relevant
degree is at most the subgroup size and `q >= n^2`, then it is at most `sqrt q`. -/
theorem degree_le_sqrtField_of_le_subgroup {d n q : ℝ}
    (hd : d ≤ n) (hn : 0 ≤ n) (hq : n ^ 2 ≤ q) :
    d ≤ Real.sqrt q := by
  calc
    d ≤ n := hd
    _ = Real.sqrt (n ^ 2) := by rw [Real.sqrt_sq hn]
    _ ≤ Real.sqrt q := Real.sqrt_le_sqrt hq

/-- Exact beta-four identity: if `q = n^4`, then subgroup density is `n^-3`. -/
theorem subgroupDensity_eq_invCube_at_beta_four {n q : ℝ}
    (hn : n ≠ 0) (hq : q = n ^ 4) :
    subgroupDensity n q = 1 / n ^ 3 := by
  subst q
  unfold subgroupDensity
  field_simp [hn]

/-- Prize-scale density ceiling: for `q >= n^4`, the subgroup occupies at most `n^-3` of the
field. -/
theorem subgroupDensity_le_invCube_of_prize {n q : ℝ}
    (hn : 0 < n) (hprize : n ^ 4 ≤ q) :
    subgroupDensity n q ≤ 1 / n ^ 3 := by
  unfold subgroupDensity
  have hn4pos : 0 < n ^ 4 := by positivity
  have hqpos : 0 < q := lt_of_lt_of_le hn4pos hprize
  have hcoef : 0 ≤ 1 / n ^ 3 := by positivity
  have hmul : (1 / n ^ 3) * n ^ 4 ≤ (1 / n ^ 3) * q :=
    mul_le_mul_of_nonneg_left hprize hcoef
  have hleft : (1 / n ^ 3) * n ^ 4 = n := by
    field_simp [ne_of_gt hn]
  have hnle : n ≤ (1 / n ^ 3) * q := by
    calc
      n = (1 / n ^ 3) * n ^ 4 := hleft.symm
      _ ≤ (1 / n ^ 3) * q := hmul
  exact (div_le_iff₀ hqpos).2 hnle

/-- If all information is supported on the subgroup, then any full-field threshold above the
subgroup density cannot be certified.  `globalAgreement` is an abstract full-field agreement
quantity; the hypothesis says the subgroup-supported data can certify at most density `n/q`. -/
theorem fullField_threshold_impossible_of_sparse_support
    {tau globalAgreement n q : ℝ}
    (hglobal : globalAgreement ≤ subgroupDensity n q)
    (hdensity : subgroupDensity n q < tau) :
    ¬ tau ≤ globalAgreement := by
  intro hthreshold
  exact (not_lt_of_ge (le_trans hthreshold hglobal)) hdensity

/-- Prize-scale version: if the required full-field agreement threshold is above `n^-3`, then
perfect subgroup-supported data cannot trigger that theorem. -/
theorem fullField_threshold_misses_prize
    {tau globalAgreement n q : ℝ}
    (hn : 0 < n) (hprize : n ^ 4 ≤ q)
    (hglobal : globalAgreement ≤ subgroupDensity n q)
    (htau : 1 / n ^ 3 < tau) :
    ¬ tau ≤ globalAgreement := by
  have hdensity : subgroupDensity n q < tau :=
    lt_of_le_of_lt (subgroupDensity_le_invCube_of_prize hn hprize) htau
  exact fullField_threshold_impossible_of_sparse_support hglobal hdensity

/-- Packaged transfer gate.  At prize scale, a full-field theorem may pass its degree hypothesis
while still being unusable because the available values live on density at most `n^-3`. -/
theorem fullField_noisyCharacter_transfer_gate
    {d n q tau globalAgreement : ℝ}
    (hd : d ≤ n) (hn : 0 < n) (hq2 : n ^ 2 ≤ q) (hprize : n ^ 4 ≤ q)
    (hglobal : globalAgreement ≤ subgroupDensity n q)
    (htau : 1 / n ^ 3 < tau) :
    d ≤ Real.sqrt q ∧ ¬ tau ≤ globalAgreement := by
  exact ⟨degree_le_sqrtField_of_le_subgroup hd hn.le hq2,
    fullField_threshold_misses_prize hn hprize hglobal htau⟩

#print axioms degree_le_sqrtField_of_le_subgroup
#print axioms subgroupDensity_eq_invCube_at_beta_four
#print axioms subgroupDensity_le_invCube_of_prize
#print axioms fullField_threshold_impossible_of_sparse_support
#print axioms fullField_threshold_misses_prize
#print axioms fullField_noisyCharacter_transfer_gate

end ArkLib.ProximityGap.Frontier.FullFieldNoisyCharacterTransferGate
