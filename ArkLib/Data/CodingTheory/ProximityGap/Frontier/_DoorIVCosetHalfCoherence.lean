/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Door IV coset-half coherence: the index-2 split has a sign-degeneracy

This file records the tiny axiom-clean arithmetic brick behind the probe
`scripts/probes/probe_dooriv_cosethalf_coherence.py`.

For the standard two-piece split of a 2-power subgroup `H = H₀ ⊔ hH₀`, each half is closed under
negation once `4 ∣ n`, so the two half-period sums are real.  Consequently the two-piece coherence

`ρ(A,B) = |A+B| / (|A|+|B|)`

has no intrinsic slack: whenever the two real half-sums have the same sign it is exactly `1`.
The probe finds such same-sign adversarial cosets throughout the thin prize regime.  This does not
prove CORE and does not use moments/completion; it is a constraint lemma saying that the **raw
index-2 coset-half coherence** is too degenerate to be the missing anti-concentration input unless
one refines the decomposition beyond two negation-stable halves.
-/

set_option linter.style.longLine false


namespace ProximityGap.Frontier.DoorIVCosetHalfCoherence

/-- Two-piece coherence of real half-period sums. -/
noncomputable def twoPieceCoherence (A B : ℝ) : ℝ := |A + B| / (|A| + |B|)

/-- If both real half-period sums are nonnegative and not both zero, their two-piece coherence is
exactly one.  This is the positive-sign half of the door-(iv) index-2 degeneracy. -/
theorem twoPieceCoherence_eq_one_of_nonneg {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hpos : 0 < A + B) :
    twoPieceCoherence A B = 1 := by
  unfold twoPieceCoherence
  rw [abs_of_nonneg hA, abs_of_nonneg hB, abs_of_nonneg (add_nonneg hA hB)]
  field_simp [ne_of_gt hpos]

/-- If both real half-period sums are nonpositive and not both zero, their two-piece coherence is
exactly one.  This is the negative-sign half of the door-(iv) index-2 degeneracy. -/
theorem twoPieceCoherence_eq_one_of_nonpos {A B : ℝ}
    (hA : A ≤ 0) (hB : B ≤ 0) (hneg : A + B < 0) :
    twoPieceCoherence A B = 1 := by
  unfold twoPieceCoherence
  have hA' : 0 ≤ -A := neg_nonneg.mpr hA
  have hB' : 0 ≤ -B := neg_nonneg.mpr hB
  have hsum' : 0 ≤ -(A + B) := le_of_lt (neg_pos.mpr hneg)
  rw [abs_of_nonpos hA, abs_of_nonpos hB, abs_of_nonpos (le_of_lt hneg)]
  have hden : -A + -B = -(A + B) := by ring
  rw [hden]
  exact div_self (ne_of_gt (neg_pos.mpr hneg))

/-- A compact same-sign formulation: if the two real half-sums are both nonnegative or both
nonpositive, and their total is nonzero, then their two-piece coherence is exactly one.  This is the
formal constraint used by the probe: once the two half-sums are forced onto the real line, same-sign
adversarial cosets saturate `ρ`. -/
theorem twoPieceCoherence_eq_one_of_sameSign {A B : ℝ}
    (hsign : (0 ≤ A ∧ 0 ≤ B) ∨ (A ≤ 0 ∧ B ≤ 0)) (hsum : A + B ≠ 0) :
    twoPieceCoherence A B = 1 := by
  rcases hsign with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact twoPieceCoherence_eq_one_of_nonneg hA hB
      (lt_of_le_of_ne (add_nonneg hA hB) hsum.symm)
  · exact twoPieceCoherence_eq_one_of_nonpos hA hB
      (lt_of_le_of_ne (add_nonpos hA hB) hsum)

/-- Opposite nonzero signs give strict slack in the real two-piece coherence.  Thus the only
possible saving in the raw index-2 split is a sign-cancellation event; magnitude imbalance alone
cannot produce a nontrivial door-(iv) theorem. -/
theorem twoPieceCoherence_lt_one_of_pos_neg {A B : ℝ}
    (hA : 0 < A) (hB : B < 0) :
    twoPieceCoherence A B < 1 := by
  unfold twoPieceCoherence
  rw [abs_of_pos hA, abs_of_neg hB]
  have hden : 0 < A + -B := by linarith
  have hnum_lt : |A + B| < A + -B := by
    rw [abs_lt]
    constructor <;> linarith
  calc
    |A + B| / (A + -B) < (A + -B) / (A + -B) :=
      div_lt_div_of_pos_right hnum_lt hden
    _ = 1 := div_self (ne_of_gt hden)


/-- Opposite-sign half-period sums compress exactly to the absolute imbalance ratio.  Writing the
positive half-mass as `P` and the negative half-mass as `N`, the raw index-2 coherence is
`|P-N|/(P+N)`. -/
theorem twoPieceCoherence_pos_neg_eq_abs_diff_ratio {P N : ℝ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) (_htotal : 0 < P + N) :
    twoPieceCoherence P (-N) = |P - N| / (P + N) := by
  unfold twoPieceCoherence
  rw [abs_of_nonneg hP, abs_of_nonpos (neg_nonpos.mpr hN)]
  ring_nf

/-- Exact opposite-sign slack for the raw coset-half split: the coherence is one minus twice the
minority half-mass fraction.  Thus an index-2 door-(iv) anti-concentration theorem must prove a
quantitative lower bound on the smaller of the positive and negative half-masses at the adversarial
frequency; opposite signs alone are not enough. -/
theorem abs_diff_ratio_eq_one_sub_two_mul_min_ratio {P N : ℝ}
    (_hP : 0 ≤ P) (_hN : 0 ≤ N) (htotal : 0 < P + N) :
    |P - N| / (P + N) = 1 - 2 * min P N / (P + N) := by
  have hden_ne : P + N ≠ 0 := ne_of_gt htotal
  by_cases hPN : P ≤ N
  · have hmin : min P N = P := min_eq_left hPN
    have habs : |P - N| = N - P := by
      rw [abs_of_nonpos (sub_nonpos.mpr hPN)]
      ring
    rw [hmin, habs]
    field_simp [hden_ne]
    ring
  · have hNP : N ≤ P := le_of_not_ge hPN
    have hmin : min P N = N := min_eq_right hNP
    have habs : |P - N| = P - N := by
      rw [abs_of_nonneg (sub_nonneg.mpr hNP)]
    rw [hmin, habs]
    field_simp [hden_ne]
    ring

/-- Bridged form of the exact index-2 slack identity for half-period sums `P` and `-N`. -/
theorem twoPieceCoherence_pos_neg_eq_one_sub_two_mul_min_ratio {P N : ℝ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) (htotal : 0 < P + N) :
    twoPieceCoherence P (-N) = 1 - 2 * min P N / (P + N) := by
  rw [twoPieceCoherence_pos_neg_eq_abs_diff_ratio hP hN htotal,
    abs_diff_ratio_eq_one_sub_two_mul_min_ratio hP hN htotal]


/-- Quantitative form of the exact index-2 slack identity.  For opposite-sign halves, obtaining a
uniform coherence saving `ε` is **equivalent** to proving that the minority half-mass contributes at
least an `ε/2` fraction of the total absolute half-mass.  This pins the remaining arithmetic content
of any raw coset-half door-(iv) lever to a minority-mass lower bound, rather than to the formal
index-2 decomposition itself. -/
theorem twoPieceCoherence_pos_neg_le_one_sub_iff {P N ε : ℝ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) (htotal : 0 < P + N) :
    twoPieceCoherence P (-N) ≤ 1 - ε ↔ ε ≤ 2 * min P N / (P + N) := by
  rw [twoPieceCoherence_pos_neg_eq_one_sub_two_mul_min_ratio hP hN htotal]
  constructor <;> intro h <;> linarith

/-- Denominator-cleared quantitative obstruction.  Since `P+N` is the total absolute mass of the
two half-sums in the opposite-sign case, a saving `ε` is equivalent to the concrete minority-mass
inequality `ε*(P+N) ≤ 2*min(P,N)`.  This is the form useful for probes: the raw coset-half split can
only beat `1` when the smaller signed half carries a proportional share of the mass. -/
theorem twoPieceCoherence_pos_neg_le_one_sub_iff_min_mass {P N ε : ℝ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) (htotal : 0 < P + N) :
    twoPieceCoherence P (-N) ≤ 1 - ε ↔ ε * (P + N) ≤ 2 * min P N := by
  rw [twoPieceCoherence_pos_neg_le_one_sub_iff hP hN htotal]
  exact le_div_iff₀ htotal

/-- Strict quantitative form of the same constraint: strict coherence saving is exactly strict
minority-mass participation. -/
theorem twoPieceCoherence_pos_neg_lt_one_sub_iff {P N ε : ℝ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) (htotal : 0 < P + N) :
    twoPieceCoherence P (-N) < 1 - ε ↔ ε < 2 * min P N / (P + N) := by
  rw [twoPieceCoherence_pos_neg_eq_one_sub_two_mul_min_ratio hP hN htotal]
  constructor <;> intro h <;> linarith

/-- Strict denominator-cleared obstruction.  A strict saving by `ε` is exactly the strict
minority-mass inequality `ε*(P+N) < 2*min(P,N)`.  This is the probe-facing strict counterpart to
the non-strict cleared form: below this mass threshold, the raw index-2 split cannot certify a
strict door-(iv) coherence drop. -/
theorem twoPieceCoherence_pos_neg_lt_one_sub_iff_min_mass {P N ε : ℝ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) (htotal : 0 < P + N) :
    twoPieceCoherence P (-N) < 1 - ε ↔ ε * (P + N) < 2 * min P N := by
  rw [twoPieceCoherence_pos_neg_lt_one_sub_iff hP hN htotal]
  exact lt_div_iff₀ htotal

/-- Symmetric opposite-sign slack. -/
theorem twoPieceCoherence_lt_one_of_neg_pos {A B : ℝ}
    (hA : A < 0) (hB : 0 < B) :
    twoPieceCoherence A B < 1 := by
  unfold twoPieceCoherence
  rw [abs_of_neg hA, abs_of_pos hB]
  have hden : 0 < -A + B := by linarith
  have hnum_lt : |A + B| < -A + B := by
    rw [abs_lt]
    constructor <;> linarith
  calc
    |A + B| / (-A + B) < (-A + B) / (-A + B) :=
      div_lt_div_of_pos_right hnum_lt hden
    _ = 1 := div_self (ne_of_gt hden)

end ProximityGap.Frontier.DoorIVCosetHalfCoherence

#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_eq_one_of_nonneg
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_eq_one_of_nonpos
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_eq_one_of_sameSign
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_lt_one_of_pos_neg
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_lt_one_of_neg_pos
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_pos_neg_eq_abs_diff_ratio
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.abs_diff_ratio_eq_one_sub_two_mul_min_ratio
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_pos_neg_eq_one_sub_two_mul_min_ratio
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_pos_neg_le_one_sub_iff
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_pos_neg_le_one_sub_iff_min_mass
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_pos_neg_lt_one_sub_iff
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_pos_neg_lt_one_sub_iff_min_mass
