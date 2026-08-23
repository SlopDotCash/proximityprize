/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVRealPieceCoherence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVRealSignMassSlack

/-!
# Door IV real-piece compression: finer real refinements add only sign mass

The multiplicative-coset refinement probes for the localized door-(iv) object found that, at the
adversarial frequency, many finer piece decompositions remain collinear on the real axis.  This file
records the exact bookkeeping consequence: once a real refinement is compressed to total positive
mass `P` and total negative mass `N`, its normalized list coherence is literally the two-mass
coherence `|P-N|/(P+N)` from `_DoorIVRealSignMassSlack`.

Therefore a finer real/collinear refinement contributes no new angular degree of freedom.  Any
claimed `rho <= theta` theorem for such pieces is exactly equivalent to proving a lower bound on the
minority sign mass.  This is a Door-IV constraint lemma only: no Gauss-period cancellation, no CORE
bound, no moment/completion route.
-/

namespace ProximityGap.Frontier.DoorIVRealPieceCompression

open ProximityGap.Frontier.DoorIVRealPieceCoherence
open ProximityGap.Frontier.DoorIVRealSignMassSlack

/-- If a real piece list compresses to positive mass `P` and negative mass `N`, then its list
coherence is exactly the sign-mass coherence.  The hypotheses are intentionally just the two
compression identities, so future probes/formalizations can plug in any concrete positive/negative
partition without reopening triangle-inequality arguments. -/
theorem realPieceCoherence_eq_signMassCoherence_of_compression {xs : List ℝ} {P N : ℝ}
    (hsum : xs.sum = P - N) (habssum : (xs.map abs).sum = P + N) :
    realPieceCoherence xs = signMassCoherence P N := by
  unfold realPieceCoherence signMassCoherence
  rw [hsum, habssum]

/-- Threshold form of the compression lemma.  For any real/collinear refinement that has been
compressed to sign masses `P,N`, a target `theta` is equivalent to the minority-sign-mass lower
bound `(1-theta)(P+N)/2 <= min P N`.  Thus the only possible saving in a real refinement is a
balanced sign split, not extra angular anti-concentration. -/
theorem realPieceCoherence_le_iff_minority_mass_ge_of_compression {xs : List ℝ} {P N theta : ℝ}
    (hsum : xs.sum = P - N) (habssum : (xs.map abs).sum = P + N) (hden : 0 < P + N) :
    realPieceCoherence xs ≤ theta ↔ (1 - theta) * (P + N) / 2 ≤ min P N := by
  rw [realPieceCoherence_eq_signMassCoherence_of_compression (xs := xs) (P := P) (N := N)
      hsum habssum]
  exact signMassCoherence_le_iff_minority_mass_ge (P := P) (N := N) (theta := theta) hden

/-- Operational obstruction: if the minority sign mass is below an `eps/2` fraction of the total
compressed mass, then the compressed real refinement cannot prove a `1-eps` coherence drop. -/
theorem not_realPieceCoherence_le_one_sub_of_minority_mass_lt_of_compression {xs : List ℝ}
    {P N eps : ℝ} (hsum : xs.sum = P - N) (habssum : (xs.map abs).sum = P + N)
    (hden : 0 < P + N) (hminor : min P N < eps * (P + N) / 2) :
    ¬ realPieceCoherence xs ≤ 1 - eps := by
  rw [realPieceCoherence_eq_signMassCoherence_of_compression (xs := xs) (P := P) (N := N)
      hsum habssum]
  exact not_coherence_le_one_sub_of_minority_mass_lt (P := P) (N := N) (eps := eps) hden hminor

/-- Compressed real-piece consumer: any strict threshold below `1` forces both compressed sign
masses to be positive.  So a collinear refinement with only one sign, or with zero minority mass,
cannot be the source of a Door-IV coherence drop. -/
theorem positive_sign_masses_of_realPieceCoherence_lt_one_threshold_of_compression {xs : List ℝ}
    {P N theta : ℝ} (hsum : xs.sum = P - N) (habssum : (xs.map abs).sum = P + N)
    (hden : 0 < P + N) (htheta : theta < 1) (hcoh : realPieceCoherence xs ≤ theta) :
    0 < P ∧ 0 < N := by
  have hminor_ge : (1 - theta) * (P + N) / 2 ≤ min P N :=
    (realPieceCoherence_le_iff_minority_mass_ge_of_compression (xs := xs) (P := P) (N := N)
      (theta := theta) hsum habssum hden).1 hcoh
  have hminor_pos : 0 < min P N := by
    have htheta_pos : 0 < 1 - theta := by linarith
    have hleft : 0 < (1 - theta) * (P + N) / 2 := by
      exact div_pos (mul_pos htheta_pos hden) two_pos
    exact lt_of_lt_of_le hleft hminor_ge
  exact ⟨lt_of_lt_of_le hminor_pos (min_le_left P N),
    lt_of_lt_of_le hminor_pos (min_le_right P N)⟩

/-- **Compressed strict-slack criterion.**  A compressed real refinement has list coherence strictly
below `1` if and only if its minority sign mass is positive.  Transports the two-mass criterion
`signMassCoherence_lt_one_iff_min_pos` to the list level under compression. -/
theorem realPieceCoherence_lt_one_iff_min_pos_of_compression {xs : List ℝ} {P N : ℝ}
    (hsum : xs.sum = P - N) (habssum : (xs.map abs).sum = P + N) (hden : 0 < P + N) :
    realPieceCoherence xs < 1 ↔ 0 < min P N := by
  rw [realPieceCoherence_eq_signMassCoherence_of_compression (xs := xs) (P := P) (N := N)
      hsum habssum]
  exact signMassCoherence_lt_one_iff_min_pos (P := P) (N := N) hden

/-- A compressed real refinement with zero minority sign mass has no slack: coherence is exactly
`1`.  Hence a single-sign collinear refinement cannot be the source of a Door-IV coherence drop. -/
theorem realPieceCoherence_eq_one_of_min_eq_zero_of_compression {xs : List ℝ} {P N : ℝ}
    (hsum : xs.sum = P - N) (habssum : (xs.map abs).sum = P + N) (hden : 0 < P + N)
    (hmin : min P N = 0) :
    realPieceCoherence xs = 1 := by
  rw [realPieceCoherence_eq_signMassCoherence_of_compression (xs := xs) (P := P) (N := N)
      hsum habssum]
  exact signMassCoherence_eq_one_of_min_eq_zero (P := P) (N := N) hden hmin

/-- **Compressed slack forces a positive minority mass AND genuine list-level sign mixing.**  This
binds the two views: a compressed real refinement with positive total mass and nonzero signed sum
that achieves coherence below `1` has strictly positive minority sign mass `min P N`, and the
underlying piece list contains BOTH a strictly positive and a strictly negative entry.  The signed
sum being nonzero is derived from the compression identity `xs.sum = P - N` together with `P ≠ N`
(equivalently the slack itself), so the hypotheses are exactly the compression data plus the slack. -/
theorem min_pos_and_both_signs_of_realPieceCoherence_lt_one_of_compression {xs : List ℝ} {P N : ℝ}
    (hsum : xs.sum = P - N) (habssum : (xs.map abs).sum = P + N) (hden : 0 < P + N)
    (hsumne : xs.sum ≠ 0) (hcoh : realPieceCoherence xs < 1) :
    0 < min P N ∧ (∃ x ∈ xs, 0 < x) ∧ (∃ x ∈ xs, x < 0) := by
  refine ⟨?_, realPieceCoherence_lt_one_forces_both_signs hsumne hcoh⟩
  exact (realPieceCoherence_lt_one_iff_min_pos_of_compression hsum habssum hden).1 hcoh

end ProximityGap.Frontier.DoorIVRealPieceCompression

open ProximityGap.Frontier.DoorIVRealPieceCompression

#print axioms realPieceCoherence_eq_signMassCoherence_of_compression
#print axioms realPieceCoherence_le_iff_minority_mass_ge_of_compression
#print axioms not_realPieceCoherence_le_one_sub_of_minority_mass_lt_of_compression
#print axioms positive_sign_masses_of_realPieceCoherence_lt_one_threshold_of_compression
#print axioms realPieceCoherence_lt_one_iff_min_pos_of_compression
#print axioms realPieceCoherence_eq_one_of_min_eq_zero_of_compression
#print axioms min_pos_and_both_signs_of_realPieceCoherence_lt_one_of_compression
