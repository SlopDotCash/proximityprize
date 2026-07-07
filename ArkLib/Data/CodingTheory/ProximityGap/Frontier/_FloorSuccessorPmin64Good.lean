/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorClosureContract
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._FloorLinnikRungInstances

/-!
# The `p_min(64)` good certificate kills singleton floor-successor exactness

The July 2026 FS1 meet-in-the-middle scan found that `193 = p_min(64)` is **not** floor-bad
for the real adjacent-realizability floor predicate.  The scan result itself is external; this
file supplies the Lean socket that consumes such a certificate:

* the candidate selected by `CandidateListExactAt _ 6` is exactly `193`;
* therefore a certificate `¬ FloorBad 64 193` refutes the exact singleton list at rung `a = 6`;
* consequently the uniform singleton-family hypothesis needed by the old floor-successor lane
  is false under that certificate.

This is a contract theorem, not a proof of the external scan.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.FloorSuccessorPmin64Good

open ArkLib.ProximityGap.Frontier.FloorLocalization
open ArkLib.ProximityGap.Frontier.FloorClosureContract
open ArkLib.ProximityGap.Frontier.FloorLinnikRung

/-- The least prime `≡ 1 mod 64` under the `2^(5*6)` search bound is `193`.
This avoids evaluating the huge range by using the witness characterization. -/
theorem smallestPrime1ModN_64_pow30_eq_193 :
    smallestPrime1ModN (2 ^ 6) (2 ^ (5 * 6)) = 193 := by
  apply smallestPrime1ModN_eq_of_witness
  · norm_num
  · norm_num
  · norm_num
  · intro m hm
    interval_cases m <;>
    decide

/-- If the exact scanner certifies that `193 = p_min(64)` is not floor-bad, then the singleton
candidate-list exactness statement at rung `a = 6` is false. -/
theorem not_candidateListExactAt_six_of_pmin64_good
    (FloorBad : ℕ → ℕ → Prop) (hgood193 : ¬ FloorBad 64 193) :
    ¬ CandidateListExactAt FloorBad 6 := by
  intro hexact
  have hex : CandidateListExactInAP FloorBad (2 ^ 6)
      [smallestPrime1ModN (2 ^ 6) (2 ^ (5 * 6))] := hexact
  rw [smallestPrime1ModN_64_pow30_eq_193] at hex
  have hbad193 : FloorBad 64 193 := by
    have hiff := hex 193 (by norm_num) (by norm_num)
    exact hiff.mpr (by simp)
  exact hgood193 hbad193

/-- The same `p_min(64)` good certificate refutes the uniform singleton-family exactness input
needed by the old floor-localization successor lane. -/
theorem not_candidateListExactSmallestFamily_of_pmin64_good
    (FloorBad : ℕ → ℕ → Prop) (hgood193 : ¬ FloorBad 64 193) :
    ¬ CandidateListExactSmallestFamily FloorBad :=
  not_candidateListExactSmallestFamily_of_next_failure FloorBad (a := 5) (by norm_num)
    (not_candidateListExactAt_six_of_pmin64_good FloorBad hgood193)

/-- In the presence of an exact rung-five certificate, the `p_min(64)` good certificate also
refutes the successor step itself.  This is the adjacent-rung normal form of the FS1 result. -/
theorem not_candidateListExactSuccessor_of_five_exact_and_pmin64_good
    (FloorBad : ℕ → ℕ → Prop)
    (hexact5 : CandidateListExactAt FloorBad 5)
    (hgood193 : ¬ FloorBad 64 193) :
    ¬ CandidateListExactSuccessor FloorBad :=
  (not_candidateListExactSuccessor_iff_exists_exact_rung_next_fails FloorBad).mpr
    ⟨5, by norm_num, hexact5,
      not_candidateListExactAt_six_of_pmin64_good FloorBad hgood193⟩

#print axioms smallestPrime1ModN_64_pow30_eq_193
#print axioms not_candidateListExactAt_six_of_pmin64_good
#print axioms not_candidateListExactSmallestFamily_of_pmin64_good
#print axioms not_candidateListExactSuccessor_of_five_exact_and_pmin64_good

end ArkLib.ProximityGap.Frontier.FloorSuccessorPmin64Good
