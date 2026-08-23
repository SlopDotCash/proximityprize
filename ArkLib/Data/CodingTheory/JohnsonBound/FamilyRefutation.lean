/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.JohnsonBound.Family

/-!
# Johnson-bound statement-level witness data

This file records the concrete three-word binary code used to audit
`johnson_bound_lambda_le_ell`.  The full Lambda contradiction is intentionally not asserted here:
the current kernel-clean artifact is the finite witness and its minimum-distance computation.
The *complete* machine-checked refutation (the `Λ ≥ 3 > 2 = ℓ` contradiction and the
inconsistency implication) lives in `FamilyRefutationComplete.lean`; see disposition
`docs/kb/audits/proximity-prize/dispositions/issue-49-johnson-family.md` (lalalune/ArkLib#49).
-/

set_option linter.unusedSectionVars false

namespace JohnsonBound.FamilyRefutation

open ListDecodable JohnsonBound Code

/-- The refuting alphabet/index types: `ι = α = Fin 2` (so `n = 2`, `q = 2`). -/
abbrev ι : Type := Fin 2
abbrev α : Type := Fin 2

/-- The three codewords. -/
def c0 : ι → α := ![0, 0]
def c1 : ι → α := ![0, 1]
def c2 : ι → α := ![1, 0]

/-- The explicit three-word code `C = { ![0,0], ![0,1], ![1,0] }`. -/
def C : Set (ι → α) := {c0, c1, c2}

/-- The three codewords are pairwise distinct. -/
theorem c0_ne_c1 : c0 ≠ c1 := by decide
theorem c0_ne_c2 : c0 ≠ c2 := by decide
theorem c1_ne_c2 : c1 ≠ c2 := by decide

/-- Pairwise Hamming distances. -/
theorem ham_c0_c1 : hammingDist c0 c1 = 1 := by decide
theorem ham_c0_c2 : hammingDist c0 c2 = 1 := by decide
theorem ham_c1_c2 : hammingDist c1 c2 = 2 := by decide

/-- Membership in `C` is membership in the explicit three-element set. -/
theorem mem_C_iff (x : ι → α) : x ∈ C ↔ x = c0 ∨ x = c1 ∨ x = c2 := by
  simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- Every distinct pair of codewords has Hamming distance `≥ 1`, and the pair
`(c0, c1)` attains `1`. Hence `Code.minDist C = 1`. -/
theorem minDist_C : Code.minDist C = 1 := by
  apply le_antisymm
  · refine Nat.sInf_le ?_
    refine ⟨c0, ?_, c1, ?_, c0_ne_c1, ham_c0_c1⟩
    · exact (mem_C_iff c0).mpr (Or.inl rfl)
    · exact (mem_C_iff c1).mpr (Or.inr (Or.inl rfl))
  · refine le_csInf ⟨1, ⟨c0, (mem_C_iff c0).mpr (Or.inl rfl), c1,
      (mem_C_iff c1).mpr (Or.inr (Or.inl rfl)), c0_ne_c1, ham_c0_c1⟩⟩ ?_
    rintro d ⟨u, _, v, _, huv, rfl⟩
    exact Nat.one_le_iff_ne_zero.mpr (by simpa [hammingDist_eq_zero] using huv)

end JohnsonBound.FamilyRefutation
