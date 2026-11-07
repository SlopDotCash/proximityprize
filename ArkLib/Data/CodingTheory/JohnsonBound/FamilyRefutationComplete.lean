/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ProximityPrize.Extensions.Data.CodingTheory.JohnsonBound.Family

/-!
# Three-word Johnson-radius regression fixture

The former refutation used an obsolete `Jqℓ` definition with factor `ℓ/(ℓ-1)`.
Canonical upstream corrects that factor to `(ℓ-1)/ℓ` and proves
`CodingTheory.johnson_bound_lambda_le_ell`. At `q = ℓ = 2`, `δ = 1/2`, the corrected
radius is `(1 - sqrt (1/2)) / 2`, strictly smaller than `1/2`.

The three-word code, its minimum distance, and its large list at radius `1/2` remain valid
and are retained below. They do not refute the corrected radius. The obsolete radius equality
and inconsistency claims are retired in `scripts/integration/johnson-radius-retirement.json`.
The historical module path and namespace remain for clients of the valid finite-code facts.
-/

set_option linter.unusedSectionVars false

namespace JohnsonBound.JqlRefutation

open ListDecodable JohnsonBound Code

/-- The refuting alphabet/index types: `ι = α = Fin 2` (so `n = 2`, `q = 2`). -/
abbrev ι : Type := Fin 2
abbrev α : Type := Fin 2

/-- The three codewords. -/
def c0 : ι → α := ![0, 0]
def c1 : ι → α := ![0, 1]
def c2 : ι → α := ![1, 0]

/-- The explicit refuting code `C = { ![0,0], ![0,1], ![1,0] }`. -/
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

/-- `card ι = 2`. -/
theorem card_ι : Fintype.card ι = 2 := by decide

/-- **`Code.minDist C = 1`.**  The defining set of distinct-pair distances is `{1, 2}`
(`d(c0,c1) = d(c0,c2) = 1`, `d(c1,c2) = 2`), and every distinct pair has distance `≥ 1`. -/
theorem minDist_C : Code.minDist C = 1 := by
  apply le_antisymm
  · -- `minDist C ≤ 1`: `1` is in the defining set, witnessed by the pair `(c0, c1)`.
    refine Nat.sInf_le ⟨c0, (mem_C_iff c0).mpr (Or.inl rfl), c1,
      (mem_C_iff c1).mpr (Or.inr (Or.inl rfl)), c0_ne_c1, ham_c0_c1⟩
  · -- `1 ≤ minDist C`: every distinct pair `(u, v)` has `hammingDist u v ≥ 1`.
    refine le_csInf ⟨1, ⟨c0, (mem_C_iff c0).mpr (Or.inl rfl), c1,
      (mem_C_iff c1).mpr (Or.inr (Or.inl rfl)), c0_ne_c1, ham_c0_c1⟩⟩ ?_
    rintro d ⟨u, _, v, _, huv, rfl⟩
    exact Nat.one_le_iff_ne_zero.mpr (by simpa [hammingDist_eq_zero] using huv)

/-- **Ball membership (canonical instance).**  Every codeword lies within relative distance
`1/2` of `c0` (distances `0, 1/2, 1/2`).  Stated with the ambient (canonical `Fin 2`)
`DecidableEq` instance, under which the `Fin 2` Hamming-distance facts compute. -/
theorem relDist_le_half (c : ι → α) (hc : c = c0 ∨ c = c1 ∨ c = c2) :
    ((Code.relHammingDist c0 c : ℚ≥0) : ℝ) ≤ (1 / 2 : ℝ) := by
  rcases hc with rfl | rfl | rfl
  · -- distance `0`
    have h0 : Code.relHammingDist c0 c0 = 0 := by
      rw [Code.relHammingDist, hammingDist_self]; simp
    rw [h0]; norm_num
  · -- distance `1/2`
    have h1 : Code.relHammingDist c0 c1 = 1 / 2 := by
      rw [Code.relHammingDist, ham_c0_c1, card_ι]; norm_num
    rw [h1]; push_cast; norm_num
  · -- distance `1/2`
    have h2 : Code.relHammingDist c0 c2 = 1 / 2 := by
      rw [Code.relHammingDist, ham_c0_c2, card_ι]; norm_num
    rw [h2]; push_cast; norm_num

/-- **The ball of radius `1/2` about `c0` is the whole code:** `closeCodewordsRel C c0 (1/2) = C`.

`relHammingBall` is defined with `open Classical`, so the membership predicate carries the
`Classical.propDecidable` instance; `DecidableEq (Fin 2)` is a subsingleton, so we transport
to the canonical instance (under which `relDist_le_half` is stated) by `Subsingleton.elim`. -/
theorem closeCodewordsRel_eq_C :
    ListDecodable.closeCodewordsRel C c0 (1 / 2 : ℝ) = C := by
  ext c
  simp only [ListDecodable.closeCodewordsRel, ListDecodable.relHammingBall, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcC, _⟩; exact hcC
  · intro hcC
    refine ⟨hcC, ?_⟩
    -- the ball's (classical) `relHammingDist` instance is a subsingleton-equal to the
    -- canonical one used by `relDist_le_half`; bridge with `Subsingleton.elim`.
    have hkey := relDist_le_half c ((mem_C_iff c).mp hcC)
    convert hkey using 3

/-- The refuting code has exactly three codewords. -/
theorem ncard_C : C.ncard = 3 := by
  rw [C, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_singleton]
  · simp only [Set.mem_singleton_iff]; exact c1_ne_c2
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨c0_ne_c1, c0_ne_c2⟩

/-- **`Λ(C, 1/2) ≥ 3`.**  The point-list at the centre `c0` is all of `C` (`ncard = 3`), and
`Lambda` is the supremum over centres. -/
theorem three_le_Lambda : (3 : ℕ∞) ≤ ListDecodable.Lambda C (1 / 2 : ℝ) := by
  have hpt : ((ListDecodable.closeCodewordsRel C c0 (1 / 2 : ℝ)).ncard : ℕ∞) ≤ ListDecodable.Lambda C (1 / 2 : ℝ) :=
    le_iSup (fun f : ι → α => ((ListDecodable.closeCodewordsRel C f (1 / 2 : ℝ)).ncard : ℕ∞)) c0
  rwa [closeCodewordsRel_eq_C, ncard_C] at hpt

/-- The corrected canonical radius for this binary fixture. -/
theorem corrected_Jqℓ_value :
    Jqℓ (2 : ℚ) (2 : ℚ) ((1 : ℚ) / 2) = (1 - Real.sqrt (1 / 2)) / 2 := by
  norm_num [Jqℓ, JohnsonBound.J]
  ring

/-- The corrected radius lies below the radius of the large-list fixture. -/
theorem corrected_Jqℓ_lt_half :
    Jqℓ (2 : ℚ) (2 : ℚ) ((1 : ℚ) / 2) < (1 / 2 : ℝ) := by
  rw [corrected_Jqℓ_value]
  have hpos : 0 < Real.sqrt (1 / 2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  linarith

/-- The canonical Johnson theorem holds at its corrected radius for this code. -/
theorem corrected_johnson_bound :
    Code.Lambda C
      (Jqℓ (Fintype.card α : ℚ) 2 ((Code.minDist C : ℚ) / Fintype.card ι)) ≤
      (2 : ℕ∞) :=
  CodingTheory.johnson_bound_lambda_le_ell C 2 (by decide)

#print axioms three_le_Lambda
#print axioms minDist_C
#print axioms corrected_Jqℓ_value
#print axioms corrected_Jqℓ_lt_half
#print axioms corrected_johnson_bound

end JohnsonBound.JqlRefutation
