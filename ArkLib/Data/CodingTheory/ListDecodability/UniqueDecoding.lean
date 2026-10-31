/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# List size within the unique-decoding radius

Adapted from ArkLib main `35ddcaa83f683011f944f58904be779495a5709a`, using the native
natural-cardinality list-size definition. The proof first establishes that every
point list is a subsingleton; no finiteness assumption on the alphabet is needed.
-/

namespace ListDecodable

/-- Every point list within the relative unique-decoding radius has at most one word. -/
theorem Lambda_le_one_of_le_relativeUniqueDecodingRadius
    {ι F : Type*} [Fintype ι] [DecidableEq F]
    (C : Set (ι → F)) {r : ℝ} (hr : r ≤ (Code.relativeUniqueDecodingRadius C : ℝ)) :
    Lambda C r ≤ 1 := by
  classical
  refine iSup_le fun y => ?_
  have hsub : (closeCodewordsRel C y r).Subsingleton := by
    intro c hc c' hc'
    rcases isEmpty_or_nonempty ι with _ | _
    · exact Subsingleton.elim c c'
    · have key : ∀ z : ι → F, z ∈ closeCodewordsRel C y r →
          hammingDist y z ≤ Code.uniqueDecodingRadius C := by
        intro z hz
        have h2 : ((hammingDist y z : NNReal) / (Fintype.card ι : NNReal))
            ≤ Code.relativeUniqueDecodingRadius C := by
          have hmem : (Code.relHammingDist y z : ℝ) ≤ r := by
            simpa only [relHammingBall, Set.mem_ofPred_eq, Code.relHammingDist,
              hammingDist] using hz.2
          have hle := hmem.trans hr
          simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast] at hle
          rw [← NNReal.coe_le_coe]
          push_cast
          exact hle
        exact (Code.dist_le_UDR_iff_relDist_le_relUDR C (hammingDist y z)).mpr h2
      exact Code.eq_of_le_uniqueDecodingRadius C y hc.1 hc'.1 (key c hc) (key c' hc')
  exact_mod_cast (Set.ncard_le_one hsub.finite).mpr (fun _ ha _ hb => hsub ha hb)

end ListDecodable
