/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly

/-!
# Subspace polynomial of a disjoint union

`subspacePoly (⊔ⱼ Lⱼ) = ∏ⱼ subspacePoly Lⱼ` for a pairwise-disjoint family of root finsets.
A char-free identity (`subspacePoly L = ∏_{ℓ∈L}(X - C ℓ)` and `Finset.prod_biUnion`), the
combinatorial ingredient of the subspace-polynomial recursion (grouping the roots of
`V = V' ⊕ 𝔽_q·u` into the `|F|` disjoint cosets `V' + c·u`).
-/

open Polynomial BigOperators

namespace BKR06

variable {K : Type*} [Field K]

/-- **Subspace polynomial of a disjoint union.** For a pairwise-disjoint family `t : ι → Finset K`
indexed by `s`, `subspacePoly (s.biUnion t) = ∏_{c ∈ s} subspacePoly (t c)`. -/
theorem subspacePoly_biUnion {ι : Type*} [DecidableEq ι] [DecidableEq K]
    (s : Finset ι) (t : ι → Finset K) (h : (s : Set ι).PairwiseDisjoint t) :
    subspacePoly (s.biUnion t) = ∏ c ∈ s, subspacePoly (t c) := by
  unfold subspacePoly
  rw [Finset.prod_biUnion h]

end BKR06

-- Axiom audit.
#print axioms BKR06.subspacePoly_biUnion
