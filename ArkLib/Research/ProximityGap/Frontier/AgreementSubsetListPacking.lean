/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ListDecodability.SampleIncidence
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved

/-!
# Sample packing for interleaved Reed–Solomon lists

Distinct interleaved codewords cannot both agree with a received word on the same
`k` coordinates. A list member with `t` agreements uses at least `t.choose k` of
the `n.choose k` available samples. The radius condition below keeps the whole
open interval up to the next Hamming-distance step.
-/

namespace ProximityGap.AgreementSubsetListPacking

open Code

/-- Every interleaved Reed–Solomon list at a radius forcing at least `t ≥ k`
agreements has size at most `n.choose k / t.choose k`, over any field. -/
theorem interleaved_lambda_le_choose_div {ι F : Type*} [Fintype ι] [Nonempty ι] [Field F]
    (D : ι ↪ F) (k t arity : ℕ) (δ : ℝ) (hkt : k ≤ t)
    (hδ : δ * (Fintype.card ι : ℝ) < (Fintype.card ι : ℝ) - t + 1) :
    Lambda (interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D k : Set (ι → F))) δ ≤
      ((Fintype.card ι).choose k / t.choose k : ℕ) := by
  classical
  let C := interleavedCodeSet (κ := Fin arity) (ReedSolomon.code D k : Set (ι → F))
  apply Lambda_le_iff_forall_ncard_le.mpr
  intro y
  obtain ⟨hfin, hpack⟩ := agreement_set_finite_and_ncard_mul_choose_le C y t k hkt
    (fun _ hc _ hc' hne ↦ ReedSolomon.Interleaved.agree_lt_of_mem_interleavedCodeSet hc hc' hne)
  have hsub : closeCodewordsRel C y δ ⊆ {c | c ∈ C ∧ t ≤ agree c y} := by
    intro c hc
    obtain ⟨hcC, hd⟩ := mem_closeCodewordsRel_iff.mp hc
    refine ⟨hcC, ?_⟩
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    rw [relHammingDist_coe, hammingDist_comm, div_le_iff₀ hn] at hd
    have htotal : (agree c y : ℝ) + (hammingDist c y : ℝ) = Fintype.card ι := by
      exact_mod_cast agree_add_hammingDist
    have hround : t < agree c y + 1 := by
      exact_mod_cast (show (t : ℝ) < (agree c y : ℝ) + 1 by linarith)
    omega
  exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans
    ((Nat.le_div_iff_mul_le (Nat.choose_pos hkt)).mpr hpack)⟩

end ProximityGap.AgreementSubsetListPacking

#print axioms ProximityGap.AgreementSubsetListPacking.interleaved_lambda_le_choose_div
