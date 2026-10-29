/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JointAgreement

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.GoodCoeffs
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon

/-!
# BCIKS20 affine lines — joint agreement from a large good-coefficient set

Building on `GoodCoeffs`, this file produces the bivariate Berlekamp-Welch factorization
`RS_exists_bivariate_AB_of_goodCoeffs_card_gt` from a sufficiently large good-coefficient set,
and derives joint (correlated) agreement of the two words `u₀, u₁` with the Reed-Solomon code
in `RS_jointAgreement_of_goodCoeffs_card_gt`. This is the agreement-extraction step of the
[BCIKS20] correlated-agreement argument over affine lines.
-/

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

universe u v w k l

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
/-- **Joint agreement collapses the whole pencil into the close set.**
If the pencil `u` jointly agrees with the Reed–Solomon code on a set of relative size `≥ 1 - δ`,
then *every* scalar `γ` has its line `u₀ + γ • u₁` within relative distance `δ` of the code, i.e.
`RS_goodCoeffs u δ = univ`. The witness is the codeword `v₀ + γ • v₁` (a code element because the
RS code is a submodule), which agrees with the line on the joint-agreement set. -/
theorem RS_jointAgreement_imp_goodCoeffs_eq_univ {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin 2) ι)
    (hja : jointAgreement (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ) (W := u)) :
    RS_goodCoeffs (deg := deg) (domain := domain) u δ = Finset.univ := by
  classical
  obtain ⟨S, hScard, v, hv⟩ := hja
  ext γ
  simp only [Finset.mem_univ, iff_true]
  rw [RS_goodCoeffs, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  set c : ι → F := v 0 + γ • v 1 with hc
  have hcmem : c ∈ (ReedSolomon.code domain deg : Set (ι → F)) :=
    (ReedSolomon.code domain deg).add_mem (hv 0).1
      ((ReedSolomon.code domain deg).smul_mem γ (hv 1).1)
  have hagree : ∀ j ∈ S, (u 0 + γ • u 1) j = c j := by
    intro j hj
    have h0 : v 0 j = u 0 j := by
      have := (hv 0).2 hj; rw [Finset.mem_filter] at this; exact this.2
    have h1 : v 1 j = u 1 j := by
      have := (hv 1).2 hj; rw [Finset.mem_filter] at this; exact this.2
    simp only [hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, h1]
  have hclose : δᵣ(u 0 + γ • u 1, c) ≤ δ := by
    rw [relCloseToWord_iff_exists_agreementCols]
    refine ⟨S, ?_, ?_⟩
    · rw [relDist_floor_bound_iff_complement_bound]; exact hScard
    · intro colIdx
      refine ⟨fun hmem => hagree colIdx hmem, fun hne => ?_⟩
      by_contra hmem
      exact hne (hagree colIdx hmem)
  exact (relCloseToCode_iff_relCloseToCodeword_of_minDist (u 0 + γ • u 1) δ).2 ⟨c, hcmem, hclose⟩

omit [DecidableEq ι] in
/-- **Correlated-agreement proximity-gap dichotomy for Reed–Solomon (below the UDR).**
For every pencil `u`, the number of `δ`-close scalars is *either* at most `|ι|` *or* equal to `|F|`
— it never lands strictly in between. Combines `RS_jointAgreement_of_goodCoeffs_card_gt` (the
Polishchuk–Spielman-backed agreement extraction, issue #232) with
`RS_jointAgreement_imp_goodCoeffs_eq_univ`. -/
theorem RS_goodCoeffs_card_dichotomy {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg))
    (u : WordStack F (Fin 2) ι) :
    (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card ≤ Fintype.card ι
    ∨ RS_goodCoeffs (deg := deg) (domain := domain) u δ = Finset.univ := by
  classical
  by_cases h : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι
  · exact Or.inr (RS_jointAgreement_imp_goodCoeffs_eq_univ u
      (RS_jointAgreement_of_goodCoeffs_card_gt hδ u h))
  · exact Or.inl (not_lt.mp h)

end CoreResults

end ProximityGap
