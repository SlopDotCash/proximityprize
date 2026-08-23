/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCABandTwoExact
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Round 2 (#357): the second band for every Reed–Solomon code

The connector from the universal band-2 theorems (`MCABandTwoCollapse`/`MCABandTwoExact`)
to the prize code family. A nonzero polynomial of degree `< k` has at most `k − 1` roots,
so a nonzero RS codeword has weight `≥ n − k + 1` — for `n ≥ k + 3` the `NoLowWeight`
hypothesis (`distance ≥ 4`) holds, and the universal second band lands:

  `epsMCA_rs_band_two` : `ε_mca(RS[F, domain, k], δ) = 2/|F|` for every `1 ≤ δ·n < 2`,
  whenever `n ≥ k + 3` (no other hypotheses).

In particular every production-scale Reed–Solomon code of the prize statement (`ρ ≤ 1/2`,
`n ≥ 8`) has its first two MCA staircase steps as exact theorems:
`1/|F|` on `[0, 1/n)` and `2/|F|` on `[1/n, 2/n)`.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (the δ* campaign; round 2 — the staircase program).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCABandTwoRS

open ProximityGap.MCABandTwoCollapse ProximityGap.MCABandTwoExact

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **RS codes have no low-weight codewords** for `n ≥ k + 3`: a nonzero polynomial of
degree `< k` cannot vanish at `n − 3 ≥ k` distinct points. -/
theorem rs_noLowWeight (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) :
    NoLowWeight (ReedSolomon.code domain k) := by
  rintro w hw ⟨T, hT3, hsupp⟩
  obtain ⟨p, hp, rfl⟩ := hw
  have hp0 : p = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (v := domain)
      (Finset.univ \ T) (Set.injOn_of_injective domain.injective) ?_ ?_
    · -- degree p < k ≤ #(univ \ T)
      have hdeg : p.degree < (k : WithBot ℕ) := Polynomial.mem_degreeLT.mp hp
      refine lt_of_lt_of_le hdeg ?_
      have hsplit : (Finset.univ \ T).card + T.card = (Finset.univ : Finset ι).card :=
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
      rw [Finset.card_univ] at hsplit
      have hcard : k ≤ (Finset.univ \ T).card := by omega
      exact_mod_cast hcard
    · intro i hi
      have hiT : i ∉ T := (Finset.mem_sdiff.mp hi).2
      exact hsupp i hiT
  rw [hp0, map_zero]

/-- **The second band of every Reed–Solomon code** (`n ≥ k + 3`):
`ε_mca(RS[F, domain, k], δ) = 2/|F|` exactly, on the whole band `1 ≤ δ·n < 2`. The first
two MCA staircase steps of every prize-scale RS code are now exact theorems. -/
theorem epsMCA_rs_band_two (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι)
    {δ : ℝ≥0} (hδ1 : 1 ≤ δ * (Fintype.card ι : ℝ≥0))
    (hδ2 : δ * (Fintype.card ι : ℝ≥0) < 2) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ
      = 2 / (Fintype.card F : ℝ≥0∞) := by
  have hn : 3 ≤ Fintype.card ι := by omega
  obtain ⟨i₁, i₂, hne⟩ := Fintype.exists_pair_of_one_lt_card (by omega) (α := ι)
  exact epsMCA_eq_two_div_card_of_dist4 (ReedSolomon.code domain k)
    (rs_noLowWeight domain hk) hn hδ1 hδ2 hne (one_ne_zero)

/-! ## Source audit -/

#print axioms rs_noLowWeight
#print axioms epsMCA_rs_band_two

end ProximityGap.MCABandTwoRS
