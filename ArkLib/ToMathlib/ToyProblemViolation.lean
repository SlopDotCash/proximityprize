/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.Definitions
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Toy-problem violation bridge (ABF26 §6.4.1)

A single self-contained helper closing the **violation-certificate** gap that the
`epsCA_le_winningSetSoundness` leaderboard lemma needs (`Leaderboard.lean`).

`simplified_iop_soundness_ca_lb` produces a CA-maximising winning-set witness
`(0, 0, 0, f₁, f₂)` at a word stack `u₀` lying in the `¬ jointProximity` branch of
`epsCA` (otherwise the supremum term is `0`). To package that witness as a
`ViolatingInstance` the leaderboard needs the **violation certificate**
`¬ relaxedRelation (ℓ := 2) C δ 0 ![0,0] ![f₁,f₂]`.

This file provides the missing bridge:

  `relaxedRelation (ℓ := 2) C δ 0 ![0,0] ![f₁,f₂] → jointProximity C ![f₁,f₂] δ`

so the contrapositive turns `¬ jointProximity` (the `epsCA` non-trivial branch) into
the required violation certificate. The mathematical content is exactly that the
relaxed two-row relation at `v = μ = 0` *is* joint δ-proximity of `(f₁, f₂)` to the
interleaved code `C^{≡2}`: a `relation`-witness stack has both rows in `C` (the linear
constraint is vacuous at `v = 0`), its transpose lies in `interleavedCodeSet C`, and the
shared per-row agreement set is exactly the symbol-agreement set of the two interleaved
words, so the interleaved relative Hamming distance is `≤ δ`.

This is in-tree faithful plumbing for the §6.4.1 winning-set construction: no statement
of any owned declaration is changed, and the lemma is axiom-clean.
-/

namespace ToyProblem

open Code InterleavedCode
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.show false

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]

/-- **Violation bridge (ABF26 §6.4.1).** The relaxed two-row relation `R̃²_{C,δ}` at
`v = 0`, `μ = (0,0)` implies joint δ-proximity of the word stack `![f₁,f₂]` to the
interleaved code `C^{≡2}`.

The contrapositive supplies the `ViolatingInstance` certificate
`¬ relaxedRelation (ℓ := 2) C δ 0 ![0,0] ![f₁,f₂]` from the `¬ jointProximity` branch of
`epsCA`, which is what `epsCA_le_winningSetSoundness` consumes. -/
theorem relaxedRelation_two_zero_imp_jointProximity [Nonempty ι] {k : ℕ}
    (C : Set (ι → F)) (δ : ℝ≥0) (u : WordStack F (Fin 2) ι)
    (h : relaxedRelation (k := k) (ℓ := 2) C δ (0 : Fin k → F) ![0, 0] u) :
    jointProximity C (u := u) δ := by
  classical
  obtain ⟨Wstar, hrel, S, hScard, hSag⟩ := h
  -- From `relation … Wstar` extract: each row `Wstar i ∈ C`.
  obtain ⟨M, ⟨encode, hEnc_mem, hWeq⟩, _hconstr⟩ := hrel
  have hWstar_mem : ∀ i, Wstar i ∈ C := by
    intro i; rw [hWeq i]; exact hEnc_mem (M i)
  -- View `Wstar` at the `WordStack` type so the `⋈|` (Interleavable) notation resolves.
  set Wm : WordStack F (Fin 2) ι := Wstar with hWm
  -- The interleaved word of `Wstar` (as a WordStack) lies in `interleavedCodeSet C`.
  have hWstar_interleaved : (⋈| Wm) ∈ interleavedCodeSet C := by
    rw [interleave_wordStack_eq]
    intro k
    -- `(Wm.transpose).transpose k = Wm k = Wstar k ∈ C`.
    show Wm.transpose.transpose k ∈ C
    rw [Matrix.transpose_transpose]
    exact hWstar_mem k
  -- The two interleaved words agree on the symbol-set `S`.
  have hagree : ∀ i ∈ S, (⋈| u) i = (⋈| Wm) i := by
    intro i hi
    rw [interleave_wordStack_eq, interleave_wordStack_eq]
    funext k
    show u k i = Wm k i
    exact hSag k i hi
  -- Hence the relative Hamming distance of the two interleaved words is ≤ δ.
  have hclose_word : δᵣ((⋈| u), (⋈| Wm)) ≤ δ := by
    rw [relCloseToWord_iff_exists_agreementCols]
    refine ⟨S, ?_, ?_⟩
    · -- `|ι| - ⌊δ·|ι|⌋ ≤ |S|`, from `(1-δ)·|ι| ≤ |S|`.
      rw [relDist_floor_bound_iff_complement_bound]
      -- `hScard : (1 - (δ:ℝ)) * |ι| ≤ |S|` in ℝ; lift the ℝ≥0 goal `(1 - δ) * |ι| ≤ |S|`.
      rcases le_total (δ : ℝ≥0) 1 with hδle | hδgt
      · -- `δ ≤ 1`: `((1:ℝ≥0) - δ) = ((1:ℝ) - δ).toNNReal`, so the ℝ bound transfers.
        have hcoe : ((1 : ℝ≥0) - δ : ℝ≥0) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := by
          rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast,
            NNReal.coe_sub hδle, NNReal.coe_one]
          exact hScard
        exact hcoe
      · -- `δ ≥ 1`: `(1:ℝ≥0) - δ = 0`, so the bound is `0 ≤ |S|`.
        rw [tsub_eq_zero_of_le hδgt, zero_mul]
        exact zero_le _
    · intro colIdx
      refine ⟨fun hmem => hagree colIdx hmem, ?_⟩
      intro hne
      by_contra hmem
      exact hne (hagree colIdx hmem)
  -- Conclude joint proximity. `δᵣ(·,C)` is ENNReal-valued; `hclose_word` is the
  -- ℚ≥0-into-ℝ≥0 word-word bound, so lift it to ENNReal for the transitive chain.
  unfold jointProximity
  have hclose_E : (δᵣ((⋈| u), (⋈| Wm)) : ENNReal) ≤ (δ : ENNReal) := by
    -- `↑(q : ℚ≥0) ≤ (δ : ℝ≥0)` (in ℝ≥0) ⟹ the same cast into ENNReal.
    exact_mod_cast hclose_word
  exact le_trans (relDistFromCode_le_relDist_to_mem _ _ hWstar_interleaved) hclose_E

end ToyProblem
