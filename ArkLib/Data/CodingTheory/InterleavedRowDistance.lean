/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Row distance is dominated by interleaved distance

For an interleaved word `⋈|u = uᵀ` (the transpose of a word stack `u`), the relative distance of any
single row `u k` to the base code `C` is at most the relative distance of the whole interleaved word
to the interleaved code `C^⋈`.  Equivalently: making the interleaved word close to the interleaved
code forces every row to be close to `C`.

The proof is a projection: applying the "evaluate at column `k`" map to the interleaved word recovers
the row `u k` and to a codeword `V` recovers its row `Vᵀ k ∈ C`; `hammingDist_comp_le_hammingDist`
then bounds the row Hamming distance by the interleaved one, and `sInf` antitone-monotonicity lifts
this to the distance-to-code.

## Motivation (DG25 L4.19 / ABF26 Lemma 4.19, issue #77)

This is the bridge from `jointProximity` to a single-row distance bound: choosing a word `w` beyond
the covering radius (`δ < δᵣ(w,C)`) makes `¬ jointProximity (u₀, w) δ` for every base word `u₀`,
which is exactly the hypothesis the covering-radius sampling lower bound needs so the `ε_ca` body is
the bare line probability rather than `0`.
-/

open scoped NNReal ENNReal BigOperators
open Code

namespace ArkLib

/-- **Row distance ≤ interleaved distance.** The relative distance of row `u k` to `C` is at most
the relative distance of the interleaved word `uᵀ` to the interleaved code `interleavedCodeSet C`. -/
theorem relDistFromCode_row_le_interleaved {κ ι A : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    [DecidableEq A] (C : Set (ι → A)) (u : Matrix κ ι A) (k : κ) :
    relDistFromCode (u k) C ≤ relDistFromCode (Matrix.transpose u) (interleavedCodeSet C) := by
  unfold relDistFromCode
  apply sInf_le_sInf
  rintro d ⟨V, hVmem, hVle⟩
  refine ⟨Matrix.transpose V k, hVmem k, ?_⟩
  refine le_trans ?_ hVle
  have hproj : hammingDist (u k) (Matrix.transpose V k)
      ≤ hammingDist (Matrix.transpose u) V := by
    have h := hammingDist_comp_le_hammingDist (fun (_ : ι) (col : κ → A) => col k)
                (x := Matrix.transpose u) (y := V)
    simpa [Matrix.transpose_apply] using h
  have hrel : relHammingDist (u k) (Matrix.transpose V k)
      ≤ relHammingDist (Matrix.transpose u) V := by
    unfold relHammingDist
    gcongr
  simp only [ENNReal.coe_NNRat_coe_NNReal]
  exact ENNReal.coe_le_coe.mpr (by exact_mod_cast hrel)

/-- **`jointProximity → second-row distance` (the DG25 covering-radius hypothesis).**
If the pair `(u₀, w)` is jointly `δ`-close to the interleaved code, then the second row `w` is
`δ`-close to the base code.  Contrapositive: a `w` beyond the covering radius (`δ < δᵣ(w,C)`) is never
part of a jointly-`δ`-close pair, so the `ε_ca` body at `(u₀, w)` is never zeroed. -/
theorem relDistFromCode_snd_le_of_jointProximity {ι A : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq A] {C : Set (ι → A)} {u₀ w : ι → A} {δ : ℝ≥0}
    (h : jointProximity C (finMapTwoWords u₀ w) δ) :
    relDistFromCode w C ≤ (δ : ℝ≥0∞) := by
  have hrow := relDistFromCode_row_le_interleaved C (finMapTwoWords u₀ w) 1
  have hw : (finMapTwoWords u₀ w) (1 : Fin 2) = w := rfl
  rw [hw] at hrow
  exact le_trans hrow h

end ArkLib

