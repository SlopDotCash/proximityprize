/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.InterleavedListSize

/-!
# Unary interleaving preserves the list size exactly (#232)

`InterleavedListSize` proves `Lambda (interleavedCodeSet (Fin 1) C) δ ≤ Lambda C δ` (the `m = 1`
case of the product bound). This file proves the matching lower bound, hence the **equality**

  `Lambda_interleaved_fin_one_eq` — `Lambda (interleavedCodeSet (Fin 1) C) δ = Lambda C δ`.

The lower bound embeds each base codeword `c` as the unary matrix `φ c = (fun i _ => c i)`; this is
injective, lands in the interleaved code (its single column is `c`), and preserves relative Hamming
distance (a unary matrix differs from another in a row iff the underlying base words differ there),
so it injects each base point list into the interleaved point list. The distance-preservation step
is handled at the `Prop` level (filter-set equality), sidestepping the `DecidableEq`-instance
transport.

This completes the interleaved list-size API at `m = 1`, and is the bridge needed to propagate a
base-code list-size *lower* bound (e.g. the capacity-exponent overflow) into the faithful lattice,
which uses `C^⋈(Fin 1)` at single column. Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

open ListDecodable Code InterleavedCode

namespace InterleavedCode.ListSize

variable {ι F : Type} [Fintype ι]

/-- **Unary interleaving does not shrink the list size.** Embedding base codewords as unary matrices
injects each base point list into the interleaved point list, so `Lambda C δ ≤ Lambda (C^⋈ Fin 1) δ`. -/
theorem Lambda_interleaved_fin_one_ge [Fintype F] [Nonempty ι] [DecidableEq F]
    (C : Set (ι → F)) (δ : ℝ) :
    Lambda C δ ≤ Lambda (interleavedCodeSet (κ := Fin 1) C) δ := by
  classical
  refine iSup_le fun g => ?_
  set G : Matrix ι (Fin 1) F := fun i _ => g i with hG
  set φ : (ι → F) → Matrix ι (Fin 1) F := fun c => fun i _ => c i with hφ
  have hmaps : Set.MapsTo φ (closeCodewordsRel C g δ)
      (closeCodewordsRel (interleavedCodeSet (κ := Fin 1) C) G δ) := by
    intro c hc
    obtain ⟨hcC, hcball⟩ := hc
    refine ⟨?_, ?_⟩
    · intro k
      have hcol : (φ c).transpose k = c := by funext i; simp [hφ, Matrix.transpose_apply]
      rw [hcol]; exact hcC
    · rw [relHammingBall, Set.mem_setOf_eq] at hcball ⊢
      -- reduce to the (instance-uniform) distance equality inside the `convert` goal
      convert hcball using 3
      unfold Code.relHammingDist
      congr 1
      unfold hammingDist
      congr 1
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hφ, hG, ne_eq,
        funext_iff, Fin.forall_fin_one]
  have hinj : Set.InjOn φ (closeCodewordsRel C g δ) := by
    intro a _ b _ hab
    funext i
    have := congrFun (congrFun hab i) 0
    simpa [hφ] using this
  calc ((closeCodewordsRel C g δ).ncard : ℕ∞)
      = (closeCodewordsRel C g δ).encard := (Set.toFinite _).cast_ncard_eq
    _ ≤ (closeCodewordsRel (interleavedCodeSet (κ := Fin 1) C) G δ).encard :=
        Set.encard_le_encard_of_injOn hmaps hinj
    _ = ((closeCodewordsRel (interleavedCodeSet (κ := Fin 1) C) G δ).ncard : ℕ∞) :=
        ((Set.toFinite _).cast_ncard_eq).symm
    _ ≤ Lambda (interleavedCodeSet (κ := Fin 1) C) δ :=
        le_iSup
          (fun f => ((closeCodewordsRel (interleavedCodeSet (κ := Fin 1) C) f δ).ncard : ℕ∞)) G

/-- **Unary interleaving preserves the list size exactly.** -/
theorem Lambda_interleaved_fin_one_eq [Fintype F] [Nonempty ι] [DecidableEq F]
    (C : Set (ι → F)) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin 1) C) δ = Lambda C δ :=
  le_antisymm (Lambda_interleaved_fin_one_le C δ) (Lambda_interleaved_fin_one_ge C δ)

#print axioms Lambda_interleaved_fin_one_eq

end InterleavedCode.ListSize
