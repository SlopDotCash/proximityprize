/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.InterleavedListSize

/-!
# Interleaving does not shrink the list size, for every arity (#232)

`InterleavedListSize` gives the upper product bound `Λ(C^⋈Fin m, δ) ≤ (Λ C δ)^m`, and
`InterleavedFinOneEq` the `m = 1` equality. This file proves the matching **lower bound for every
`m ≥ 1`**:

  `Lambda_interleaved_ge` — `Λ(C, δ) ≤ Λ(interleavedCodeSet (Fin m) C, δ)` for `m ≠ 0`.

The diagonal embedding `c ↦ (fun i _ => c i)` (every column equals `c`) is injective, lands in the
interleaved code (each column is `c`), and — received against the diagonal embedding of `g` —
preserves relative Hamming distance (a diagonal matrix differs from another in a row iff the base
words differ there). So each base point list injects into the interleaved point list. As with the
`m = 1` case, the `DecidableEq`-instance transport is handled inside the `convert … using 3` goal
(uniform `Classical` instance), reducing to the instance-agnostic predicate equivalence
`(fun _ => c i) = (fun _ => g i) ↔ c i = g i` (via `forall_const`, using `Nonempty (Fin m)`).

Together with `Lambda_interleaved_le_pow` this gives `Λ C δ ≤ Λ(C^⋈Fin m, δ) ≤ (Λ C δ)^m`. The
lower bound is the bridge that propagates a base-code list-size *lower* bound into the faithful
lattice at **any** arity `m`. Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

open ListDecodable Code InterleavedCode

namespace InterleavedCode.ListSize

variable {ι F : Type} [Fintype ι]

/-- **Interleaving does not shrink the list size.** For every arity `m ≠ 0`, the diagonal embedding
injects each base point list into the interleaved point list, so `Λ C δ ≤ Λ(C^⋈Fin m, δ)`. -/
theorem Lambda_interleaved_ge [Fintype F] [Nonempty ι] [DecidableEq F] {m : ℕ} [NeZero m]
    (C : Set (ι → F)) (δ : ℝ) :
    Lambda C δ ≤ Lambda (interleavedCodeSet (κ := Fin m) C) δ := by
  classical
  haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  refine iSup_le fun g => ?_
  set G : Matrix ι (Fin m) F := fun i _ => g i with hG
  set φ : (ι → F) → Matrix ι (Fin m) F := fun c => fun i _ => c i with hφ
  have hmaps : Set.MapsTo φ (closeCodewordsRel C g δ)
      (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) G δ) := by
    intro c hc
    obtain ⟨hcC, hcball⟩ := hc
    refine ⟨?_, ?_⟩
    · intro k
      have hcol : (φ c).transpose k = c := by funext i; simp [hφ, Matrix.transpose_apply]
      rw [hcol]; exact hcC
    · rw [relHammingBall, Set.mem_setOf_eq] at hcball ⊢
      convert hcball using 3
      unfold Code.relHammingDist
      congr 1
      unfold hammingDist
      congr 1
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hφ, hG, ne_eq,
        funext_iff, forall_const]
  have hinj : Set.InjOn φ (closeCodewordsRel C g δ) := by
    intro a _ b _ hab
    funext i
    have := congrFun (congrFun hab i) (Classical.arbitrary (Fin m))
    simpa [hφ] using this
  calc ((closeCodewordsRel C g δ).ncard : ℕ∞)
      = (closeCodewordsRel C g δ).encard := (Set.toFinite _).cast_ncard_eq
    _ ≤ (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) G δ).encard :=
        Set.encard_le_encard_of_injOn hmaps hinj
    _ = ((closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) G δ).ncard : ℕ∞) :=
        ((Set.toFinite _).cast_ncard_eq).symm
    _ ≤ Lambda (interleavedCodeSet (κ := Fin m) C) δ :=
        le_iSup
          (fun f => ((closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).ncard : ℕ∞)) G

#print axioms Lambda_interleaved_ge

end InterleavedCode.ListSize
