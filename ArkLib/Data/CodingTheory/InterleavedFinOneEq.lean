/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.InterleavedListSize
import ArkLib.Data.CodingTheory.InterleavedLambdaGe

/-!
# Unary interleaving preserves the list size exactly (#232)

`InterleavedListSize` proves `Lambda (interleavedCodeSet (Fin 1) C) δ ≤ Lambda C δ` (the `m = 1`
case of the product bound). This file records the matching lower bound, hence the **equality**

  `Lambda_interleaved_fin_one_eq` — `Lambda (interleavedCodeSet (Fin 1) C) δ = Lambda C δ`.

The lower bound is the `m = 1` instance of the arity-general `Lambda_interleaved_ge`
(`InterleavedLambdaGe.lean`), which embeds each base codeword `c` as the diagonal matrix
`φ c = (fun i _ => c i)`: this is injective, lands in the interleaved code, and preserves relative
Hamming distance, so it injects each base point list into the interleaved point list.
`Lambda_interleaved_fin_one_ge` is kept as a compatibility name for that instance rather than a
second copy of the injection proof.

This completes the interleaved list-size API at `m = 1`, and is the bridge needed to propagate a
base-code list-size *lower* bound (e.g. the capacity-exponent overflow) into the faithful lattice,
which uses `C^⋈(Fin 1)` at single column. Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

open ListDecodable Code InterleavedCode

namespace InterleavedCode.ListSize

variable {ι F : Type} [Fintype ι]

/-- **Unary interleaving does not shrink the list size.** `Lambda C δ ≤ Lambda (C^⋈ Fin 1) δ`:
the `m = 1` instance of `Lambda_interleaved_ge`. -/
theorem Lambda_interleaved_fin_one_ge [Fintype F] [Nonempty ι] [DecidableEq F]
    (C : Set (ι → F)) (δ : ℝ) :
    ListDecodable.Lambda C δ ≤ ListDecodable.Lambda (interleavedCodeSet (κ := Fin 1) C) δ :=
  Lambda_interleaved_ge (m := 1) C δ

/-- **Unary interleaving preserves the list size exactly.** -/
theorem Lambda_interleaved_fin_one_eq [Fintype F] [Nonempty ι] [DecidableEq F]
    (C : Set (ι → F)) (δ : ℝ) :
    ListDecodable.Lambda (interleavedCodeSet (κ := Fin 1) C) δ = ListDecodable.Lambda C δ :=
  le_antisymm (Lambda_interleaved_fin_one_le C δ) (Lambda_interleaved_fin_one_ge C δ)

#print axioms Lambda_interleaved_fin_one_eq

end InterleavedCode.ListSize
