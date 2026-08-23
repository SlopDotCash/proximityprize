/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# Binius multilinear-weight even/odd recursion (issue #33)

The testBit even/odd splits + multilinearWeight_split: the binary-tower multilinear weight recursion
feeding the fold-step consistency. Pure GF(2)-tower bit algebra.
-/

open Finset

namespace Issue33Binius

/-- Tensor product weight `⊗_{j<ϑ}(1 - r_j, r_j)` at index `i` given challenges `r`.
This is a verbatim copy of `ArkLib`'s `multilinearWeight`
(`ArkLib/Data/CodingTheory/Prelims.lean:23`), kept local so the file is self-contained.
The `j`-th factor selects `r_j` when the `j`-th bit of `i` is set, else `1 - r_j`. -/
def multilinearWeight {F : Type*} [CommRing F] {ϑ : ℕ} (r : Fin ϑ → F) (i : Fin (2 ^ ϑ)) : F :=
  ∏ j : Fin ϑ, if i.val.testBit j.val then r j else 1 - r j

/-! ### The two binary-tower bit facts (pure `Nat.testBit` algebra)

These are the only number-theoretic inputs; they are the same facts the in-repo proof
`multilinearCombine_recursive_form_first` (Incremental.lean:687) derives from `ArkLib`'s
`Nat.getBit_*` lemmas.  Here we derive them straight from core `Nat.testBit`. -/

/-- LSB of an even number is `false`.  `(2*n).testBit 0 = false`. -/
theorem testBit_zero_two_mul (n : ℕ) : (2 * n).testBit 0 = false := by
  -- `Nat.testBit_zero : n.testBit 0 = n.bodd`; `(2*n).bodd = false`.
  rw [Nat.testBit_zero]
  -- `2 * n` is even, so `decide (1 &&& (2*n) = 1)`-style normal form is `false`.
  simp [Nat.mul_mod_right]

/-- LSB of an odd number is `true`.  `(2*n+1).testBit 0 = true`. -/
theorem testBit_zero_two_mul_add_one (n : ℕ) : (2 * n + 1).testBit 0 = true := by
  rw [Nat.testBit_zero]
  simp

/-- The `(k+1)`-th bit of `2*n` is the `k`-th bit of `n`.  `(2*n).testBit (k+1) = n.testBit k`. -/
theorem testBit_succ_two_mul (n k : ℕ) : (2 * n).testBit (k + 1) = n.testBit k := by
  -- `Nat.testBit_succ : n.testBit (k+1) = (n / 2).testBit k`; `(2*n)/2 = n`.
  rw [Nat.testBit_succ]
  congr 1
  omega

/-- The `(k+1)`-th bit of `2*n+1` is the `k`-th bit of `n`.
`(2*n+1).testBit (k+1) = n.testBit k`. -/
theorem testBit_succ_two_mul_add_one (n k : ℕ) :
    (2 * n + 1).testBit (k + 1) = n.testBit k := by
  rw [Nat.testBit_succ]
  congr 1
  omega

/-! ### The even/odd tail factorization of the product

The product over `Fin (ϑ+1)` peels its `0`-th factor via `Fin.prod_univ_succ`; the
remaining product over `Fin.succ`-indices reindexes onto the `tail` challenges using the
bit-shift facts above. -/

variable {F : Type*} [CommRing F]

/-- **Tail product reindexing (even rows).**  For the even index `2*i`, the product over the
non-`0` factors of `multilinearWeight (ϑ+1)` equals `multilinearWeight ϑ` of the challenge
tail at index `i`. -/
theorem tailProd_even {ϑ : ℕ} (r : Fin (ϑ + 1) → F) (i : Fin (2 ^ ϑ)) :
    (∏ j : Fin ϑ,
        if (2 * i.val).testBit (Fin.succ j).val then r (Fin.succ j) else 1 - r (Fin.succ j))
      = ∏ j : Fin ϑ, if i.val.testBit j.val then r (Fin.succ j) else 1 - r (Fin.succ j) := by
  refine Finset.prod_congr rfl (fun j _ => ?_)
  -- `(Fin.succ j).val = j.val + 1`, then `testBit_succ_two_mul`.
  rw [Fin.val_succ, testBit_succ_two_mul]

/-- **Tail product reindexing (odd rows).**  Same as `tailProd_even` for index `2*i+1`. -/
theorem tailProd_odd {ϑ : ℕ} (r : Fin (ϑ + 1) → F) (i : Fin (2 ^ ϑ)) :
    (∏ j : Fin ϑ,
        if (2 * i.val + 1).testBit (Fin.succ j).val then r (Fin.succ j) else 1 - r (Fin.succ j))
      = ∏ j : Fin ϑ, if i.val.testBit j.val then r (Fin.succ j) else 1 - r (Fin.succ j) := by
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Fin.val_succ, testBit_succ_two_mul_add_one]

/-! ### Main extracted identities

The genuine algebra: the LSB challenge `r 0` factors out of the tensor weight as the
affine-line coefficient `(1 - r 0)` on even rows and `(r 0)` on odd rows.  This is the
basefold/FRI fold step at the weight level, over any `CommRing` (hence any binary tower
field). -/

/-- **`multilinearWeight` even-row factorization.**
`multilinearWeight r (2*i) = (1 - r 0) * multilinearWeight (tail r) i`. -/
theorem multilinearWeight_even {ϑ : ℕ} (r : Fin (ϑ + 1) → F) (i : Fin (2 ^ ϑ))
    (h : 2 * i.val < 2 ^ (ϑ + 1)) :
    multilinearWeight r ⟨2 * i.val, h⟩
      = (1 - r 0) * multilinearWeight (fun j => r (Fin.succ j)) i := by
  unfold multilinearWeight
  -- Peel factor `0` from the (ϑ+1)-product.
  rw [Fin.prod_univ_succ]
  -- Factor `0`: bit 0 of `2*i` is `false`, so the `if` is `1 - r 0`.
  have h0 : (2 * i.val).testBit (0 : Fin (ϑ + 1)).val = false := by
    simp
  rw [h0]
  -- Reindex the tail product. The rewrite closes the goal: both sides become
  -- `(1 - r 0) * (shared tail product)`.
  rw [if_neg (by simp), tailProd_even r i]

/-- **`multilinearWeight` odd-row factorization.**
`multilinearWeight r (2*i+1) = (r 0) * multilinearWeight (tail r) i`. -/
theorem multilinearWeight_odd {ϑ : ℕ} (r : Fin (ϑ + 1) → F) (i : Fin (2 ^ ϑ))
    (h : 2 * i.val + 1 < 2 ^ (ϑ + 1)) :
    multilinearWeight r ⟨2 * i.val + 1, h⟩
      = (r 0) * multilinearWeight (fun j => r (Fin.succ j)) i := by
  unfold multilinearWeight
  rw [Fin.prod_univ_succ]
  have h0 : (2 * i.val + 1).testBit (0 : Fin (ϑ + 1)).val = true := by
    simp
  rw [h0]
  rw [if_pos (by simp), tailProd_odd r i]

/-! ### Affine-line packaging (the fold-step kernel)

Combining the even and odd rows: the two children of the binary challenge tree are an
affine combination governed by the LSB challenge.  This is the weight-level statement of
`affineLineEvaluation u₀ u₁ r = (1 - r) • u₀ + r • u₁` specialized to tensor weights, which
is precisely what `multilinearCombine_recursive_form_first` uses to drive the basefold
recursion. -/

/-- **Affine-line fold kernel at the weight level.**  Over a `CommRing`, the even and odd
tensor weights of the `(ϑ+1)`-challenge expansion are the `(1 - r0, r0)` affine combination
of the single shared `ϑ`-challenge tail weight.  Stated as the pair identity consumed by the
fold recursion. -/
theorem multilinearWeight_split {ϑ : ℕ} (r : Fin (ϑ + 1) → F) (i : Fin (2 ^ ϑ))
    (hE : 2 * i.val < 2 ^ (ϑ + 1)) (hO : 2 * i.val + 1 < 2 ^ (ϑ + 1)) :
    multilinearWeight r ⟨2 * i.val, hE⟩ + multilinearWeight r ⟨2 * i.val + 1, hO⟩
      = multilinearWeight (fun j => r (Fin.succ j)) i := by
  rw [multilinearWeight_even r i hE, multilinearWeight_odd r i hO]
  -- `(1 - r0) * w + r0 * w = w`.
  ring

/-! ### Single-challenge base case (sanity check that the convention matches ArkLib)

`challengeTensorExpansion 1 (fun _ => c) = ![1 - c, c]` — the `n = 1` base of the
expansion (cf. `Prelude.lean:1911 challengeTensorExpansion_one`).  We verify our
`multilinearWeight` reproduces it, pinning down that the bit/orientation convention here
is the same `multilinearWeight` ArkLib uses (testBit = MSB-of-index ↔ challenge j). -/

/-- `multilinearWeight (single challenge c) 0 = 1 - c` and `... 1 = c`. -/
theorem multilinearWeight_one (c : F) :
    multilinearWeight (ϑ := 1) (fun _ => c) 0 = 1 - c
      ∧ multilinearWeight (ϑ := 1) (fun _ => c) 1 = c := by
  constructor <;>
  · unfold multilinearWeight
    rw [Fin.prod_univ_one]
    simp [Nat.testBit]

#print axioms testBit_zero_two_mul
#print axioms testBit_zero_two_mul_add_one
#print axioms testBit_succ_two_mul
#print axioms testBit_succ_two_mul_add_one
#print axioms tailProd_even
#print axioms tailProd_odd
#print axioms multilinearWeight_even
#print axioms multilinearWeight_odd
#print axioms multilinearWeight_split
#print axioms multilinearWeight_one

end Issue33Binius
