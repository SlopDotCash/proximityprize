/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Interleaved-code list-size product bound (additive)

Standalone companion to `lambda_le_ggr11` (ABF26 Lemma 2.10 = GGR11) in
`ArkLib.Data.CodingTheory.InterleavedCode`.

The full GGR11 theorem gives the *`m`-independent* bound
`|Λ(C^{≡m}, δ)| ≤ (b+r choose r)·|Λ(C,δ)|^r`, whose proof is a deep
list-recovery / column-pruning recursion that has no in-tree analogue.

This file proves, fully `sorry`-free, the **elementary product bound** that
*is* reachable from the in-tree projection lemmas:

  `Lambda (interleavedCodeSet (Fin m) C) δ ≤ (Lambda C δ) ^ m`.

The argument:
* A close interleaved codeword `V` is determined by its `m` columns
  `V.transpose k`, and each column lands in the per-column base-code list
  `closeCodewordsRel C (f.transpose k) δ` (lemma `transpose_mem_closeCodewordsRel`,
  proved from the in-tree projection-distance lemma `relHammingDist_transpose_le`).
* The column map `V ↦ (fun k => V.transpose k)` is injective on the close set
  (a matrix is determined by its columns), so by `Set.encard_le_encard_of_injOn`
  the per-word list cardinality is at most that of the `m`-fold product
  `Set.pi univ (fun k => closeCodewordsRel C (f.transpose k) δ)`.
* `Set.encard_pi_eq_prod_encard` turns the product cardinality into
  `∏ k, (closeCodewordsRel C (f.transpose k) δ).encard`, each factor `≤ Lambda C δ`.

This is strictly weaker than GGR11 (it is **not** `m`-independent), but it is a
fully kernel-checked upper bound on the interleaved list size — the deepest
verified sub-stack toward the interleaved list-decoding theory that current
in-tree leaf lemmas support.  Requires `[Fintype F]` (so all lists are finite,
and `Lambda` is the genuine maximised cardinality).
-/

open ListDecodable Code InterleavedCode

namespace InterleavedCode.ListSize

variable {ι F : Type} [Fintype ι]

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false
set_option maxHeartbeats 1000000

-- The instance-transport conversions around relative Hamming distance are heartbeat-heavy.
/-- A close interleaved codeword projects, column-wise, to a close codeword of the base code.

This re-derives the projection close-list membership from the in-tree
projection-distance lemma `relHammingDist_transpose_le`. -/
lemma transpose_mem_closeCodewordsRel [DecidableEq F] [Nonempty ι] {m : ℕ}
    {C : Set (ι → F)} {δ : ℝ}
    {f V : Matrix ι (Fin m) F}
    (hV : V ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    (k : Fin m) :
    V.transpose k ∈ closeCodewordsRel C (f.transpose k) δ := by
  classical
  obtain ⟨hmem, hball⟩ := hV
  refine ⟨hmem k, ?_⟩
  rw [relHammingBall, Set.mem_setOf_eq] at hball ⊢
  have hproj : (δᵣ(V.transpose k, f.transpose k) : ℝ) ≤ (δᵣ(V, f) : ℝ) := by
    have h := relHammingDist_transpose_le (ι := ι) (F := F) f V k
    exact_mod_cast h
  -- comm at the column level (ι → F)
  have hcomm : ∀ (a b : ι → F), (δᵣ(a, b) : ℝ) = (δᵣ(b, a) : ℝ) := by
    intro a b; unfold relHammingDist; rw [hammingDist_comm]
  -- comm at the matrix level (ι → (Fin m → F))
  have hcommM : (δᵣ(f, V) : ℝ) = (δᵣ(V, f) : ℝ) := by
    unfold relHammingDist; rw [hammingDist_comm]
  -- `relHammingDist` values are independent of the `DecidableEq` instance (a `Subsingleton`):
  -- prove the inequality for the inferred instances, then transport instance choices.
  have hballI : (δᵣ(f, V) : ℝ) ≤ δ := by convert hball using 3
  have key : (δᵣ(f.transpose k, V.transpose k) : ℝ) ≤ δ :=
    calc (δᵣ(f.transpose k, V.transpose k) : ℝ)
        = (δᵣ(V.transpose k, f.transpose k) : ℝ) := hcomm _ _
      _ ≤ (δᵣ(V, f) : ℝ) := hproj
      _ = (δᵣ(f, V) : ℝ) := hcommM.symm
      _ ≤ δ := hballI
  convert key using 3

/-- The per-column base-code list size is bounded by the maximised list size `Lambda C δ`
(when `F` is finite, so all lists are finite). -/
lemma encard_closeCodewordsRel_le_Lambda [Fintype F] {C : Set (ι → F)} {δ : ℝ} (g : ι → F) :
    (closeCodewordsRel C g δ).encard ≤ Lambda C δ := by
  have hfin : (closeCodewordsRel C g δ).Finite := Set.toFinite _
  calc (closeCodewordsRel C g δ).encard
      = ((closeCodewordsRel C g δ).ncard : ℕ∞) := (hfin.cast_ncard_eq).symm
    _ ≤ Lambda C δ := le_iSup (fun f => ((closeCodewordsRel C f δ).ncard : ℕ∞)) g

/-- **Per-word interleaved list-size product bound.**  For a fixed received interleaved word
`f`, the number of close interleaved codewords is at most `(Lambda C δ) ^ m`. -/
lemma encard_closeCodewordsRel_interleaved_le [Fintype F] [Nonempty ι] {m : ℕ}
    {C : Set (ι → F)} {δ : ℝ} (f : Matrix ι (Fin m) F) :
    (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard ≤ (Lambda C δ) ^ m := by
  classical
  -- target product of per-column lists
  set T : Set (Fin m → (ι → F)) :=
    Set.pi Set.univ (fun k => closeCodewordsRel C (f.transpose k) δ) with hT
  -- column map: a close interleaved codeword to its tuple of columns
  set Φ : Matrix ι (Fin m) F → (Fin m → (ι → F)) := fun V k => V.transpose k with hΦ
  have hmaps : Set.MapsTo Φ (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ) T := by
    intro V hV
    simp only [hT, Set.mem_pi, Set.mem_univ, true_implies]
    intro k
    exact transpose_mem_closeCodewordsRel hV k
  have hinj : Set.InjOn Φ (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ) := by
    intro V _ W _ heq
    -- two matrices with equal column tuples are equal
    ext i k
    have := congrFun heq k
    exact congrFun this i
  calc (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard
      ≤ T.encard := Set.encard_le_encard_of_injOn hmaps hinj
    _ = ∏ k, (closeCodewordsRel C (f.transpose k) δ).encard := by
          rw [hT]; exact Set.encard_pi_eq_prod_encard
    _ ≤ ∏ _k : Fin m, Lambda C δ := by
          apply Finset.prod_le_prod'
          intro k _
          exact encard_closeCodewordsRel_le_Lambda (f.transpose k)
    _ = (Lambda C δ) ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Interleaved list-size product bound** (companion to `lambda_le_ggr11`).

For a finite field `F` and `m`-fold interleaving, the maximised list size of the
interleaved code is bounded by the `m`-th power of the base-code list size:

  `Lambda (interleavedCodeSet (Fin m) C) δ ≤ (Lambda C δ) ^ m`.

This is the elementary, `m`-*dependent* bound (the GGR11 theorem improves the
exponent from `m` down to the `m`-independent `r = ⌈log₂(δ_C/η)⌉`, via a deep
list-recovery recursion that is external to the current in-tree development). -/
theorem Lambda_interleaved_le_pow [Fintype F] [Nonempty ι] {m : ℕ}
    (C : Set (ι → F)) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) C) δ ≤ (Lambda C δ) ^ m := by
  refine iSup_le (fun f => ?_)
  calc ((closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).ncard : ℕ∞)
      = (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard :=
        (Set.toFinite _).cast_ncard_eq
    _ ≤ (Lambda C δ) ^ m := encard_closeCodewordsRel_interleaved_le f

/-- Unary interleaving specializes the product bound to the base list size. -/
theorem Lambda_interleaved_fin_one_le [Fintype F] [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin 1) C) δ ≤ Lambda C δ := by
  simpa using (Lambda_interleaved_le_pow (m := 1) C δ)

/-- Empty interleaving has list size at most one under the elementary product bound. -/
theorem Lambda_interleaved_fin_zero_le_one [Fintype F] [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin 0) C) δ ≤ 1 := by
  simpa using (Lambda_interleaved_le_pow (m := 0) C δ)

end InterleavedCode.ListSize
