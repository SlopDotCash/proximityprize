/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.GMMDS.LovettDualSpanConnector

/-!
# `FieldLargeForMinor` is unsatisfiable for `2 ≤ k ≤ |ι|` (#389 / r3_thm211)

`FieldLargeForMinor ι F k` asks that a **fixed** finite field `F` beat the total degree of
**every** nonzero square minor of every reduced intersection matrix, for **every** vertex count
`t`. A nonzero `tk × tk` minor of `RIM` has degree growing linearly in `t` once `k ≥ 2`
(column `(c, m)` carries degree `m`), so no finite field satisfies the premise.

The witness, for `k` distinct edges `emb : Fin k ↪ ι`:

* every edge is the whole vertex set `Fin (t + 1)`, and row `(c, m)` is (edge `emb m`, vertex
  `c`), with the reduced vertex `t` standing in for `c = 0`;
* `fullRowsMinor_blockTriangular` — the minor is block triangular for `p ↦ p.1.rev`, with the
  `k × k` Vandermonde matrix of `X (emb ·)` (block `0`) or its negation (other blocks) on the
  diagonal;
* `fullRowsMinor_det_isHomogeneous`, `fullRowsMinor_det_ne_zero` — its determinant is a nonzero
  homogeneous polynomial of degree `t · d`, where `d ≥ 1` is the Vandermonde degree;
* `not_fieldLargeForMinor` — `¬ FieldLargeForMinor ι F k` for every finite field `F` and
  `2 ≤ k ≤ |ι|`, by taking `t = |F|`.

Consequence: every theorem that takes `FieldLargeForMinor ι F k` as a hypothesis
(`lovettSystemToDualSpan_of_connector`, `lovettSystemToDualSpan_unconditional`,
`gmmDsDualZeroPatternTheorem_via_connector`, `gmmDsDualZeroPatternTheorem_unconditional`,
`gmmDsResidual_unconditional`, `symbolicFullRank_lovett_free`,
`gmmDsDualZeroPatternTheoremPinned_via_lovett`, `symbolicFullRank_via_lovett_pinned`) is vacuous
for `2 ≤ k ≤ |ι|`: its premise can never be supplied. For `k > |ι|` no `tk × tk` minor with
`t ≥ 1` is nonzero (there are at most `|ι| · t` rows), and `SymbolicFullRankResidual` is vacuous
there too. These reductions therefore do not localize `SymbolicFullRankResidual` for any
`k ≥ 2` until the field-size hypothesis is stated per instance (for the `t` and the minor being
specialized) rather than uniformly over all `t`.
-/

open Finset MvPolynomial

namespace ArkLib.GMMDS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-- The vertex used by row block `c`: the reduced vertex `t` for `c = 0`, else `c` itself. -/
def blockVertex {t : ℕ} (c : Fin t) : Fin (t + 1) :=
  if c.val = 0 then Fin.last t else c.castSucc

theorem zero_lt_blockVertex {t : ℕ} (c : Fin t) : (0 : Fin (t + 1)) < blockVertex c := by
  unfold blockVertex
  split_ifs with h
  · rw [Fin.lt_def]
    simp only [Fin.val_zero, Fin.val_last]
    exact lt_of_le_of_lt (Nat.zero_le _) c.isLt
  · rw [Fin.lt_def]
    simp only [Fin.val_zero, Fin.val_castSucc]
    omega

/-- The full edge family: every edge is the whole vertex set. -/
abbrev fullEdges (ι : Type*) (t : ℕ) : ι → Finset (Fin (t + 1)) := fun _ => univ

/-- Row selection `(c, m) ↦ (edge emb m, vertex blockVertex c)`. -/
def fullRows {t k : ℕ} (emb : Fin k ↪ ι) (p : Fin t × Fin k) :
    AGL24.RIMRowIdx (fullEdges ι t) :=
  ⟨emb p.2, ⟨blockVertex p.1, mem_univ _, 0, mem_univ _, zero_lt_blockVertex p.1⟩⟩

theorem univ_min'_eq_zero {t : ℕ} (h : (univ : Finset (Fin (t + 1))).Nonempty) :
    (univ : Finset (Fin (t + 1))).min' h = 0 :=
  le_antisymm (min'_le _ _ (mem_univ _)) (Fin.zero_le _)

omit [Fintype ι] [DecidableEq ι] in
/-- Entries of the selected minor: the Vandermonde row in block `0`, its negation in the row's
own block, and zero elsewhere. -/
theorem rim_fullRows_apply {t k : ℕ} (emb : Fin k ↪ ι) (p q : Fin t × Fin k) :
    AGL24.RIM F (fullEdges ι t) (fullRows emb p) q =
      if q.1.val = 0 then (X (emb p.2) : MvPolynomial ι F) ^ (q.2 : ℕ)
      else if q.1 = p.1 then -((X (emb p.2) : MvPolynomial ι F) ^ (q.2 : ℕ))
      else 0 := by
  simp only [AGL24.RIM, fullRows, univ_min'_eq_zero]
  have h0 : q.1.castSucc = (0 : Fin (t + 1)) ↔ q.1.val = 0 := by
    rw [Fin.ext_iff]; simp
  by_cases hq : q.1.val = 0
  · rw [if_pos (h0.2 hq), if_pos hq]
  · rw [if_neg (fun h => hq (h0.1 h)), if_neg hq]
    have hv : q.1.castSucc = blockVertex p.1 ↔ q.1 = p.1 := by
      unfold blockVertex
      split_ifs with hp
      · constructor
        · intro h
          exact absurd h (Fin.castSucc_ne_last q.1)
        · intro h
          exact absurd (h ▸ hp) hq
      · exact Fin.castSucc_inj
    by_cases hqp : q.1 = p.1
    · rw [if_pos (hv.2 hqp), if_pos hqp]
    · rw [if_neg (fun h => hqp (hv.1 h)), if_neg hqp]

omit [Fintype ι] [DecidableEq ι] in
/-- The selected minor is block triangular for the block map `p ↦ p.1.rev`: an entry is
nonzero only in block `0` (the largest under `rev`) or in the row's own block. -/
theorem fullRowsMinor_blockTriangular {t k : ℕ} (emb : Fin k ↪ ι) :
    ((AGL24.RIM F (fullEdges ι t)).submatrix (fullRows emb) id).BlockTriangular
      (fun p : Fin t × Fin k => p.1.rev) := by
  intro p q hlt
  rw [Matrix.submatrix_apply, id, rim_fullRows_apply]
  have hpq : p.1 < q.1 := Fin.rev_lt_rev.1 hlt
  have hq : q.1.val ≠ 0 := by
    have := Fin.lt_def.1 hpq
    omega
  rw [if_neg hq, if_neg (ne_of_gt hpq)]

/-- The rows of block `a` (under `p ↦ p.1.rev`) are indexed by `Fin k`. -/
def blockEquiv {t k : ℕ} (a : Fin t) : Fin k ≃ {p : Fin t × Fin k // p.1.rev = a} where
  toFun m := ⟨(a.rev, m), Fin.rev_rev a⟩
  invFun p := p.1.2
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨⟨c, m⟩, hp⟩ := p
    simp only at hp
    subst hp
    simp [Fin.rev_rev]

omit [Fintype ι] [DecidableEq ι] in
/-- Every diagonal block, reindexed by `Fin k`, is the Vandermonde matrix of `X (emb ·)`
(block `0`) or its negation (every other block). -/
theorem fullRowsMinor_block_eq {t k : ℕ} (emb : Fin k ↪ ι) (a : Fin t) :
    (((AGL24.RIM F (fullEdges ι t)).submatrix (fullRows emb) id).toSquareBlock
      (fun p : Fin t × Fin k => p.1.rev) a).submatrix (blockEquiv a) (blockEquiv a) =
      if a.rev.val = 0 then Matrix.vandermonde (fun m => (X (emb m) : MvPolynomial ι F))
      else -Matrix.vandermonde (fun m => (X (emb m) : MvPolynomial ι F)) := by
  ext m m'
  simp only [Matrix.submatrix_apply, Matrix.toSquareBlock_def, blockEquiv, Equiv.coe_fn_mk,
    Matrix.of_apply, id, rim_fullRows_apply]
  split_ifs <;> simp_all [Matrix.vandermonde_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- The Vandermonde determinant of `X (emb ·)` is homogeneous. -/
theorem det_vandermonde_X_isHomogeneous {k : ℕ} (emb : Fin k ↪ ι) :
    (Matrix.vandermonde (fun m => (X (emb m) : MvPolynomial ι F))).det.IsHomogeneous
      (∑ i : Fin k, ∑ _j ∈ Ioi i, 1) := by
  rw [Matrix.det_vandermonde]
  exact IsHomogeneous.prod _ _ _ fun i _ =>
    IsHomogeneous.prod _ _ _ fun j _ => (isHomogeneous_X F _).sub (isHomogeneous_X F _)

omit [Fintype ι] [DecidableEq ι] in
theorem det_vandermonde_X_ne_zero {k : ℕ} (emb : Fin k ↪ ι) :
    (Matrix.vandermonde (fun m => (X (emb m) : MvPolynomial ι F))).det ≠ 0 :=
  Matrix.det_vandermonde_ne_zero_iff.2 fun _ _ h => emb.injective (X_injective h)

omit [Fintype ι] [DecidableEq ι] in
/-- Each diagonal block's determinant is `±` the Vandermonde determinant. -/
theorem fullRowsMinor_block_det {t k : ℕ} (emb : Fin k ↪ ι) (a : Fin t) :
    (((AGL24.RIM F (fullEdges ι t)).submatrix (fullRows emb) id).toSquareBlock
        (fun p : Fin t × Fin k => p.1.rev) a).det =
        (Matrix.vandermonde (fun m => (X (emb m) : MvPolynomial ι F))).det ∨
      (((AGL24.RIM F (fullEdges ι t)).submatrix (fullRows emb) id).toSquareBlock
        (fun p : Fin t × Fin k => p.1.rev) a).det =
        -(Matrix.vandermonde (fun m => (X (emb m) : MvPolynomial ι F))).det := by
  rw [← Matrix.det_submatrix_equiv_self (blockEquiv a), fullRowsMinor_block_eq]
  split_ifs
  · exact Or.inl rfl
  · rw [Matrix.det_neg, Fintype.card_fin]
    rcases neg_one_pow_eq_or (MvPolynomial ι F) k with h | h <;> rw [h] <;> simp

theorem image_rev_fst_eq_univ {t k : ℕ} (hk : 0 < k) :
    (univ : Finset (Fin t × Fin k)).image (fun p => p.1.rev) = univ :=
  eq_univ_iff_forall.2 fun a =>
    mem_image.2 ⟨(a.rev, ⟨0, hk⟩), mem_univ _, Fin.rev_rev a⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **The full-edge minor's determinant is homogeneous of degree `t · d`.** -/
theorem fullRowsMinor_det_isHomogeneous {t k : ℕ} (hk : 0 < k) (emb : Fin k ↪ ι) :
    ((AGL24.RIM F (fullEdges ι t)).submatrix (fullRows emb) id).det.IsHomogeneous
      (t * ∑ i : Fin k, ∑ _j ∈ Ioi i, 1) := by
  classical
  rw [(fullRowsMinor_blockTriangular emb).det]
  have hdeg : ∑ _a ∈ (univ : Finset (Fin t × Fin k)).image (fun p => p.1.rev),
      (∑ i : Fin k, ∑ _j ∈ Ioi i, 1) = t * ∑ i : Fin k, ∑ _j ∈ Ioi i, 1 := by
    rw [sum_const, image_rev_fst_eq_univ hk, card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← hdeg]
  refine IsHomogeneous.prod _ _ _ fun a _ => ?_
  rcases fullRowsMinor_block_det (F := F) emb a with h | h <;> rw [h]
  · exact det_vandermonde_X_isHomogeneous emb
  · exact (det_vandermonde_X_isHomogeneous emb).neg

omit [Fintype ι] [DecidableEq ι] in
/-- **The full-edge minor is nonzero.** -/
theorem fullRowsMinor_det_ne_zero {t k : ℕ} (emb : Fin k ↪ ι) :
    ((AGL24.RIM F (fullEdges ι t)).submatrix (fullRows emb) id).det ≠ 0 := by
  classical
  rw [(fullRowsMinor_blockTriangular emb).det]
  refine prod_ne_zero_iff.2 fun a _ => ?_
  rcases fullRowsMinor_block_det (F := F) emb a with h | h <;> rw [h]
  · exact det_vandermonde_X_ne_zero emb
  · exact neg_ne_zero.2 (det_vandermonde_X_ne_zero emb)

/-- The Vandermonde degree is positive once `k ≥ 2`. -/
theorem one_le_vandermonde_degree {k : ℕ} (hk : 2 ≤ k) : 1 ≤ ∑ i : Fin k, ∑ _j ∈ Ioi i, 1 := by
  have h0 : (∑ _j ∈ Ioi (⟨0, by omega⟩ : Fin k), 1) ≤ ∑ i : Fin k, ∑ _j ∈ Ioi i, 1 :=
    single_le_sum (f := fun i : Fin k => ∑ _j ∈ Ioi i, 1) (fun _ _ => Nat.zero_le _)
      (mem_univ _)
  have h1 : (∑ _j ∈ Ioi (⟨0, by omega⟩ : Fin k), 1) = k - 1 := by
    rw [sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]
    simp
  omega

/-- **`FieldLargeForMinor` is unsatisfiable for `2 ≤ k ≤ |ι|`.** For every finite field `F`,
the full-edge family at `t = |F|` has a nonzero minor that is homogeneous of degree
`|F| · d ≥ |F|`, which no `|F| > deg + C(|ι|, 2)` bound allows. -/
theorem not_fieldLargeForMinor [Fintype F] {k : ℕ} (hk : 2 ≤ k) (hkι : k ≤ Fintype.card ι) :
    ¬ FieldLargeForMinor ι F k := by
  intro h
  let emb : Fin k ↪ ι :=
    (Fin.castLEEmb hkι).trans (Fintype.equivFin ι).symm.toEmbedding
  have hne := fullRowsMinor_det_ne_zero (F := F) (t := Fintype.card F) emb
  have hlt := h (fullEdges ι (Fintype.card F)) (fullRows emb) hne
  rw [(fullRowsMinor_det_isHomogeneous (by omega) emb).totalDegree hne] at hlt
  have hd := one_le_vandermonde_degree hk
  have : Fintype.card F ≤ Fintype.card F * ∑ i : Fin k, ∑ _j ∈ Ioi i, 1 :=
    Nat.le_mul_of_pos_right _ hd
  omega

/-- **The `k = 2` instance**: `FieldLargeForMinor ι F 2` fails for every finite field `F`
whenever `ι` has two elements. -/
theorem not_fieldLargeForMinor_two [Fintype F] [Nontrivial ι] :
    ¬ FieldLargeForMinor ι F 2 :=
  not_fieldLargeForMinor le_rfl Fintype.one_lt_card

#print axioms fullRowsMinor_det_ne_zero
#print axioms not_fieldLargeForMinor
#print axioms not_fieldLargeForMinor_two

end ArkLib.GMMDS
