/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Geometry of codewords and the Johnson-bound Gram argument

This file develops the real-valued geometric embedding of words `ι → α` used to derive
Johnson-type list-size bounds. The embedding `emb` and inner product `codeInner` translate
agreement and Hamming distance into Euclidean data: `agree_add_hammingDist`,
`codeInner_eq_agree_sub`, and `codeInner_eq_card_mul_sub_hammingDist` relate the inner product
to agreement/distance, while `codeInner_self` computes the self inner product.

The Gram-matrix lemmas (`sum_sum_codeInner_nonneg`, `sum_sum_shiftInner_nonneg`,
`card_le_of_gram_bounds`) and their specializations (`shiftInner_diag_le`,
`shiftInner_offdiag_le`, `johnson_quadratic_cap`) culminate in the list-size bounds
`card_le_of_johnson_condition`, `card_le_of_johnson_sq`, and `card_le_of_johnson_sq_dist`.
-/

namespace CodeGeometry
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def emb (w : ι → α) : ι × α → ℝ :=
  fun p => (if w p.1 = p.2 then 1 else 0) - 1 / (Fintype.card α : ℝ)

noncomputable def codeInner (u v : ι → α) : ℝ := ∑ p : ι × α, emb u p * emb v p
def agree (u v : ι → α) : ℕ := (Finset.univ.filter (fun i => u i = v i)).card

omit [DecidableEq ι] [Fintype α] in
/-- Agreement and Hamming distance partition the coordinate set. -/
theorem agree_add_hammingDist (u v : ι → α) :
    agree u v + hammingDist u v = Fintype.card ι := by
  classical
  simpa [agree, hammingDist] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i => u i = v i))

omit [Fintype ι] [DecidableEq ι] in
/-- Per-coordinate inner-product identity. -/
private lemma row_identity (u v : ι → α) (i : ι) (hq : 0 < Fintype.card α) :
    (∑ a : α, ((if u i = a then (1:ℝ) else 0) - 1/(Fintype.card α:ℝ))
              * ((if v i = a then 1 else 0) - 1/(Fintype.card α:ℝ)))
      = (if u i = v i then (1:ℝ) else 0) - 1/(Fintype.card α:ℝ) := by
  classical
  set q : ℝ := (Fintype.card α : ℝ) with hqdef
  have hqne : q ≠ 0 := by positivity
  have hprod : ∀ a : α,
      ((if u i = a then (1:ℝ) else 0) - 1/q) * ((if v i = a then 1 else 0) - 1/q)
      = (if u i = a then (1:ℝ) else 0) * (if v i = a then 1 else 0)
        - (1/q) * (if u i = a then (1:ℝ) else 0)
        - (1/q) * (if v i = a then (1:ℝ) else 0)
        + (1/q)*(1/q) := by intro a; ring
  rw [Finset.sum_congr rfl (fun a _ => hprod a)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  -- ∑ indicator products = if u i = v i then 1 else 0
  have h1 : (∑ a : α, (if u i = a then (1:ℝ) else 0) * (if v i = a then 1 else 0))
      = if u i = v i then 1 else 0 := by
    rw [Finset.sum_eq_single (u i)]
    · by_cases h : u i = v i <;> simp [h, eq_comm]
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : (∑ a : α, (1/q) * (if u i = a then (1:ℝ) else 0)) = 1/q := by
    rw [← Finset.mul_sum]; simp
  have h3 : (∑ a : α, (1/q) * (if v i = a then (1:ℝ) else 0)) = 1/q := by
    rw [← Finset.mul_sum]; simp
  have h4 : (∑ _a : α, (1/q)*(1/q)) = 1/q := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hqdef]
    field_simp
  rw [h1, h2, h3, h4]; ring

omit [DecidableEq ι] in
theorem codeInner_eq_agree_sub (u v : ι → α) (hq : 0 < Fintype.card α) :
    codeInner u v = (agree u v : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ) := by
  classical
  rw [codeInner, Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun i _ => by
    simpa [emb] using row_identity u v i hq)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [agree, Finset.card_filter, Nat.cast_sum, ← div_eq_mul_inv]
  congr 1
  apply Finset.sum_congr rfl; intro i _; by_cases h : u i = v i <;> simp [h]

omit [DecidableEq ι] in
/-- Simplex inner products are constant norm minus Hamming distance. -/
theorem codeInner_eq_card_mul_sub_hammingDist (u v : ι → α) (hq : 0 < Fintype.card α) :
    codeInner u v =
      (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) -
        (hammingDist u v : ℝ) := by
  have hdist_le : hammingDist u v ≤ Fintype.card ι := hammingDist_le_card_fintype
  have hagree :
      (agree u v : ℝ) = (Fintype.card ι : ℝ) - (hammingDist u v : ℝ) := by
    have hsum := agree_add_hammingDist u v
    have hsub : agree u v = Fintype.card ι - hammingDist u v := by omega
    rw [hsub]
    exact (Nat.cast_sub hdist_le :
      ((Fintype.card ι - hammingDist u v : ℕ) : ℝ) =
        (Fintype.card ι : ℝ) - (hammingDist u v : ℝ))
  rw [codeInner_eq_agree_sub u v hq, hagree]
  ring

omit [DecidableEq ι] in
/-- **Constant norm.** `⟨x_w, x_w⟩ = n(1 − 1/q)` (every coordinate agrees with
itself). -/
theorem codeInner_self (w : ι → α) (hq : 0 < Fintype.card α) :
    codeInner w w = (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) := by
  have hself : agree w w = Fintype.card ι := by
    rw [agree]
    simp [Finset.filter_true_of_mem, Finset.card_univ]
  rw [codeInner_eq_agree_sub w w hq, hself]
  have hqne : (Fintype.card α : ℝ) ≠ 0 := by positivity
  field_simp

omit [DecidableEq ι] in
/-- **The Plotkin / positive-semidefiniteness inequality.** For any finite
family of words, the Gram-sum of their simplex embeddings is nonnegative:
`∑ i ∑ j ⟨x_{c i}, x_{c j}⟩ = ‖∑ i x_{c i}‖² ≥ 0`. This is the engine of the
quadratic-in-`L` counting in Johnson-type list-size bounds. -/
theorem sum_sum_codeInner_nonneg {L : ℕ} (c : Fin L → ι → α) :
    0 ≤ ∑ i, ∑ j, codeInner (c i) (c j) := by
  classical
  have hswap : (∑ i, ∑ j, codeInner (c i) (c j))
      = ∑ p : ι × α, (∑ i, emb (c i) p) ^ 2 := by
    calc (∑ i, ∑ j, codeInner (c i) (c j))
        = ∑ i, ∑ j, ∑ p : ι × α, emb (c i) p * emb (c j) p := rfl
      _ = ∑ i, ∑ p : ι × α, ∑ j, emb (c i) p * emb (c j) p := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact Finset.sum_comm
      _ = ∑ p : ι × α, ∑ i, ∑ j, emb (c i) p * emb (c j) p := Finset.sum_comm
      _ = ∑ p : ι × α, (∑ i, emb (c i) p) ^ 2 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [sq, Finset.sum_mul_sum]
  rw [hswap]
  exact Finset.sum_nonneg fun p _ => sq_nonneg _

omit [DecidableEq ι] in
/-- Ordered-pair Plotkin upper bound for a finite indexed family, in total-distance
form. This is the simplex-embedding step needed before translating to the
Johnson-bound average-distance notation. -/
theorem sum_sum_hammingDist_le {L : ℕ} (c : Fin L → ι → α)
    (hq : 0 < Fintype.card α) :
    (∑ i : Fin L, ∑ j : Fin L, (hammingDist (c i) (c j) : ℝ)) ≤
      (L : ℝ) * (L : ℝ) * ((Fintype.card ι : ℝ) *
        (1 - 1 / (Fintype.card α : ℝ))) := by
  classical
  have hpsd := sum_sum_codeInner_nonneg (ι := ι) (α := α) c
  have hrewrite :
      (∑ i : Fin L, ∑ j : Fin L, codeInner (c i) (c j)) =
        ∑ i : Fin L, ∑ j : Fin L,
          ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) -
            (hammingDist (c i) (c j) : ℝ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    exact codeInner_eq_card_mul_sub_hammingDist (c i) (c j) hq
  rw [hrewrite] at hpsd
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hpsd
  nlinarith

omit [DecidableEq ι] in
/-- **Shifted PSD.** The Gram-sum of the center-shifted embeddings
`y_i = x_{c i} − β·x_g` is nonnegative — the form of the Plotkin inequality
actually used in Johnson list-size arguments. -/
theorem sum_sum_shiftInner_nonneg {L : ℕ} (c : Fin L → ι → α) (g : ι → α) (β : ℝ) :
    0 ≤ ∑ i, ∑ j, (codeInner (c i) (c j)
      - β * codeInner (c i) g - β * codeInner (c j) g
      + β ^ 2 * codeInner g g) := by
  classical
  have hswap : (∑ i, ∑ j, (codeInner (c i) (c j)
      - β * codeInner (c i) g - β * codeInner (c j) g
      + β ^ 2 * codeInner g g))
      = ∑ p : ι × α, (∑ i, (emb (c i) p - β * emb g p)) ^ 2 := by
    calc (∑ i, ∑ j, (codeInner (c i) (c j)
        - β * codeInner (c i) g - β * codeInner (c j) g
        + β ^ 2 * codeInner g g))
        = ∑ i, ∑ j, ∑ p : ι × α,
            (emb (c i) p - β * emb g p) * (emb (c j) p - β * emb g p) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          simp only [codeInner, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ = ∑ i, ∑ p : ι × α, ∑ j,
            (emb (c i) p - β * emb g p) * (emb (c j) p - β * emb g p) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact Finset.sum_comm
      _ = ∑ p : ι × α, ∑ i, ∑ j,
            (emb (c i) p - β * emb g p) * (emb (c j) p - β * emb g p) :=
          Finset.sum_comm
      _ = ∑ p : ι × α, (∑ i, (emb (c i) p - β * emb g p)) ^ 2 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [sq, Finset.sum_mul_sum]
  rw [hswap]
  exact Finset.sum_nonneg fun p _ => sq_nonneg _

/-- **Abstract Gram counting.** If a symmetric-style Gram-sum is nonnegative,
the diagonal entries are at most `Dd`, and the off-diagonal entries are at most
`Do < 0`, then the family size obeys `(L−1)·(−Do) ≤ Dd` — the quadratic-in-`L`
cap of the Johnson list-size bound. -/
theorem card_le_of_gram_bounds {L : ℕ} (hL : 0 < L) (S : Fin L → Fin L → ℝ)
    {Dd Do : ℝ} (hpsd : 0 ≤ ∑ i, ∑ j, S i j)
    (hdiag : ∀ i, S i i ≤ Dd)
    (hoff : ∀ i j, i ≠ j → S i j ≤ Do) (hDo : Do < 0) :
    ((L : ℝ) - 1) * (-Do) ≤ Dd := by
  classical
  -- pick any i₀ and bound its row? No: use the full-sum bound.
  -- Σᵢⱼ S i j = Σᵢ S i i + Σᵢ Σ_{j≠i} S i j ≤ L·Dd + L(L−1)·Do
  have hdiag_sum : (∑ i, S i i) ≤ (L : ℝ) * Dd := by
    calc (∑ i, S i i) ≤ ∑ _i : Fin L, Dd := Finset.sum_le_sum fun i _ => hdiag i
      _ = (L : ℝ) * Dd := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  have hoff_sum : (∑ i, ∑ j ∈ Finset.univ.erase i, S i j)
      ≤ (L : ℝ) * ((L : ℝ) - 1) * Do := by
    have hrow : ∀ i : Fin L, (∑ j ∈ Finset.univ.erase i, S i j) ≤ ((L : ℝ) - 1) * Do := by
      intro i
      have hcard : (Finset.univ.erase i).card = L - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      calc (∑ j ∈ Finset.univ.erase i, S i j)
          ≤ ∑ _j ∈ Finset.univ.erase i, Do :=
            Finset.sum_le_sum fun j hj => hoff i j (Finset.ne_of_mem_erase hj).symm
        _ = ((L : ℝ) - 1) * Do := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
            congr 1
            have : (1 : ℕ) ≤ L := hL
            push_cast [Nat.cast_sub this]
            ring
    calc (∑ i, ∑ j ∈ Finset.univ.erase i, S i j)
        ≤ ∑ _i : Fin L, ((L : ℝ) - 1) * Do := Finset.sum_le_sum fun i _ => hrow i
      _ = (L : ℝ) * (((L : ℝ) - 1) * Do) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (L : ℝ) * ((L : ℝ) - 1) * Do := by ring
  have hdecomp : (∑ i, ∑ j, S i j)
      = (∑ i, S i i) + ∑ i, ∑ j ∈ Finset.univ.erase i, S i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase Finset.univ (S i) (Finset.mem_univ i)]
  have hfull : (0 : ℝ) ≤ (L : ℝ) * Dd + (L : ℝ) * ((L : ℝ) - 1) * Do := by
    calc (0 : ℝ) ≤ ∑ i, ∑ j, S i j := hpsd
      _ = (∑ i, S i i) + ∑ i, ∑ j ∈ Finset.univ.erase i, S i j := hdecomp
      _ ≤ (L : ℝ) * Dd + (L : ℝ) * ((L : ℝ) - 1) * Do := add_le_add hdiag_sum hoff_sum
  -- rearrange: L(L−1)(−Do) ≤ L·Dd, divide by L > 0
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hDo_le : Do ≤ 0 := le_of_lt hDo
  nlinarith [hfull, hLpos, hDo_le]

omit [DecidableEq ι] in
/-- Diagonal bound for the shifted Gram entries: if the listed word agrees with
the center on at least `A` coordinates, then (with `β ≥ 0`)
`⟨y,y⟩ ≤ n(1−1/q)(1+β²) − 2β(A − n/q)`. -/
theorem shiftInner_diag_le (hq : 0 < Fintype.card α)
    {f w : ι → α} {A : ℕ} (hA : A ≤ agree w f) {β : ℝ} (hβ : 0 ≤ β) :
    codeInner w w - β * codeInner w f - β * codeInner w f + β ^ 2 * codeInner f f
      ≤ (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)) := by
  have h1 := codeInner_self w hq
  have h2 := codeInner_eq_agree_sub w f hq
  have h3 := codeInner_self f hq
  rw [h1, h2, h3]
  have hAle : (A : ℝ) ≤ (agree w f : ℝ) := by exact_mod_cast hA
  nlinarith [hβ, hAle]

omit [DecidableEq ι] in
/-- Off-diagonal bound: if two listed words agree with the center on at least
`A` coordinates each, and with each other on at most `B` coordinates, then
(with `β ≥ 0`)
`⟨y_i,y_j⟩ ≤ (B − n/q) − 2β(A − n/q) + β²·n(1−1/q)`. -/
theorem shiftInner_offdiag_le (hq : 0 < Fintype.card α)
    {f u v : ι → α} {A B : ℕ}
    (hAu : A ≤ agree u f) (hAv : A ≤ agree v f) (hB : agree u v ≤ B)
    {β : ℝ} (hβ : 0 ≤ β) :
    codeInner u v - β * codeInner u f - β * codeInner v f + β ^ 2 * codeInner f f
      ≤ ((B : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) := by
  have h1 := codeInner_eq_agree_sub u v hq
  have h2 := codeInner_eq_agree_sub u f hq
  have h3 := codeInner_eq_agree_sub v f hq
  have h4 := codeInner_self f hq
  rw [h1, h2, h3, h4]
  have hAu' : (A : ℝ) ≤ (agree u f : ℝ) := by exact_mod_cast hAu
  have hAv' : (A : ℝ) ≤ (agree v f : ℝ) := by exact_mod_cast hAv
  have hB' : (agree u v : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  nlinarith [hβ, hAu', hAv', hB']

omit [DecidableEq ι] in
/-- **The abstract Johnson list-size cap.** Let `f` be a center and
`c : Fin L → ι → α` a family of words each agreeing with `f` on at least `A`
coordinates and pairwise agreeing on at most `B` coordinates. For any shift
parameter `β ≥ 0` making the off-diagonal Gram bound
`Do := (B − n/q) − 2β(A − n/q) + β²·n(1−1/q)` negative, the family size obeys
the quadratic cap `(L − 1)·(−Do) ≤ Dd` with
`Dd := n(1−1/q)(1+β²) − 2β(A − n/q)`.

Composes the simplex-embedding identities, the shifted PSD inequality, and the
Gram counting lemma; instantiating `A`/`B`/`β` at the `J_{q,ℓ}` radius yields
the q-ary Johnson list-size bound (ABF26 Theorem 3.2). -/
theorem johnson_quadratic_cap (hq : 0 < Fintype.card α) {L : ℕ} (hL : 0 < L)
    (f : ι → α) (c : Fin L → ι → α) {A B : ℕ}
    (hA : ∀ i, A ≤ agree (c i) f)
    (hB : ∀ i j, i ≠ j → agree (c i) (c j) ≤ B)
    {β : ℝ} (hβ : 0 ≤ β)
    (hDo : ((B : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) < 0) :
    ((L : ℝ) - 1) *
      (-(((B : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))))
      ≤ (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)) := by
  classical
  set S : Fin L → Fin L → ℝ := fun i j =>
    codeInner (c i) (c j) - β * codeInner (c i) f - β * codeInner (c j) f
      + β ^ 2 * codeInner f f with hS
  refine card_le_of_gram_bounds hL S ?_ ?_ ?_ hDo
  · -- PSD
    simpa [hS] using sum_sum_shiftInner_nonneg c f β
  · -- diagonal
    intro i
    simpa [hS] using shiftInner_diag_le hq (hA i) hβ
  · -- off-diagonal
    intro i j hij
    simpa [hS] using shiftInner_offdiag_le hq (hA i) (hA j) (hB i j hij) hβ

omit [DecidableEq ι] in
/-- **Radical-free Johnson list-size bound (finite form).** Under the
agreement/distance constraints of `johnson_quadratic_cap`, if the shift
parameter additionally satisfies `Dd + ℓ·Do < 0`, then `L ≤ ℓ`. Stated without
square roots: instantiating `β` optimally at the `J_{q,ℓ}` radius discharges
the side condition, recovering ABF26 Theorem 3.2. -/
theorem card_le_of_johnson_condition (hq : 0 < Fintype.card α) {L : ℕ} (hL : 0 < L)
    (f : ι → α) (c : Fin L → ι → α) {A B : ℕ} (ℓ : ℕ)
    (hA : ∀ i, A ≤ agree (c i) f)
    (hB : ∀ i j, i ≠ j → agree (c i) (c j) ≤ B)
    {β : ℝ} (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))
      + (ℓ : ℝ) * (((B : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) < 0) :
    L ≤ ℓ := by
  classical
  -- Dd is nonnegative: it dominates the (PSD-nonnegative) single-word Gram entry
  have hDd_nonneg : (0 : ℝ) ≤
      ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))) := by
    have hpsd := sum_sum_shiftInner_nonneg (fun _ : Fin 1 => c ⟨0, hL⟩) f β
    simp only [Fin.sum_univ_one] at hpsd
    have hdiag := shiftInner_diag_le hq (hA ⟨0, hL⟩) hβ
    linarith [hpsd, hdiag]
  -- hence Do < 0
  have hDo_neg : (((B : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) < 0 := by
    rcases lt_or_ge (((B : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) 0 with h | h
    · exact h
    · exfalso
      have hnn : (0 : ℝ) ≤
          (ℓ : ℝ) * (((B : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) :=
        mul_nonneg (by positivity) h
      linarith [hcond, hDd_nonneg, hnn]
  -- the quadratic cap
  have hcap := johnson_quadratic_cap hq hL f c hA hB hβ hDo_neg
  -- finish: (L−1)(−Do) ≤ Dd < ℓ(−Do), −Do > 0 ⟹ L−1 < ℓ
  have hfin : ((L : ℝ) - 1) < (ℓ : ℝ) := by
    nlinarith [hcap, hcond, hDo_neg]
  have : (L : ℝ) < (ℓ : ℝ) + 1 := by linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

omit [DecidableEq ι] in
/-- **Optimal-β squared-form q-ary Johnson list-size bound.** With center
correlation `P := A − n/q ≥ 0`, block parameter `N := n(1−1/q) > 0`, and the
squared Johnson condition `(ℓ+1)·P² > N·(N + ℓ·(B − n/q))`, the family size
obeys `L ≤ ℓ`. The optimal shift `β = P/N` discharges the
`card_le_of_johnson_condition` side condition exactly into `hsq`. This is the
radical-free form of ABF26 Theorem 3.2. -/
theorem card_le_of_johnson_sq (hq1 : 1 < Fintype.card α) (hn : 0 < Fintype.card ι)
    {L : ℕ} (hL : 0 < L)
    (f : ι → α) (c : Fin L → ι → α) {A B : ℕ} (ℓ : ℕ)
    (hA : ∀ i, A ≤ agree (c i) f)
    (hB : ∀ i j, i ≠ j → agree (c i) (c j) ≤ B)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card α : ℝ) ≤ (A : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))
            + (ℓ : ℝ) * ((B : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))) :
    L ≤ ℓ := by
  classical
  set nR : ℝ := (Fintype.card ι : ℝ) with hnR
  set qR : ℝ := (Fintype.card α : ℝ) with hqR
  have hqpos : (0 : ℝ) < qR := by rw [hqR]; positivity
  have hq1R : (1 : ℝ) < qR := by rw [hqR]; exact_mod_cast hq1
  have hnpos : (0 : ℝ) < nR := by rw [hnR]; exact_mod_cast hn
  have hq_ne : qR ≠ 0 := ne_of_gt hqpos
  have hfrac : (1 : ℝ) / qR < 1 := by rw [div_lt_one hqpos]; exact hq1R
  have hμpos : (0 : ℝ) < 1 - 1 / qR := by linarith
  have hNpos : (0 : ℝ) < nR * (1 - 1 / qR) := by positivity
  have hNne : nR * (1 - 1 / qR) ≠ 0 := ne_of_gt hNpos
  have hPnn : (0 : ℝ) ≤ (A : ℝ) - nR / qR := by rw [hnR, hqR]; linarith [hP]
  refine card_le_of_johnson_condition (by omega : 0 < Fintype.card α) hL f c ℓ hA hB
    (β := ((A : ℝ) - nR / qR) / (nR * (1 - 1 / qR)))
    (div_nonneg hPnn (le_of_lt hNpos)) ?_
  rw [← hnR, ← hqR]
  have hμne : (1 : ℝ) - 1 / qR ≠ 0 := ne_of_gt hμpos
  have hnRne : nR ≠ 0 := ne_of_gt hnpos
  have hqm1 : qR - 1 ≠ 0 := by linarith
  have hμeq : (1 : ℝ) - 1 / qR = (qR - 1) / qR := by field_simp
  -- the side-condition LHS, at β = (A−n/q)/(n(1−1/q)), equals NUM / (n(1−1/q))
  have hid :
      nR * (1 - 1 / qR)
          * (1 + (((A : ℝ) - nR / qR) / (nR * (1 - 1 / qR))) ^ 2)
        - 2 * (((A : ℝ) - nR / qR) / (nR * (1 - 1 / qR))) * ((A : ℝ) - nR / qR)
        + (ℓ : ℝ) * (((B : ℝ) - nR / qR)
            - 2 * (((A : ℝ) - nR / qR) / (nR * (1 - 1 / qR))) * ((A : ℝ) - nR / qR)
            + (((A : ℝ) - nR / qR) / (nR * (1 - 1 / qR))) ^ 2 * nR * (1 - 1 / qR))
      = (nR * (1 - 1 / qR)
            * (nR * (1 - 1 / qR) + (ℓ : ℝ) * ((B : ℝ) - nR / qR))
          - ((ℓ : ℝ) + 1) * ((A : ℝ) - nR / qR) ^ 2) / (nR * (1 - 1 / qR)) := by
    simp only [hμeq]
    field_simp
    ring
  rw [hid]
  apply div_neg_of_neg_of_pos _ hNpos
  rw [hnR, hqR] at hsq
  nlinarith [hsq]

omit [DecidableEq ι] in
/-- **q-ary Johnson list-size bound, distance form.** A family of words each
within Hamming distance `e` of a center `f`, pairwise at Hamming distance `≥ d`
(the code minimum distance), has size `≤ ℓ` whenever the squared Johnson
condition `(ℓ+1)(n−e−n/q)² > N(N + ℓ(n−d−n/q))` holds (`N := n(1−1/q)`,
`n−e ≥ n/q`). This is the directly-consumable code-distance form of ABF26
Theorem 3.2 — the `agree`-based `card_le_of_johnson_sq` with `A = n−e`,
`B = n−d` supplied from the `agree ↔ hammingDist` bridge. -/
theorem card_le_of_johnson_sq_dist (hq1 : 1 < Fintype.card α) (hn : 0 < Fintype.card ι)
    {L : ℕ} (hL : 0 < L)
    (f : ι → α) (c : Fin L → ι → α) {e d : ℕ} (ℓ : ℕ)
    (hclose : ∀ i, hammingDist (c i) f ≤ e)
    (hdist : ∀ i j, i ≠ j → d ≤ hammingDist (c i) (c j))
    (hP :
      (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)
        ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * (((Fintype.card ι - e : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - d : ℕ) : ℝ)
              - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))) :
    L ≤ ℓ := by
  classical
  -- A := n − e is a lower bound for each agree(c i, f)
  have hA : ∀ i, (Fintype.card ι - e) ≤ agree (c i) f := by
    intro i
    have hbridge := agree_add_hammingDist (c i) f
    have := hclose i
    omega
  -- B := n − d is an upper bound for each pairwise agree
  have hB : ∀ i j, i ≠ j → agree (c i) (c j) ≤ (Fintype.card ι - d) := by
    intro i j hij
    have hbridge := agree_add_hammingDist (c i) (c j)
    have := hdist i j hij
    omega
  exact card_le_of_johnson_sq hq1 hn hL f c ℓ hA hB hP hsq

end CodeGeometry
