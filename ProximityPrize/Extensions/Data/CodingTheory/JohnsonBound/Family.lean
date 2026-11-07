/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.JohnsonBound.Family

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.JohnsonBound.Basic
import ProximityPrize.Extensions.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.CodeGeometry
import Mathlib.Algebra.Order.Chebyshev

/-!
# ABF26 §3.1 — Johnson family `J_{q,ℓ}, J_q, J` and Theorem 3.2 / Corollary 3.3

Extensions to `JohnsonBound/Basic.lean` matching the paper-shaped statements from
ABF26 §3.1 (Arnon-Boneh-Fenzi, *Open Problems in List Decoding and Correlated
Agreement*, 2026).

The existing `JohnsonBound.J q δ : ℝ` matches the paper's `J_q(δ)`. This file adds:

- Canonical `JohnsonBound.Jqℓ q ℓ δ` uses the corrected `(ℓ-1)/ℓ` factor.
  The former inverse-factor diagnostic is retired; the imported canonical theorem is authoritative.
- `JohnsonBound.Jcap δ` — paper's asymptotic Johnson bound `J(δ) := 1 - √(1 - δ)`.

The three are related by `J_{q,ℓ}(δ) →_{ℓ → ∞} J_q(δ) →_{q → ∞} J(δ)`; we state the
limit relationships in docstrings but do not formalise the limits (the paper does
not prove them either).

The file also states the paper-shaped versions of:

- `johnson_bound_lambda_le_ell` — ABF26 Theorem 3.2 [Joh62]:
  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`.
- `mds_johnson_lambda_le` — ABF26 Corollary 3.3:
  for any MDS code `C` of rate `ρ` and `η > 0`, `|Λ(C, 1 - √ρ - η)| ≤ 1/(2·η·ρ)`.

Both are admitted as external results (T3.2 has an existing in-tree proof via
`johnson_bound` / `johnson_bound_alphabet_free` in `JohnsonBound/Basic.lean` that
needs porting from the absolute-distance form to ABF26's `Lambda` form; C3.3
follows from L2.6 + T3.2, but uses the asymptotic Johnson radius which crosses
ArkLib's existing rate/distance bridge).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [Joh62] Johnson. (Original Johnson bound paper.)
-/

set_option linter.style.longFile 2000
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace JohnsonBound

open Real
open Finset

/-- Reciprocal finite-list Johnson radius reached by the current quadratic-cap
route, stated over reals for direct use with `Code.minDist C / n`.

This accepts real parameters, while canonical `Jqℓ` accepts rational parameters. Both now use
`(ℓ-1)/ℓ`; the former downstream `Jqℓ` with inverse factor `ℓ/(ℓ-1)` is retired. -/
noncomputable def JqℓRecipReal (q ℓ δ : ℝ) : ℝ :=
  (1 - 1 / q) *
    (1 - √(1 - (1 / (1 - 1 / q)) * ((ℓ - 1) / ℓ) * δ))

/-- Indexed q-ary Plotkin average-distance upper bound, with the same ordered-pair
normalisation as `JohnsonBound.d`.

This packages the simplex-embedding PSD bound from `CodeGeometry` into the
Johnson-bound denominator shape:
`2 * choose_2 M = M * (M - 1)`.

The statement is intentionally indexed by `Fin M`; the separate translation to
`Finset` images is the mechanical bridge needed by `johnson_bound_lambda_le_ell`. -/
theorem indexed_averageDist_le_plotkin
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    {M : ℕ} (c : Fin M → ι → α) (hM : 1 < M) (hq : 0 < Fintype.card α) :
    (1 : ℝ) / (2 * ((choose_2 (M : ℚ)) : ℝ)) *
        (∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (hammingDist (c i) (c j) : ℝ)) ≤
      (M : ℝ) / ((M : ℝ) - 1) *
        (Fintype.card ι : ℝ) *
          (1 - 1 / (Fintype.card α : ℝ)) := by
  classical
  let C0 : ℝ :=
    (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))
  have htotal := CodeGeometry.sum_sum_hammingDist_le (ι := ι) (α := α) c hq
  have hoff_le_total :
      (∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (hammingDist (c i) (c j) : ℝ)) ≤
        (∑ i : Fin M, ∑ j : Fin M,
          (hammingDist (c i) (c j) : ℝ)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      exact Finset.mem_univ j
    · intro j _ _
      exact_mod_cast Nat.zero_le (hammingDist (c i) (c j))
  have hoff_bound :
      (∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (hammingDist (c i) (c j) : ℝ)) ≤ (M : ℝ) * (M : ℝ) * C0 :=
    le_trans hoff_le_total htotal
  have hden :
      2 * (((choose_2 (M : ℚ)) : ℚ) : ℝ) = (M : ℝ) * ((M : ℝ) - 1) := by
    norm_num [choose_2]
    ring
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hM
  have hMsub_pos : 0 < (M : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast hM)
  have hden_nonneg : 0 ≤ 1 / ((M : ℝ) * ((M : ℝ) - 1)) := by
    positivity
  rw [hden]
  calc
    (1 : ℝ) / ((M : ℝ) * ((M : ℝ) - 1)) *
        (∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (hammingDist (c i) (c j) : ℝ))
        ≤ (1 : ℝ) / ((M : ℝ) * ((M : ℝ) - 1)) *
            ((M : ℝ) * (M : ℝ) * C0) :=
          mul_le_mul_of_nonneg_left hoff_bound hden_nonneg
    _ = (M : ℝ) / ((M : ℝ) - 1) * C0 := by
          field_simp [hMpos.ne', hMsub_pos.ne']
    _ = (M : ℝ) / ((M : ℝ) - 1) *
        (Fintype.card ι : ℝ) *
          (1 - 1 / (Fintype.card α : ℝ)) := by
          simp [C0, mul_assoc]

/-- Rewrites the indexed off-diagonal ordered-pair sum as a product-filter sum. -/
private lemma offdiag_sum_eq_product {M : ℕ} (f : Fin M → Fin M → ℝ) :
    (∑ i : Fin M, ∑ j ∈ (Finset.univ : Finset (Fin M)).erase i, f i j) =
      ∑ p ∈ (Finset.univ : Finset (Fin M × Fin M)) with p.1 ≠ p.2, f p.1 p.2 := by
  rw [Finset.sum_filter]
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [show (∑ y : Fin M, if (i, y).1 ≠ (i, y).2 then f (i, y).1 (i, y).2 else 0) =
      ∑ y : Fin M, if i ≠ y then f i y else 0 by rfl]
  rw [← Finset.sum_erase (s := (Finset.univ : Finset (Fin M))) (a := i)
      (f := fun y => if i ≠ y then f i y else 0) (by simp)]
  refine Finset.sum_congr rfl ?_
  intro y hy
  have hyne : i ≠ y := (Finset.mem_erase.mp hy).1.symm
  simp [hyne]

/-- Transports an indexed off-diagonal sum along `Finset.equivFin`. -/
private lemma offdiag_sum_equivFin
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α] (B : Finset (ι → α)) :
    (∑ i : Fin B.card, ∑ j ∈ (Finset.univ : Finset (Fin B.card)).erase i,
      (hammingDist ((Finset.equivFin B).symm i).1 ((Finset.equivFin B).symm j).1 : ℝ)) =
    ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (hammingDist x.1 x.2 : ℝ) := by
  rw [offdiag_sum_eq_product]
  let e : Fin B.card ≃ B := (Finset.equivFin B).symm
  let s : Finset (Fin B.card × Fin B.card) :=
    (Finset.univ : Finset (Fin B.card × Fin B.card)).filter (fun p => p.1 ≠ p.2)
  let t : Finset ((ι → α) × (ι → α)) := (B ×ˢ B).filter (fun x => x.1 ≠ x.2)
  change (∑ p ∈ s, (hammingDist (e p.1).1 (e p.2).1 : ℝ)) =
    ∑ x ∈ t, (hammingDist x.1 x.2 : ℝ)
  refine Finset.sum_bij (fun p _hp => ((e p.1).1, (e p.2).1)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [t, mem_filter, mem_product]
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    refine ⟨⟨(e p.1).2, (e p.2).2⟩, ?_⟩
    intro hval
    apply hpne
    exact e.injective (Subtype.ext hval)
  · intro p _hp q _hq h
    simp only [Prod.mk.injEq] at h
    cases p with
    | mk p₁ p₂ =>
      cases q with
      | mk q₁ q₂ =>
        simp only at h
        have h₁ : p₁ = q₁ := e.injective (Subtype.ext h.1)
        have h₂ : p₂ = q₂ := e.injective (Subtype.ext h.2)
        simp [h₁, h₂]
  · intro x hx
    simp only [t, mem_filter, mem_product] at hx
    let a : B := ⟨x.1, hx.1.1⟩
    let b : B := ⟨x.2, hx.1.2⟩
    refine ⟨(e.symm a, e.symm b), ?_, ?_⟩
    · simp only [s, mem_filter, mem_univ, true_and]
      intro hidx
      apply hx.2
      have hsub : a = b := e.symm.injective hidx
      exact congrArg Subtype.val hsub
    · simp [e, a, b]
  · intro p _hp
    rfl

/-- Ordered-pair average distance for a finite family over an arbitrary finite index type.

This is `JohnsonBound.d` without the historical `Fin n` restriction. -/
noncomputable def averageDistOn
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α] (B : Finset (ι → α)) : ℚ :=
  (1 : ℚ) / (2 * choose_2 B.card) *
    ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, Δ₀(x.1, x.2)

/-- Average absolute distance from a fixed center to a finite family. -/
noncomputable def averageDistToOn
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α]
    (B : Finset (ι → α)) (f : ι → α) : ℚ :=
  (1 : ℚ) / B.card * ∑ x ∈ B, Δ₀(f, x)

/-- If every word in a finite family has absolute distance at most `r` from `f`,
then its average absolute distance from `f` is at most `r`. -/
theorem averageDistToOn_real_le_of_forall_dist_le
    {ι : Type} [Fintype ι]
    {α : Type} [DecidableEq α]
    {B : Finset (ι → α)} {f : ι → α} {r : ℝ}
    (hB : 0 < B.card)
    (hdist : ∀ x ∈ B, (hammingDist f x : ℝ) ≤ r) :
    ((averageDistToOn B f : ℚ) : ℝ) ≤ r := by
  unfold averageDistToOn
  have hsum : (∑ x ∈ B, (hammingDist f x : ℝ)) ≤
      ∑ x ∈ B, r :=
    Finset.sum_le_sum hdist
  have hcard_pos : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hB
  calc
    ((1 : ℚ) / B.card * ∑ x ∈ B, Δ₀(f, x) : ℚ) =
        (1 : ℝ) / B.card * ∑ x ∈ B, (hammingDist f x : ℝ) := by
          simp [Nat.cast_sum]
    _ ≤ (1 : ℝ) / B.card * ∑ x ∈ B, r :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = r := by
          rw [sum_const, nsmul_eq_mul]
          field_simp [hcard_pos.ne']

/-- A relative-distance bound gives the corresponding absolute Hamming-distance
bound after multiplying by the block length. -/
lemma hammingDist_real_le_of_relHammingDist_le
    {ι : Type} [Fintype ι] [Nonempty ι]
    {α : Type} [DecidableEq α] {f c : ι → α} {δ : ℝ}
    (h : ((Code.relHammingDist f c : ℚ≥0) : ℝ) ≤ δ) :
    (hammingDist f c : ℝ) ≤ δ * (Fintype.card ι : ℝ) := by
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold Code.relHammingDist at h
  simp only [NNRat.cast_div, NNRat.cast_natCast] at h
  rw [div_le_iff₀ hn_pos] at h
  exact h

/-- A relative-distance bound also gives the corresponding integer absolute
Hamming-distance bound by flooring `δ · n`. -/
lemma hammingDist_le_floor_mul_card_of_relHammingDist_le
    {ι : Type} [Fintype ι] [Nonempty ι]
    {α : Type} [DecidableEq α] {f c : ι → α} {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ((Code.relHammingDist f c : ℚ≥0) : ℝ) ≤ δ) :
    hammingDist f c ≤ ⌊δ * (Fintype.card ι : ℝ)⌋₊ := by
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold Code.relHammingDist at h
  simp only [NNRat.cast_div, NNRat.cast_natCast] at h
  rw [div_le_iff₀ hn_pos] at h
  exact (Nat.le_floor_iff (mul_nonneg hδ (Nat.cast_nonneg _))).mpr h

/-- Elements of a finite point-list are within absolute radius `δ · n` of the
received word. -/
lemma hammingDist_real_le_of_mem_closeCodewordsRelFinset
    {ι : Type} [Fintype ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    {C : ListDecodable.Code ι α} {f c : ι → α} {δ : ℝ}
    (h : c ∈ ListDecodable.closeCodewordsRelFinset C f δ) :
    (hammingDist f c : ℝ) ≤ δ * (Fintype.card ι : ℝ) := by
  have hrel := (ListDecodable.mem_closeCodewordsRelFinset.mp h).2
  simp only [ListDecodable.relHammingBall, Set.mem_setOf_eq] at hrel
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold Code.relHammingDist at hrel
  simp only [NNRat.cast_div, NNRat.cast_natCast] at hrel
  rw [div_le_iff₀ hn_pos] at hrel
  convert hrel using 1
  congr

/-- Elements of a finite point-list are within integer radius
`⌊δ · n⌋₊` of the received word. -/
lemma hammingDist_le_floor_mul_card_of_mem_closeCodewordsRelFinset
    {ι : Type} [Fintype ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    {C : ListDecodable.Code ι α} {f c : ι → α} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (h : c ∈ ListDecodable.closeCodewordsRelFinset C f δ) :
    hammingDist f c ≤ ⌊δ * (Fintype.card ι : ℝ)⌋₊ := by
  have hrel := (ListDecodable.mem_closeCodewordsRelFinset.mp h).2
  simp only [ListDecodable.relHammingBall, Set.mem_setOf_eq] at hrel
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold Code.relHammingDist at hrel
  simp only [NNRat.cast_div, NNRat.cast_natCast] at hrel
  rw [div_le_iff₀ hn_pos] at hrel
  apply (Nat.le_floor_iff (mul_nonneg hδ (Nat.cast_nonneg _))).mpr
  convert hrel using 1
  congr

/-- A close-list word agrees with the received word on at least
`n - ⌊δ · n⌋₊` coordinates. -/
lemma card_sub_floor_mul_card_le_agree_of_mem_closeCodewordsRelFinset
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    {C : ListDecodable.Code ι α} {f c : ι → α} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (h : c ∈ ListDecodable.closeCodewordsRelFinset C f δ) :
    Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ ≤ CodeGeometry.agree c f := by
  have hdist := hammingDist_le_floor_mul_card_of_mem_closeCodewordsRelFinset hδ h
  have hsum := CodeGeometry.agree_add_hammingDist c f
  have hdist_symm : hammingDist c f = hammingDist f c := by
    unfold hammingDist
    simp_rw [ne_comm]
  rw [hdist_symm] at hsum
  omega

/-- The finite point-list average distance to its received word is bounded by
the relative radius times the block length. -/
theorem averageDistToOn_closeCodewordsRelFinset_le_radius_mul_card
    {ι : Type} [Fintype ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) (f : ι → α) (δ : ℝ)
    (hB : 0 < (ListDecodable.closeCodewordsRelFinset C f δ).card) :
    ((averageDistToOn (ListDecodable.closeCodewordsRelFinset C f δ) f : ℚ) : ℝ) ≤
      δ * (Fintype.card ι : ℝ) := by
  apply averageDistToOn_real_le_of_forall_dist_le hB
  intro x hx
  exact hammingDist_real_le_of_mem_closeCodewordsRelFinset hx

/-- Any two distinct members of a code are separated by at least `Code.minDist`. -/
lemma minDist_le_hammingDist_of_mem_ne
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α]
    {C : Set (ι → α)} {u v : ι → α}
    (hu : u ∈ C) (hv : v ∈ C) (hne : u ≠ v) :
    Code.minDist C ≤ hammingDist u v := by
  unfold Code.minDist
  apply Nat.sInf_le
  exact ⟨u, hu, v, hv, hne, rfl⟩

/-- The ordered off-diagonal pair count matches the Johnson `choose_2`
normalisation. -/
private lemma two_mul_choose_two_card_eq_offdiag_card
    {β : Type} [DecidableEq β] (B : Finset β) :
    2 * choose_2 (B.card : ℚ) = (({ x ∈ B ×ˢ B | x.1 ≠ x.2 }.card : ℕ) : ℚ) := by
  simp only [ne_eq]
  unfold choose_2
  ring_nf
  have BBcard : (B ×ˢ B).card = B.card ^ 2 := by rw [card_product, sq]
  have BBdiagcard : { x ∈ B ×ˢ B | x.1 = x.2 }.card = B.card := by simp
  have BBdisjoint : { x ∈ B ×ˢ B | x.1 = x.2 } ∩
      { x ∈ B ×ˢ B | x.1 ≠ x.2 } = ∅ := by
    grind only [= mem_inter, ← notMem_empty, = mem_filter]
  have BBunion : B ×ˢ B =
      { x ∈ B ×ˢ B | x.1 = x.2 } ∪ { x ∈ B ×ˢ B | x.1 ≠ x.2 } := by
    grind only [= mem_union, = mem_filter]
  have BBcount : { x ∈ B ×ˢ B | x.1 ≠ x.2 }.card =
      (B ×ˢ B).card - { x ∈ B ×ˢ B | x.1 = x.2 }.card := by
    grind only [usr card_filter_le, usr card_union_add_card_inter, = Finset.card_empty]
  rw [BBcount, BBcard, BBdiagcard, Nat.cast_sub]
  · grind only
  · grind only [usr card_filter_le]

/-- A finite sublist of a code has average pairwise distance at least the code
minimum distance. -/
theorem minDist_le_averageDistOn_of_subset
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α]
    {C : Set (ι → α)} {B : Finset (ι → α)}
    (hB : 1 < B.card) (hsub : ∀ x ∈ B, x ∈ C) :
    (Code.minDist C : ℚ) ≤ averageDistOn B := by
  unfold averageDistOn
  let dmin : ℚ := Code.minDist C
  have h_d : ∀ x ∈ { x ∈ B ×ˢ B | x.1 ≠ x.2 }, dmin ≤ Δ₀(x.1, x.2) := by
    intro x hx
    simp only [ne_eq, mem_filter, mem_product] at hx
    dsimp [dmin]
    exact_mod_cast minDist_le_hammingDist_of_mem_ne
      (hsub x.1 hx.1.1) (hsub x.2 hx.1.2) hx.2
  have B2_card :
      2 * choose_2 (B.card : ℚ) =
        (({ x ∈ B ×ˢ B | x.1 ≠ x.2 }.card : ℕ) : ℚ) :=
    two_mul_choose_two_card_eq_offdiag_card B
  have B2_card_pos : 0 < { x ∈ B ×ˢ B | x.1 ≠ x.2 }.card := by
    have ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp hB
    have : { x ∈ B ×ˢ B | x.1 ≠ x.2 }.Nonempty := by
      use ⟨u, v⟩
      simp [hu, hv, huv]
    exact card_pos.mpr this
  have h_bound : ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, dmin ≤
      ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, Δ₀(x.1, x.2) :=
    by simpa [Nat.cast_sum] using sum_le_sum h_d
  have h_eq : dmin =
      1 / (2 * choose_2 (B.card : ℚ)) *
        ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, dmin := by
    rw [sum_const, B2_card]
    simp only [ne_eq, one_div]
    set c := ({ x ∈ B ×ˢ B | ¬x.1 = x.2 }.card : ℚ) with hc
    have c_pos : 0 < c := by
      unfold c
      exact_mod_cast B2_card_pos
    rw [nsmul_eq_mul]
    change dmin = c⁻¹ * (c * dmin)
    field_simp [ne_of_gt c_pos]
  change dmin ≤ 1 / (2 * choose_2 (B.card : ℚ)) *
    ↑(∑ x ∈ B ×ˢ B with x.1 ≠ x.2, Δ₀(x.1, x.2))
  rw [h_eq]
  have c2_nonneg : 0 ≤ (1 / (2 * choose_2 (B.card : ℚ)) : ℚ) := by
    have c2_pos : 0 < (2 * choose_2 (B.card : ℚ) : ℚ) := by
      rw [B2_card]
      exact_mod_cast B2_card_pos
    positivity
  exact mul_le_mul_of_nonneg_left h_bound c2_nonneg

/-- Arbitrary-index q-ary Plotkin average-distance upper bound. -/
theorem averageDistOn_le_plotkin
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (B : Finset (ι → α)) (hB : 2 ≤ B.card) (hq : 0 < Fintype.card α) :
    ((averageDistOn B : ℚ) : ℝ) ≤
      (B.card : ℝ) / ((B.card : ℝ) - 1) * (Fintype.card ι : ℝ) *
        (1 - 1 / (Fintype.card α : ℝ)) := by
  let e : Fin B.card ≃ B := (Finset.equivFin B).symm
  let c : Fin B.card → ι → α := fun i => (e i).1
  have hM : 1 < B.card := by omega
  have hplot := indexed_averageDist_le_plotkin (ι := ι) (α := α)
    (M := B.card) c hM hq
  have hsum :
      (∑ i : Fin B.card, ∑ j ∈ (Finset.univ : Finset (Fin B.card)).erase i,
        (hammingDist (c i) (c j) : ℝ)) =
      ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (hammingDist x.1 x.2 : ℝ) := by
    simpa [c, e] using offdiag_sum_equivFin B
  rw [hsum] at hplot
  unfold averageDistOn
  simpa [Nat.cast_sum] using hplot

/-- Finset form of the q-ary Plotkin average-distance upper bound for
`JohnsonBound.d`.

This is the theorem needed to connect the simplex PSD development in
`CodeGeometry` to the existing Johnson-bound average-distance notation. -/
theorem averageDist_le_plotkin
    {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (B : Finset (Fin n → α)) (hB : 2 ≤ B.card) (hq : 0 < Fintype.card α) :
    ((d B : ℚ) : ℝ) ≤
      (B.card : ℝ) / ((B.card : ℝ) - 1) * (n : ℝ) *
        (1 - 1 / (Fintype.card α : ℝ)) := by
  let e : Fin B.card ≃ B := (Finset.equivFin B).symm
  let c : Fin B.card → Fin n → α := fun i => (e i).1
  have hM : 1 < B.card := by omega
  have hplot := indexed_averageDist_le_plotkin (ι := Fin n) (α := α)
    (M := B.card) c hM hq
  have hsum :
      (∑ i : Fin B.card, ∑ j ∈ (Finset.univ : Finset (Fin B.card)).erase i,
        (hammingDist (c i) (c j) : ℝ)) =
      ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (hammingDist x.1 x.2 : ℝ) := by
    simpa [c, e] using offdiag_sum_equivFin B
  rw [hsum] at hplot
  unfold d
  simpa [Nat.cast_sum] using hplot

/-- A finite point-list `Λ(C,δ,f)` has average pairwise distance at least the
minimum distance of `C`, provided it contains at least two words. -/
theorem minDist_le_averageDistOn_closeCodewordsRelFinset
    {ι : Type} [Fintype ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) (f : ι → α) (δ : ℝ)
    (hB : 1 < (ListDecodable.closeCodewordsRelFinset C f δ).card) :
    (Code.minDist C : ℚ) ≤
      averageDistOn (ListDecodable.closeCodewordsRelFinset C f δ) := by
  apply minDist_le_averageDistOn_of_subset hB
  intro x hx
  exact (ListDecodable.mem_closeCodewordsRelFinset.mp hx).1

/-- Distinct codewords agree in at most `n - minDist(C)` coordinates. -/
lemma agree_le_card_sub_minDist_of_mem_ne
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    {C : Set (ι → α)} {u v : ι → α}
    (hu : u ∈ C) (hv : v ∈ C) (hne : u ≠ v) :
    CodeGeometry.agree u v ≤ Fintype.card ι - Code.minDist C := by
  have hsum := CodeGeometry.agree_add_hammingDist u v
  have hmin := minDist_le_hammingDist_of_mem_ne hu hv hne
  omega

/-- Pairwise agreement upper bound for finite point-lists, derived from the
ambient code minimum distance. -/
lemma closeCodewordsRelFinset_pairwise_agree_le_card_sub_minDist
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    {C : ListDecodable.Code ι α} {f : ι → α} {δ : ℝ}
    {u v : ι → α}
    (hu : u ∈ ListDecodable.closeCodewordsRelFinset C f δ)
    (hv : v ∈ ListDecodable.closeCodewordsRelFinset C f δ)
    (hne : u ≠ v) :
    CodeGeometry.agree u v ≤ Fintype.card ι - Code.minDist C := by
  exact agree_le_card_sub_minDist_of_mem_ne
    (ListDecodable.mem_closeCodewordsRelFinset.mp hu).1
    (ListDecodable.mem_closeCodewordsRelFinset.mp hv).1 hne

/-- The minimum distance of a code is at most the block length. -/
lemma minDist_le_card
    {ι : Type} [Fintype ι]
    {α : Type} [DecidableEq α]
    (C : ListDecodable.Code ι α) :
    Code.minDist C ≤ Fintype.card ι := by
  rw [← Code.dist_eq_minDist]
  exact Code.dist_le_card C

/-- Close-list wrapper for the radical-free `CodeGeometry` Johnson cap.

This converts the finite point-list into an indexed family via `Finset.equivFin`.
The remaining hypotheses are exactly the agreement lower bound to the received
word, the pairwise agreement upper bound from the code distance, and the
radical-free Johnson algebra side condition. -/
theorem closeCodewordsRelFinset_card_le_of_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) (f : ι → α) (δ : ℝ)
    {A B ℓ : ℕ} {β : ℝ}
    (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hA : ∀ x ∈ ListDecodable.closeCodewordsRelFinset C f δ,
      A ≤ CodeGeometry.agree x f)
    (hB : ∀ u ∈ ListDecodable.closeCodewordsRelFinset C f δ,
      ∀ v ∈ ListDecodable.closeCodewordsRelFinset C f δ,
        u ≠ v → CodeGeometry.agree u v ≤ B)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))
      + (ℓ : ℝ) * (((B : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) < 0) :
    (ListDecodable.closeCodewordsRelFinset C f δ).card ≤ ℓ := by
  classical
  let S := ListDecodable.closeCodewordsRelFinset C f δ
  by_cases hS : S.card = 0
  · simp [S, hS]
  · have hSpos : 0 < S.card := Nat.pos_of_ne_zero hS
    let e : Fin S.card ≃ S := (Finset.equivFin S).symm
    let c : Fin S.card → ι → α := fun i => (e i).1
    have hAidx : ∀ i, A ≤ CodeGeometry.agree (c i) f := by
      intro i
      exact hA (c i) (e i).2
    have hBidx : ∀ i j, i ≠ j → CodeGeometry.agree (c i) (c j) ≤ B := by
      intro i j hij
      apply hB (c i) (e i).2 (c j) (e j).2
      intro hval
      apply hij
      exact e.injective (Subtype.ext hval)
    exact CodeGeometry.card_le_of_johnson_condition hq hSpos f c ℓ hAidx hBidx hβ hcond

/-- Close-list Johnson cap with the canonical agreement parameters:

* `A = n - ⌊δ·n⌋₊`, forced by membership in the radius-`δ` close-list;
* `B = n - minDist(C)`, forced by pairwise separation inside the code.

This leaves only the nonnegativity/field-size assumptions, the shift parameter,
and the radical-free Johnson algebra condition. -/
theorem closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) (f : ι → α) (δ : ℝ)
    {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))
      + (ℓ : ℝ) * ((((Fintype.card ι - Code.minDist C : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) < 0) :
    (ListDecodable.closeCodewordsRelFinset C f δ).card ≤ ℓ := by
  apply closeCodewordsRelFinset_card_le_of_johnson_condition
      (C := C) (f := f) (δ := δ)
      (A := Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊)
      (B := Fintype.card ι - Code.minDist C)
      (ℓ := ℓ) (β := β) hq hβ
  · intro x hx
    exact card_sub_floor_mul_card_le_agree_of_mem_closeCodewordsRelFinset hδ hx
  · intro u hu v hv hne
    exact closeCodewordsRelFinset_pairwise_agree_le_card_sub_minDist hu hv hne
  · exact hcond

set_option maxHeartbeats 5000000 in
-- The squared-distance Johnson wrapper unfolds several finite-code geometry bounds.
/-- Close-list wrapper for the squared-distance `CodeGeometry` Johnson cap.

This consumes the directly usable distance-form theorem:
each listed word is within Hamming distance `e` of the received word, and
distinct listed codewords are separated by at least `d`. -/
theorem closeCodewordsRelFinset_card_le_of_johnson_sq_dist
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) (f : ι → α) (δ : ℝ)
    {e d ℓ : ℕ}
    (hq1 : 1 < Fintype.card α) (hn : 0 < Fintype.card ι)
    (hclose : ∀ x ∈ ListDecodable.closeCodewordsRelFinset C f δ,
      hammingDist x f ≤ e)
    (hdist : ∀ u ∈ ListDecodable.closeCodewordsRelFinset C f δ,
      ∀ v ∈ ListDecodable.closeCodewordsRelFinset C f δ,
        u ≠ v → d ≤ hammingDist u v)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card α : ℝ) ≤
      ((Fintype.card ι - e : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * (((Fintype.card ι - e : ℕ) : ℝ) -
            (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - d : ℕ) : ℝ) -
                (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))) :
    (ListDecodable.closeCodewordsRelFinset C f δ).card ≤ ℓ := by
  classical
  let S := ListDecodable.closeCodewordsRelFinset C f δ
  by_cases hS : S.card = 0
  · simp [S, hS]
  · have hSpos : 0 < S.card := Nat.pos_of_ne_zero hS
    let idx : Fin S.card ≃ S := (Finset.equivFin S).symm
    let c : Fin S.card → ι → α := fun i => (idx i).1
    have hclose_idx : ∀ i, hammingDist (c i) f ≤ e := by
      intro i
      exact hclose (c i) (idx i).2
    have hdist_idx : ∀ i j, i ≠ j → d ≤ hammingDist (c i) (c j) := by
      intro i j hij
      apply hdist (c i) (idx i).2 (c j) (idx j).2
      intro hval
      apply hij
      exact idx.injective (Subtype.ext hval)
    exact CodeGeometry.card_le_of_johnson_sq_dist
      (ι := ι) (α := α)
      hq1 hn hSpos f c ℓ hclose_idx hdist_idx hP hsq

/-- Canonical close-list squared-distance Johnson cap with
`e = ⌊δ·n⌋₊` and `d = minDist(C)`. -/
theorem closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_sq_dist
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) (f : ι → α) (δ : ℝ)
    {ℓ : ℕ}
    (hδ : 0 ≤ δ) (hq1 : 1 < Fintype.card α)
    (hP : (Fintype.card ι : ℝ) / (Fintype.card α : ℝ) ≤
      ((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ))
    (hsq : ((ℓ : ℝ) + 1)
        * ((((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)) -
            (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)) ^ 2
      > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)))
        * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))
            + (ℓ : ℝ) * (((Fintype.card ι - Code.minDist C : ℕ) : ℝ) -
                (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))) :
    (ListDecodable.closeCodewordsRelFinset C f δ).card ≤ ℓ := by
  have hclose : ∀ x ∈ ListDecodable.closeCodewordsRelFinset C f δ,
      hammingDist x f ≤ ⌊δ * (Fintype.card ι : ℝ)⌋₊ := by
    intro x hx
    have hdist := hammingDist_le_floor_mul_card_of_mem_closeCodewordsRelFinset hδ hx
    have hsymm : hammingDist x f = hammingDist f x := by
      unfold hammingDist
      simp_rw [ne_comm]
    rwa [hsymm]
  have hdist : ∀ u ∈ ListDecodable.closeCodewordsRelFinset C f δ,
      ∀ v ∈ ListDecodable.closeCodewordsRelFinset C f δ,
        u ≠ v → Code.minDist C ≤ hammingDist u v := by
    intro u hu v hv hne
    exact minDist_le_hammingDist_of_mem_ne
      (ListDecodable.mem_closeCodewordsRelFinset.mp hu).1
      (ListDecodable.mem_closeCodewordsRelFinset.mp hv).1 hne
  exact closeCodewordsRelFinset_card_le_of_johnson_sq_dist
    (ι := ι) (α := α) (C := C) (f := f) (δ := δ)
    (e := ⌊δ * (Fintype.card ι : ℝ)⌋₊)
    (d := Code.minDist C) (ℓ := ℓ)
    hq1 (Fintype.card_pos) hclose hdist hP hsq

/-- Lambda-level Johnson cap with the canonical close-list agreement parameters.

This is the pointwise close-list cap packaged through the maximised
`ListDecodable.Lambda`; the remaining obligation is the same radical-free
Johnson algebra condition, independent of the received word. -/
theorem Lambda_le_of_floor_minDist_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))
      + (ℓ : ℝ) * ((((Fintype.card ι - Code.minDist C : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) < 0) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  apply ListDecodable.Lambda_le_natCast_of_forall_closeFinset_card_le
  intro f
  exact closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_condition
    C f δ hδ hq hβ hcond

/-- Package a pointwise close-list cap at the paper-facing `Jqℓ` radius into a
`Lambda` bound.

This isolates the list-size supremum step in ABF26 Theorem 3.2 from the
remaining q-ary Plotkin/radius algebra. -/
theorem Lambda_le_of_forall_closeCodewordsRelFinset_card_le_Jqℓ
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {ℓ : ℕ}
    (hpoint :
      ∀ f : ι → α,
        (ListDecodable.closeCodewordsRelFinset C f
          (Jqℓ (Fintype.card α : ℚ) ℓ
            ((Code.minDist C : ℚ) / Fintype.card ι))).card ≤ ℓ) :
    ListDecodable.Lambda C
      (Jqℓ (Fintype.card α : ℚ) ℓ
        ((Code.minDist C : ℚ) / Fintype.card ι)) ≤ (ℓ : ℕ∞) := by
  exact ListDecodable.Lambda_le_natCast_of_forall_closeFinset_card_le hpoint

/-- Lambda-level Johnson cap with the close-list radius side condition written
using the real radius `n - δ*n` instead of the floored integer radius.

The floored agreement lower bound is at least this real quantity, and the
radical-free Johnson expression is monotone decreasing in that agreement
parameter when `β ≥ 0`. -/
theorem Lambda_le_of_real_radius_minDist_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * (((Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))
      + (ℓ : ℝ) * ((((Fintype.card ι - Code.minDist C : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * (((Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) < 0) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  apply Lambda_le_of_floor_minDist_johnson_condition C hδ hq hβ
  have hx_nonneg : 0 ≤ δ * (Fintype.card ι : ℝ) := by positivity
  have hfloor_le :
      (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) ≤ δ * (Fintype.card ι : ℝ) :=
    Nat.floor_le hx_nonneg
  have hA_le :
      (Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ) ≤
        (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)) := by
    by_cases hf : ⌊δ * (Fintype.card ι : ℝ)⌋₊ ≤ Fintype.card ι
    · rw [Nat.cast_sub hf]
      linarith
    · have hlt : Fintype.card ι < ⌊δ * (Fintype.card ι : ℝ)⌋₊ :=
        Nat.lt_of_not_ge hf
      have hxgt : (Fintype.card ι : ℝ) < δ * (Fintype.card ι : ℝ) :=
        lt_of_lt_of_le (by exact_mod_cast hlt) hfloor_le
      have hsub : Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ = 0 := by omega
      rw [hsub]
      linarith
  have hℓ_nonneg : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
  have hcenter_le :
      -2 * β * ((((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        ≤ -2 * β * (((Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)) := by
    nlinarith [hA_le, hβ]
  have hcenter_scaled_le :
      (ℓ : ℝ) * (-2 * β *
          ((((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ))
            - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))
        ≤ (ℓ : ℝ) * (-2 * β *
          (((Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ))
            - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))) :=
    mul_le_mul_of_nonneg_left hcenter_le hℓ_nonneg
  apply lt_of_le_of_lt ?_ hcond
  nlinarith [hcenter_le, hcenter_scaled_le]

/-- Lambda-level Johnson cap with both canonical agreement parameters written
as real-valued expressions: `n - δ*n` for the center agreement and
`n - minDist(C)` for pairwise agreement.

This is the algebra-facing form for the final `Jqℓ` radius calculation. -/
theorem Lambda_le_of_real_radius_real_minDist_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * (((Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))
      + (ℓ : ℝ) * ((((Fintype.card ι : ℝ) - (Code.minDist C : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * (((Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) < 0) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  apply Lambda_le_of_real_radius_minDist_johnson_condition C hδ hq hβ
  have hmin_le : Code.minDist C ≤ Fintype.card ι := minDist_le_card C
  have hB :
      (((Fintype.card ι - Code.minDist C : ℕ) : ℝ)) =
        (Fintype.card ι : ℝ) - (Code.minDist C : ℝ) := by
    rw [Nat.cast_sub hmin_le]
  simpa [hB] using hcond

/-- Lambda-level Johnson cap with the algebraic side condition divided by the
block length. This relative-distance form is the natural target for the
`Jqℓ` radius algebra: the minimum distance appears as `minDist(C)/n`, and the
close-list radius appears as `δ` rather than `δ*n`. -/
theorem Lambda_le_of_normalized_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hcond : ((1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * ((1 - δ) - 1 / (Fintype.card α : ℝ)))
      + (ℓ : ℝ) * (((1 - (Code.minDist C : ℝ) / (Fintype.card ι : ℝ))
          - 1 / (Fintype.card α : ℝ))
        - 2 * β * ((1 - δ) - 1 / (Fintype.card α : ℝ))
        + β ^ 2 * (1 - 1 / (Fintype.card α : ℝ))) < 0) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  apply Lambda_le_of_real_radius_real_minDist_johnson_condition C hδ hq hβ
  have hn_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hscaled :
      (Fintype.card ι : ℝ) *
        (((1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
          - 2 * β * ((1 - δ) - 1 / (Fintype.card α : ℝ)))
        + (ℓ : ℝ) * (((1 - (Code.minDist C : ℝ) / (Fintype.card ι : ℝ))
            - 1 / (Fintype.card α : ℝ))
          - 2 * β * ((1 - δ) - 1 / (Fintype.card α : ℝ))
          + β ^ 2 * (1 - 1 / (Fintype.card α : ℝ)))) < 0 :=
    mul_neg_of_pos_of_neg hn_pos hcond
  convert hscaled using 1
  field_simp [hn_pos.ne']

/-- Compact relative-distance version of `Lambda_le_of_normalized_johnson_condition`.

Writing `γ = 1 - 1/q` and `drel = minDist(C)/n`, the Johnson side condition is
the scalar quadratic
`γ(1+β²) - 2β(γ-δ) + ℓ((γ-drel) - 2β(γ-δ) + β²γ) < 0`. -/
theorem Lambda_le_of_gamma_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hcond :
      let γ : ℝ := 1 - 1 / (Fintype.card α : ℝ)
      let drel : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι : ℝ)
      γ * (1 + β ^ 2) - 2 * β * (γ - δ)
        + (ℓ : ℝ) * ((γ - drel) - 2 * β * (γ - δ) + β ^ 2 * γ) < 0) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  apply Lambda_le_of_normalized_johnson_condition C hδ hq hβ
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcond

/-- Gamma-form Johnson cap specialized to the quadratic minimizer
`β = (γ - δ)/γ`.

This is the Lean-facing algebra target for the final `Jqℓ` instantiation: after
showing the radius lies below `γ` and the displayed scalar expression is
negative, the Lambda bound follows. -/
theorem Lambda_le_of_gamma_optimal_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hδ : 0 ≤ δ) (hq_one : 1 < Fintype.card α)
    (hδ_le_gamma : δ ≤ 1 - 1 / (Fintype.card α : ℝ))
    (hcond :
      let γ : ℝ := 1 - 1 / (Fintype.card α : ℝ)
      let drel : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι : ℝ)
      γ + (ℓ : ℝ) * (γ - drel) - ((ℓ : ℝ) + 1) * (γ - δ) ^ 2 / γ < 0) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  let γ : ℝ := 1 - 1 / (Fintype.card α : ℝ)
  let drel : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι : ℝ)
  have hq : 0 < Fintype.card α := lt_trans Nat.zero_lt_one hq_one
  have hq_real : 1 < (Fintype.card α : ℝ) := by exact_mod_cast hq_one
  have hq_real_pos : 0 < (Fintype.card α : ℝ) := lt_trans zero_lt_one hq_real
  have hγ_pos : 0 < γ := by
    have hfrac_pos :
        0 < ((Fintype.card α : ℝ) - 1) / (Fintype.card α : ℝ) :=
      div_pos (sub_pos.mpr hq_real) hq_real_pos
    have hγ_eq :
        γ = ((Fintype.card α : ℝ) - 1) / (Fintype.card α : ℝ) := by
      dsimp [γ]
      field_simp [hq_real_pos.ne']
    rw [hγ_eq]
    exact hfrac_pos
  have hβ_nonneg : 0 ≤ (γ - δ) / γ := by
    exact div_nonneg (sub_nonneg.mpr (by simpa [γ] using hδ_le_gamma)) hγ_pos.le
  apply Lambda_le_of_gamma_johnson_condition C hδ hq hβ_nonneg
  change γ * (1 + ((γ - δ) / γ) ^ 2) - 2 * ((γ - δ) / γ) * (γ - δ)
      + (ℓ : ℝ) * ((γ - drel) - 2 * ((γ - δ) / γ) * (γ - δ)
        + ((γ - δ) / γ) ^ 2 * γ) < 0
  have hquad :
      γ * (1 + ((γ - δ) / γ) ^ 2) - 2 * ((γ - δ) / γ) * (γ - δ)
          + (ℓ : ℝ) * ((γ - drel) - 2 * ((γ - δ) / γ) * (γ - δ)
            + ((γ - δ) / γ) ^ 2 * γ)
        = γ + (ℓ : ℝ) * (γ - drel) - ((ℓ : ℝ) + 1) * (γ - δ) ^ 2 / γ := by
    field_simp [hγ_pos.ne']
    ring
  rw [hquad]
  simpa [γ, drel] using hcond

/-- Gamma-form optimal-beta Johnson cap with the remaining condition stated as
a square lower bound.

This is the most compact handoff to radius algebra: prove that the squared
gap from the alphabet cap dominates the affine distance term, and the Lambda
bound follows. -/
theorem Lambda_le_of_gamma_square_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hδ : 0 ≤ δ) (hq_one : 1 < Fintype.card α)
    (hδ_le_gamma : δ ≤ 1 - 1 / (Fintype.card α : ℝ))
    (hsquare :
      let γ : ℝ := 1 - 1 / (Fintype.card α : ℝ)
      let drel : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι : ℝ)
      γ + (ℓ : ℝ) * (γ - drel) <
        ((ℓ : ℝ) + 1) * (γ - δ) ^ 2 / γ) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  apply Lambda_le_of_gamma_optimal_johnson_condition C hδ hq_one hδ_le_gamma
  simpa using sub_neg.mpr hsquare

/-- Johnson Lambda cap at the reciprocal finite-list radius reached by the
current quadratic-cap route.

This uses the corrected factor `(ℓ-1)/ℓ`, as does canonical `Jqℓ`. The former downstream
inverse-factor radius is retired. The strict inequality requires positive minimum distance; when
`minDist(C) = 0`, the square condition degenerates to equality. -/
theorem Lambda_le_of_reciprocal_johnson_radius
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (hq_one : 1 < Fintype.card α)
    (hmin_pos : 0 < Code.minDist C)
    (hrad :
      0 ≤ 1
        - (1 / (1 - 1 / (Fintype.card α : ℝ)))
          * (((ℓ : ℝ) - 1) / (ℓ : ℝ))
          * ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))) :
    ListDecodable.Lambda C
      ((1 - 1 / (Fintype.card α : ℝ)) *
        (1 - Real.sqrt
          (1
            - (1 / (1 - 1 / (Fintype.card α : ℝ)))
              * (((ℓ : ℝ) - 1) / (ℓ : ℝ))
              * ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))))) ≤
        (ℓ : ℕ∞) := by
  let γ : ℝ := 1 - 1 / (Fintype.card α : ℝ)
  let drel : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι : ℝ)
  let L : ℝ := ((ℓ : ℝ) - 1) / (ℓ : ℝ)
  let z : ℝ := 1 - (1 / γ) * L * drel
  have hq_real : 1 < (Fintype.card α : ℝ) := by exact_mod_cast hq_one
  have hq_real_pos : 0 < (Fintype.card α : ℝ) := lt_trans zero_lt_one hq_real
  have hγ_pos : 0 < γ := by
    have hfrac_pos :
        0 < ((Fintype.card α : ℝ) - 1) / (Fintype.card α : ℝ) :=
      div_pos (sub_pos.mpr hq_real) hq_real_pos
    have hγ_eq :
        γ = ((Fintype.card α : ℝ) - 1) / (Fintype.card α : ℝ) := by
      dsimp [γ]
      field_simp [hq_real_pos.ne']
    rw [hγ_eq]
    exact hfrac_pos
  have hℓ_real_pos : 0 < (ℓ : ℝ) := by
    have : (0 : ℕ) < ℓ := lt_of_lt_of_le (by norm_num) hℓ
    exact_mod_cast this
  have hL_nonneg : 0 ≤ L := by
    have hℓ_real_ge_one : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hℓ)
    dsimp [L]
    exact div_nonneg (sub_nonneg.mpr hℓ_real_ge_one) hℓ_real_pos.le
  have hdrel_pos : 0 < drel := by
    have hn_real_pos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    dsimp [drel]
    exact div_pos (by exact_mod_cast hmin_pos) hn_real_pos
  have hz : 0 ≤ z := by
    simpa [γ, drel, L, z] using hrad
  have hz_le_one : z ≤ 1 := by
    have hterm_nonneg : 0 ≤ (1 / γ) * L * drel := by positivity
    dsimp [z]
    linarith
  have hsqrt_le_one : Real.sqrt z ≤ 1 := by
    calc
      Real.sqrt z ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hz_le_one
      _ = 1 := by norm_num
  have hδ_nonneg : 0 ≤ γ * (1 - Real.sqrt z) :=
    mul_nonneg hγ_pos.le (sub_nonneg.mpr hsqrt_le_one)
  have hδ_le_gamma : γ * (1 - Real.sqrt z) ≤ γ := by
    nlinarith [hγ_pos, Real.sqrt_nonneg z]
  apply Lambda_le_of_gamma_square_condition C hδ_nonneg hq_one
      (by simpa [γ, z] using hδ_le_gamma)
  dsimp [γ, drel, L, z]
  have hsq : (Real.sqrt (1 - (1 / γ) * L * drel)) ^ 2 =
      1 - (1 / γ) * L * drel := by
    exact Real.sq_sqrt hz
  have htarget :
      γ + (ℓ : ℝ) * (γ - drel) <
        ((ℓ : ℝ) + 1) *
          (γ - γ * (1 - Real.sqrt (1 - (1 / γ) * L * drel))) ^ 2 / γ := by
    have hdrel_div_pos : 0 < drel / (ℓ : ℝ) := div_pos hdrel_pos hℓ_real_pos
    have hgap :
        γ - γ * (1 - Real.sqrt (1 - (1 / γ) * L * drel)) =
          γ * Real.sqrt (1 - (1 / γ) * L * drel) := by
      ring
    rw [hgap]
    rw [show (γ * Real.sqrt (1 - (1 / γ) * L * drel)) ^ 2 =
        γ ^ 2 * (Real.sqrt (1 - (1 / γ) * L * drel)) ^ 2 by ring]
    rw [hsq]
    have hrhs_eq :
        ((ℓ : ℝ) + 1) * (γ ^ 2 * (1 - (1 / γ) * L * drel)) / γ =
          ((ℓ : ℝ) + 1) * (γ - drel * L) := by
      field_simp [hγ_pos.ne']
    rw [hrhs_eq]
    dsimp [L]
    field_simp [hℓ_real_pos.ne']
    nlinarith [hdrel_pos, hℓ_real_pos]
  simpa [γ, drel, L, z] using htarget

/-- Named-radius wrapper for `Lambda_le_of_reciprocal_johnson_radius`. -/
theorem Lambda_le_of_JqℓRecipReal_minDist
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (hq_one : 1 < Fintype.card α)
    (hmin_pos : 0 < Code.minDist C)
    (hrad :
      0 ≤ 1
        - (1 / (1 - 1 / (Fintype.card α : ℝ)))
          * (((ℓ : ℝ) - 1) / (ℓ : ℝ))
          * ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))) :
    ListDecodable.Lambda C
      (JqℓRecipReal (Fintype.card α : ℝ) (ℓ : ℝ)
        ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))) ≤
        (ℓ : ℕ∞) := by
  simpa [JqℓRecipReal] using
    Lambda_le_of_reciprocal_johnson_radius C hℓ hq_one hmin_pos hrad

/-- Monotone-radius corollary of the named reciprocal Johnson radius bound. -/
theorem Lambda_le_of_le_JqℓRecipReal_minDist
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hδ_le : δ ≤ JqℓRecipReal (Fintype.card α : ℝ) (ℓ : ℝ)
      ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ)))
    (hℓ : 2 ≤ ℓ) (hq_one : 1 < Fintype.card α)
    (hmin_pos : 0 < Code.minDist C)
    (hrad :
      0 ≤ 1
        - (1 / (1 - 1 / (Fintype.card α : ℝ)))
          * (((ℓ : ℝ) - 1) / (ℓ : ℝ))
          * ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  exact le_trans (ListDecodable.Lambda_mono (C := C) hδ_le)
    (Lambda_le_of_JqℓRecipReal_minDist C hℓ hq_one hmin_pos hrad)

/-- Named reciprocal Johnson bound with the radicand hypothesis expressed as
the scaled-distance condition `((ℓ-1)/ℓ) * drel ≤ γ`. -/
theorem Lambda_le_of_JqℓRecipReal_minDist_of_scaled_distance_le
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (hq_one : 1 < Fintype.card α)
    (hmin_pos : 0 < Code.minDist C)
    (hscaled :
      (((ℓ : ℝ) - 1) / (ℓ : ℝ)) *
          ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))
        ≤ 1 - 1 / (Fintype.card α : ℝ)) :
    ListDecodable.Lambda C
      (JqℓRecipReal (Fintype.card α : ℝ) (ℓ : ℝ)
        ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))) ≤
        (ℓ : ℕ∞) := by
  apply Lambda_le_of_JqℓRecipReal_minDist C hℓ hq_one hmin_pos
  let γ : ℝ := 1 - 1 / (Fintype.card α : ℝ)
  let drel : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι : ℝ)
  have hq_real : 1 < (Fintype.card α : ℝ) := by exact_mod_cast hq_one
  have hq_real_pos : 0 < (Fintype.card α : ℝ) := lt_trans zero_lt_one hq_real
  have hγ_pos : 0 < γ := by
    have hfrac_pos :
        0 < ((Fintype.card α : ℝ) - 1) / (Fintype.card α : ℝ) :=
      div_pos (sub_pos.mpr hq_real) hq_real_pos
    have hγ_eq :
        γ = ((Fintype.card α : ℝ) - 1) / (Fintype.card α : ℝ) := by
      dsimp [γ]
      field_simp [hq_real_pos.ne']
    rw [hγ_eq]
    exact hfrac_pos
  change 0 ≤ 1 - (1 / γ) * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * drel
  have hscaled' :
      (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * drel ≤ γ := by
    simpa [γ, drel] using hscaled
  rw [sub_nonneg]
  have hmul :
      (1 / γ) * ((((ℓ : ℝ) - 1) / (ℓ : ℝ)) * drel) ≤ (1 / γ) * γ :=
    mul_le_mul_of_nonneg_left hscaled' (by positivity)
  have hcancel : (1 / γ) * γ = 1 := by
    field_simp [hγ_pos.ne']
  nlinarith

/-- Monotone-radius version of
`Lambda_le_of_JqℓRecipReal_minDist_of_scaled_distance_le`. -/
theorem Lambda_le_of_le_JqℓRecipReal_minDist_of_scaled_distance_le
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hδ_le : δ ≤ JqℓRecipReal (Fintype.card α : ℝ) (ℓ : ℝ)
      ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ)))
    (hℓ : 2 ≤ ℓ) (hq_one : 1 < Fintype.card α)
    (hmin_pos : 0 < Code.minDist C)
    (hscaled :
      (((ℓ : ℝ) - 1) / (ℓ : ℝ)) *
          ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))
        ≤ 1 - 1 / (Fintype.card α : ℝ)) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  exact le_trans (ListDecodable.Lambda_mono (C := C) hδ_le)
    (Lambda_le_of_JqℓRecipReal_minDist_of_scaled_distance_le C hℓ hq_one hmin_pos hscaled)

/-- Nontrivial-code version of
`Lambda_le_of_JqℓRecipReal_minDist_of_scaled_distance_le`.

This packages the structural fact that a code with two distinct codewords has
positive minimum distance, so downstream callers can use the natural
nontriviality hypothesis instead of separately proving `0 < Code.minDist C`. -/
theorem Lambda_le_of_JqℓRecipReal_minDist_of_scaled_distance_le_of_nontrivial
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (hq_one : 1 < Fintype.card α)
    (hC : Set.Nontrivial C)
    (hscaled :
      (((ℓ : ℝ) - 1) / (ℓ : ℝ)) *
          ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))
        ≤ 1 - 1 / (Fintype.card α : ℝ)) :
    ListDecodable.Lambda C
      (JqℓRecipReal (Fintype.card α : ℝ) (ℓ : ℝ)
        ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))) ≤
        (ℓ : ℕ∞) := by
  have hmin_pos : 0 < Code.minDist C := by
    simpa [Code.dist_eq_minDist] using
      Code.dist_pos_of_Nontrivial (ι := ι) (F := α) (C := C) hC
  exact Lambda_le_of_JqℓRecipReal_minDist_of_scaled_distance_le C hℓ hq_one hmin_pos hscaled

/-- Monotone-radius nontrivial-code version of
`Lambda_le_of_le_JqℓRecipReal_minDist_of_scaled_distance_le`. -/
theorem Lambda_le_of_le_JqℓRecipReal_minDist_of_scaled_distance_le_of_nontrivial
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hδ_le : δ ≤ JqℓRecipReal (Fintype.card α : ℝ) (ℓ : ℝ)
      ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ)))
    (hℓ : 2 ≤ ℓ) (hq_one : 1 < Fintype.card α)
    (hC : Set.Nontrivial C)
    (hscaled :
      (((ℓ : ℝ) - 1) / (ℓ : ℝ)) *
          ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))
        ≤ 1 - 1 / (Fintype.card α : ℝ)) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  have hmin_pos : 0 < Code.minDist C := by
    simpa [Code.dist_eq_minDist] using
      Code.dist_pos_of_Nontrivial (ι := ι) (F := α) (C := C) hC
  exact Lambda_le_of_le_JqℓRecipReal_minDist_of_scaled_distance_le C hδ_le hℓ
    hq_one hmin_pos hscaled

/-- A violated finite `Lambda` bound produces a concrete point-list whose average
distance is controlled by the q-ary Plotkin bound.

This is the contradiction-entry bridge for `johnson_bound_lambda_le_ell`: after
assuming `ℓ < Lambda C δ`, one can work with the finite close-list around a
specific received word. -/
theorem exists_closeList_gt_and_averageDistOn_le_plotkin_of_natCast_lt_Lambda
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hq : 0 < Fintype.card α)
    (hΛ : (ℓ : ℕ∞) < ListDecodable.Lambda C δ) :
    ∃ f : ι → α,
      ℓ < (ListDecodable.closeCodewordsRelFinset C f δ).card ∧
        ((averageDistOn (ListDecodable.closeCodewordsRelFinset C f δ) : ℚ) : ℝ) ≤
          ((ListDecodable.closeCodewordsRelFinset C f δ).card : ℝ) /
              (((ListDecodable.closeCodewordsRelFinset C f δ).card : ℝ) - 1) *
            (Fintype.card ι : ℝ) *
              (1 - 1 / (Fintype.card α : ℝ)) := by
  rcases ListDecodable.exists_closeFinset_card_gt_of_natCast_lt_Lambda hΛ with ⟨f, hf⟩
  refine ⟨f, hf, ?_⟩
  exact averageDistOn_le_plotkin (ListDecodable.closeCodewordsRelFinset C f δ)
    (by omega) hq

/-- A violated finite `Lambda` bound produces one concrete close-list carrying
both sides of the average-distance squeeze: its average distance is at least
`Code.minDist C`, and at most the q-ary Plotkin expression. -/
theorem exists_closeList_gt_and_minDist_le_averageDistOn_and_averageDistOn_le_plotkin
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hq : 0 < Fintype.card α)
    (hΛ : (ℓ : ℕ∞) < ListDecodable.Lambda C δ) :
    ∃ f : ι → α,
      ℓ < (ListDecodable.closeCodewordsRelFinset C f δ).card ∧
        ((Code.minDist C : ℚ) : ℝ) ≤
          ((averageDistOn (ListDecodable.closeCodewordsRelFinset C f δ) : ℚ) : ℝ) ∧
        ((averageDistOn (ListDecodable.closeCodewordsRelFinset C f δ) : ℚ) : ℝ) ≤
          ((ListDecodable.closeCodewordsRelFinset C f δ).card : ℝ) /
              (((ListDecodable.closeCodewordsRelFinset C f δ).card : ℝ) - 1) *
            (Fintype.card ι : ℝ) *
              (1 - 1 / (Fintype.card α : ℝ)) := by
  rcases exists_closeList_gt_and_averageDistOn_le_plotkin_of_natCast_lt_Lambda
      C hℓ hq hΛ with ⟨f, hf_card, hf_plotkin⟩
  refine ⟨f, hf_card, ?_, hf_plotkin⟩
  exact_mod_cast minDist_le_averageDistOn_closeCodewordsRelFinset C f δ (by omega)

end JohnsonBound

namespace CodingTheory

open scoped NNReal
open ListDecodable JohnsonBound

/-- ABF26 Theorem 3.2 reduced to the pointwise close-list cap at the
paper-facing `Jqℓ` radius.

This is the final `Lambda`/`ℕ∞` packaging layer; the remaining hard theorem is
the pointwise q-ary Plotkin/radius-algebra bound for each received word. -/
theorem johnson_bound_lambda_le_ell_of_forall_closeCodewordsRelFinset_card_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : Set (ι → α)) (ℓ : ℕ)
    (hpoint :
      ∀ f : ι → α,
        (ListDecodable.closeCodewordsRelFinset C f
          (Jqℓ (Fintype.card α : ℚ) ℓ
            ((Code.minDist C : ℚ) / Fintype.card ι))).card ≤ ℓ) :
    let q : ℚ := Fintype.card α
    let δ_min : ℚ := Code.minDist C / Fintype.card ι
    Lambda C (Jqℓ q ℓ δ_min) ≤ (ℓ : ℕ∞) := by
  dsimp
  exact Lambda_le_of_forall_closeCodewordsRelFinset_card_le_Jqℓ
    (C := C) (ℓ := ℓ) hpoint

/-- Pure-algebra engine for `mds_johnson_lambda_le`: the `β = √ρ` Johnson cap
`2·η·T²·(Dd − Do) ≤ −Do` after clearing the field-size denominator `Q = q`.

Here `T = √ρ`, `S = A − N·(T+η) ≥ 0` is the slack in the agreement lower bound,
`N` is the block length, and the two Gram quantities are written in closed form
(`−Do` and `Dd − Do`). The decisive use of the radius constraint `η ≤ 1 − T`
(equivalent to `1 − √ρ − η ≥ 0`) appears via `hEle`. -/
private lemma mds_core_ineq
    (N Q T E S : ℝ) (hN : 1 ≤ N) (hQ : 0 < Q) (hT0 : 0 < T) (hT1 : T < 1)
    (hE : 0 < E) (hEle : E ≤ 1 - T) (hS : 0 ≤ S) :
    2 * E * T ^ 2 * (N * (1 - 1 / Q) - (T ^ 2 * N - 1) + N / Q)
      ≤ (2 * T) * S + 1 + 2 * N * T * E + N * (1 / Q) * (1 - T) ^ 2 := by
  -- `F := 2QE(NT(T³−T+1) − T²) + N(1−T)² + Q ≥ 0`, the heart of the bound.
  have hcube : 0 ≤ T ^ 3 - T + 1 := by
    nlinarith [sq_nonneg (T - 1), hT0, hT1, mul_pos hT0 hT0]
  have ht2 : 2 * T ^ 2 * (1 - T) ≤ 1 := by
    nlinarith [sq_nonneg (3 * T - 2), hT0, hT1,
      mul_nonneg (sq_nonneg T) (le_of_lt (by linarith : (0 : ℝ) < 1 - T))]
  have p1 : 0 ≤ 2 * Q * E * N * T * (T ^ 3 - T + 1) := by positivity
  have p2 : 0 ≤ N * (1 - T) ^ 2 := by positivity
  have p3 : 0 ≤ 2 * Q * T ^ 2 * (1 - T - E) :=
    mul_nonneg (by positivity) (by linarith)
  have p4 : 0 ≤ Q * (1 - 2 * T ^ 2 * (1 - T)) :=
    mul_nonneg (le_of_lt hQ) (by linarith)
  have hF : 0 ≤ 2 * Q * E * (N * T * (T ^ 3 - T + 1) - T ^ 2) + N * (1 - T) ^ 2 + Q := by
    nlinarith [p1, p2, p3, p4]
  have hST : 0 ≤ 2 * Q * S * T := by positivity
  -- Clear the `1/Q` denominators and finish from `2QST + F ≥ 0`.
  rw [← sub_nonneg]
  have hid :
      ((2 * T) * S + 1 + 2 * N * T * E + N * (1 / Q) * (1 - T) ^ 2)
        - 2 * E * T ^ 2 * (N * (1 - 1 / Q) - (T ^ 2 * N - 1) + N / Q)
      = (2 * Q * S * T
          + (2 * Q * E * (N * T * (T ^ 3 - T + 1) - T ^ 2) + N * (1 - T) ^ 2 + Q)) / Q := by
    field_simp; ring
  rw [hid]
  exact div_nonneg (by linarith [hF, hST]) (le_of_lt hQ)
/-! ## q-ary Plotkin average-distance development (frontier helper)

The docstring of `johnson_bound_lambda_le_ell` (T3.2) identifies the **q-ary Plotkin
average-distance upper bound** as the only nontrivial gap blocking the ABF26 §3.1
Johnson family theorems:

  `d(B') ≤ (1 - 1/q) · n · M / (M - 1)`     where `M = |B'|`, `q = |F|`,

whose combinatorial core is the Cauchy–Schwarz / power-mean step
`∑_α K_i(α)² ≥ M²/q`.  This is realised below, fully `sorry`-free, **from scratch**
(the in-tree column-count machinery `K`, `sum_choose_K_i`, `Fi`, … in
`JohnsonBound/Lemmas.lean` is `private`, so it is rebuilt here in the `MdsPlotkin`
namespace; only the *exported* `JohnsonBound.d_eq_sum`,
`JohnsonBound.choose_2`, `JohnsonBound.d` are reused).

The pipeline:
* `agree_eq_sum_sq` — for each coordinate `i`, the number of ordered pairs of `B`
  agreeing at `i` equals `∑_α K_i(α)²` (double-counting).
* `cs_lb` — Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`): `∑_α K_i(α)² ≥ M²/q`.
* `split_pairs` / `filter_redundant` — agree + disagree counts sum to `M²`.
* `col_disagree_le` — per-coordinate disagreement count `≤ M²·(1 - 1/q)`.
* `sum_disagree_le` — summed over the `n` coordinates: `≤ n·M²·(1 - 1/q)`.
* `plotkin_d_le` — combined with `d_eq_sum` (`2·C₂(M)·d(B) = ∑_i (disagreements)`):
  the q-ary Plotkin bound `d(B) ≤ (1-1/q)·n·M/(M-1)`.

This closes the math wall documented in T3.2.  (The *final* assembly of C3.3 below
additionally needs the `Lambda`/`closeCodewordsRel` → `Finset (Fin n → F)` transport
and the second-moment / Plotkin real-analysis algebra; that bridge is left as the
remaining `sorry`.) -/
namespace MdsPlotkin

open JohnsonBound Finset Fintype

variable {n : ℕ} {F : Type} [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- The `x.1 ≠ x.2` filter is redundant for the coordinate-`i` disagreement indicator
(the diagonal contributes `0` to `[x.1 i ≠ x.2 i]`). -/
lemma filter_redundant (B : Finset (Fin n → F)) (i : Fin n) :
    (∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then (1:ℚ) else 0))
    = (∑ x ∈ B ×ˢ B, (if x.1 i ≠ x.2 i then (1:ℚ) else 0)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : x.1 i = x.2 i
  · simp [h]
  · have : x.1 ≠ x.2 := fun he => h (by rw [he])
    simp [this, h]

/-- **Double counting.** The number of ordered pairs `(x, y) ∈ B × B` that *agree*
at coordinate `i` equals `∑_α (#{x ∈ B | x i = α})²`. -/
lemma agree_eq_sum_sq (B : Finset (Fin n → F)) (i : Fin n) :
    (∑ x ∈ B ×ˢ B, (if x.1 i = x.2 i then (1:ℚ) else 0))
    = ∑ α : F, ((B.filter (fun x => x i = α)).card : ℚ)^2 := by
  have expand : ∀ x y : Fin n → F,
      (if x i = y i then (1:ℚ) else 0)
      = ∑ α : F, (if x i = α then (1:ℚ) else 0) * (if y i = α then (1:ℚ) else 0) := by
    intro x y
    rw [Finset.sum_eq_single (x i)]
    · by_cases h : x i = y i <;> simp [h, eq_comm]
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ (x i)) h
  have colcount : ∀ α : F, ((B.filter (fun x => x i = α)).card : ℚ)
      = ∑ x ∈ B, (if x i = α then (1:ℚ) else 0) := by
    intro α; rw [Finset.sum_boole]
  have rhs_eq : (∑ α : F, ((B.filter (fun x => x i = α)).card : ℚ)^2)
      = ∑ α : F, ∑ x ∈ B, ∑ y ∈ B,
          (if x i = α then (1:ℚ) else 0) * (if y i = α then (1:ℚ) else 0) := by
    apply Finset.sum_congr rfl; intro α _
    rw [colcount α, sq, Finset.sum_mul_sum]
  rw [rhs_eq, Finset.sum_product]
  simp_rw [expand]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

omit [Fintype F] in
/-- Agreement count plus disagreement count over `B × B` equals `M²`. -/
lemma split_pairs (B : Finset (Fin n → F)) (i : Fin n) :
    (∑ x ∈ B ×ˢ B, (if x.1 i = x.2 i then (1:ℚ) else 0))
    + (∑ x ∈ B ×ˢ B, (if x.1 i ≠ x.2 i then (1:ℚ) else 0))
    = (B.card:ℚ)^2 := by
  rw [← Finset.sum_add_distrib]
  rw [show (B.card:ℚ)^2 = ∑ _x ∈ B ×ˢ B, (1:ℚ) by
    rw [Finset.sum_const, Finset.card_product]; ring]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : x.1 i = x.2 i <;> simp [h]

/-- **Cauchy–Schwarz lower bound.** `∑_α (#{x ∈ B | x i = α})² ≥ M²/q`, via
`sq_sum_le_card_mul_sum_sq` and `∑_α #{x ∈ B | x i = α} = M` (fiberwise count). -/
lemma cs_lb (B : Finset (Fin n → F)) (i : Fin n) (hq : 0 < Fintype.card F) :
    (B.card:ℚ)^2 / (Fintype.card F : ℚ)
      ≤ ∑ α : F, ((B.filter (fun x => x i = α)).card : ℚ)^2 := by
  have hsum : (∑ α : F, ((B.filter (fun x => x i = α)).card : ℚ)) = (B.card:ℚ) := by
    rw [← Nat.cast_sum]; congr 1
    exact (Finset.card_eq_sum_card_fiberwise (f := fun x => x i) (s := B) (t := univ)
      (fun x _ => Finset.mem_univ _)).symm
  have hcard : (Finset.univ : Finset F).card = Fintype.card F := by simp
  have cs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset F))
    (f := fun α => ((B.filter (fun x => x i = α)).card : ℚ))
  rw [hsum, hcard] at cs
  rw [div_le_iff₀ (by exact_mod_cast hq), mul_comm]; exact cs

/-- **Per-coordinate Plotkin step.** The number of distinct ordered pairs of `B`
disagreeing at coordinate `i` is at most `M²·(1 - 1/q)`. -/
lemma col_disagree_le (B : Finset (Fin n → F)) (i : Fin n) (hq : 0 < Fintype.card F) :
    (∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then (1:ℚ) else 0))
    ≤ (B.card:ℚ)^2 * (1 - 1 / (Fintype.card F : ℚ)) := by
  rw [filter_redundant]
  have hsplit := split_pairs B i
  have hagree := agree_eq_sum_sq B i
  have hcs := cs_lb B i hq
  have hq' : (0:ℚ) < (Fintype.card F : ℚ) := by exact_mod_cast hq
  have hdis : (∑ x ∈ B ×ˢ B, (if x.1 i ≠ x.2 i then (1:ℚ) else 0))
      = (B.card:ℚ)^2 - (∑ α : F, ((B.filter (fun x => x i = α)).card : ℚ)^2) := by
    rw [← hagree]; linarith
  rw [hdis]
  have hexp : (B.card:ℚ)^2 * (1 - 1/(Fintype.card F : ℚ))
      = (B.card:ℚ)^2 - (B.card:ℚ)^2/(Fintype.card F : ℚ) := by field_simp
  rw [hexp]; linarith

/-- Sum over all `n` coordinates of the per-coordinate disagreement count. -/
lemma sum_disagree_le (B : Finset (Fin n → F)) (hq : 0 < Fintype.card F) :
    (∑ i : Fin n, ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then (1:ℚ) else 0))
    ≤ (n:ℚ) * (B.card:ℚ)^2 * (1 - 1 / (Fintype.card F : ℚ)) := by
  calc (∑ i : Fin n, ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then (1:ℚ) else 0))
      ≤ ∑ _i : Fin n, (B.card:ℚ)^2 * (1 - 1 / (Fintype.card F : ℚ)) :=
        Finset.sum_le_sum (fun i _ => col_disagree_le B i hq)
    _ = (n:ℚ) * (B.card:ℚ)^2 * (1 - 1 / (Fintype.card F : ℚ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- **q-ary Plotkin average-distance bound** (the missing ingredient flagged in the
T3.2 docstring). For any `B ⊆ Fⁿ` with `|B| ≥ 2`,

  `d(B) ≤ (1 - 1/q) · n · |B| / (|B| - 1)`.

Proof: `JohnsonBound.d_eq_sum` rewrites `2·C₂(|B|)·d(B)` as the total coordinate
disagreement count `∑_i (…)`, which `sum_disagree_le` bounds by
`n·|B|²·(1 - 1/q)`; since `2·C₂(|B|) = |B|·(|B|-1)`, cancelling `|B| > 0` gives the
claim. -/
lemma plotkin_d_le (B : Finset (Fin n → F)) (h_B : 2 ≤ B.card) (hq : 0 < Fintype.card F) :
    JohnsonBound.d B
      ≤ (n:ℚ) * (B.card:ℚ) * (1 - 1/(Fintype.card F:ℚ)) / ((B.card:ℚ) - 1) := by
  have hM : (2:ℚ) ≤ (B.card:ℚ) := by exact_mod_cast h_B
  have hMpos : (0:ℚ) < (B.card:ℚ) := by linarith
  have hM1pos : (0:ℚ) < (B.card:ℚ) - 1 := by linarith
  have key : 2 * JohnsonBound.choose_2 (B.card:ℚ) * JohnsonBound.d B
      ≤ (n:ℚ) * (B.card:ℚ)^2 * (1 - 1 / (Fintype.card F : ℚ)) := by
    rw [JohnsonBound.d_eq_sum h_B]; exact sum_disagree_le B hq
  have hch : 2 * JohnsonBound.choose_2 (B.card:ℚ) = (B.card:ℚ) * ((B.card:ℚ) - 1) := by
    simp [JohnsonBound.choose_2]; ring
  have key2 : (B.card:ℚ) * ((B.card:ℚ) - 1) * JohnsonBound.d B
      ≤ (n:ℚ) * (B.card:ℚ)^2 * (1 - 1 / (Fintype.card F : ℚ)) := by
    rw [← hch]; linarith [key]
  rw [le_div_iff₀ hM1pos]
  nlinarith [key2, hMpos, mul_pos hMpos hM1pos]

/-- **Index transport for `hammingDist`.** Reindexing both arguments by a bijection
`κ ≃ ι` leaves the Hamming distance unchanged (used to move the `ι → F` statement of
C3.3 to the `Fin n → F` apparatus of `JohnsonBound`). -/
lemma hammingDist_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {G : Type} [DecidableEq G]
    (eqv : κ ≃ ι) (u v : ι → G) :
    hammingDist (u ∘ eqv) (v ∘ eqv) = hammingDist u v := by
  unfold hammingDist
  refine Finset.card_bij (fun a _ => eqv a) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply] at ha ⊢; exact ha
  · intro a _ b _ h; exact eqv.injective h
  · intro b hb
    refine ⟨eqv.symm b, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply,
      Equiv.apply_symm_apply] at hb ⊢; exact hb

/-- **Real-analysis closing step for C3.3.** Given the second-moment Johnson output
`M·(2η√ρ) ≤ 1` with `ρ ∈ (0,1]`, `η > 0`, one gets `M ≤ 1/(2ηρ)` (because
`√ρ ≥ ρ` on `(0,1]`). This is the final inequality of the C3.3 bound. -/
lemma mds_real_close (M ρ η : ℝ) (hM : 0 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hη : 0 < η) (hbound : M * (2 * η * Real.sqrt ρ) ≤ 1) :
    M ≤ 1 / (2 * η * ρ) := by
  have hsq : ρ ≤ Real.sqrt ρ := by
    have h := Real.sqrt_le_sqrt hρ1
    rw [Real.sqrt_one] at h
    nlinarith [Real.sq_sqrt hρ0.le, Real.sqrt_nonneg ρ, Real.sqrt_pos.mpr hρ0]
  have hden_pos : 0 < 2 * η * ρ := by positivity
  rw [le_div_iff₀ hden_pos]
  calc M * (2 * η * ρ) ≤ M * (2 * η * Real.sqrt ρ) := by
        apply mul_le_mul_of_nonneg_left _ hM; nlinarith [hsq]
    _ ≤ 1 := hbound

/-- **Reduced denominator inequality (frac-free core).** With `s = √ρ`, average radius
`e0 ∈ [0, 1 - s - η]`, relative distance `δ ≥ 1 - s²`, the elementary inequality
`2·η·s²·δ ≤ δ - 2·e0 + e0²` holds. This is the `frac = 1` reduction of the
second-moment denominator (the general `frac ≥ 1` case follows by `frac·e0² ≥ e0²`).
The proof is by monotonicity: the LHS-minus-RHS is decreasing in `e0` (on `[0,1]`) and
increasing in `δ`, so its minimum is the boundary value
`η·(η + 2s³ - 2s² + 2s) ≥ 0` (using `2s³ - 2s² + 1 > 0` on `(0,1)`). -/
lemma den_reduced
    (e0 δ s η : ℝ)
    (hη : 0 < η) (hs0 : 0 < s) (hs1 : s < 1)
    (he0_nonneg : 0 ≤ e0) (he0_le : e0 ≤ 1 - s - η) (hδ_ge : 1 - s ^ 2 ≤ δ) :
    2 * η * s ^ 2 * δ ≤ δ - 2 * e0 + e0 ^ 2 := by
  have hη_le : η ≤ 1 - s := by linarith
  have he0_le1 : e0 ≤ 1 := by linarith
  have hpoly : 0 < 2*s^3 - 2*s^2 + 1 := by
    nlinarith [sq_nonneg (s - 1), mul_nonneg hs0.le (sq_nonneg (s-1)), sq_nonneg s,
      mul_pos hs0 hs0, mul_nonneg hs0.le hs0.le]
  have h2ηs2 : 0 < 1 - 2 * η * s^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hη_le (mul_nonneg hs0.le hs0.le), hpoly]
  have hstep1 : (1 - s^2) * (1 - 2*η*s^2) ≤ δ * (1 - 2*η*s^2) :=
    mul_le_mul_of_nonneg_right hδ_ge h2ηs2.le
  have hmono : 2*e0 - e0^2 ≤ 2*(1-s-η) - (1-s-η)^2 := by
    nlinarith [he0_le, he0_nonneg, he0_le1]
  have hbdry : 0 ≤ (1 - s^2) * (1 - 2*η*s^2) - (2*(1-s-η) - (1-s-η)^2) := by
    nlinarith [mul_pos hη hη, mul_pos hη hs0, mul_pos hs0 (mul_pos hs0 hs0),
      mul_nonneg hη.le (mul_nonneg hs0.le (mul_nonneg hs0.le hs0.le)),
      mul_nonneg hη.le hs0.le, sq_nonneg s, mul_pos hη (mul_pos hs0 hs0)]
  nlinarith [hstep1, hmono, hbdry]

/-- **C3.3 second-moment core (over ℝ).** This is the complete, sound real-analysis
argument behind ABF26 Corollary 3.3 via the second-moment (`johnson_bound_lemma`) route.

Given the raw Johnson output `M · Den ≤ frac·δ` with `Den = (1 - frac·e0)² - (1 - frac·δ)`,
where `frac = q/(q-1) ≥ 1`, the average ball radius `e0 ∈ [0, 1 - √ρ - η]`, and the MDS
relative distance `δ ≥ 1 - ρ`, one concludes `M ≤ 1/(2·η·ρ)`.

**This generalises and corrects the `frac = 1` heuristic** in the prior C3.3 inline note:
the denominator there was approximated as `(√ρ+η)² - ρ = η(2√ρ+η)`, which is the `frac → 1`
(asymptotic) value. Here the bound is established for *every* `frac ≥ 1` (hence every finite
alphabet `q ≥ 2`), since `Den = frac·(δ - 2e0 + frac·e0²) ≥ frac·(δ - 2e0 + e0²) ≥
frac·(2ηρδ)` by `frac·e0² ≥ e0²` (`frac ≥ 1`) and `den_reduced`. Cancelling `frac·δ > 0`
from `M·(2ηρ·frac·δ) ≤ M·Den ≤ frac·δ` gives `M·(2ηρ) ≤ 1`. -/
lemma c33_core
    (M frac δ e0 ρ η : ℝ)
    (hM : 0 ≤ M)
    (hfrac1 : 1 ≤ frac)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη : 0 < η)
    (he0_nonneg : 0 ≤ e0)
    (he0_le : e0 ≤ 1 - Real.sqrt ρ - η)
    (hδ_ge : 1 - ρ ≤ δ) (_hδ_le : δ ≤ 1)
    (hjohnson : M * ((1 - frac * e0) ^ 2 - (1 - frac * δ)) ≤ frac * δ) :
    M ≤ 1 / (2 * η * ρ) := by
  set s := Real.sqrt ρ with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hρ0
  have hs1 : s < 1 := by
    rw [hs]; calc Real.sqrt ρ < Real.sqrt 1 := Real.sqrt_lt_sqrt hρ0.le hρ1
      _ = 1 := Real.sqrt_one
  have hssq : s^2 = ρ := Real.sq_sqrt hρ0.le
  have hfrac_pos : 0 < frac := by linarith
  have hδ_pos : 0 < δ := by linarith [hρ1, hδ_ge]
  have hfracδ_pos : 0 < frac * δ := mul_pos hfrac_pos hδ_pos
  have hred : 2 * η * s^2 * δ ≤ δ - 2 * e0 + e0^2 := by
    apply den_reduced e0 δ s η hη hs0 hs1 he0_nonneg he0_le
    rw [hssq]; exact hδ_ge
  have hfe2 : e0^2 ≤ frac * e0^2 := le_mul_of_one_le_left (sq_nonneg e0) hfrac1
  have hDen_eq : (1 - frac * e0)^2 - (1 - frac * δ) = frac * (δ - 2*e0 + frac*e0^2) := by ring
  have hDen_ge : 2 * η * s^2 * (frac * δ) ≤ (1 - frac * e0)^2 - (1 - frac * δ) := by
    rw [hDen_eq, show 2 * η * s^2 * (frac * δ) = frac * (2 * η * s^2 * δ) by ring]
    apply mul_le_mul_of_nonneg_left _ hfrac_pos.le
    calc 2 * η * s^2 * δ ≤ δ - 2*e0 + e0^2 := hred
      _ ≤ δ - 2*e0 + frac*e0^2 := by linarith [hfe2]
  have hchain : M * (2 * η * s^2 * (frac * δ)) ≤ frac * δ := by
    calc M * (2 * η * s^2 * (frac * δ))
        ≤ M * ((1 - frac * e0)^2 - (1 - frac * δ)) := mul_le_mul_of_nonneg_left hDen_ge hM
      _ ≤ frac * δ := hjohnson
  have hcancel : M * (2 * η * s^2) ≤ 1 := by
    have h : (M * (2 * η * s^2)) * (frac * δ) ≤ 1 * (frac * δ) := by
      rw [show (M * (2 * η * s^2)) * (frac * δ) = M * (2 * η * s^2 * (frac * δ)) by ring, one_mul]
      exact hchain
    exact le_of_mul_le_mul_right h hfracδ_pos
  rw [hssq] at hcancel
  rw [le_div_iff₀ (by positivity)]
  linarith [hcancel]

end MdsPlotkin

end CodingTheory
