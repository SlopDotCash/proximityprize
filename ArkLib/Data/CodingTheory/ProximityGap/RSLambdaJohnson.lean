/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ReedSolomonJohnson
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Reed–Solomon list size up to the Johnson radius (#232)

The previous pins bound `δ*` from below only at the *unique-decoding* radius `δ_min/2`. This file
pushes the lower side up to the **Johnson radius** `1 − √ρ` — the lower edge of the open prize gap
`[1 − √ρ, 1 − ρ)` — using the *elementary second-moment Johnson bound*. (Crucially, reaching the
Johnson radius needs **no** Guruswami–Sudan multiplicity interpolation: that wall is only for the
Johnson→capacity *interior*. The combinatorial list-size bound up to Johnson is just the
second-moment/Gram argument.)

  `reedSolomon_Lambda_le_johnson` — for `RS[F, α, k]` with the Johnson gap `n·(k−1) < a²`
  (`a = n − ⌊δn⌋` the agreement count), `Λ(RS[k], δ) ≤ ⌊n²/(a² − n·(k−1))⌋`.

Built on the axiom-clean `ArkLib.CodingTheory.ReedSolomonJohnson.reedSolomon_johnson_list_bound`
(second-moment Johnson bound + RS root-counting pairwise agreement `≤ k−1`) — *not* on the
`sorryAx`-tainted `ArkLib.JohnsonList.johnson_list_bound_div`. With `a = n − e`, `d = n − k + 1`, the
gap `n(k−1) < a²` is exactly `e < n(1 − √((k−1)/n)) ≈ n(1 − √ρ)`, the Johnson radius.

This is the strongest *provable* lower edge: it traps `δ*` into the genuine open gap
`[1 − √ρ, 1 − ρ)`. Pinning the exact value inside that gap is the open prize.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap

open scoped NNReal Polynomial
open ListDecodable
open ArkLib.CodingTheory.ReedSolomonJohnson ArkLib.CodingTheory.JohnsonSimplex

/-- **Reed–Solomon list size up to the Johnson radius.** If the Johnson gap `n·(k−1) < a²` holds for
the agreement count `a = n − ⌊δn⌋`, then the maximised list size of `RS[F, α, k]` at relative radius
`δ` is at most `⌊n² / (a² − n·(k−1))⌋`. Reaching the Johnson radius requires only the elementary
second-moment bound (`reedSolomon_johnson_list_bound`), no multiplicity interpolation. -/
theorem reedSolomon_Lambda_le_johnson
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {k : ℕ} [NeZero k] {α : ι ↪ F} {δ : ℝ}
    (hgap : Fintype.card ι * (k - 1) <
        (Fintype.card ι - ⌊δ * Fintype.card ι⌋₊) ^ 2) :
    ListDecodable.Lambda ((ReedSolomon.code α k : Set (ι → F))) δ ≤
      ((Fintype.card ι ^ 2 /
        ((Fintype.card ι - ⌊δ * Fintype.card ι⌋₊) ^ 2
          - Fintype.card ι * (k - 1)) : ℕ) : ℕ∞) := by
  classical
  set e : ℕ := ⌊δ * (Fintype.card ι : ℝ)⌋₊ with he
  set a : ℕ := Fintype.card ι - e with ha
  set Den : ℕ := a ^ 2 - Fintype.card ι * (k - 1) with hD
  have hDpos : 0 < Den := by rw [hD]; exact Nat.sub_pos_of_lt hgap
  apply ListDecodable.Lambda_le_natCast_of_forall_closeFinset_card_le
  intro f
  set L : Finset (ι → F) := closeCodewordsRelFinset ((ReedSolomon.code α k : Set (ι → F))) f δ
    with hL
  -- every element of the point list is a degree-`<k` polynomial evaluation
  have hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (α i) := by
    intro c hcL
    have hcmem : c ∈ (ReedSolomon.code α k : Set (ι → F)) :=
      (mem_closeCodewordsRelFinset.mp hcL).1
    rw [SetLike.mem_coe, ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero] at hcmem
    obtain ⟨p, hpdeg, hpc⟩ := hcmem
    refine ⟨p, hpdeg, ?_⟩
    rw [hpc]; funext i; simp [ReedSolomon.evalOnPoints]
  -- every element agrees with `f` on at least `a` coordinates
  have hclose : ∀ c ∈ L, a ≤ agree c f := by
    intro c hcL
    have hmem := mem_closeCodewordsRelFinset.mp hcL
    have hd : hammingDist c f ≤ e := by
      have hrel : (Code.relHammingDist f c : ℝ) ≤ δ := by
        have h := hmem.2
        simp only [ListDecodable.relHammingBall, Set.mem_setOf_eq] at h
        convert h using 3
      have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
      have hreleq : (Code.relHammingDist f c : ℝ)
          = (hammingDist f c : ℝ) / Fintype.card ι := by
        rw [Code.relHammingDist]; push_cast; ring
      rw [hreleq, div_le_iff₀ hnpos] at hrel
      rw [hammingDist_comm]
      exact Nat.le_floor hrel
    have hae : agree c f + hammingDist c f = Fintype.card ι := by
      simp only [ArkLib.CodingTheory.JohnsonSimplex.agree, hammingDist, ne_eq]
      rw [← Finset.card_univ (α := ι)]
      exact Finset.filter_card_add_filter_neg_card_eq_card _
    omega
  -- second-moment Johnson bound (real-valued) and conversion to a ℕ list-size cap
  have hreal := reedSolomon_johnson_list_bound (D := α) (k := k) (w := f) L a hpoly hclose
  have hsub : ((a : ℝ) ^ 2 - (Fintype.card ι : ℝ) * ((k - 1 : ℕ) : ℝ)) = ((Den : ℕ) : ℝ) := by
    rw [hD, Nat.cast_sub (le_of_lt hgap)]; push_cast; ring
  rw [hsub] at hreal
  have hnat : L.card * Den ≤ Fintype.card ι ^ 2 := by
    have hcast : (L.card : ℝ) * ((Den : ℕ) : ℝ) ≤ ((Fintype.card ι ^ 2 : ℕ) : ℝ) := by
      calc (L.card : ℝ) * ((Den : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 := hreal
        _ = ((Fintype.card ι ^ 2 : ℕ) : ℝ) := by push_cast; ring
    exact_mod_cast hcast
  exact (Nat.le_div_iff_mul_le hDpos).2 hnat

#print axioms reedSolomon_Lambda_le_johnson

end ProximityGap
