/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SliceLocusCount

/-!
# Issue #232 — The UNION-OVER-LOCI budget: the Conjecture-D counting skeleton closes
into a single quantitative bound (O99)

O96 (`SliceLocusCount`) ended with: "the surviving open content of the all-words
question is purely the LOCUS INCIDENCE: how the per-locus spaces overlap across the
`C(n/2,·)` loci and how the weight filter cuts them".  This file lands the first
quantitative answer — the UNION BOUND over loci, which needs no incidence
information at all:

    `#{f : deg f < k, wt_D(f) ≤ w} ≤ C(N, z₀) · q^(k − 2·z₀)`,   `z₀ = N − w`,

where `D` is an antipodally closed evaluation domain (`0 ∉ D`, `char ≠ 2`) and
`N = |D²|` is the squared-domain size.  Mechanism — pure composition of the landed
skeleton, no new analytic content:

* every weight-`≤ w` error has a dead locus of size `≥ N − w = z₀` with both slices
  locator-divisible (O94 `low_weight_slice_structure`);
* shrink the locus to size exactly `z₀` (divisibility survives shrinking — the
  locator of the smaller set divides evaluation at each of its points);
* the weight filter therefore sits inside the union of the `C(N, z₀)` per-locus
  spaces, each of EXACT size `q^(k − 2·z₀)` (O96
  `card_polysDegLT_slices_vanishing`);
* union bound.

Numerically verified (brute force over all `q^k` polynomials, `ZMod 5/7`, all
admissible `(k, w)`, exit OK): the bound holds with equality at `w = 0` (the
full-locus stratum, where the count IS the per-locus space) and is loose in the
mid-range — exactly the slack the open incidence question is about.

## Honest scope

This is the INCIDENCE-FREE upper bound.  Improving it requires genuine
inclusion–exclusion over locus overlaps (the open content O96 names); iterating it
down the folding tower multiplies the budgets but needs the per-level weight
bookkeeping (queued).  Note `wt_D` counts nonvanishing points of `f` on `D` itself
(level-1 evaluation weight), matching the O94 skeleton.
-/

namespace LamLeungTwoPow

open Polynomial Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The union-over-loci budget** (the incidence-free Conjecture-D bound): on an
antipodally closed domain `D` (`0 ∉ D`, `char ≠ 2`) with squared-domain size
`N = |D²|`, the degree-`< k` polynomials of evaluation weight `≤ w` on `D` number
at most `C(N, z₀) · q^(k − 2·z₀)` where `z₀ + w = N` — choose a dead locus of size
exactly `z₀`, then count its per-locus space exactly (O96). -/
theorem low_weight_union_budget {D : Finset F}
    (hneg : ∀ x ∈ D, -x ∈ D) (h0 : (0 : F) ∉ D) (h2 : (2 : F) ≠ 0)
    {k w z₀ : ℕ} (hz₀ : z₀ + w = (D.image (· ^ 2)).card) (hk : 2 * z₀ ≤ k) :
    ((polysDegLT (F := F) k).filter
        (fun f => (D.filter (fun x => f.eval x ≠ 0)).card ≤ w)).card
      ≤ ((D.image (· ^ 2)).card).choose z₀ * Fintype.card F ^ (k - 2 * z₀) := by
  classical
  have hsub : (polysDegLT (F := F) k).filter
      (fun f => (D.filter (fun x => f.eval x ≠ 0)).card ≤ w)
      ⊆ ((D.image (· ^ 2)).powersetCard z₀).biUnion
          (fun Z => (polysDegLT (F := F) k).filter (fun f =>
            (∀ z ∈ Z, (evenSlice f).eval z = 0) ∧
            (∀ z ∈ Z, (oddSlice f).eval z = 0))) := by
    intro f hf
    obtain ⟨hfk, hfw⟩ := Finset.mem_filter.mp hf
    obtain ⟨Z, he, ho, hZsub, hZcard, hhe, hho, _⟩ :=
      low_weight_slice_structure hneg h0 h2 f
    have hz₀le : z₀ ≤ Z.card := by omega
    obtain ⟨Z', hZ'sub, hZ'card⟩ := Finset.exists_subset_card_eq hz₀le
    refine Finset.mem_biUnion.mpr ⟨Z', ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨hZ'sub.trans hZsub, hZ'card⟩
    · refine Finset.mem_filter.mpr ⟨hfk, ?_, ?_⟩
      · intro z hz
        rw [hhe, eval_mul, TopLine.loc_eval_zero (hZ'sub hz), zero_mul]
      · intro z hz
        rw [hho, eval_mul, TopLine.loc_eval_zero (hZ'sub hz), zero_mul]
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  have hterm : ∀ Z ∈ (D.image (· ^ 2)).powersetCard z₀,
      ((polysDegLT (F := F) k).filter (fun f =>
        (∀ z ∈ Z, (evenSlice f).eval z = 0) ∧
        (∀ z ∈ Z, (oddSlice f).eval z = 0))).card
        = Fintype.card F ^ (k - 2 * z₀) := by
    intro Z hZ
    have hZc : Z.card = z₀ := (Finset.mem_powersetCard.mp hZ).2
    rw [card_polysDegLT_slices_vanishing h2 Z (by omega), hZc]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
    smul_eq_mul]

/-- **The Conjecture-D budget in weight form**: for `w ≤ N = |D²|`, the weight-`≤ w`
errors of degree `< k` number at most `C(N, N−w) · q^(k − 2·(N−w))` — the level-1
list budget with every constant explicit. -/
theorem low_weight_union_budget' {D : Finset F}
    (hneg : ∀ x ∈ D, -x ∈ D) (h0 : (0 : F) ∉ D) (h2 : (2 : F) ≠ 0)
    {k w : ℕ} (hw : w ≤ (D.image (· ^ 2)).card)
    (hk : 2 * ((D.image (· ^ 2)).card - w) ≤ k) :
    ((polysDegLT (F := F) k).filter
        (fun f => (D.filter (fun x => f.eval x ≠ 0)).card ≤ w)).card
      ≤ ((D.image (· ^ 2)).card).choose ((D.image (· ^ 2)).card - w)
          * Fintype.card F ^ (k - 2 * ((D.image (· ^ 2)).card - w)) :=
  low_weight_union_budget hneg h0 h2 (by omega) hk

end LamLeungTwoPow

#print axioms LamLeungTwoPow.low_weight_union_budget
#print axioms LamLeungTwoPow.low_weight_union_budget'
