/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.CurveAgreementThreshold
import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodability
import ArkLib.Data.CodingTheory.ProximityGap.GG25SpreadBound
import ArkLib.Data.CodingTheory.ProximityGap.GG25MCAFromCurveDecodability


/-!
# Bounding the GG25 curve close-set against a codeword-curve (B2 producer ingredient) (#389, #334)

The GG25 curve-decodability *consumer* (`all_seeds_close_of_curveDecodable`) takes a
`CurveDecodable` hypothesis; the open *producer* side must bound `curveCloseSet` for the explicit
code.  This file supplies the per-target piece: `curveCloseSet δ u (comb c)`, the seeds at which the
tested curve `comb u` is `δᵣ`-close to a fixed **codeword** curve `comb c`, is bounded by the
list bound `curve_agreement_card_le` (`CurveAgreementThreshold.lean`).

`curveCloseSet_codewordCurve_card_le`: with `Pᵢ = ∑ⱼ (uⱼᵢ − cⱼᵢ)·Xʲ` (degree `≤ ℓ`), a close seed
is a common root of `≥ a = n − ⌊δn⌋` of the `Pᵢ` (closeness = agreement on `≥ n−⌊δn⌋`
coordinates, via `hammingDist_le_floor_of_relHam_le`).  Hence
`|curveCloseSet δ u (comb c)| · (a − b) ≤ ℓ · n` (`b` = identically-zero coordinates) — a single
codeword-curve explains `≤ ℓ·n/(a−b)` seeds.  Unfolded (`A = F`) case.  Axiom-clean.
-/
open Finset Polynomial
open scoped NNReal

namespace ProximityGap

open GG25Lemma32

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Field F] [Fintype F] [DecidableEq F]

/-- **The curve close-set against a fixed codeword-curve is `≤ ℓ·n/(a−b)` (B2 producer
ingredient).**
For the tested curve `comb u` and a *codeword* curve `comb c` (degree `≤ ℓ`), the set of seeds `α`
at which the two curves are `δᵣ`-close has size bounded by the curve list bound: each coordinate
`i` contributes the degree-`≤ ℓ` polynomial `Pᵢ = ∑ⱼ (uⱼᵢ − cⱼᵢ)·Xʲ`, and a close seed is a common
root of `≥ a = n − ⌊δn⌋` of them.  Combined with `curve_agreement_card_le`:
`|curveCloseSet δ u (comb c : F → ι → F)| · (a − b) ≤ ℓ · n`, with `b` the identically-zero
coordinates.
This bounds how many seeds a single codeword-curve can explain — the per-target piece of
curve decodability. -/
theorem curveCloseSet_codewordCurve_card_le {ℓ : ℕ} (u c : Fin (ℓ + 1) → ι → F)
    {b : ℕ}
    (hb : (univ.filter (fun i => ((∑ j : Fin (ℓ + 1),
        Polynomial.C (u j i - c j i) * Polynomial.X ^ (j : ℕ) : Polynomial F) = 0))).card = b)
    {δ : ℝ≥0} (hab : b < Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊) :
    (curveCloseSet δ u (comb c : F → ι → F)).card
        * ((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊) - b)
      ≤ ℓ * Fintype.card ι := by
  classical
  set P : ι → Polynomial F :=
    fun i => ∑ j : Fin (ℓ + 1), Polynomial.C (u j i - c j i) * Polynomial.X ^ (j : ℕ) with hP
  set a := Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ with ha
  -- degree bound
  have hdeg : ∀ i, (P i).natDegree ≤ ℓ := by
    intro i
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun k _ => ?_)
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    exact Nat.lt_succ_iff.mp k.isLt
  -- evaluation matches the curve difference
  have hev : ∀ (α : F) (i : ι), (P i).eval α = comb u α i - comb c α i := by
    intro α i
    rw [hP]
    simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, comb, smul_eq_mul]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  -- the close set lands inside the `≥ a`-agreement (Heavy) set
  have hsub : curveCloseSet δ u (comb c : F → ι → F)
      ⊆ univ.filter (fun α : F => a ≤ (univ.filter (fun i => (P i).eval α = 0)).card) := by
    intro α hα
    simp only [curveCloseSet, mem_filter, mem_univ, true_and] at hα
    have hham : hammingDist (comb u α) (comb c α) ≤ ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ :=
      hammingDist_le_floor_of_relHam_le hα
    rw [mem_filter]
    refine ⟨mem_univ α, ?_⟩
    -- agreement + hammingDist = n, and hammingDist ≤ ⌊δn⌋, so agreement ≥ n − ⌊δn⌋ = a
    have hpart : (univ.filter (fun i => (P i).eval α = 0)).card
        + hammingDist (comb u α) (comb c α) = Fintype.card ι := by
      rw [hammingDist,
        show (univ.filter (fun i => (P i).eval α = 0))
            = univ.filter (fun i => comb u α i = comb c α i) from
          Finset.filter_congr (fun i _ => by rw [hev α i, sub_eq_zero]),
        ← Finset.card_univ (α := ι)]
      exact Finset.card_filter_add_card_filter_not (s := univ)
        (fun i => comb u α i = comb c α i)
    rw [ha]
    omega
  calc (curveCloseSet δ u (comb c : F → ι → F)).card * (a - b)
      ≤ (univ.filter (fun α : F =>
          a ≤ (univ.filter (fun i => (P i).eval α = 0)).card)).card * (a - b) :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ ℓ * Fintype.card ι := curve_agreement_card_le P hdeg hb hab

end ProximityGap
