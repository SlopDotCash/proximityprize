/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24ConditionalAssembly
import ArkLib.Data.CodingTheory.AGL24ProbDischarge

/-!
# [AGL24] Theorem 1.1 under uniform evaluation embeddings, conditional on Theorem 2.11

`conditional_failure_bound` (AGL24ConditionalAssembly) bounds the `Λ`-failure probability of a
random Reed–Solomon code under an evaluation-embedding distribution `D : PMF (ι ↪ F)`, given
the Lemma 3.1 interface `RIMFullRankFailureProbResidual` for the mapped distribution
`D.map (fun φ i => φ i)` at every weakly-partition-connected index. The in-tree discharge
`rimFailureProb_of_symbolic` (AGL24ProbDischarge) proves that interface only for the uniform
distribution on all tuples `ι → F`. Until now no theorem connected the two, so the assembly
had no instance.

This file connects them for the uniform distribution on embeddings, which is the distinct
evaluation-point sampling of [AGL24] §3:

* `toOuterMeasure_map_uniformEmbedding_le` — the transfer bound: for every event
  `A ⊆ (ι → F)`, `Pr_{φ ↪}[φ ∈ A] ≤ (|F|^|ι| / #(ι ↪ F)) · Pr_{α ∈ F^ι}[α ∈ A]`.
* `RIMRankDeficitSet_of_t_eq_zero` — at `t = 0` the reduced intersection matrix has no
  columns, so the rank-deficit event is empty (the `t' = 0` indices of `WpcIndex`).
* `failure_bound_uniformEmbedding_of_symbolic` — **the assembly instance**: conditional only
  on `SymbolicFullRankResidual` ([AGL24] Theorem 2.11, the GM-MDS input),
  `Pr_{φ ↪}[Λ(RS[φ, k]) > L] ≤ #WpcIndex · (|F|^|ι| / #(ι ↪ F)) · (L+1)k(k−1)/|F|`.

The transfer factor `|F|^n / (|F|)_n` is the standard cost of moving from independent to
distinct evaluation points; it tends to `1` when `n² = o(|F|)`.

## What remains open

`SymbolicFullRankResidual` ([AGL24] Theorem 2.11) is the only hypothesis. The quantitative
form of the bound (the `#WpcIndex` count and the per-hypergraph Schwartz–Zippel degree) is
that of `conditional_failure_bound` and `rimFailureProb_of_symbolic`; this file does not
sharpen it to the paper's `C(n,r)(t^r 2^{(t−1)k}/(q−n))^r` form.
-/

open Finset ListDecodable
open scoped ENNReal

namespace AGL24

variable {ι F : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F]
  [DecidableEq F]

omit [Nonempty ι] [DecidableEq F] in
/-- **Transfer bound.** Pushing the uniform distribution on evaluation embeddings to tuples
costs at most the factor `#(ι → F) / #(ι ↪ F)` against the uniform distribution on all
tuples, for every event. -/
theorem toOuterMeasure_map_uniformEmbedding_le [Nonempty (ι ↪ F)] (A : Set (ι → F)) :
    ((PMF.uniformOfFintype (ι ↪ F)).map (fun φ i => φ i)).toOuterMeasure A
      ≤ ((Fintype.card (ι → F) : ℝ≥0∞) / Fintype.card (ι ↪ F)) *
        (PMF.uniformOfFintype (ι → F)).toOuterMeasure A := by
  classical
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  have hcard : Fintype.card ((fun φ : ι ↪ F => fun i => φ i) ⁻¹' A) ≤ Fintype.card A :=
    Fintype.card_le_of_injective
      (fun x => ⟨(fun i => x.1 i), x.2⟩)
      (fun x y h => Subtype.ext (DFunLike.coe_injective (congrArg Subtype.val h)))
  have hQ0 : (Fintype.card (ι → F) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hQT : (Fintype.card (ι → F) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc (Fintype.card ((fun φ : ι ↪ F => fun i => φ i) ⁻¹' A) : ℝ≥0∞)
        / Fintype.card (ι ↪ F)
      ≤ (Fintype.card A : ℝ≥0∞) / Fintype.card (ι ↪ F) := by
        gcongr
    _ = (Fintype.card (ι → F) : ℝ≥0∞) / Fintype.card (ι ↪ F) *
          ((Fintype.card A : ℝ≥0∞) / Fintype.card (ι → F)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        rw [show (Fintype.card (ι → F) : ℝ≥0∞) * (Fintype.card (ι ↪ F) : ℝ≥0∞)⁻¹ *
            ((Fintype.card A : ℝ≥0∞) * (Fintype.card (ι → F) : ℝ≥0∞)⁻¹)
            = (Fintype.card A : ℝ≥0∞) * (Fintype.card (ι ↪ F) : ℝ≥0∞)⁻¹ *
              ((Fintype.card (ι → F) : ℝ≥0∞) * (Fintype.card (ι → F) : ℝ≥0∞)⁻¹) by ring]
        rw [ENNReal.mul_inv_cancel hQ0 hQT, mul_one]

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- At `t = 0` the reduced intersection matrix has no columns (`Fin 0 × Fin k`), so no
nonzero kernel vector exists and the rank-deficit event is empty. -/
theorem RIMRankDeficitSet_of_t_eq_zero {k : ℕ} (e : ι → Finset (Fin (0 + 1))) :
    RIMRankDeficitSet (F := F) (k := k) e = ∅ := by
  ext α
  simp only [RIMRankDeficitSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨v, hv, -⟩
  exact hv (funext fun c => c.1.elim0)

omit [DecidableEq F] in
/-- **[AGL24] Theorem 1.1 failure bound under uniform evaluation embeddings, conditional only
on Theorem 2.11.** Instantiates `conditional_failure_bound` at the uniform embedding
distribution, discharging its Lemma 3.1 hypothesis at every index by the transfer bound and
`rimFailureProb_of_symbolic` (with the empty `t = 0` event handled directly). -/
theorem failure_bound_uniformEmbedding_of_symbolic {k L : ℕ} (hL : 1 ≤ L) {r : ℝ}
    (hr : 0 ≤ r) (hk : k ≤ Fintype.card ι)
    (hrad : (L + 1 : ℝ) * r * (Fintype.card ι : ℝ)
      ≤ ((L * (Fintype.card ι - k) : ℕ) : ℝ))
    [Nonempty (ι ↪ F)]
    (hsym : SymbolicFullRankResidual (ι := ι) F k) :
    (PMF.uniformOfFintype (ι ↪ F)).toOuterMeasure
        {φ : ι ↪ F | ¬ Lambda (ReedSolomon.code φ k : Set (ι → F)) r ≤ (L : ℕ∞)}
      ≤ (Fintype.card (WpcIndex ι k L) : ℝ≥0∞) *
        (((Fintype.card (ι → F) : ℝ≥0∞) / Fintype.card (ι ↪ F)) *
          (((L + 1) * k * (k - 1) : ℕ) / (Fintype.card F : ℝ≥0∞))) := by
  classical
  refine conditional_failure_bound hL hr hk hrad _ _ fun idx => ?_
  obtain ⟨t', e, hwpc⟩ := idx
  unfold RIMFullRankFailureProbResidual
  refine (toOuterMeasure_map_uniformEmbedding_le _).trans ?_
  gcongr ?_ * ?_
  obtain ⟨t, ht⟩ := t'
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · simp [RIMRankDeficitSet_of_t_eq_zero]
  · have hprov := rimFailureProb_of_symbolic hsym htpos e hwpc
    unfold RIMFullRankFailureProbResidual at hprov
    refine hprov.trans ?_
    gcongr
    omega

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.toOuterMeasure_map_uniformEmbedding_le
#print axioms AGL24.RIMRankDeficitSet_of_t_eq_zero
#print axioms AGL24.failure_bound_uniformEmbedding_of_symbolic
