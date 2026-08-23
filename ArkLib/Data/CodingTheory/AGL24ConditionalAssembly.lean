/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24FrontDoorBridge
import ArkLib.Data.CodingTheory.AGL24UnionBound

/-!
# [AGL24] the conditional Theorem 1.1 assembly (issue #346, brick 10)

The probability plumbing over the deterministic chain: under a random evaluation embedding,
the probability that the Reed–Solomon code fails the `Λ ≤ L` list bound is at most the
number of small weakly-partition-connected hypergraphs times the per-hypergraph
rank-deficit probability — **conditional on the named Lemma 3.1 interface**
(`RIMFullRankFailureProbResidual`), which is the campaign's remaining research core.

* `rankDeficitEvent` — the per-hypergraph bad event in embedding space;
* `rankDeficitEvent_toOuterMeasure_eq_map` — the exact PMF-map pullback from the raw
  evaluation-function event to the embedding-space event;
* `failure_subset_union` — the deterministic inclusion (the pointwise implication of brick 9
  re-packaged as an event inclusion into the finite union over weakly-partition-connected
  hypergraphs);
* `conditional_failure_bound` — **the assembly**: outer-measure monotonicity + finite
  subadditivity + the per-hypergraph interface bound.
-/

open Finset ListDecodable

namespace AGL24

variable {ι F : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Field F] [Fintype F]
  [DecidableEq F]

/-- The per-hypergraph rank-deficit event, in embedding space. -/
def rankDeficitEvent (k : ℕ) {t : ℕ} (e : ι → Finset (Fin (t + 1))) :
    Set (ι ↪ F) :=
  {φ | ∃ v : Fin t × Fin k → F, v ≠ 0 ∧
    ((RIM F e).map (MvPolynomial.eval (fun i => φ i))).mulVec v = 0}

/-- The embedding-space rank-deficit event is the pullback of the raw evaluation-function
event. -/
theorem rankDeficitEvent_eq_preimage (k : ℕ) {t : ℕ}
    (e : ι → Finset (Fin (t + 1))) :
    rankDeficitEvent k e =
      (fun φ : ι ↪ F => fun i => φ i) ⁻¹'
        RIMRankDeficitSet (F := F) (k := k) e := by
  rfl

/-- Exact outer-measure transport for the embedding-space rank-deficit event. -/
theorem rankDeficitEvent_toOuterMeasure_eq_map (D : PMF (ι ↪ F)) (k : ℕ) {t : ℕ}
    (e : ι → Finset (Fin (t + 1))) :
    D.toOuterMeasure (rankDeficitEvent k e)
      = (D.map (fun φ i => φ i)).toOuterMeasure
          (RIMRankDeficitSet (F := F) (k := k) e) := by
  rw [toOuterMeasure_map_RIMRankDeficitSet (F := F) (D := D)
    (f := fun φ i => φ i) (e := e)]
  rfl

/-- The (finite) index of the union: a raw vertex-count parameter `t < L + 2` (the chain's
output `t ≤ L` embeds with **no dependent cast**) together with a weakly-partition-connected
edge family on `t + 1` vertices. -/
def WpcIndex (ι : Type*) [Fintype ι] [DecidableEq ι] (k L : ℕ) : Type _ :=
  Σ t' : Fin (L + 2), {e : ι → Finset (Fin (t'.val + 1)) //
    WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t'.val + 1))) e}

noncomputable instance (k L : ℕ) : Fintype (WpcIndex ι k L) := by
  classical
  unfold WpcIndex
  infer_instance

/-- **The deterministic inclusion**: the `Λ`-failure event is contained in the finite union
of per-hypergraph rank-deficit events over weakly-partition-connected hypergraphs with at
most `L + 1` vertices. -/
theorem failure_subset_union {k L : ℕ} (hL : 1 ≤ L) {r : ℝ} (hr : 0 ≤ r)
    (hk : k ≤ Fintype.card ι)
    (hrad : (L + 1 : ℝ) * r * (Fintype.card ι : ℝ)
      ≤ ((L * (Fintype.card ι - k) : ℕ) : ℝ)) :
    {φ : ι ↪ F | ¬ Lambda (ReedSolomon.code φ k : Set (ι → F)) r ≤ (L : ℕ∞)}
      ⊆ ⋃ idx : WpcIndex ι k L, rankDeficitEvent k idx.2.val := by
  intro φ hφ
  obtain ⟨t, htL, ht1, g, y, hwpc, v, hv, hker⟩ :=
    lambda_gt_gives_wpc_rank_deficit hL φ hr hk hrad hφ
  -- The chain's t embeds directly: ⟨t, t < L + 2⟩ with t + 1 vertices, no cast.
  exact Set.mem_iUnion.mpr
    ⟨⟨⟨t, by omega⟩, ⟨agreementEdge y (rsEval (fun i => φ i) g), hwpc⟩⟩, v, hv, hker⟩

open scoped ENNReal in
/-- **The conditional Theorem 1.1 assembly**: under any random evaluation embedding `D`, if
every weakly-partition-connected hypergraph with at most `L+1` vertices satisfies the named
Lemma 3.1 interface at level `bound`, then the probability of the `Λ`-failure of the
Reed–Solomon code is at most `(#hypergraphs) · bound`. -/
theorem conditional_failure_bound {k L : ℕ} (hL : 1 ≤ L) {r : ℝ} (hr : 0 ≤ r)
    (hk : k ≤ Fintype.card ι)
    (hrad : (L + 1 : ℝ) * r * (Fintype.card ι : ℝ)
      ≤ ((L * (Fintype.card ι - k) : ℕ) : ℝ))
    (D : PMF (ι ↪ F)) (bound : ENNReal)
    (hres : ∀ idx : WpcIndex ι k L,
      RIMFullRankFailureProbResidual (F := F) (k := k)
        (D.map (fun φ i => φ i)) idx.2.val bound) :
    D.toOuterMeasure
        {φ : ι ↪ F | ¬ Lambda (ReedSolomon.code φ k : Set (ι → F)) r ≤ (L : ℕ∞)}
      ≤ (Fintype.card (WpcIndex ι k L) : ENNReal) * bound := by
  classical
  -- Name the failure event (the embedded ≤ inside the set-builder confuses calc parsing).
  set E : Set (ι ↪ F) :=
    {φ : ι ↪ F | ¬ Lambda (ReedSolomon.code φ k : Set (ι → F)) r ≤ (L : ℕ∞)} with hE
  show D.toOuterMeasure E ≤ _
  -- Monotonicity into the union, then finite subadditivity.
  calc D.toOuterMeasure E
      ≤ D.toOuterMeasure (⋃ idx : WpcIndex ι k L, rankDeficitEvent k idx.2.val) :=
        D.toOuterMeasure.mono (hE ▸ failure_subset_union hL hr hk hrad)
  _ ≤ ∑ idx : WpcIndex ι k L, D.toOuterMeasure (rankDeficitEvent k idx.2.val) :=
        MeasureTheory.measure_iUnion_fintype_le D.toOuterMeasure _
  _ ≤ ∑ _idx : WpcIndex ι k L, bound := by
        refine Finset.sum_le_sum fun idx _ => ?_
        have h := hres idx
        unfold RIMFullRankFailureProbResidual at h
        -- The mapped-PMF event pulls back to the embedding-space event.
        rw [PMF.toOuterMeasure_map_apply] at h
        simpa [rankDeficitEvent, RIMRankDeficitSet] using h
  _ = (Fintype.card (WpcIndex ι k L) : ENNReal) * bound := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.rankDeficitEvent_eq_preimage
#print axioms AGL24.rankDeficitEvent_toOuterMeasure_eq_map
#print axioms AGL24.failure_subset_union
#print axioms AGL24.conditional_failure_bound
