/-
Copyright (c) 2026 Khang. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: Khang
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24UnionBound
import ArkLib.Data.CodingTheory.AGL24WeakPartition

/-!
# [AGL24] §3: boundary instances of the failure-probability interface

`AGL24.RIMFullRankFailureProbResidual` (AGL24UnionBound) is the recorded [AGL24] §3
"Lemma 3.1 interface" of issue #354 — a plug-in predicate in its three parameters
(`D`, `e`, `bound`). The providers `AGL24.rimFailureProb_of_symbolic` and
`AGL24.rimFailureProb_of_rootedOutCut_and_dualZeroPattern` use uniform tuples,
a WPC family and a Schwartz–Zippel bound. The embedding-based assembly
consumes this predicate through
hypotheses that carry those side conditions (`AGL24.conditional_failure_bound`). It
is not a universal claim, so nothing in this file refutes it and no census status
changes.

What this file adds are two kernel-checked *boundary* facts delimiting where the
interface predicate fails to hold, making explicit why every consumer must carry the
side conditions:

* at a non-WPC family — the empty one-slot family — the reduced intersection matrix
  has no rows, the deficit set is everything, and its outer measure under any
  tuple PMF, including the uniform distribution, is `1`
  (`rimRankDeficitSet_empty_family`, `toOuterMeasure_deficit_empty_family_eq_one`);
* at a genuinely 2-WPC family — both slots the complete edge on two vertices
  (`wpc_two_complete_family`) — a point mass at the all-zero tuple gives the
  deficit set measure `1` (`zero_eval_mem_rimRankDeficitSet_complete_family`,
  `toOuterMeasure_deficit_complete_family_pure_eq_one`). Every tuple obtained
  from an embedding `Fin 2 ↪ ZMod 2` takes two distinct values, so the mapped
  distribution assigns zero mass to this tuple. This particular point mass is
  outside the assembly's scope.

The distribution bridge that `AGL24.conditional_failure_bound`'s hypothesis actually
needs — from the uniform-over-tuples bound to the embedding-mapped evaluation PMF —
is tracked in PR #338 and deliberately out of scope here.
-/

open Finset

namespace AGL24

/-! ## Boundary instance 1: a non-WPC family under any tuple distribution -/

/-- The deficit set at the empty one-slot family is everything: the reduced
intersection matrix has no rows, so `mulVec` is vacuously zero. -/
theorem rimRankDeficitSet_empty_family :
    RIMRankDeficitSet (F := ZMod 2) (k := 1) (fun _ : Fin 1 => (∅ : Finset (Fin 2)))
      = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun α => ⟨fun _ => 1, ?_, ?_⟩
  · intro hzero
    exact one_ne_zero (congrFun hzero (⟨(0 : Fin 1), (0 : Fin 1)⟩ : Fin 1 × Fin 1))
  · funext r
    exact absurd r.2.2.1 (by simp)

/-- The empty-family deficit set has measure `1` under any tuple PMF.
The weak partition-connectivity hypothesis excludes this family. -/
theorem toOuterMeasure_deficit_empty_family_eq_one (D : PMF (Fin 1 → ZMod 2)) :
    D.toOuterMeasure
      (RIMRankDeficitSet (F := ZMod 2) (k := 1) (fun _ : Fin 1 => (∅ : Finset (Fin 2))))
      = 1 := by
  rw [rimRankDeficitSet_empty_family]
  exact (PMF.toOuterMeasure_apply_eq_one_iff D Set.univ).2 (Set.subset_univ _)

/-! ## Boundary instance 2: a genuinely 2-WPC family at a point-mass distribution -/

/-- The complete two-slot family on two vertices is genuinely
`2`-weakly-partition-connected: a partition of two vertices has at most two cells
(`Finpartition.card_parts_le_card`); with one cell the left side is zero, and with two
cells every cell is nonempty (`Finpartition.nonempty_of_mem_parts`), so the complete
edge touches both and the defining sum is exactly `2`. -/
theorem wpc_two_complete_family :
    WeaklyPartitionConnected 2 (Finset.univ : Finset (Fin 2))
      (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) := by
  intro P
  have hcardle : P.parts.card ≤ 2 := by
    have h := P.card_parts_le_card
    simpa using h
  have htouch : ∀ i : Fin 2, (touchedCells P
      ((fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) i ∩ Finset.univ)).card
      = P.parts.card := by
    intro i
    have hfil : P.parts.filter (fun c =>
        (((fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) i ∩
          Finset.univ) ∩ c).Nonempty) = P.parts :=
      Finset.filter_eq_self.mpr fun c hc => by
        simpa using P.nonempty_of_mem_parts hc
    simp only [touchedCells, hfil]
  rcases Nat.lt_or_ge P.parts.card 2 with hlt | hge
  · calc (2 : ℕ) * (P.parts.card - 1) = 0 := by omega
      _ ≤ ∑ i : Fin 2, ((touchedCells P
          ((fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) i ∩
            Finset.univ)).card - 1) := Nat.zero_le _
  · have hcard : P.parts.card = 2 := le_antisymm hcardle hge
    have hsum : ∑ i : Fin 2, ((touchedCells P
        ((fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) i ∩
          Finset.univ)).card - 1) = 2 := by
      have hev : ∑ i : Fin 2, ((touchedCells P
          ((fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) i ∩
            Finset.univ)).card - 1)
          = ∑ i : Fin 2, (2 - 1) :=
        Finset.sum_congr rfl fun i _ => by rw [htouch i, hcard]
      rw [hev]
      simp
    rw [show (2 : ℕ) * (P.parts.card - 1) = 2 from by omega, hsum]

/-- The all-zero evaluation lies in the deficit set of the complete two-slot family at
`k = 2`: the minimal vertex of the complete edge is `0`, so every column's vertex is the
minimal one (`RIM_apply_min`) and the evaluated entries are `0 ^ c.2.val`; the kernel
column vector `v = fun c => c.2.val` annihilates both rows (`0 ^ 0 * 0 = 0` and
`0 ^ 1 * 1 = 0`). -/
theorem zero_eval_mem_rimRankDeficitSet_complete_family :
    (fun _ : Fin 2 => (0 : ZMod 2)) ∈
      RIMRankDeficitSet (F := ZMod 2) (k := 2)
        (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) := by
  refine ⟨fun c => (c.2.val : ZMod 2), fun hzero => ?_, ?_⟩
  · exact one_ne_zero (congrFun hzero
      (⟨(0 : Fin 1), (1 : Fin 2)⟩ : Fin 1 × Fin 2))
  · funext r
    obtain ⟨i, ⟨j, hy⟩⟩ := r
    have hy1 : j ∈ (Finset.univ : Finset (Fin 2)) := hy.1
    have hmin : (Finset.univ : Finset (Fin 2)).min' ⟨j, hy1⟩ = (0 : Fin 2) :=
      Fin.le_antisymm
        ((Finset.univ : Finset (Fin 2)).min'_le (0 : Fin 2) (Finset.mem_univ _))
        (Fin.zero_le _)
    -- every column's vertex is the minimal vertex `0`
    have hcast : ∀ c : Fin 1 × Fin 2, (c.1).castSucc = (0 : Fin 2) := by
      intro c
      have hc1 : c.1 = (0 : Fin 1) := Fin.val_injective (Nat.lt_one_iff.mp c.1.isLt)
      rw [hc1]
      rfl
    show (∑ c : Fin 1 × Fin 2,
        MvPolynomial.eval (fun _ : Fin 2 => (0 : ZMod 2))
          ((RIM (ZMod 2) (k := 2)
            (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) ⟨i, j, hy⟩) c)
        * ((fun c : Fin 1 × Fin 2 => (c.2.val : ZMod 2)) c)) = 0
    refine Finset.sum_eq_zero fun c _ => ?_
    have hRIM : (RIM (ZMod 2) (k := 2) (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2)))
        ⟨i, j, hy⟩) c
        = (MvPolynomial.X i : MvPolynomial (Fin 2) (ZMod 2)) ^ (c.2 : ℕ) :=
      RIM_apply_min (ZMod 2) (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2)))
        ⟨i, j, hy⟩ c ((hcast c).trans hmin.symm)
    rw [hRIM, map_pow, MvPolynomial.eval_X]
    rcases Nat.lt_or_ge c.2.val 1 with hc2 | hc2
    · have hc20 : c.2.val = 0 := by omega
      simp [hc20]
    · have hc21 : c.2.val = 1 := by omega
      simp [hc21]

/-- A point-mass distribution on the all-zero evaluation gives the complete-family
deficit set measure `1`. The all-zero tuple is outside the image of evaluation
embeddings `Fin 2 ↪ ZMod 2`, which take two distinct values. The embedding-based
assembly therefore cannot use this particular point mass. -/
theorem toOuterMeasure_deficit_complete_family_pure_eq_one :
    (PMF.pure (fun _ : Fin 2 => (0 : ZMod 2))).toOuterMeasure
      (RIMRankDeficitSet (F := ZMod 2) (k := 2)
        (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2)))) = 1 := by
  rw [PMF.toOuterMeasure_pure_apply,
    ite_eq_left zero_eval_mem_rimRankDeficitSet_complete_family]

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.rimRankDeficitSet_empty_family
#print axioms AGL24.toOuterMeasure_deficit_empty_family_eq_one
#print axioms AGL24.wpc_two_complete_family
#print axioms AGL24.zero_eval_mem_rimRankDeficitSet_complete_family
#print axioms AGL24.toOuterMeasure_deficit_complete_family_pure_eq_one
