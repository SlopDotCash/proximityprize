/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.A3InstanceCore
import ArkLib.Data.CodingTheory.ProximityGap.GeneratorMCA

/-!
# The A3 sharpness instance: the badness leg (issue #334, assembly stage 2, leg 1)

Every seed of the cancellation-pair instance is generator-MCA-bad for the interleaved
repetition code: the witness set is the seed's own block — the combination is the constant
pair `(0,1)` there (`a3_combination`), explained by the global constant interleaved codeword,
while the stack's `(b,0)` row has a coordinate equal to the position index on the block, which
no constant-rowed interleaved word can match at two points.

* `repetitionSubmodule` — the base code (global constants);
* `a3_seed_bad` — **leg 1**: under the radius bound `(1−δ)·n ≤ q` (the consumer-friendly,
  cast-free form of `δ ≥ 1 − 1/(q+1)`), every seed `b` satisfies `mcaEventG` for the
  interleaved instance at witness `T = block b`.
-/

open Finset
open scoped NNReal

namespace ProximityGap

variable (F : Type) [Field F] [DecidableEq F]

/-- The repetition code: globally constant functions, as a submodule. -/
def repetitionSubmodule : Submodule F (A3Pos F → F) where
  carrier := {w | ∃ a : F, ∀ i, w i = a}
  zero_mem' := ⟨0, fun _ => rfl⟩
  add_mem' := by
    rintro w v ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, fun i => by simp [ha i, hb i]⟩
  smul_mem' := by
    rintro c w ⟨a, ha⟩
    exact ⟨c * a, fun i => by simp [ha i, smul_eq_mul]⟩

variable {F}

/-- The `Fin`-reindexing of the stack rows (the `mcaEventG` surface requires `Fin l`). -/
noncomputable def a3RowEquiv (F : Type) [Field F] [DecidableEq F] [Fintype F] :
    (Option F × Fin 2) ≃ Fin (Fintype.card (Option F × Fin 2)) :=
  Fintype.equivFin _

/-- The stack, `Fin`-indexed. -/
noncomputable def a3StackFin [Fintype F] :
    Fin (Fintype.card (Option F × Fin 2)) → A3Pos F → Fin 2 → F :=
  fun r => a3Stack ((a3RowEquiv F).symm r)

/-- The seed coefficients, `Fin`-indexed. -/
noncomputable def a3GenFin [Fintype F] (b : Option F) :
    Fin (Fintype.card (Option F × Fin 2)) → F :=
  fun r => a3Gen b ((a3RowEquiv F).symm r)

/-- The `Fin`-indexed combination agrees with the structured one (sum transport along the
row equivalence). -/
theorem a3_combinationFin [Fintype F] (b : Option F) (pos : A3Pos F) (k : Fin 2) :
    (∑ r, a3GenFin (F := F) b r • a3StackFin (F := F) r pos k)
      = if pos.1 = b then (if k = 0 then 0 else 1) else 0 := by
  classical
  rw [← a3_combination (F := F) b pos k]
  exact Fintype.sum_equiv (a3RowEquiv F).symm _ _ fun r => rfl

/-- The seed-`b` block as a finset of positions. -/
def a3Block [Fintype F] (b : Option F) : Finset (A3Pos F) :=
  Finset.univ.filter (fun pos => pos.1 = b)

theorem a3Block_card [Fintype F] (b : Option F) :
    (a3Block (F := F) b).card = Fintype.card F := by
  classical
  unfold a3Block
  rw [show (Finset.univ.filter (fun pos : A3Pos F => pos.1 = b))
      = Finset.univ.image (fun j : F => ((b, j) : A3Pos F)) from ?_]
  · rw [Finset.card_image_of_injective _ (fun a a' h => (Prod.mk.injEq _ _ _ _).mp h |>.2),
      Finset.card_univ]
  · ext pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨pos.2, by rw [← h]⟩
    · rintro ⟨j, rfl⟩
      rfl

/-- **Leg 1 (badness)**: every seed of the cancellation-pair instance is generator-MCA-bad
over the interleaved repetition code, with its own block as the witness set, provided the
radius accommodates a single block: `(1−δ)·|ι| ≤ q`. -/
theorem a3_seed_bad [Fintype F] (hq : 2 ≤ Fintype.card F) {δ : ℝ≥0}
    (hδ : (1 - δ) * (Fintype.card (A3Pos F) : ℝ≥0) ≤ (Fintype.card F : ℝ≥0))
    (b : Option F) :
    mcaEventG (((repetitionSubmodule F : Submodule F (A3Pos F → F)) :
        Set (A3Pos F → F))^⋈ (Fin 2)) δ
      (a3StackFin (F := F)) (a3GenFin b) := by
  classical
  refine ⟨a3Block b, ?_, ?_, ?_⟩
  · -- Cardinality: the block has q positions and (1−δ)·n ≤ q.
    rw [a3Block_card]
    exact_mod_cast hδ
  · -- The combination is explained by the constant interleaved word (0, 1).
    refine ⟨fun _ k => if k = 0 then 0 else 1, ?_, ?_⟩
    · -- Each row of the witness is a global constant.
      intro k
      exact ⟨if k = 0 then 0 else 1, fun i => rfl⟩
    · -- Agreement with the combination on the block (the Pi-sum bridge + a3_combination).
      intro i hi
      funext k
      have hsum : (∑ r, a3GenFin (F := F) b r • a3StackFin (F := F) r i) k
          = ∑ r, a3GenFin (F := F) b r • a3StackFin (F := F) r i k := by
        rw [Finset.sum_apply]
        exact Finset.sum_congr rfl fun r _ => rfl
      rw [hsum, a3_combinationFin]
      unfold a3Block at hi
      rw [Finset.mem_filter] at hi
      rw [if_pos hi.2]
  · -- No joint agreement: row (b, 0) has a position-index coordinate on the block.
    rintro ⟨v, hv, hag⟩
    -- Two distinct positions in the block (q ≥ 2).
    obtain ⟨j₀, j₁, hne⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card F)
    -- The distinguishing component: 0 on affine blocks, 1 on the vertical block.
    set kd : Fin 2 := if b = none then 1 else 0 with hkd
    -- The stack row (b,0) at component kd equals the position index on the block.
    have hrow : ∀ j : F, a3Stack (F := F) (b, 0) (b, j) kd = j := by
      intro j
      unfold a3Stack
      simp only [if_pos rfl]
      by_cases hb : b = none
      · rw [hkd, if_pos hb]
        simp [hb]
      · rw [hkd, if_neg hb]
        simp [hb]
    -- The joint witness row at index e(b,0) is interleaved-constant; agreement contradicts.
    set r0 := (a3RowEquiv F) (b, 0) with hr0
    have hstackFin : ∀ pos, a3StackFin (F := F) r0 pos = a3Stack (F := F) (b, 0) pos := by
      intro pos
      unfold a3StackFin
      rw [hr0, Equiv.symm_apply_apply]
    have hvconst := hv r0 kd
    obtain ⟨a, ha⟩ := hvconst
    have h0 := congrFun (hag (b, j₀) (by
      unfold a3Block; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩) r0) kd
    have h1 := congrFun (hag (b, j₁) (by
      unfold a3Block; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩) r0) kd
    rw [hstackFin, hrow j₀] at h0
    rw [hstackFin, hrow j₁] at h1
    -- v (b,0) · kd is constant a, but equals j₀ and j₁.
    have e0 : a = j₀ := by rw [← ha (b, j₀)]; exact h0
    have e1 : a = j₁ := by rw [← ha (b, j₁)]; exact h1
    exact hne (e0 ▸ e1)

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.a3Block_card
#print axioms ProximityGap.a3_seed_bad
