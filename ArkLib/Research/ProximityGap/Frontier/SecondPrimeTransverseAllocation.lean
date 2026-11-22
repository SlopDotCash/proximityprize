/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterSuccessorSplitCriterion
import ArkLib.Research.ProximityGap.Frontier.SplitPencilFiberData

/-! # Allocating a split pencil for the second-prime transverse construction -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeTransverseAllocation

open Polynomial Finset SmoothFourHeadColored SmoothFourHeadFibers QuarterSuccessorSplitCriterion

/-- Assign two private sites to each head and reserve 268435456 sites on which
all three evaluations are distinct. Color two is exactly the zero fiber of the
second polynomial head. -/
theorem allocation {I F : Type} [Fintype I] [Field F] (dom : I ↪ F)
    (hn : Fintype.card I = 1073741824) (pencil : splitPencil dom) :
    ∃ col : I → Fin 8, ∃ f : Fin 3 → F[X],
      (∀ j, (univ.filter (fun x => col x = j)).card = weight 268435454 0 2 268435456 j) ∧
      (∀ i, (f i).natDegree ≤ 268435454) ∧ f 0 = 0 ∧
      (∀ x, col x = 2 ↔ (f 1).eval (dom x) = 0) ∧
      (∀ x i, col x ∈ coreClasses i → (f i).eval (dom x) = (f (owner (col x))).eval (dom x)) ∧
      (∀ x, col x ∈ ordinaryClasses →
        (f (miss (col x))).eval (dom x) ≠ (f (owner (col x))).eval (dom x)) ∧
      (∀ x, col x = 7 → Function.Injective (fun i => (f i).eval (dom x))) := by
  classical
  obtain ⟨P,Q,dp,dq,hp,hq,hr,cop⟩ := pencil
  let f : Fin 3 → F[X] := ![0,P,Q]
  obtain ⟨raw,counts,pairs⟩ := QuarterSuccessorSplitPencil.split_fiber_data dom hn P Q hp hq hr cop
  change ∀ x i j, (f i).eval (dom x) = (f j).eval (dom x) ↔ coincide (raw x) i j at pairs
  obtain ⟨col, hf, hc⟩ := refine_fibers raw 268435454 0 2 268435456 counts
  have no_three (x : I) : col x ≠ 3 := by
    intro bad
    have he := hc 3
    have hp := card_pos.mpr (show (univ.filter fun y => col y = 3).Nonempty from
      ⟨x, mem_filter.mpr ⟨mem_univ _, bad⟩⟩)
    change _ = 0 at he
    omega
  refine ⟨col, f, hc, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [f,dp,dq]
  · intro x
    have h := (by decide : ∀ c, c = 2 ↔ coincide (coarse c) 1 0) (col x)
    rw [hf] at h
    simpa [f] using h.trans (pairs x 1 0).symm
  · intro x i hi
    apply (pairs x _ _).2
    rw [← hf]
    exact (by decide : ∀ c i, c ∈ coreClasses i → c ≠ 3 → coincide (coarse c) i (owner c))
      _ _ hi (no_three x)
  · intro x hx h
    exact (by decide : ∀ c, c ∈ ordinaryClasses → ¬coincide (coarse c) (miss c) (owner c))
      _ hx (hf x ▸ (pairs x _ _).1 h)
  · intro x hx i j h
    have he := (pairs x i j).1 h
    rw [← hf, hx] at he
    exact (by decide : ∀ i j, coincide (coarse 7) i j → i = j) _ _ he

end ArkLib.ProximityGap.Frontier.SecondPrimeTransverseAllocation
