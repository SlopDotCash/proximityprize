/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24KernelVector

/-!
# [AGL24] display (A.5): kernel vectors force edge-wise agreement (issue #346, brick 23)

The Appendix A proof's central observation, formalized: a kernel vector of the evaluated
reduced intersection matrix (stacked coefficient blocks with the last block zero — the
paper's `f⁽ᵗ⁾ = 0` normalization) makes the block evaluations **agree across every edge**:
`cᵢ⁽ʲ⁾ = cᵢ⁽ʲ'⁾` for all `j, j' ∈ eᵢ`. This is the well-definedness of the paper's `y`
vector, and the bridge from the RIM kernel to the codeword-collapse endgame
(bricks 21 + 22).

* `kernel_gives_edge_agreement` — **display (A.5)**: each non-minimal row's kernel equation,
  evaluated through `RIM_eval_row_dot`, equates the block evaluation at the row's vertex
  with the evaluation at the edge's minimum (the `ju = last` case rides on the zero
  normalization).
-/

open Finset

namespace AGL24

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-- **Display (A.5)**: a kernel vector of the evaluated RIM (in stacked-block form with the
last block zero) forces the block evaluations to agree across every edge. -/
theorem kernel_gives_edge_agreement {t k : ℕ} (e : ι → Finset (Fin (t + 1)))
    (α : ι → F) (g : Fin (t + 1) → Fin k → F)
    (hglast : g (Fin.last t) = 0)
    (hker : ((RIM F e).map (MvPolynomial.eval α)).mulVec
      (fun jm => g jm.1.castSucc jm.2) = 0) :
    ∀ i : ι, ∀ j ∈ e i, ∀ j' ∈ e i, rsEval α g j i = rsEval α g j' i := by
  classical
  -- It suffices to pin every member to the edge minimum.
  suffices hmin : ∀ i : ι, ∀ j (hj : j ∈ e i),
      rsEval α g j i = rsEval α g ((e i).min' ⟨j, hj⟩) i by
    intro i j hj j' hj'
    rw [hmin i j hj, hmin i j' hj']
  intro i ju hju
  by_cases hjumin : ju = (e i).min' ⟨ju, hju⟩
  · rw [← hjumin]
  · -- ju is non-minimal: its row exists, and its kernel equation is the (A.5) identity.
    have hnonmin : ∃ j' ∈ e i, j' < ju := by
      refine ⟨(e i).min' ⟨ju, hju⟩, Finset.min'_mem _ _, ?_⟩
      exact lt_of_le_of_ne (Finset.min'_le _ _ hju) (fun h => hjumin h.symm)
    have hrow := congrFun hker ⟨i, ⟨ju, hju, hnonmin⟩⟩
    rw [show (0 : RIMRowIdx e → F) ⟨i, ⟨ju, hju, hnonmin⟩⟩ = 0 from rfl] at hrow
    -- The row dot in difference form (the last block is zero).
    have hdot := RIM_eval_row_dot (F := F) e α g i ju hju hnonmin
    have hveq : (fun jm : Fin t × Fin k => g jm.1.castSucc jm.2)
        = (fun jm : Fin t × Fin k => g jm.1.castSucc jm.2 - g (Fin.last t) jm.2) := by
      funext jm
      rw [hglast]
      simp
    rw [show ((RIM F e).map (MvPolynomial.eval α)).mulVec
          (fun jm => g jm.1.castSucc jm.2) ⟨i, ⟨ju, hju, hnonmin⟩⟩
        = ∑ jm : Fin t × Fin k,
            (MvPolynomial.eval α) (RIM F e ⟨i, ⟨ju, hju, hnonmin⟩⟩ jm)
              * (g jm.1.castSucc jm.2 - g (Fin.last t) jm.2) from by
      rw [hveq] at hker ⊢
      rfl] at hrow
    rw [hdot] at hrow
    -- Unpack with the zero normalization.
    have hglast' : ∀ m : Fin k, g (Fin.last t) m = 0 := fun m => by rw [hglast]; rfl
    by_cases hjul : ju = Fin.last t
    · -- The row pins the minimum's evaluation to zero; the last block is zero too.
      rw [if_pos hjul] at hrow
      rw [sub_zero] at hrow
      have hminval : rsEval α g ((e i).min' ⟨ju, hju⟩) i = 0 := by
        unfold rsEval
        rw [← hrow]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hglast' m, sub_zero]
        ring
      have hjuval : rsEval α g ju i = 0 := by
        unfold rsEval
        rw [hjul]
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [hglast' m, zero_mul]
      rw [hjuval, hminval]
    · -- The row equates the two evaluations directly.
      rw [if_neg hjul] at hrow
      have : rsEval α g ((e i).min' ⟨ju, hju⟩) i - rsEval α g ju i = 0 := by
        unfold rsEval
        rw [← hrow]
        congr 1
        · refine Finset.sum_congr rfl fun m _ => ?_
          rw [hglast' m, sub_zero]
          ring
        · refine Finset.sum_congr rfl fun m _ => ?_
          rw [hglast' m, sub_zero]
          ring
      have := sub_eq_zero.mp this
      rw [this]

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.kernel_gives_edge_agreement
