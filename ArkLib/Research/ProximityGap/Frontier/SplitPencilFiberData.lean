/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothFourHeadFibers

/-! # The site classes determined by three split pencil members -/

namespace ArkLib.ProximityGap.Frontier.QuarterSuccessorSplitPencil

open Polynomial Finset SmoothFourHeadFibers

/-- The three full pairwise intersections and the remaining distinct evaluations
of the polynomial heads zero, P and Q. -/
theorem split_fiber_data {I F : Type} [Fintype I] [Field F] [DecidableEq F] (dom : I ↪ F)
    (hn : Fintype.card I = 1073741824) (P Q : F[X])
    (hp : (univ.filter fun x => P.eval (dom x) = 0).card = 268435454)
    (hq : (univ.filter fun x => Q.eval (dom x) = 0).card = 268435454)
    (hr : (univ.filter fun x => P.eval (dom x) = Q.eval (dom x)).card = 268435454)
    (cop : ∀ x, P.eval (dom x) = 0 → Q.eval (dom x) ≠ 0) :
    ∃ raw : I → Fin 4,
      (∀ j, (univ.filter (fun x => raw x = j)).card =
        (![268435454, 268435454, 268435454, 268435462] : Fin 4 → ℕ) j) ∧
      ∀ x i j, ((![0, P, Q] : Fin 3 → F[X]) i).eval (dom x) =
        ((![0, P, Q] : Fin 3 → F[X]) j).eval (dom x) ↔ coincide (raw x) i j := by
  classical
  let raw (x : I) : Fin 4 := if P.eval (dom x) = 0 then 2 else if Q.eval (dom x) = 0 then 1
    else if P.eval (dom x) = Q.eval (dom x) then 0 else 3
  have tab (x : I) : (raw x = 2 ↔ P.eval (dom x) = 0) ∧ (raw x = 1 ↔ Q.eval (dom x) = 0) ∧
      (raw x = 0 ↔ P.eval (dom x) = Q.eval (dom x)) := by
    by_cases p : P.eval (dom x) = 0
    · simp [raw, p, cop x p, Ne.symm (cop x p)]
    by_cases q : Q.eval (dom x) = 0
    · simp [raw, p, q]
    by_cases r : P.eval (dom x) = Q.eval (dom x) <;> simp [raw, p, q, r]
  have c₂ : (univ.filter fun x => raw x = 2).card = 268435454 := by
    simpa only [fun x => (tab x).1] using hp
  have c₁ : (univ.filter fun x => raw x = 1).card = 268435454 := by
    simpa only [fun x => (tab x).2.1] using hq
  have c₀ : (univ.filter fun x => raw x = 0).card = 268435454 := by
    simpa only [fun x => (tab x).2.2] using hr
  have total := sum_card_fiberwise_eq_card_filter (univ : Finset I) (univ : Finset (Fin 4)) raw
  refine ⟨raw, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact c₀
    · exact c₁
    · exact c₂
    · change (univ.filter fun x => raw x = 3).card = 268435462
      have sum : (univ.filter fun x => raw x = 0).card + ((univ.filter fun x => raw x = 1).card +
        ((univ.filter fun x => raw x = 2).card + ((univ.filter fun x => raw x = 3).card + 0))) =
          1073741824 := by simpa [Fin.sum_univ_succ, hn] using total
      rw [c₀, c₁, c₂] at sum
      omega
  · intro x i j
    by_cases p : P.eval (dom x) = 0
    · have q := cop x p
      fin_cases i <;> fin_cases j <;> simp [coincide, raw, p, q, Ne.symm q]
    by_cases q : Q.eval (dom x) = 0
    · fin_cases i <;> fin_cases j <;> simp [coincide, raw, p, q, Ne.symm p]
    by_cases r : P.eval (dom x) = Q.eval (dom x)
    · fin_cases i <;> fin_cases j <;> simp [coincide, raw, q, Ne.symm q, r]
    · fin_cases i <;> fin_cases j <;> simp [coincide, raw, p, q, Ne.symm p, Ne.symm q, r, Ne.symm r]

end ArkLib.ProximityGap.Frontier.QuarterSuccessorSplitPencil
