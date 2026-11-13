/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Fin.Basic

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Tactic.FinCases
import Batteries.Data.Fin.Fold
import CompPoly.Data.Classes.DCast

/-!
  # Lemmas on `Fin` and `Fin`-indexed tuples

  We define operations on `Fin` and `Fin`-indexed tuples that are needed for ArkLib.
-/

universe u v w

-- We may need special naming for these objects `FinTuple` and `FinVec`
-- in order to consolidate a pattern that we find in this development
-- i.e. `ProtocolSpec` is a `FinVec`, `(Full)Transcript` is a `FinTuple`, and so on

namespace Fin

open Function

@[simp]
theorem induction_four {motive : Fin 5 → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin 4, motive i.castSucc → motive i.succ} :
      induction (motive := motive) zero succ (last 4) =
        succ 3 (succ 2 (succ 1 (succ 0 zero))) := rfl

/-- Alternate version of `Fin.induction_four` that uses `4 : Fin 5` instead of `last 4`. -/
@[simp]
theorem induction_four' {motive : Fin 5 → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin 4, motive i.castSucc → motive i.succ} :
      induction (motive := motive) zero succ (4 : Fin 5) =
        succ 3 (succ 2 (succ 1 (succ 0 zero))) := by rfl

section Append

variable {m n : ℕ} {α β : Sort*}

end Append

section Sum

-- Append multiple `Fin` tuples?

/-- Embed a block into the sum by its position, distinguishing repeated block sizes. -/
def castSumAt : (l : List ℕ) → (k : Fin l.length) → Fin (l.get k) → Fin l.sum
  | _ :: l', ⟨0, _⟩, i => castAdd l'.sum i
  | n' :: l', ⟨k + 1, hk⟩, i =>
      natAdd n' (castSumAt l' ⟨k, Nat.succ_lt_succ_iff.mp hk⟩ i)

/-- Dependent elimination for `Fin l.sum`: every index lies in exactly one positional block
`castSumAt l k i`. -/
def sumCases {l : List ℕ} {motive : Fin l.sum → Sort*}
    (cases : ∀ (k : Fin l.length) (i : Fin (l.get k)), motive (castSumAt l k i))
    (i : Fin l.sum) : motive i :=
  match l, motive, cases, i with
  | [], _, _, i => elim0 i
  | n' :: l', motive, cases, i =>
    if hi : i.val < n' then
      have heq : castSumAt (n' :: l') ⟨0, by simp⟩ ⟨i.val, hi⟩ = i := Fin.ext rfl
      heq ▸ cases ⟨0, by simp⟩ ⟨i.val, hi⟩
    else
      have hsum : i.val < n' + l'.sum := by
        have h := i.isLt; simp only [List.sum_cons] at h; exact h
      have hj' : i.val - n' < l'.sum := by omega
      have ih := sumCases (l := l') (motive := fun j => motive (natAdd n' j))
        (fun k j => cases ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ j)
        ⟨i.val - n', hj'⟩
      have heq : natAdd n' (⟨i.val - n', hj'⟩ : Fin l'.sum) = i := by
        apply Fin.ext; simp [natAdd]; omega
      heq ▸ ih

end Sum

section OptionEquivPrime

-- Experimenting with `Fin n` instead of `Fin (n + 1)`, but it seems we'd need to re-define every
-- existing `Fin` functions, which is bad

variable {n : ℕ}

end OptionEquivPrime

end Fin
