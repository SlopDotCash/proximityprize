/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityGap.RSDistinctness
import ArkLib.Data.CodingTheory.ProximityLeaves2

/-! Scratch development of the faithful JH01 list-size separation. -/

namespace CodingTheoryScratch

open scoped NNReal
open ListDecodable Polynomial CodingTheory

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/- ### Step 2: for each point x, an interpolant codeword agreeing with w off x. -/

omit [Fintype F] [DecidableEq F] in
theorem step2 (j : ℕ) (domain : Fin (j + 1) ↪ F) (w : Fin (j + 1) → F) (x : Fin (j + 1)) :
    ∃ c ∈ ReedSolomon.code domain j, (∀ i, i ≠ x → c i = w i) := by
  classical
  set S : Finset (Fin (j + 1)) := Finset.univ.filter (fun i => i ≠ x) with hS
  have hScard : S.card ≤ j := by
    have : S.card = j := by
      rw [hS, Finset.filter_ne']
      simp
    omega
  obtain ⟨c, hc_mem, hc_agree⟩ :=
    ReedSolomon.ReedSolomon_interpolate_through_subset (k := j) domain S hScard w
  refine ⟨c, hc_mem, ?_⟩
  intro i hi
  apply hc_agree
  rw [hS]; simp [hi]

end CodingTheoryScratch
