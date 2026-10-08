/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Fin.Basic

/-!
Regression for the duplicate-summand defect documented in upstream ArkLib PR #1297.
The native API indexes blocks by position, so repeated sizes retain distinct embeddings
and dependent elimination reaches the second block.
-/

namespace Fin

theorem castSum_duplicate_blocks_distinct :
    castSum [1, 1] ⟨0, by decide⟩ ⟨0, by decide⟩ ≠
      castSum [1, 1] ⟨1, by decide⟩ ⟨0, by decide⟩ := by
  decide

theorem sumCases_duplicate_second_block :
    sumCases (l := [1, 1]) (motive := fun _ => ℕ) (fun k _ => k.val) ⟨1, by decide⟩ = 1 := by
  rfl

end Fin

#print axioms Fin.castSum_duplicate_blocks_distinct
#print axioms Fin.sumCases_duplicate_second_block
