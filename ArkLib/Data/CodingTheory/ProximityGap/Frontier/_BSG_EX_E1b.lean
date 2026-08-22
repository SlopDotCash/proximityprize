/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_DRC1

/-!
# BSG / DRC extraction — sub-lemma E1b (`leftNbhd_subset_e1b`)

The left-neighbourhood `leftNbhd A G b = {a ∈ A | (a,b) ∈ G}` of any right-vertex `b` is a
subset of `A`. This is the containment datum (`A' ⊆ A`) needed for the `BareDRCExtract`
conclusion, where `A' := leftNbhd A G b₀`.

Trivial — `leftNbhd` is a `Finset.filter` of `A`, so `Finset.filter_subset` finishes it.
-/

open Finset

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

omit [AddCommGroup α] in
/-- **E1b — containment.** The left-neighbourhood of any right-vertex `b` is contained in `A`. -/
lemma leftNbhd_subset_e1b (A : Finset α) (G : Finset (α × α)) (b : α) :
    leftNbhd A G b ⊆ A :=
  Finset.filter_subset _ _

end Finset.BSG

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Finset.BSG.leftNbhd_subset_e1b
