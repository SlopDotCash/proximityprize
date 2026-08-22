/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.GMMDS.LovettUnconditionalWiring
import ArkLib.Data.CodingTheory.AGL24FrankInterface

/-!
# [AGL24] Theorem 2.11 with Lovett's algebraic core discharged (#389 / r3_thm211)

This file states the **sharpest honest residual ledger** for `AGL24.SymbolicFullRankResidual`
— the consolidated GM-MDS open core (AGL24 Theorem 2.11, the GM-MDS-line full-column-rank
theorem that sits below the whole AGL24 list-decoding tower).

## Where the campaign stands (verified, axiom-clean)

The capstone `AGL24.symbolicFullRank_of_classical_imports` reduces `SymbolicFullRankResidual`
to **two** classical imports: `FrankOrientationResidual` (Frank's orientation theorem A.3) and
`GMMDSResidual` (GM-MDS theorem A.2). Two further developments have since reduced *each* import:

* **Frank side.** `frankOrientationResidual_of_rootedOutCutTheorem` reduces
  `FrankOrientationResidual` to the textbook rooted-out-cut form `FrankRootedOutCutTheorem`.
  The uncrossing engine (`inBorder_submodular`, `cutDeficiency_supermodular_of_deficient`) is
  proven in-tree; the orientation **existence** is the genuine published Frank import.

* **GM-MDS side.** Lovett's Theorem 1.7 (`lovettThm17_unconditional`, the *algebraic
  kernel-merge core* of GM-MDS) is **proven unconditionally in-tree, axiom-clean**. The Lovett
  route therefore reduces `GMMDSResidual` to exactly the GM-MDS *matrix-encoding* moves
  `SymbolicMinorFromLovett ∧ DualRowsFromNonsingularEval ∧ FieldLargeForMinor`
  (`ArkLib.GMMDS.gmmDsResidual_unconditional`), with the Lovett premise eliminated — **not**
  to the refuted bare-`GZPCondition` ring-change transfer `RIMKernelTrivialFromLovett`
  (machine-checked FALSE, the 14th false-residual; see `LovettRIMKernelTrivial.lean`), and
  **not** circularly through `SymbolicFullRankResidual` itself.

## What this file delivers

`symbolicFullRank_lovett_free` — `SymbolicFullRankResidual` from
`FrankRootedOutCutTheorem` ∧ `SymbolicMinorFromLovett` ∧ `DualRowsFromNonsingularEval` ∧
`FieldLargeForMinor` ∧ nonemptiness, **with no Lovett hypothesis**. This is the consolidated,
minimal, non-circular ledger: every premise is either a single published theorem
(Frank's orientation theorem) or one of the three named GM-MDS *matrix-construction* moves;
Lovett's algebraic core no longer appears, because it is discharged in-tree.

So the honest residual after this file is **exactly**:

> Frank's hypergraph orientation theorem (A.3, [20], not in Mathlib)
> ∧ the GM-MDS matrix encoding (A.2, [9] / Lovett §1: the `pFamUnion`-over-`F[a]` ⟹
>   `RIM`-minor-over-`F[X]` correspondence + dual repackaging + field-size regime).

Both are self-contained, published, *non-character-sum* statements. This precisely localizes
the GM-MDS → AGL24 lever to those two imports and certifies that the in-tree Lovett algebra is
not part of the gap.

Issue #389 / r3_thm211.
-/

open Finset

namespace ArkLib.GMMDS

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : Type*} [Field F] [Fintype F]

/-- **[AGL24] Theorem 2.11 with Lovett's algebraic core discharged.**

`AGL24.SymbolicFullRankResidual F k` — the consolidated GM-MDS open core — follows from:

* `hfrank : FrankRootedOutCutTheorem k` — Frank's hypergraph orientation theorem (A.3), the
  single published combinatorial import (its uncrossing engine is in-tree; existence is the
  import);
* `hminor : SymbolicMinorFromLovett ι F k` — the GM-MDS *encoding* move (Lovett's `pFamUnion`
  independence ⟹ a nonzero polynomial `RIM` minor);
* `hdual : DualRowsFromNonsingularEval ι F k` — the GM-MDS *dual repackaging* move (a
  nonsingular evaluated `RIM` minor ⟹ edge-supported dual rows spanning the RS dual);
* `hfield : FieldLargeForMinor ι F k` — the Schwartz–Zippel field-size regime;
* `hnonempty` — the construction's nonemptiness side condition.

Crucially, **there is no `(∀ m, LovettThm17 F m)` premise**: Lovett's Theorem 1.7 is supplied
unconditionally by `lovettThm17_unconditional`. Every remaining premise is a single published
theorem or one of the three named GM-MDS matrix-construction moves. Axiom-clean.

This consolidates the residual ledger: the entire GM-MDS → AGL24 list-decoding lever rests on
**Frank's orientation theorem + the GM-MDS matrix encoding only**. -/
theorem symbolicFullRank_lovett_free {k : ℕ} (hk : 1 ≤ k)
    (hfrank : AGL24.FrankRootedOutCutTheorem (ι := ι) k)
    (hminor : SymbolicMinorFromLovett ι F k)
    (hdual : DualRowsFromNonsingularEval ι F k)
    (hfield : FieldLargeForMinor ι F k)
    (hnonempty : ∀ {t : ℕ}, ∀ e : ι → Finset (Fin (t + 1)),
      AGL24.WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
      ∀ i, (e i).Nonempty) :
    AGL24.SymbolicFullRankResidual (ι := ι) F k := by
  letI : DecidableEq F := Classical.decEq F
  intro t ht e hwpc v hker
  exact AGL24.symbolicFullRank_of_classical_imports (ι := ι) (F := F)
    (AGL24.frankOrientationResidual_of_rootedOutCutTheorem (ι := ι) hfrank)
    (gmmDsResidual_unconditional hk hminor hdual hfield)
    hnonempty ht e hwpc v hker

end ArkLib.GMMDS

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.GMMDS.symbolicFullRank_lovett_free
