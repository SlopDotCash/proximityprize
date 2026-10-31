/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.GMMDS.LovettUnconditionalWiring
import ArkLib.Data.CodingTheory.AGL24FrankInterface

/-!
# [AGL24] Theorem 2.11 with Lovett's algebraic core discharged (#389 / r3_thm211)

**Status correction (#389):** the ledger below is *vacuous as stated*. Its GM-MDS premises
`SymbolicMinorFromLovett` (refuted for `1 ≤ k`, `not_symbolicMinorFromLovett`) and
`DualRowsFromNonsingularEval` (refuted for `k < card ι`, `not_dualRowsFromNonsingularEval`, the
12th catch) cannot be supplied, so `symbolicFullRank_lovett_free` is a valid but inapplicable
conditional. The narrative below is retained as the historical design record; the live route is
the pinned capstone `AGL24.symbolicFullRank_of_classical_imports_pinned`.

This file was intended to state the residual ledger for `AGL24.SymbolicFullRankResidual`
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
`FieldLargeForMinor`, **with no Lovett hypothesis**. This is the consolidated,
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
* `hfield : FieldLargeForMinor ι F k` — the Schwartz–Zippel field-size regime.

(The former `hnonempty` premise — "every WPC family has nonempty edges" — was false for every
`k` and has been removed; see `AGL24.symbolicFullRankResidual_of_nonempty_edges`.)

**Vacuous as stated:** `hminor` is refuted for every `1 ≤ k` (`not_symbolicMinorFromLovett`) and
`hdual` for `k < card ι` (`not_dualRowsFromNonsingularEval`), so with `hk : 1 ≤ k` this theorem
can never be applied. It is retained as historical wiring, not as a residual ledger.

Crucially, **there is no `(∀ m, LovettThm17 F m)` premise**: Lovett's Theorem 1.7 is supplied
unconditionally by `lovettThm17_unconditional`. Every remaining premise is a single published
theorem or one of the three named GM-MDS matrix-construction moves. Axiom-clean.

This consolidates the residual ledger: the entire GM-MDS → AGL24 list-decoding lever rests on
**Frank's orientation theorem + the GM-MDS matrix encoding only**. -/
theorem symbolicFullRank_lovett_free {k : ℕ} (hk : 1 ≤ k)
    (hfrank : AGL24.FrankRootedOutCutTheorem (ι := ι) k)
    (hminor : SymbolicMinorFromLovett ι F k)
    (hdual : DualRowsFromNonsingularEval ι F k)
    (hfield : FieldLargeForMinor ι F k) :
    AGL24.SymbolicFullRankResidual (ι := ι) F k := by
  letI : DecidableEq F := Classical.decEq F
  intro t ht e hwpc v hker
  exact AGL24.symbolicFullRank_of_classical_imports (ι := ι) (F := F)
    (AGL24.frankOrientationResidual_of_rootedOutCutTheorem (ι := ι) hfrank)
    (gmmDsResidual_unconditional hk hminor hdual hfield)
    ht e hwpc v hker

end ArkLib.GMMDS

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.GMMDS.symbolicFullRank_lovett_free
