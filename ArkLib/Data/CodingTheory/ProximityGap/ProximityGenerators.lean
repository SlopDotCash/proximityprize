/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.Basic

/-!
# Compatibility import

Compatibility import for the former proximity-generator definitions. The canonical definitions live in `ProximityGenerator.Basic`.

Caveat (audit PG-201): `CoreDefinitions.IsMDSGenerator` in `ProximityGenerator.Basic` asks only
that the code spanned by the columns of `M_G` be MDS. It does not require `M_G` to have full
column rank, so a generator that ignores an output coordinate can satisfy it. For example, with
two seeds and two output coordinates over `F₃`, `G(s) = (1, 0)` for both seeds has the MDS
repetition `[2, 1, 2]` column code, yet `v = (0, 1) ≠ 0` has `G(s) ⬝ᵥ v = 0` for every seed.
Read the predicate in this weaker intrinsic-rank sense unless a full-rank hypothesis
`LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ` is added.
-/
