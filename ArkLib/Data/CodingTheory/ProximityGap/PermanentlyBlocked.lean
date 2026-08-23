/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Data.CodingTheory.ProximityGap.MuTwoPowDerandRefutation

/-!
# Permanently blocked proximity-prize routes

This module is an ArkLib-side index of routes that should not be revived as ordinary
proof-obligation issues.  Each item below is either mathematically false as stated, refuted by
an in-tree counterexample, or an open research problem rather than a missing Lean proof.

## Capacity-form MCA statements

The capacity-radius MCA target with `BStar = rho` is not a theorem to prove.  The source
comments around `mca_capacity_bound_CONJECTURE` explain the 2025-2026 disproof cascade:
Crites--Stewart, BCHKS/BCKHS, and Diamond--Gruen refute the naive up-to-capacity
correlated-agreement / mutual-correlated-agreement readings.  ArkLib therefore keeps capacity
targets as conjecture-shaped `Prop` data or repaired witness interfaces, never as theorem
stubs carrying `sorry`.

## Smooth-domain AGL24 derandomization

`MuTwoPowDerandRefutation.not_kwpc_rigidity` and
`MuTwoPowDerandRefutation.not_kwpc_rigidity_zmod17` refute the universal
`mu_{2^t}` reduced-intersection-matrix full-rank derandomization route.  The counterexample
is already formalized in ArkLib for `k = 3`, three vertices, and eight geometric coordinates.
The matrix-level form — the explicit 6×6 reduced intersection matrix, its kernel
certificate, and the determinant/rank drop (`rimMatrix_det_eq_zero`, `rimMatrix_rank_lt_six`,
`rimMatrix_rank_drop`, with `ZMod 17` instances; the determinant form lives in
`MuTwoPowDerandRefutation`) — lives in
`ArkLib.Data.CodingTheory.ProximityGap.MuTwoPowDerandRIMRank`.
Future work on the Grand List Decoding value question must account for this evenness /
plus-minus-pair obstruction instead of attempting to prove the false universal RIM statement.

## Grand Challenge predicates

The original real-threshold existence predicates in `GrandChallenges.lean` are intentionally
kept as paper-facing `Prop` definitions.  Their faithful mathematical content lives in the
lattice-threshold and witness modules, where current results bracket the threshold and consume
future Johnson/capacity-side improvements.  The remaining value questions are open research,
not local missing proof bodies.

## Toy-problem up-to-capacity readings

The ToyProblem leaderboard and soundness-bound modules keep their own ABF26 section-6 residuals.
Any reading that would require an up-to-capacity list-decoding or MCA theorem for smooth
Reed--Solomon codes should be treated as blocked by the same capacity disproofs above.  The
closeable work is the repaired Johnson-range / residualized protocol content, not a capacity
theorem with the old statement shape.
-/

namespace ProximityGap

/-! This namespace is intentionally empty.  The module exists as a searchable import target for
blocked-route documentation and imports the formal counterexample modules cited above. -/

end ProximityGap
