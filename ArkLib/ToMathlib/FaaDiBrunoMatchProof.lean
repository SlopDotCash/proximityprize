/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchProof

/-!
# BCIKS20 A.4 P2 — `RestrictedFaaDiBrunoMatch` status (issue #139)

**De-fabricated.** This file previously declared an `axiom restrictedFaaDiBrunoMatch_residual`
asserting `RestrictedFaaDiBrunoMatch`, plus a `restrictedFaaDiBrunoMatch_holds` theorem "closing"
it via that axiom. That was unsound: `RestrictedFaaDiBrunoMatch` is **provably false** for
non-monic `H` at order 0 (the un-cleared obstruction; `BCIKS20.AlphaWeightClearedObstruction`).
The asserting `axiom` and the laundering `_holds` are removed.

The honest named residual lives in `P2MatchProof.lean` as the non-asserting
`def BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchResidual : Prop`, threaded through
`P2_closed_of_residual` as an explicit hypothesis. The genuine remaining content is the cleared,
`t ≥ 1` ξ-telescoped Faà-di-Bruno bijection (the monic order-0 W-free pieces are
verified — see the `_nubs_research` workflow lemmas). Closing it is the open #139 obligation.
-/
