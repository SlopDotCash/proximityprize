/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeightClearedObstruction
import ArkLib.ResidualAxioms

/-!
# BCIKS20 App-A (P1) — `AlphaGenuineRegularWeightLe` status (issue #138)

**De-fabricated.** This file previously contained
`theorem alphaGenuineRegularWeightLe_holds … := alphaGenuineRegularWeightLe_residual …`, which
"closed" the P1 weight-1 invariant via a fabricated `axiom`. That was unsound: the un-cleared
invariant `AlphaGenuineRegularWeightLe` is **provably false** for non-monic `H`
(`BCIKS20.AlphaWeightClearedObstruction.not_alphaGenuineRegularWeightLe`, axiom-clean), so no honest
proof of it exists. The laundering theorem and the asserting `axiom` are removed.

`alphaGenuineRegularWeightLe_residual` is now a non-asserting `def : Prop` open residual
(`ArkLib.ResidualAxioms`). The genuine, *true* order-0 statement is the **cleared** invariant,
already proven on `main`:
`BCIKS20.HenselNumerator.AlphaWeight.alphaWeight_zero_cleared_fixed` (witness `βHensel 0`,
weight `≤ 1`). Closing all orders is the open #138 P1 obligation.
-/
