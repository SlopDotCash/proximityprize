/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The odd Wick coefficient `(2r-1)‼` (#407)

Minimal recovery of the dependency consumed by `_WickMonotonicityReduction.lean`. That file's
landing commit imported `…Frontier.WickMomentCapability` but the module itself was never committed
to the build manifest (`git add` omitted), leaving the whole-project `lake build` broken: the
consumer is in `ArkLib.lean` while this provider was not. This module restores exactly the one
symbol the consumer uses, `oddWickCoeff`, with the shape forced by its call sites (a `Finset.prod`
of successive odd numbers, with `oddWickCoeff 1 = 1`).

`oddWickCoeff r = ∏_{i<r} (2i+1) = 1·3·5···(2r−1) = (2r−1)‼` is the **odd double factorial** — the
`2r`-th moment of a real Gaussian of variance `1` (the Wick value coefficient). Issue #407.
-/

set_option autoImplicit false

namespace ProximityGap.Frontier.WickMomentCapability

open Finset

/-- The odd double factorial `(2r-1)‼ = 1·3·5···(2r−1)`, written as `∏_{i<r} (2i+1)`.
The `2r`-th moment of a standard real Gaussian; `oddWickCoeff 0 = 1` (empty product),
`oddWickCoeff 1 = 1`, `oddWickCoeff 2 = 3`, `oddWickCoeff 3 = 15`. -/
def oddWickCoeff (r : ℕ) : ℕ := ∏ i ∈ Finset.range r, (2 * i + 1)

end ProximityGap.Frontier.WickMomentCapability
