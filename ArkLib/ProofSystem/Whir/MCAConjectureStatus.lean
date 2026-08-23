/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# WHIR MCA conjecture status

This module is a greppable audit index for the WHIR mutual-correlated-agreement surfaces in
`ArkLib.ProofSystem.Whir.MutualCorrAgreement`.

## Current `*_CONJECTURE` names

* `MutualCorrAgreement.mca_johnson_bound_CONJECTURE` is the live Johnson-radius target.
  It should stay conjecture-shaped until the ABF26 section-4 chain is fully connected:
  Reed-Solomon Johnson/list-decoding, correlated agreement, MCA, and the WHIR
  `proximityCondition` event.
* `MutualCorrAgreement.mca_capacity_bound_CONJECTURE` records the old capacity-shaped claim.
  It is not a theorem backlog item.  The up-to-capacity correlated-agreement / MCA reading is
  refuted by the 2025-2026 proximity-gap counterexamples, so this name is retained only as a
  historical/refuted `Prop` surface.

## Proven WHIR-side envelope pieces

The following modules are the in-tree envelope around the Johnson target:

* `MCAJohnsonErrStar` and `MCAJohnsonErrStarBounds`: well-definedness, positivity, and basic
  arithmetic bounds for the Johnson `errStar` expression.
* `MCAJohnsonEnvelope`: the conditional comparison between the BCHKS25-style Johnson-regime
  bound and the ABF26 errStar expression, with the multiplicity-domination condition exposed.
* `MCAJohnsonTrivialRegime` and `MCAJohnsonHardRegime`: the `errStar >= 1` part is closed, and
  the remaining mathematical content is isolated to the nontrivial `errStar < 1` regime.
* `MCAJohnsonReduction`: the structural reduction from an `epsMCA` bound to WHIR affine-line MCA.
* `MCAJohnsonMutualExtract`, `MCAJohnsonJointAgreement`, `MCAJohnsonCurveExtract`,
  `MCAJohnsonCurveJoint`, and `MCAJohnsonUniqueness`: local extraction/joint-agreement scaffolding.

## Remaining closure criterion

Closing the Johnson target still requires the external/proximity side of the chain: connect the
Reed-Solomon Johnson-range list-decoding/correlated-agreement theorem to the `epsMCA` bound consumed
by `MCAJohnsonReduction`, then reconcile that event with WHIR's `proximityCondition`.  Until then,
the Johnson declaration must remain a named `Prop` conjecture, not a `theorem` with a hidden admit.

## Audit command

```sh
rg -n 'CONJECTURE|placeholder|sorry|residual' ArkLib/ProofSystem/Whir
```

Expected live hits after the 2026-06 status cleanup are the two explicit
`MutualCorrAgreement.*_CONJECTURE` names, downstream comments documenting MCA-gated WHIR soundness,
and ordinary residual prose.  New theorem-shaped `CONJECTURE` names in WHIR should be treated as
regressions.
-/

namespace Whir

/-! This namespace is intentionally empty; see the module docstring. -/

end Whir
