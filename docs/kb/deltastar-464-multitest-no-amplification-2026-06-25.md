# Issue #464: multi-test tail bounds do not amplify by themselves

Date: 2026-06-25.

Status: **decorrelation guardrail**, not a delta-star proof.

## What Was Formalized

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_MultiTestNoAmplification.lean
```

formalizes a common failure mode in distributional attacks on the #464 floor.

For a finite atom set `alpha` and a finite family of tests `iota`, it defines:

```lean
testTailMass
jointTailMass
```

where `jointTailMass` counts atoms bad for every test.  Lean proves:

```lean
jointTailMass_le_testTailMass
forall_not_joint_of_individualTailMass_bound_lt_inv_card
individual_budget_allows_common_spike
atomScaleGate_for_multiTest_common_bad
```

The exact gate is:

```text
individual bounds for every test rule out a common bad atom
iff the individual budget is already < 1 / #alpha.
```

## Why This Matters

Several tempting routes try to run many certificates at once:

```text
many smoothings,
many projections,
many moments,
many quotient tests,
many local probes.
```

The hope is that the common exceptional set shrinks like a product.  This file records the finite
obstruction: the bad atoms may align.  The aligned singleton model has one atom bad for every test,
so every individual tail has mass `1 / #alpha` and the common tail also has mass `1 / #alpha`.

## Critical Consequence

Multi-test amplification is prize-facing only after a genuine decorrelation or transversality
theorem is proved:

```text
bad sets for different tests cannot align.
```

Without that extra theorem, repeating distributional certificates does not beat the same one-atom
gate already isolated by the vertical-tail, quotient-tail, Wasserstein, and moment guardrails.
