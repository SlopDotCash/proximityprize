/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# Coding-theory external theorem debt

This module is a repository-level audit index for coding-theory obligations whose remaining
content is a cited paper theorem, a substantial missing formalization stack, or a deliberately
named residual interface.  It complements the proximity-prize-specific index in
`ArkLib.Data.CodingTheory.ProximityGap.ExternalDebt`.

The goal is triage clarity: future issues should distinguish small Lean proof gaps from external
formalization work.  A closeable in-tree task should either prove one of the named residuals from
new formalized mathematics or narrow the residual surface while preserving a proved
`_of_residuals` bridge.

## ListDecoding/Bounds.lean

The ABF26 section-3 theorem family contains several paper-main-theorem residuals:

* **MS77 / ST20 volume and Singleton-style lower bounds.**  Existing helper material handles
  parts of the counting algebra; the remaining work is the puncturing, coset-agreement, and
  pigeonhole core needed by the final theorem statements.
* **BDG24 / AGL23 large-alphabet barrier.**  ArkLib keeps the parameter extraction surfaces
  explicit, but the barrier theorem itself is external.
* **GLMRSW22 random-linear lower bound.**  This requires probability infrastructure for random
  linear codes plus the paper's lower-bound proof.
* **BKR06 extension-field Reed-Solomon lower bound.**  The `ToMathlib/BKR06*` files narrow the
  residuals to family-size, linearizedness, and arithmetic witnesses.
* **GHSZ02 prime-field Reed-Solomon lower bound.**  `ArkLib.ToMathlib.GHSZ02Cor20` reduces the
  remaining external input to `GHSZ02LargeN`.
* **JH01 high-rate Reed-Solomon separation.**  The high-rate construction remains a paper-level
  formalization item.
* **CZ25 subspace-design / capacity list-decoding.**  Local design and capacity-reduction
  interfaces exist, but the appendix-level list-decoding theorem remains external.

## JohnsonBound/Family.lean

`JohnsonBound.Family` contains the paper-shaped Johnson family `J_{q,l}`, `J_q`, and `J` plus
MDS corollaries.  The issue is not just a missing arithmetic simplification: the remaining work is
the port from the already-proven absolute-distance Johnson machinery into ABF26's `Lambda`
interface, including rate/distance and strictness bookkeeping.

## InterleavedCode.lean and GGR11Interleaved.lean

The current ArkLib split is the right one.  The Pascal/tree-counting part is in tree; the external
residual is the GGR11 Erase-Decode tree construction, recorded as
`InterleavedCode.GGR11.GGR11TreeStructure`, and consumed by the `GGR11PerWordBound` chain.

## SubspaceDesign.lean and GK16 support

`SubspaceDesign.lean` proves the ABF26/GK16 folded-RS subspace-design theorem modulo
`CodingTheory.GK16DegreeBudget`.  Supporting modules such as `GK16Structural` and
`GK16Claim16Witness` discharge structural pieces, but the GK16 section-4 degree-budget argument is
still the named external frontier.

## ProximityGap and bridge modules

The proximity-prize residuals are indexed separately in
`ArkLib.Data.CodingTheory.ProximityGap.ExternalDebt`.  In particular, the ABF26 section-5
list-decoding / correlated-agreement bridge should stay split into named residuals such as
`hPerStack`, `hBadLine`, `hMain`, and `hLoss` rather than being treated as anonymous admits.

This file intentionally adds no declarations.  It is an importable, greppable ledger for paper
families and residual names: `EXTERNAL-PAPER`, `GGR11TreeStructure`, `GHSZ02LargeN`,
`GK16DegreeBudget`, `hPerStack`, `hBadLine`, `hMain`, `hLoss`.
-/

namespace CodingTheory

/-! The namespace is intentionally empty; see the module docstring. -/

end CodingTheory
