/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds

/-!
# External-irreducible proximity-prize debt

This module indexes the remaining proximity-prize obligations whose content is another
paper's main theorem, a substantial construction not yet ported into ArkLib, or a
personal-communication result with no formalizable paper text.  These should not be tracked as
ordinary local proof holes.  The intended ArkLib shape is a named `Prop` residual plus a proven
`_of_residuals` reduction that demonstrates exactly how the external theorem would close the
ArkLib-facing statement.

## ABF26 Section 3 list-decoding barriers

* **T3.10: BDG24/AGL23 large-alphabet barrier.**  The local work is to keep the alphabet-size
  extraction and parameter bookkeeping explicit.  The actual barrier theorem remains external;
  see the AGL23 barrier/list-decoding bounds modules for the residualized surface.
* **T3.11: GLMRSW22 random-linear lower bound.**  Closing this in tree requires a probability
  space over random linear codes and the GLMRSW lower-bound argument.  Until that infrastructure is
  ported, the statement should remain a named external residual rather than a `sorry`.
* **T3.4: CZ25 Appendix B.5 subspace-design LD.**  ArkLib has subspace-design and
  capacity-reduction interfaces, but the paper-level design-to-list-decoding theorem is still an
  external theorem.

## GGR11 interleaved-code recursion

`ArkLib.Data.CodingTheory.InterleavedCode` and `ArkLib.ToMathlib.GGR11Interleaved` already separate
the proven Pascal/tree-counting bricks from the remaining Erase-Decode tree-construction theorem.
The honest residual is `InterleavedCode.GGR11.GGR11TreeStructure`, whose content is GGR11
Algorithm 1 and Lemmas 3.3-3.5.  The `GGR11PerWordBound` chain is the correct downstream consumer.

## GHSZ02 Corollary 20

`ArkLib.ToMathlib.GHSZ02Cor20` documents the corrected premise and proves the averaging/counting
bricks.  The remaining external item is `GHSZ02LargeN`, the asymptotic large-prime estimate from
GHSZ02 Corollary 20.  This is not a character-sum dependency and should not be replaced by a broad
finite-field-analysis task.

## ABF26 Section 5 list-decoding / correlated-agreement bridge

`ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA` contains the residualized front doors for
T5.1, T5.2, and T5.4:

* `hPerStack` / bad-count variants for GCXK25 T5.1.
* `hBadLine` for BCHKS25 T5.2.
* `hMain` and `hLoss` for BGKS20 T5.4.

Large in-tree cores already exist for the associated first-moment, second-moment, and bridge
bookkeeping.  The remaining remainders are the cited papers' combinatorial/probabilistic main
arguments.

## CapacityBounds T4.8-L4.19 and T4.16

`ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds` keeps the capacity/lower-bound side as
residualized statements where the missing work is the actual paper-level threshold proof.  The
T4.8-L4.19 lower-bound side currently has multiple admits needed to pin the upper side of `delta*`.
T4.16 is even less closeable in tree: the KK25 input is recorded as personal communication rather
than a paper that can be ported.

This module intentionally introduces no declarations.  Its value is as a stable, searchable import
target for "honest debt" so future issue triage does not reclassify these external walls as small
local Lean tasks.
-/

namespace ProximityGap

/-! The namespace is intentionally empty; see the module docstring. -/

end ProximityGap
