/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.Probability.Notation
import ArkLib.Data.CodingTheory.AGL24FrankInterface
import ArkLib.Data.CodingTheory.AGL24GMMDSInterface
import ArkLib.Data.CodingTheory.AGL24ProbDischarge

/-!
# [AGL24] Issue #354 composite discharge boundary

This module wires the non-residual theorem boundaries for the Appendix A algebra into the
two issue #354 residual surfaces:

* `FrankRootedOutCutTheorem` is the standard rooted out-cut form of Frank's theorem.
* `GMMDSDualZeroPatternTheorem` is the (unpinned) copied-row GM-MDS form.
* `symbolicFullRank_of_rootedOutCut_and_dualZeroPattern` composes those boundaries into
  the symbolic full-rank interface.
* `rimFailureProb_of_rootedOutCut_and_dualZeroPattern` then applies the already-proved
  Schwartz-Zippel discharge of the RIM probability residual.

**Status (historical, vacuous in the intended regime).** The GM-MDS hypothesis
`GMMDSDualZeroPatternTheorem` is *not* a faithful published-theorem boundary: it drops the
dimension count and is refuted for every `k < card ι` (`not_gmmDsDualZeroPatternTheorem`,
`AGL24DualZeroPatternPinned.lean`, the 13th false-residual catch, #354/#389). So both theorems
below are valid conditionals whose GM-MDS hypothesis cannot be supplied when `k < card ι`. The
live consumer route is `symbolicFullRank_of_classical_imports_pinned` with the dimension-pinned
`GMMDSDualZeroPatternTheoremPinned` (itself a conditional boundary needing a large enough field).

An earlier version also required the global premise "every WPC family has only nonempty edges",
which is false for every `k` (at `t = 0` the all-empty family is WPC). That premise has been
removed: empty edges are handled by `symbolicFullRankResidual_of_nonempty_edges`. The Frank
boundary remains an external mathematical import, not proved here.
-/

namespace AGL24

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Field F]

omit [DecidableEq ι] in
/-- The issue #354 symbolic-rank surface from rooted Frank plus the (unpinned) copied-row
GM-MDS boundary. Valid conditional; vacuous for `k < card ι` since `hgm` is refuted there
(`not_gmmDsDualZeroPatternTheorem`). -/
theorem symbolicFullRank_of_rootedOutCut_and_dualZeroPattern {k : Nat}
    [Finite F]
    (hfrank : FrankRootedOutCutTheorem (ι := ι) k)
    (hgm : GMMDSDualZeroPatternTheorem (ι := ι) (F := F) k) :
    SymbolicFullRankResidual (ι := ι) F k := by
  letI : DecidableEq ι := Classical.decEq ι
  letI : DecidableEq F := Classical.decEq F
  letI := Fintype.ofFinite F
  intro t ht e hwpc v hker
  exact symbolicFullRank_of_classical_imports (ι := ι) (F := F)
    (frankOrientationResidual_of_rootedOutCutTheorem (ι := ι) hfrank)
    (gmmDsResidual_of_dualZeroPatternTheorem (ι := ι) (F := F) hgm)
    ht e hwpc v hker

/-- The issue #354 RIM probability surface from the same boundaries. The probability estimate
itself is `rimFailureProb_of_symbolic`. Valid conditional; vacuous for `k < card ι` since `hgm`
is refuted there (`not_gmmDsDualZeroPatternTheorem`). -/
theorem rimFailureProb_of_rootedOutCut_and_dualZeroPattern {k : Nat}
    [Fintype F]
    (hfrank : FrankRootedOutCutTheorem (ι := ι) k)
    (hgm : GMMDSDualZeroPatternTheorem (ι := ι) (F := F) k)
    {t : Nat} (ht : 1 <= t) (e : ι -> Finset (Fin (t + 1)))
    (hwpc : WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e) :
    RIMFullRankFailureProbResidual (F := F) (k := k)
      (ProximityPrize.Compatibility.uniformOfFintype (ι -> F)) e
      ((t * k * (k - 1) : Nat) / (Fintype.card F : ENNReal)) := by
  letI : DecidableEq F := Classical.decEq F
  exact rimFailureProb_of_symbolic
    (symbolicFullRank_of_rootedOutCut_and_dualZeroPattern hfrank hgm)
    ht e hwpc

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.symbolicFullRank_of_rootedOutCut_and_dualZeroPattern
#print axioms AGL24.rimFailureProb_of_rootedOutCut_and_dualZeroPattern
