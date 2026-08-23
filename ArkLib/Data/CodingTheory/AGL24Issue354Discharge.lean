/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.AGL24FrankInterface
import ArkLib.Data.CodingTheory.AGL24GMMDSInterface
import ArkLib.Data.CodingTheory.AGL24ProbDischarge

/-!
# [AGL24] Issue #354 composite discharge boundary

This module wires the non-residual theorem boundaries for the Appendix A algebra into the
two issue #354 residual surfaces:

* `FrankRootedOutCutTheorem` is the standard rooted out-cut form of Frank's theorem.
* `GMMDSDualZeroPatternTheorem` is the copied-row GM-MDS form matching AGL24 Theorem A.2.
* `symbolicFullRank_of_rootedOutCut_and_dualZeroPattern` composes those boundaries into
  the symbolic full-rank interface.
* `rimFailureProb_of_rootedOutCut_and_dualZeroPattern` then applies the already-proved
  Schwartz-Zippel discharge of the RIM probability residual.

The Frank and GM-MDS theorem boundaries are still external mathematical imports, not proved
here. The point of this file is to make the remaining assumptions non-residual and exact, so
the residual ledger no longer stops at intermediate placeholder names.
-/

namespace AGL24

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Field F]

omit [DecidableEq ι] in
/-- The issue #354 symbolic-rank surface from the two narrowed non-residual theorem
boundaries: rooted Frank plus copied-row GM-MDS. -/
theorem symbolicFullRank_of_rootedOutCut_and_dualZeroPattern {k : Nat}
    [Finite F]
    (hfrank : FrankRootedOutCutTheorem (ι := ι) k)
    (hgm : GMMDSDualZeroPatternTheorem (ι := ι) (F := F) k)
    (hnonempty : forall {t : Nat}, forall e : ι -> Finset (Fin (t + 1)),
      WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e ->
      forall i, (e i).Nonempty) :
    SymbolicFullRankResidual (ι := ι) F k := by
  letI : DecidableEq ι := Classical.decEq ι
  letI : DecidableEq F := Classical.decEq F
  letI := Fintype.ofFinite F
  intro t ht e hwpc v hker
  exact symbolicFullRank_of_classical_imports (ι := ι) (F := F)
    (frankOrientationResidual_of_rootedOutCutTheorem (ι := ι) hfrank)
    (gmmDsResidual_of_dualZeroPatternTheorem (ι := ι) (F := F) hgm)
    hnonempty ht e hwpc v hker

/-- The issue #354 RIM probability surface from the same narrowed non-residual theorem
boundaries. The probability estimate itself is `rimFailureProb_of_symbolic`; this theorem
only removes the intermediate residual dependency from downstream accounting. -/
theorem rimFailureProb_of_rootedOutCut_and_dualZeroPattern {k : Nat}
    [Fintype F]
    (hfrank : FrankRootedOutCutTheorem (ι := ι) k)
    (hgm : GMMDSDualZeroPatternTheorem (ι := ι) (F := F) k)
    (hnonempty : forall {t : Nat}, forall e : ι -> Finset (Fin (t + 1)),
      WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e ->
      forall i, (e i).Nonempty)
    {t : Nat} (ht : 1 <= t) (e : ι -> Finset (Fin (t + 1)))
    (hwpc : WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e) :
    RIMFullRankFailureProbResidual (F := F) (k := k)
      (PMF.uniformOfFintype (ι -> F)) e
      ((t * k * (k - 1) : Nat) / (Fintype.card F : ENNReal)) := by
  letI : DecidableEq F := Classical.decEq F
  exact rimFailureProb_of_symbolic
    (symbolicFullRank_of_rootedOutCut_and_dualZeroPattern hfrank hgm hnonempty)
    ht e hwpc

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.symbolicFullRank_of_rootedOutCut_and_dualZeroPattern
#print axioms AGL24.rimFailureProb_of_rootedOutCut_and_dualZeroPattern
