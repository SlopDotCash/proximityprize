/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicWfree
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchMonic

/-!
# BCIKS20 Appendix A.4 — monic W-free all-order interface

`P2MonicWfree.lean` exposes the fixed-order W-free residual target that remains after the
monic hypothesis `H.leadingCoeff = 1` removes every `W`-power obstruction. This file packages
the corresponding all-order predicate and connects it to the existing global P2 residuals.

The hard content is still the pointwise W-free equations themselves: they contain the ξ telescope
and the Faà-di-Bruno combinatorial reindexing. This module only gives future proof bricks a
single global target equivalent to `RestrictedFaaDiBrunoMatch` in the monic setting.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The global all-order W-free residual target: for every order `t`, the partition form equals
the W-free recursion-side form.  Under `H.leadingCoeff = 1`, this is equivalent to the carved
global P2 residual `RestrictedFaaDiBrunoMatch`. -/
def RestrictedFaaDiBrunoWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  ∀ t : ℕ,
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
      restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t

/-- The W-free global predicate is just the collection of all fixed-order W-free equations. -/
theorem restrictedFaaDiBrunoWfreeMatch_iff_forall_at
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp ↔
      ∀ t : ℕ,
        restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
          restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t :=
  Iff.rfl

/-- Project one fixed-order W-free equation from the global W-free predicate. -/
theorem RestrictedFaaDiBrunoWfreeMatch.at
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) (t : ℕ) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
      restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t :=
  hWfree t

/-- Build the global W-free predicate from all fixed-order W-free equations. -/
theorem RestrictedFaaDiBrunoWfreeMatch.of_forallAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hat :
      ∀ t : ℕ,
        restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
          restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t) :
    RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp :=
  hat

/-- Under monic `H`, the carved all-order P2 residual is equivalent to the global W-free target. -/
theorem restrictedFaaDiBrunoMatch_iff_WfreeMatch_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp ↔
      RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp := by
  rw [restrictedFaaDiBrunoMatch_iff_forall_at]
  change (∀ t : ℕ, RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t) ↔
    (∀ t : ℕ,
      restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
        restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t)
  exact forall_congr' fun t =>
    restrictedMatchAt_iff_WfreeForm_of_leadingCoeff_one H x₀ R hHyp t hlc

/-- Build the carved all-order P2 residual from the global W-free target under monic `H`. -/
theorem RestrictedFaaDiBrunoMatch.of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp :=
  (restrictedFaaDiBrunoMatch_iff_WfreeMatch_of_leadingCoeff_one H x₀ R hHyp hlc).2 hWfree

/-- Project the global W-free target from the carved all-order P2 residual under monic `H`. -/
theorem RestrictedFaaDiBrunoWfreeMatch.of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp :=
  (restrictedFaaDiBrunoMatch_iff_WfreeMatch_of_leadingCoeff_one H x₀ R hHyp hlc).1 hmatch

/-- The proved monic carved match supplies the global W-free target directly. -/
theorem RestrictedFaaDiBrunoWfreeMatch.of_monic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp :=
  RestrictedFaaDiBrunoWfreeMatch.of_restrictedMatch H x₀ R hHyp hlc
    (restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc)

/-- The proved monic carved match supplies each fixed W-free equation directly. -/
theorem WfreeForm_eq_of_monic
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hlc : H.leadingCoeff = 1) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
      restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t :=
  (RestrictedFaaDiBrunoWfreeMatch.of_monic H x₀ R hHyp hlc) t

/-- Under monic `H`, the legacy successor-sum P2 residual is equivalent to the global W-free
target. -/
theorem faaDiBrunoSuccSumZero_iff_WfreeMatch_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) :
    FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp ↔
      RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp :=
  (restrictedFaaDiBrunoMatch_iff_faaDiBrunoSuccSumZero H x₀ R hHyp).symm.trans
    (restrictedFaaDiBrunoMatch_iff_WfreeMatch_of_leadingCoeff_one H x₀ R hHyp hlc)

/-- Build the legacy successor-sum P2 residual from the global W-free target under monic `H`. -/
theorem FaaDiBrunoSuccSumZeroResidual.of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) :
    FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp :=
  (faaDiBrunoSuccSumZero_iff_WfreeMatch_of_leadingCoeff_one H x₀ R hHyp hlc).2 hWfree

/-- Project the global W-free target from the legacy successor-sum residual under monic `H`. -/
theorem RestrictedFaaDiBrunoWfreeMatch.of_faaDiBrunoSuccSumZero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp) :
    RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp :=
  (faaDiBrunoSuccSumZero_iff_WfreeMatch_of_leadingCoeff_one H x₀ R hHyp hlc).1 hzero

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoWfreeMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoWfreeMatch_iff_forall_at
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoWfreeMatch.at
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoWfreeMatch.of_forallAt
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoMatch_iff_WfreeMatch_of_leadingCoeff_one
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatch.of_WfreeMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoWfreeMatch.of_restrictedMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoWfreeMatch.of_monic
#print axioms BCIKS20.HenselNumerator.WfreeForm_eq_of_monic
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.faaDiBrunoSuccSumZero_iff_WfreeMatch_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.FaaDiBrunoSuccSumZeroResidual.of_WfreeMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoWfreeMatch.of_faaDiBrunoSuccSumZero
