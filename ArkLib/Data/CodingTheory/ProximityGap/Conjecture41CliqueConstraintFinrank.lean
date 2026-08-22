/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Conjecture41CliqueRelationReconstruct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Conjecture 41 clique constraint-space dimension: the `c = 1` finrank numeral

Round 22 (`Conjecture41CliqueRelationReconstruct`) proved the **bijection** between the clique
single-block relation space and the constrained `v`-tuple space: for `u_α = (X−α)·v_α`,

  `∑_α u_α·Λ_{E_α} = 0  ⟺  ∑_α v_α = 0`   (`relation_factor_sum_iff`).

That landed both inclusions of "the Round-20 evaluation pencil is the WHOLE kernel" as an honest
IFF, but left the **finrank numeral** itself -- the docstring-named "routine dimension bookkeeping"
(see `Conjecture41CliqueKernelStructure` §3 docstring `dim = (w+1) + (w−1)(c−1) − …`) -- UNPROVEN at
every codimension.

This file discharges the cleanest instance: the **`c = 1` (constant-`v`) constraint space**. The
constant-`v` relations are parametrised by `{ v : ↥W → F // ∑ v = 0 }`, the kernel of the sum
functional `Σ : (↥W → F) →ₗ[F] F`. We prove

  `finrank F (LinearMap.ker (sumFunctional W)) = W.card − 1 = w`            (`finrank_cliqueSumKer`)

via the dual-space rank-nullity `finrank_ker_add_one_of_ne_zero` (the sum functional is nonzero
whenever `W` is nonempty) together with `Module.finrank_pi`. Composed with `relation_factor_sum_iff`
this pins the `c = 1` instance of the clique relation-module dimension count at exactly `w`,
matching both the `evalSyndrome_family_injective` floor (`dim ≥ w+1` for the full graded module) and
the cliquebij probe's exact `kerdim = w+1` (the `+1` is the unconstrained "free constant" of the
graded module, removed here by the single linear constraint).

PROBE: `scripts/probes/probe_clique_finrank.py` -- exact-ℚ / F_p Gaussian-elimination nullity of the
constraint matrix over `w = 2..6`: single-block `dim = w` (5/5), double-block constant-`v`
`dim = w−1` (5/5). Field-universal (the clique algebra carries no thinness -- this is the
char-independent rank backbone of the §6.1 Conjecture-41 escape clause, NOT a CORE/BGK input).

HONEST SCOPE (rules 1,3,6): this is the `c = 1` numeral ONLY. The full graded `c ≥ 2` dimension
bookkeeping (degree-`< c−1` `v`-tuples) and the degeneracy escape clause's exceptional-prime height
bound (the genuine open §6.1 residual) are UNTOUCHED. NOT a CORE closure; no capacity / beyond-
Johnson / cliff-at-n/2 claim. Pure char-independent linear algebra on the proven Round-22 bijection.
-/

open Polynomial Finset Module

namespace Round22ConstraintFinrank

variable {F : Type*} [Field F]

/-- The **sum functional** on `W`-indexed tuples: `v ↦ ∑_{α∈W} v α`, as an `F`-linear map
`(↥W → F) →ₗ[F] F`. Its kernel is the `c = 1` constraint space `{v : ∑ v = 0}` that
`relation_factor_sum_iff` identifies with the constant-coefficient clique relations. -/
def sumFunctional (W : Finset F) : (↥W → F) →ₗ[F] F :=
  ∑ i : ↥W, LinearMap.proj i

@[simp]
theorem sumFunctional_apply (W : Finset F) (v : ↥W → F) :
    sumFunctional W v = ∑ i : ↥W, v i := by
  simp only [sumFunctional, LinearMap.coe_sum, Finset.sum_apply, LinearMap.proj_apply]

/-- The sum functional is **nonzero** when `W` is nonempty: it sends the indicator of any single
node to `1 ≠ 0`. -/
theorem sumFunctional_ne_zero {W : Finset F} (hW : W.Nonempty) :
    sumFunctional W ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := hW
  intro hzero
  -- evaluate at the indicator e_⟨a,ha⟩ (1 at a, 0 elsewhere): the sum is 1
  have hval : sumFunctional W (Pi.single (⟨a, ha⟩ : ↥W) (1 : F)) = 1 := by
    rw [sumFunctional_apply]
    rw [Finset.sum_eq_single (⟨a, ha⟩ : ↥W)]
    · simp
    · intro b _ hb; exact Pi.single_eq_of_ne hb 1
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hzero] at hval
  simp only [LinearMap.zero_apply] at hval
  exact one_ne_zero hval.symm

/-- **HEADLINE -- the `c = 1` constraint-space finrank numeral.**
`finrank F {v : ↥W → F // ∑ v = 0} = W.card − 1`. The constant-`v` (codimension-one,
single-block) clique relation space has dimension exactly `w = |W| − 1`. Proof: rank-nullity for
the nonzero linear functional `sumFunctional W` (`finrank_ker_add_one_of_ne_zero`), with
`finrank F (↥W → F) = W.card` (`Module.finrank_pi` + `Fintype.card_coe`). -/
theorem finrank_cliqueSumKer {W : Finset F} (hW : W.Nonempty) :
    finrank F (LinearMap.ker (sumFunctional W)) = W.card - 1 := by
  have hambient : finrank F (↥W → F) = W.card := by
    rw [Module.finrank_pi, Fintype.card_coe]
  have hadd : finrank F (LinearMap.ker (sumFunctional W)) + 1 = W.card := by
    rw [Module.Dual.finrank_ker_add_one_of_ne_zero
        (f := sumFunctional W) (sumFunctional_ne_zero hW), hambient]
  omega

/-- **Membership in the constraint kernel is the `∑ v = 0` condition** (the object the Round-22 IFF
`relation_factor_sum_iff` consumes). A tuple `v` lies in `ker (sumFunctional W)` iff `∑ v = 0`
-- i.e. the `w`-dimensional kernel of `finrank_cliqueSumKer` is exactly the constant-`v` constraint
space that `relation_factor_sum_iff` identifies with the single-block clique relation space. This
pins the `c = 1` instance of "the evaluation pencil is the whole kernel" at dimension `w`. -/
theorem mem_cliqueSumKer_iff_sum_eq_zero {W : Finset F} (v : ↥W → F) :
    v ∈ LinearMap.ker (sumFunctional W) ↔ (∑ i : ↥W, v i) = 0 := by
  rw [LinearMap.mem_ker, sumFunctional_apply]

end Round22ConstraintFinrank

#print axioms Round22ConstraintFinrank.sumFunctional_apply
#print axioms Round22ConstraintFinrank.sumFunctional_ne_zero
#print axioms Round22ConstraintFinrank.finrank_cliqueSumKer
#print axioms Round22ConstraintFinrank.mem_cliqueSumKer_iff_sum_eq_zero
