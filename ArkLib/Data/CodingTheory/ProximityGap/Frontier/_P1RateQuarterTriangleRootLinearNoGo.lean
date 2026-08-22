/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.DegreeLTDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Three-pencil pair-root constraints are linearly underdetermined

For three pencil parameters, choose two independent differences `f,g`; the
third is `f+g`.  Prescribing root blocks for all three is a homogeneous linear
map from two degree-`<k` polynomial spaces to one scalar equation per root.
Whenever the three root-block cardinalities total less than `2k`, rank-nullity
produces a nonzero solution for every evaluation domain.  At P1 the natural
three pair-overlap floors leave more than two hundred million dimensions.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000

open Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterTriangleRootLinearNoGo

/-- The homogeneous evaluation constraints `f|A=0`, `g|B=0`, and
`(f+g)|C=0`. -/
noncomputable def triangleRootConstraintMap
    {X F : Type} [DecidableEq X] [Field F]
    (domain : X → F) (A B C : Finset X) (k : Nat) :
    (Polynomial.degreeLT F k × Polynomial.degreeLT F k) →ₗ[F]
      ((A → F) × (B → F) × (C → F)) where
  toFun z :=
    (fun i => z.1.1.eval (domain i.1),
      fun i => z.2.1.eval (domain i.1),
      fun i => (z.1.1 + z.2.1).eval (domain i.1))
  map_add' z w := by
    ext i <;> simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      eval_add, Pi.add_apply] <;> ring
  map_smul' c z := by
    ext i <;> simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul,
      eval_smul, eval_add, Pi.smul_apply, RingHom.id_apply] <;> ring

/-- The constraint codomain has one dimension per requested root. -/
theorem triangleRootConstraint_codomain_finrank
    {X F : Type} [DecidableEq X] [Field F]
    (A B C : Finset X) :
    Module.finrank F ((A → F) × (B → F) × (C → F)) =
      A.card + B.card + C.card := by
  simp [add_assoc]

/-- The two independent degree-`<k` polynomials supply exactly `2k`
coefficients. -/
theorem triangleRootConstraint_domain_finrank
    {F : Type} [Field F] (k : Nat) :
    Module.finrank F
      (Polynomial.degreeLT F k × Polynomial.degreeLT F k) = 2 * k := by
  let e := Polynomial.degreeLTEquiv F k
  letI : FiniteDimensional F (Polynomial.degreeLT F k) :=
    LinearEquiv.finiteDimensional e.symm
  rw [Module.finrank_prod, Polynomial.finrank_degreeLT]
  omega

/-- **Linear no-go.**  Below `2k` total root constraints there always exists
a nonzero pair of degree-`<k` polynomials satisfying all three blocks. -/
theorem exists_nonzero_threePairRoot_solution
    {X F : Type} [DecidableEq X] [Field F]
    (domain : X → F) (A B C : Finset X) (k : Nat)
    (hcard : A.card + B.card + C.card < 2 * k) :
    ∃ f g : F[X],
      f ∈ Polynomial.degreeLT F k ∧ g ∈ Polynomial.degreeLT F k ∧
      (f ≠ 0 ∨ g ≠ 0) ∧
      (∀ i ∈ A, f.eval (domain i) = 0) ∧
      (∀ i ∈ B, g.eval (domain i) = 0) ∧
      ∀ i ∈ C, (f + g).eval (domain i) = 0 := by
  let L := triangleRootConstraintMap domain A B C k
  let e := Polynomial.degreeLTEquiv F k
  letI : FiniteDimensional F (Polynomial.degreeLT F k) :=
    LinearEquiv.finiteDimensional e.symm
  have hdim : Module.finrank F ((A → F) × (B → F) × (C → F)) <
      Module.finrank F
        (Polynomial.degreeLT F k × Polynomial.degreeLT F k) := by
    rw [triangleRootConstraint_codomain_finrank,
      triangleRootConstraint_domain_finrank]
    exact hcard
  have hker : L.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨z, hzker, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hLzero : L z = 0 := LinearMap.mem_ker.mp hzker
  refine ⟨z.1.1, z.2.1, z.1.2, z.2.2, ?_, ?_, ?_, ?_⟩
  · by_contra hzero
    push_neg at hzero
    apply hz0
    apply Prod.ext <;> apply Subtype.ext
    · exact hzero.1
    · exact hzero.2
  · intro i hi
    have hx := congrArg
      (fun out : (A → F) × (B → F) × (C → F) => out.1 ⟨i, hi⟩) hLzero
    simpa only [L, triangleRootConstraintMap, Pi.zero_apply] using hx
  · intro i hi
    have hx := congrArg
      (fun out : (A → F) × (B → F) × (C → F) => out.2.1 ⟨i, hi⟩) hLzero
    simpa only [L, triangleRootConstraintMap, Pi.zero_apply] using hx
  · intro i hi
    have hx := congrArg
      (fun out : (A → F) × (B → F) × (C → F) => out.2.2 ⟨i, hi⟩) hLzero
    simpa only [L, triangleRootConstraintMap, Pi.zero_apply] using hx

end ArkLib.ProximityGap.Frontier.P1RateQuarterTriangleRootLinearNoGo

open ArkLib.ProximityGap.Frontier.P1RateQuarterTriangleRootLinearNoGo

#print axioms triangleRootConstraint_codomain_finrank
#print axioms triangleRootConstraint_domain_finrank
#print axioms exists_nonzero_threePairRoot_solution
