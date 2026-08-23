/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Weight1FromZLinear
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicIntegrality
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicConsequences
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.S5Genuine

/-!
# BCIKS20 §5.2.7 — Claim 5.9 (T-form) CLOSED for monic `H` of `Y`-degree `≤ 2` (#302/#138)

This file closes the **in-tree (T-form) Claim 5.9 target** `gammaGenuine_Z_linear_target`
unconditionally for monic `H` with `H.natDegree ≤ 2` — the first unconditional instance of the
target, and the exact regime `ZLinearClosureAudit` FINDING 4 identified as the only one where a
span-local route is type-consistent (`d_H = 2`: the `{1,T}`-line is multiplicatively closed).

## The mechanism (integrality + canonical representative — no recursion needed)

For monic `H`, every genuine Hensel coefficient `αGenuine t` is **integral**: it is the embedding
of an `𝒪`-element (`alphaGenuine_regular_of_monic`, proven via `isUnit_ξ_of_monic` — separability
makes `ξ` a unit of `𝒪 H`, so the lift identity divides inside `𝒪`, never in `𝕃`). When
`H.natDegree ≤ 2`, the canonical `modByMonic` representative of *any* `𝒪`-element has `Y`-degree
`≤ 1`, i.e. is `C c₀ + Y·C c₁` with `c₀, c₁ : F[X]` — exactly the `{1,T}` polynomial span after
embedding. So the Claim 5.9 *shape* is automatic from integrality in the quadratic case; the
recursion-preservation problem (`ZLinearClosureAudit` FINDING 4) never has to be solved.

Consequently, for monic quadratic `H` the **entire remaining content of the #138 weight invariant
is the X-degree budget alone**: `alphaGenuineRegularWeightLe_of_monic_natDegree_two_of_budget`
derives the full `AlphaGenuineRegularWeightLe` from the per-order budget
`deg_X c₀ ≤ 1 ∧ (D+1−d) + deg_X c₁ ≤ 1` on the canonical-representative coefficients, with the
shape/existential component fully discharged. The budget is genuinely open and **cannot** be
dropped: `P1MonicWeightRefutation.weight_refuted` is itself a `d = 2` instance where the shape
holds (`a = mk (Y·C(−X))`, i.e. `c₀ = 0, c₁ = −X`) but the budget fails
(`(D+1−d) + deg c₁ = 2 > 1`), because bare `ClaimA2.Hypotheses` does not bound `deg R`.

## Honest scope

* This closes the **T-form** target only. Per `ZLinearClosureAudit` FINDING 1/2, the paper's
  ground-`Z` reading of Claim 5.9 is a curve-collapse statement (false at fixed `d_H ≥ 2`); the
  T-form target is the rendering consumed by the in-tree weight capstone
  (`Weight1FromZLinear.alphaGenuineRegularWeightLe_of_zLinear_of_degree_bounds`), and that is what
  is closed here.
* For monic `H` with `d_H ≥ 3` the shape residual stays open (and `T² ∉ {1,T}`-span there, so no
  span-local route exists — `functionFieldT_sq_no_T_repr`); for non-unit leading coefficient the
  target is false (`not_gammaGenuine_Z_linear_target_of_not_isUnit_leadingCoeff`).
* All in-tree witness instances (`myH = Y² − 2` over `ZMod 3` with `myR`/`myRG`) are monic
  quadratic, so the closure here is non-vacuously instantiable.

## Main results (axiom-clean: `[propext, Classical.choice, Quot.sound]`)

* `canonicalRepOf𝒪_degree_le_one_of_monic_natDegree_le_two` — canonical reps live below `Y`-deg 2.
* `mk_canonicalRep_zLinear_of_monic_natDegree_le_two` — every `a : 𝒪 H` is `mk (C c₀ + Y·C c₁)`.
* `embed_zLinear_of_monic_natDegree_le_two` — every regular element of `𝕃 H` is on the
  `{1,T}`-polynomial line (monic, `d ≤ 2`).
* `claim59_zLinear_of_monic_natDegree_le_two` — per-coefficient Claim 5.9 shape at EVERY order.
* `gammaGenuine_Z_linear_target_of_monic_natDegree_le_two` — **Claim 5.9 T-form target closed**
  for monic `d ≤ 2`.
* `alphaGenuineRegularWeightLe_of_monic_natDegree_two_of_budget` — the #138 weight invariant for
  monic quadratic `H` from the X-degree budget alone.
-/

noncomputable section

open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.S5Genuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- For monic `H` of `Y`-degree `≤ 2`, every canonical `𝒪`-representative has `Y`-degree `≤ 1`
(its degree is below `deg H̃' = deg H ≤ 2`). -/
lemma canonicalRepOf𝒪_degree_le_one_of_monic_natDegree_le_two
    (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1) (hd2 : H.natDegree ≤ 2) (a : 𝒪 H) :
    (canonicalRepOf𝒪 hH a).degree ≤ (1 : ℕ) := by
  have hmonic : H.Monic := hlc
  have hne : H ≠ 0 := hmonic.ne_zero
  have hdeg := canonicalRepOf𝒪_degree_lt hH a
  rw [BCIKS20.HenselNumerator.H_tilde'_eq_self_of_monic H hlc] at hdeg
  have h2 : (canonicalRepOf𝒪 hH a).degree < ((2 : ℕ) : WithBot ℕ) := by
    refine lt_of_lt_of_le hdeg ?_
    rw [Polynomial.degree_eq_natDegree hne]
    exact_mod_cast hd2
  rcases hdc : (canonicalRepOf𝒪 hH a).degree with _ | n
  · exact bot_le
  · rw [hdc] at h2
    have hn : n < 2 := WithBot.coe_lt_coe.mp h2
    exact WithBot.coe_le_coe.mpr (Nat.lt_succ_iff.mp hn)

/-- For monic `H` of `Y`-degree `≤ 2`, every `a : 𝒪 H` is `mk (C c₀ + Y·C c₁)` for the canonical
representative's coefficients (the inner `Polynomial.X` is the `Y`-variable of `F[X][Y]`). -/
lemma mk_canonicalRep_zLinear_of_monic_natDegree_le_two
    (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1) (hd2 : H.natDegree ≤ 2) (a : 𝒪 H) :
    (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        (Polynomial.C ((canonicalRepOf𝒪 hH a).coeff 0)
          + Polynomial.X * Polynomial.C ((canonicalRepOf𝒪 hH a).coeff 1)) : 𝒪 H) = a := by
  have h1 : (canonicalRepOf𝒪 hH a).degree ≤ (1 : ℕ) :=
    canonicalRepOf𝒪_degree_le_one_of_monic_natDegree_le_two H hH hlc hd2 a
  have hp : canonicalRepOf𝒪 hH a
      = Polynomial.C ((canonicalRepOf𝒪 hH a).coeff 1) * Polynomial.X
        + Polynomial.C ((canonicalRepOf𝒪 hH a).coeff 0) := by
    exact_mod_cast Polynomial.eq_X_add_C_of_degree_le_one (by exact_mod_cast h1)
  have key : Polynomial.C ((canonicalRepOf𝒪 hH a).coeff 0)
      + Polynomial.X * Polynomial.C ((canonicalRepOf𝒪 hH a).coeff 1)
        = canonicalRepOf𝒪 hH a := by
    conv_rhs => rw [hp]
    ring
  rw [key]
  exact mk_canonicalRepOf𝒪 hH a

/-- **Shape: for monic `H` of `Y`-degree `≤ 2`, EVERY regular (integral) element of `𝕃 H` lies on
the `{1, T}`-line with polynomial coefficients** — the canonical-representative coefficients. -/
theorem embed_zLinear_of_monic_natDegree_le_two
    (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1) (hd2 : H.natDegree ≤ 2) (a : 𝒪 H) :
    embeddingOf𝒪Into𝕃 H a
      = liftToFunctionField (H := H) ((canonicalRepOf𝒪 hH a).coeff 0)
        + functionFieldT (H := H)
            * liftToFunctionField (H := H) ((canonicalRepOf𝒪 hH a).coeff 1) := by
  rw [AlphaWeight.liftToFunctionField_add_T_mul_eq_embed,
    mk_canonicalRep_zLinear_of_monic_natDegree_le_two H hH hlc hd2 a]

/-- **Claim 5.9 per-coefficient Z-linearity (T-form) at EVERY order, for monic `H` of `Y`-degree
`≤ 2`.** The shape half of the §5.2.7 successor residual is automatic from integrality
(`alphaGenuine_regular_of_monic`) in the quadratic case — no recursion-preservation argument and
no geometric input is needed for the *shape*; only the X-degree budget remains geometric. -/
theorem claim59_zLinear_of_monic_natDegree_le_two {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    (hlc : H.leadingCoeff = 1) (hd2 : H.natDegree ≤ 2) (t : ℕ) :
    ∃ c₀ c₁ : F[X], αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H) c₀
        + functionFieldT (H := H) * liftToFunctionField (H := H) c₁ := by
  obtain ⟨a, ha⟩ := alphaGenuine_regular_of_monic H x₀ R hHyp
    (faaDiBrunoSuccSumZeroResidual_of_leadingCoeff_one H x₀ R hHyp hlc) hlc t
  exact ⟨(canonicalRepOf𝒪 hH a).coeff 0, (canonicalRepOf𝒪 hH a).coeff 1,
    by rw [← ha, embed_zLinear_of_monic_natDegree_le_two H hH hlc hd2 a]⟩

/-- **Claim 5.9 (T-form target) CLOSED for monic `H` of `Y`-degree `≤ 2`: the first unconditional
instance of `gammaGenuine_Z_linear_target`.** Exactly the regime `ZLinearClosureAudit` FINDING 4
singled out (`d_H = 2` is where the `{1,T}`-line is multiplicatively closed); here it is settled
positively, via integrality rather than recursion-tracking. -/
theorem gammaGenuine_Z_linear_target_of_monic_natDegree_le_two {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    (hlc : H.leadingCoeff = 1) (hd2 : H.natDegree ≤ 2) :
    gammaGenuine_Z_linear_target H x₀ R hHyp :=
  gammaGenuine_Z_linear_of_coeffs_Z_linear H hHyp
    (fun t => claim59_zLinear_of_monic_natDegree_le_two H hHyp hH hlc hd2 t)

/-- **The #138 weight invariant for monic quadratic `H`, from the X-degree budget alone.**
The shape/existential component of `AlphaGenuineRegularWeightLe` is fully discharged; what remains
as hypothesis is exactly the per-order X-degree budget on the canonical-representative
coefficients of the (unique, by `embeddingOf𝒪Into𝕃_injective`) integral preimage of `αGenuine t`.
The budget hypothesis cannot be dropped: `P1MonicWeightRefutation.weight_refuted` is a monic
quadratic instance (valid `ClaimA2.Hypotheses`) where it fails at `t = 1`. -/
theorem alphaGenuineRegularWeightLe_of_monic_natDegree_two_of_budget
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1) (hd2 : H.natDegree = 2) (D : ℕ)
    (hbudget : ∀ t : ℕ, ∀ a : 𝒪 H, embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t →
      ((canonicalRepOf𝒪 hH a).coeff 0).natDegree ≤ 1
        ∧ (D + 1 - Bivariate.natDegreeY H) + ((canonicalRepOf𝒪 hH a).coeff 1).natDegree ≤ 1) :
    AlphaWeight.AlphaGenuineRegularWeightLe H x₀ R hHyp hH D := by
  intro t
  obtain ⟨a, ha⟩ := alphaGenuine_regular_of_monic H x₀ R hHyp
    (faaDiBrunoSuccSumZeroResidual_of_leadingCoeff_one H x₀ R hHyp hlc) hlc t
  obtain ⟨hb0, hb1⟩ := hbudget t a ha
  refine ⟨a, ha, ?_⟩
  rw [← mk_canonicalRep_zLinear_of_monic_natDegree_le_two H hH hlc (le_of_eq hd2) a]
  exact weight_Λ_over_𝒪_zLinear_le_one hH (le_of_eq hd2.symm)
    ((canonicalRepOf𝒪 hH a).coeff 0) ((canonicalRepOf𝒪 hH a).coeff 1) D hb0 hb1

end BCIKS20.HenselNumerator.S5Genuine

section AxiomAudit
#print axioms
  BCIKS20.HenselNumerator.S5Genuine.canonicalRepOf𝒪_degree_le_one_of_monic_natDegree_le_two
#print axioms
  BCIKS20.HenselNumerator.S5Genuine.mk_canonicalRep_zLinear_of_monic_natDegree_le_two
#print axioms BCIKS20.HenselNumerator.S5Genuine.embed_zLinear_of_monic_natDegree_le_two
#print axioms BCIKS20.HenselNumerator.S5Genuine.claim59_zLinear_of_monic_natDegree_le_two
#print axioms
  BCIKS20.HenselNumerator.S5Genuine.gammaGenuine_Z_linear_target_of_monic_natDegree_le_two
#print axioms
  BCIKS20.HenselNumerator.S5Genuine.alphaGenuineRegularWeightLe_of_monic_natDegree_two_of_budget
end AxiomAudit
