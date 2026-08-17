/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator
import ArkLib.ToMathlib.PartitionRecursion

/-!
# BCIKS20 Appendix A.4 (P1) — order-1 closed form + integrality criterion for
`AlphaGenuineRegularWeightLe` (#138)

This file lands two verified, axiom-clean facts about the order-1 Hensel coefficient.

* `βHensel_one_eq` — the `(A.1)` recursion collapses at `k = 0` (the `i₁=0` partitions of `1` are
  killed by the `(1)∉parts` filter; `i₁=1` is the empty partition of `0`), giving
  `βHensel 1 = − hasseCoeffRepr𝒪(R, 1, 0)`.

* `not_regular_alphaGenuine_one_of_not_dvd` — for monic `H`, **if** `βHensel 1` is not `ξ`-divisible
  in `𝒪`, then no `𝒪`-element embeds to `αGenuine 1` (via the proven lift identity
  `βHensel_lift_identity` and injectivity of `𝒪 ↪ 𝕃`).  An *integrality criterion*.

**NOT a refutation.**  An earlier draft of this file claimed these refute
  `AlphaGenuineRegularWeightLe`
for monic `H` via `H = Y²−s`.  That is **wrong**: `Polynomial.Separable` is `IsCoprime f (derivative
f)` over the coefficient ring `ℚ[X]`, and `Y²−s` has discriminant `4s`, a non-unit, so `Y²−s` is not
`Separable` — it fails `ClaimA2.Hypotheses.separable_evalX`.  More structurally, for any *valid*
(separable) `g = evalX(C x₀) R` one has `IsCoprime(g, g')`, so `mk(g')` is a **unit** in
`𝒪 = F[X][Y]/(H̃')`; for monic `H`, `ξ = mk(g')`, hence **`ξ` is a unit and `ξ ∣ βHensel t` for all
`t`** — so `αGenuine t` is always integral.  The hypothesis of
`not_regular_alphaGenuine_one_of_not_dvd` is therefore unsatisfiable for genuine inputs; the
  criterion
never fires.  Consequently the integrality half of #138 is *free* from separability, and the sole
remaining open content is the weight bound `Λ_𝒪(αGenuine t) ≤ 1` (the Faà-di-Bruno
cancellation-into-weight core).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine
open ArkLib.Nat.Partition

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Closed form of the order-1 Hensel numerator.**  The `(A.1)` recursion collapses at `k = 0`:
the `i₁ = 0` inner sum (partitions of `1`) is killed by the `(1) ∉ parts` filter, and the `i₁ = 1`
inner sum is the single empty partition of `0`, so `βHensel 1 = − hasseCoeffRepr𝒪(R, 1, 0)` — minus
the lift-direction first Hasse coefficient `mk(evalX(C x₀)(∂_u R))`. -/
theorem βHensel_one_eq (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    βHensel H x₀ R hHyp 1 = - hasseCoeffRepr𝒪 H x₀ R 1 0 := by
  classical
  rw [show (1:ℕ) = 0 + 1 from rfl, βHensel_succ H x₀ R hHyp 0,
    Finset.sum_range_succ, Finset.sum_range_one]
  congr 1
  have hcard0 : (Nat.Partition.indiscrete (0:ℕ)).parts = 0 :=
    parts_eq_zero_of_zero _
  have h0 : (Finset.univ.filter
      (fun lam : Nat.Partition (0 + 1 - 0) => (0 + 1) ∉ lam.parts)) = ∅ := by
    simpa using univ_filter_notMem_one_eq_empty
  have h1 : (Finset.univ.filter
      (fun lam : Nat.Partition (0 + 1 - 1) => (0 + 1) ∉ lam.parts))
      = {Nat.Partition.indiscrete 0} := by
    simpa using univ_filter_notMem_zero_eq_singleton_indiscrete (0 + 1)
  rw [h0, h1, Finset.sum_empty, zero_add, Finset.sum_singleton]
  have hpre : prefactor R.natDegree 1 (Nat.Partition.indiscrete (0:ℕ)) = 1 := by
    simp only [prefactor, hcard0, Multiset.toFinset_zero]
    simp [Nat.multinomial]
  have hsig : sigmaLambda (Nat.Partition.indiscrete (0:ℕ)) = 0 := by
    simp only [sigmaLambda, hcard0, Multiset.card_zero]
  rw [partitionProd_zero, B_coeff, hsig, hpre]
  simp [deltaSave]

/-- **Abstract order-1 refutation reduction.**  For monic `H`, if `βHensel 1` is *not*
`ξ`-divisible in `𝒪`, then no `𝒪`-element embeds to `αGenuine 1` — so `AlphaGenuineRegularWeightLe`
fails at order 1, independently of any weight bound.  Uses only the proven lift identity
`βHensel_lift_identity` (given the FaaDiBruno sum-zero residual, automatic for monic `H` via
`restrictedFaaDiBrunoMatch_of_monic`) and injectivity of `𝒪 ↪ 𝕃`. -/
theorem not_regular_alphaGenuine_one_of_not_dvd
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp) (hlc : H.leadingCoeff = 1)
    (hnd : ¬ ∃ a : 𝒪 H, βHensel H x₀ R hHyp 1 = a * ClaimA2.ξ x₀ R H hHyp) :
    ¬ ∃ a : 𝒪 H, embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp 1 := by
  rintro ⟨a, ha⟩
  apply hnd
  refine ⟨a, ?_⟩
  have hHdeg : 0 < H.natDegree := (‹Fact (0 < H.natDegree)›).out
  apply embeddingOf𝒪Into𝕃_injective hHdeg
  have hlift := βHensel_lift_identity H x₀ R hHyp hzero 1
  rw [map_mul, ha, hlift, hlc, map_one, one_pow, mul_one,
    show (2 * 1 - 1 : ℕ) = 1 from rfl, pow_one]

#print axioms βHensel_one_eq
#print axioms not_regular_alphaGenuine_one_of_not_dvd

end BCIKS20.HenselNumerator
