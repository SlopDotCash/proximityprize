/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1BetaOneRefutation

/-!
# BCIKS20 Appendix A.4 (P1) — the integrality half of `AlphaGenuineRegularWeightLe`, PROVEN (#138)

This file proves, axiom-clean, the **integrality half** of the BCIKS20 A.4 weight-1 regularity
predicate (#138): for monic `H`, every genuine Hensel coefficient `αGenuine t` is the embedding of an
`𝒪`-element — i.e. `αGenuine t` is *integral* — with **no weight bound assumed**.

This isolates the genuine open content of #138 to the weight bound alone.  It also explains, in
machine-checked form, why the order-1 refutation criterion of `P1BetaOneRefutation` never fires for
genuine inputs: separability forces `ξ` to be a unit.

## Key steps

* `H_tilde'_eq_self_of_monic` — for monic `H`, the integral monicization `H̃' = H` (`W = 1` collapses
  the clearing sum).
* `ξ_pre_eq_of_monic` — for monic `H`, `ξ_pre = ∂_Y R` specialized at `x₀` (`W = 1` removes the
  clearing).
* `isUnit_ξ_of_monic` — **separability ⟹ `ξ` is a unit in `𝒪`.**  `separable_evalX` is
  `IsCoprime g g'` over the coefficient ring; modulo `H̃' = H`, `g ≡ 0` (as `H ∣ g`), so `mk g' = ξ`
  is a unit.
* `alphaGenuine_regular_of_monic` — dividing the proven lift identity by the unit `ξ^{2t−1}` inside
  `𝒪` exhibits the `𝒪`-preimage of `αGenuine t`.

The `FaaDiBrunoSuccSumZeroResidual` lift-identity hypothesis is carried explicitly (it is discharged
for monic `H` by `faaDiBrunoSuccSumZeroResidual_of_leadingCoeff_one`, kept in a separate module to
avoid coupling this file to the heavier P2 cone).  The remaining open content of #138 is purely the
weight-1 bound `Λ_𝒪(αGenuine t) ≤ 1`.
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- For monic `H`, the integral monicization `H_tilde'` is `H` itself (`W = 1` collapses the
clearing sum). -/
lemma H_tilde'_eq_self_of_monic (hlc : H.leadingCoeff = 1) : H_tilde' H = H := by
  have hHdeg : 0 < H.natDegree := Fact.out
  have hd : H.natDegree ≠ 0 := hHdeg.ne'
  have hW : H.coeff H.natDegree = 1 := hlc
  simp only [H_tilde', if_neg hd]
  have hsum : (∑ i ∈ Finset.range H.natDegree,
        Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) * Polynomial.X ^ i)
      = ∑ i ∈ Finset.range H.natDegree, Polynomial.C (H.coeff i) * Polynomial.X ^ i := by
    apply Finset.sum_congr rfl
    intro i _; rw [hW, one_pow, mul_one]
  rw [hsum]
  conv_rhs => rw [H.as_sum_range' (H.natDegree + 1) (Nat.lt_succ_self _), Finset.sum_range_succ, hW]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_1, one_mul]
  rw [add_comm]

/-- For monic `H`, `ξ_pre` is just `∂_Y R` specialized at `x₀` (`W = 1` removes all clearing). -/
lemma ξ_pre_eq_of_monic (x₀ : F) (R : F[X][X][Y]) (hlc : H.leadingCoeff = 1) :
    ClaimA2.ξ_pre x₀ R H = Bivariate.evalX (Polynomial.C x₀) R.derivative := by
  have hPdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 1 := by
    rw [Bivariate.evalX_eq_map]
    exact Polynomial.natDegree_map_le.trans (Polynomial.natDegree_derivative_le R)
  simp only [ClaimA2.ξ_pre]
  split_ifs with hd
  · conv_rhs => rw [(Bivariate.evalX (Polynomial.C x₀) R.derivative).as_sum_range'
        ((R.natDegree - 1) + 1) (by omega), Finset.sum_range_succ]
    simp only [hlc, one_pow, mul_one, EuclideanDomain.div_one,
      ← Polynomial.C_mul_X_pow_eq_monomial]
  · rfl

/-- **Separability ⟹ `ξ` is a unit in `𝒪` (monic).**  `separable_evalX` is `IsCoprime g g'` over the
coefficient ring; modulo `H̃' = H` (monic), `g ≡ 0` (since `H ∣ g`), so `mk g'` — which is exactly
`ξ` for monic `H` — is a unit. -/
lemma isUnit_ξ_of_monic (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) : IsUnit (ClaimA2.ξ x₀ R H hHyp) := by
  set I : Ideal (F[X][Y]) := Ideal.span {H_tilde' H} with hI
  set g : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R with hg
  have hξ : ClaimA2.ξ x₀ R H hHyp = Ideal.Quotient.mk I (Polynomial.derivative g) := by
    have hrfl : ClaimA2.ξ x₀ R H hHyp = Ideal.Quotient.mk I (ClaimA2.ξ_pre x₀ R H) := rfl
    rw [hrfl, ξ_pre_eq_of_monic H x₀ R hlc, ← ClaimA2.evalX_derivative_comm]
  have hcop : IsCoprime g (Polynomial.derivative g) := by
    have hs := hHyp.separable_evalX
    rwa [Polynomial.separable_def, ← hg] at hs
  obtain ⟨a, b, hab⟩ := hcop
  have hHmem : H ∈ I := by
    rw [hI, Ideal.mem_span_singleton, H_tilde'_eq_self_of_monic H hlc]
  have hmkg : Ideal.Quotient.mk I g = 0 := by
    obtain ⟨q, hq⟩ := hHyp.dvd_evalX
    rw [Ideal.Quotient.eq_zero_iff_mem, hg, hq]
    exact Ideal.mul_mem_right q I hHmem
  have hm : Ideal.Quotient.mk I b * Ideal.Quotient.mk I (Polynomial.derivative g) = 1 := by
    have hc := congrArg (Ideal.Quotient.mk I) hab
    rw [map_add, map_mul, map_mul, map_one, hmkg, mul_zero, zero_add] at hc
    exact hc
  rw [hξ]
  exact IsUnit.of_mul_eq_one_right _ hm

/-- **The integrality half of #138 (monic), PROVEN.**  For monic `H`, every genuine Hensel
coefficient `αGenuine t` is the embedding of an `𝒪`-element — i.e. `αGenuine t` is integral — with no
weight bound assumed.  `ξ` is a unit (`isUnit_ξ_of_monic`), so the lift identity
`embed(βHensel t) = αGenuine t · (embed ξ)^{2t−1}` (monic `W = 1`) divides by the unit `ξ^{2t−1}`
inside `𝒪`.  The *only* remaining open content of #138 is the weight-1 bound `Λ_𝒪(αGenuine t) ≤ 1`. -/
theorem alphaGenuine_regular_of_monic (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (hlc : H.leadingCoeff = 1) (t : ℕ) :
    ∃ a : 𝒪 H, embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp t := by
  obtain ⟨uξ, huξ⟩ := isUnit_ξ_of_monic H x₀ R hHyp hlc
  refine ⟨βHensel H x₀ R hHyp t * (↑uξ⁻¹ : 𝒪 H) ^ (2 * t - 1), ?_⟩
  have hlift := βHensel_lift_identity H x₀ R hHyp hzero t
  rw [map_mul, map_pow, hlift, hlc, map_one, one_pow, mul_one, mul_assoc, ← mul_pow,
    ← huξ, ← map_mul, Units.mul_inv, map_one, one_pow, mul_one]

/-- **The divisibility half of #138 (monic), PROVEN unconditionally.**  For monic `H`, `ξ` is a
unit (`isUnit_ξ_of_monic`), so `ξ^{2t+1}` divides `βHensel (t+1)` in `𝒪 H` for *every* `t`, with the
explicit witness `βHensel (t+1) · (ξ⁻¹)^{2t+1}`.  This is the *divisibility* conjunct of
`SuccDivWeightLe_of_monic` — needing **no lift identity and no degree hypothesis**.  Together with
`P1MonicWeightRefutation.weight_refuted` it isolates the entire remaining open content of #138 to the
*weight* conjunct alone: the clearing always exists; only `Λ_𝒪(quotient) ≤ 1` can fail (and does,
without a `deg R` bound). -/
theorem xi_pow_dvd_βHensel_succ_of_monic (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) (t : ℕ) :
    ∃ a : 𝒪 H, βHensel H x₀ R hHyp (t + 1) = a * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) := by
  obtain ⟨uξ, huξ⟩ := isUnit_ξ_of_monic H x₀ R hHyp hlc
  have hinv : (↑uξ⁻¹ : 𝒪 H) * ClaimA2.ξ x₀ R H hHyp = 1 := by
    rw [← huξ]; exact uξ.inv_mul
  refine ⟨βHensel H x₀ R hHyp (t + 1) * (↑uξ⁻¹ : 𝒪 H) ^ (2 * t + 1), ?_⟩
  have hregroup :
      βHensel H x₀ R hHyp (t + 1) * (↑uξ⁻¹ : 𝒪 H) ^ (2 * t + 1)
          * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1)
        = βHensel H x₀ R hHyp (t + 1)
            * ((↑uξ⁻¹ : 𝒪 H) * ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) := by
    ring
  rw [hregroup, hinv, one_pow, mul_one]

#print axioms isUnit_ξ_of_monic
#print axioms alphaGenuine_regular_of_monic
#print axioms xi_pow_dvd_βHensel_succ_of_monic

end BCIKS20.HenselNumerator
