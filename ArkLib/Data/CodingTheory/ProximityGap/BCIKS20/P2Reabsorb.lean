/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2KeystoneReindex

/-!
# BCIKS20 Appendix A.4 — Y-degree reabsorption toward `RestrictedFaaDiBrunoMatch`

This module supplies two small, P2-independent algebraic bridges used in the term-by-term
identification between the **LHS partition form** of `restrictedFaaDiBrunoSum`
(`restrictedFaaDiBrunoSum_eq_partitionForm`, indexed by the Y-degree `i` with a `C(i,|λ|)`
binomial and an `α₀^{i-|λ|}` factor) and the **RHS recursion form**
(`coeff_succ_βHenselAssembled_partitionForm`, packaging the iterated-Hasse coefficient as
`hasseEvalAtRoot` inside `B_coeff`).

* `coeff_zero_βHenselAssembled` — the order-0 coefficient of the assembled series is the base
  root `α₀ = T/W` (so the `α₀^{i-|λ|}` factor on the LHS *is* a power of `T/W`).
* `hasseEvalAtRoot_eq_binomReindex` — the α₀-Taylor identity `hasseEvalAtRoot_eq_taylorSum`,
  reindexed `j = i + m` into the **`C(j,m)·coeff j·(T/W)^{j-m}`** shape that the LHS
  partition-form inner sum (over the Y-degree `j`, at a partition with `|λ| = m` parts) exposes.
  This is the entropy-free reabsorption of the Y-degree sum into the single embedding object
  `hasseEvalAtRoot`.
* `restrictedFaaDiBrunoPartitionZeroPowerSum_eq_hasseEvalAtRoot` — the fixed `t = 0`
  specialization of that reabsorption, reducing the surviving LHS power sum to
  `hasseEvalAtRoot H x₀ R 1 0`.
* `B_coeff_indiscrete_zero_eq_hasseCoeffRepr𝒪` and the order-zero RHS normal forms — the surviving
  recursion numerator is the un-cleared `hasseCoeffRepr𝒪 H x₀ R 1 0`, and `ξ` can be expanded as
  `W^(R.natDegree - 2) * ζ` without cancelling any factors.
* `restrictedMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree` — after the legitimate
  `ζ`/`W` cancellation hypotheses, the fixed order-zero core is exactly the cleared-vs-uncleared
  `hasseEvalAtRoot = embedding(hasseCoeffRepr𝒪) / W^R.natDegree` obstruction.
* `restrictedPartitionMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree` — the same obstruction
  exposed directly at the normalized partition-residual surface.

NO `axiom`/`admit`/`native_decide`/`sorry`. Audited in-file via `#print axioms`.
-/

namespace BCIKS20.HenselNumerator

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Order-0 coefficient of the assembled series is `α₀ = T/W` (PROVEN).**  The `α₀^{i-|λ|}`
factor appearing on the LHS of `RestrictedFaaDiBrunoMatch` (via
`restrictedFaaDiBrunoSum_eq_partitionForm`, where `α₀ := coeff 0 βHenselAssembled`) is therefore a
power of the base root `T/W` — exactly the `(T/W)^i` factor in the α₀-Taylor identity
`hasseEvalAtRoot_eq_taylorSum`. -/
theorem coeff_zero_βHenselAssembled (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)
      = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, βHenselAssembled_constantCoeff]
  rfl

/-- **Y-degree reabsorption: the α₀-Taylor identity in `C(j,m)` binomial form (PROVEN).**
Reindexing `hasseEvalAtRoot_eq_taylorSum` by `j = i + m`:

  `hasseEvalAtRoot i₁ m
     = ∑_{j ∈ {m, …, N+m}} C(j,m) · (lift((Δ_X^{i₁}R)|_{x₀}).coeff j) · (T/W)^{j-m}`,

where `N = natDegreeY (Δ_X^{i₁}(Δ_Y^m R)|_{x₀})`.  This is the exact shape consumed by the LHS
partition-form inner sum (the `C(i,|λ|)·coeff i·α₀^{i-|λ|}` terms with `m = |λ|`): the Y-degree
sum over `j` collapses, term for term, into the single embedding object `hasseEvalAtRoot`. -/
theorem hasseEvalAtRoot_eq_binomReindex (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    hasseEvalAtRoot H x₀ R i1 m
      = ∑ j ∈ (Finset.range ((Bivariate.evalX (Polynomial.C x₀)
              (hasseDerivX i1 (hasseDerivY m R))).natDegree + 1)).map (addRightEmbedding m),
          (j.choose m)
            • (liftToFunctionField (H := H)
                  ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff j)
                * (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
                    ^ (j - m)) := by
  rw [hasseEvalAtRoot_eq_taylorSum, Finset.sum_map]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [addRightEmbedding_apply, Nat.add_sub_cancel]

/-- **Y-degree reabsorption over the `Q`-degree range (PROVEN).**
This is the fixed-range version consumed by the partition-form P2 comparison: over the full
`Q x₀ R H` Y-degree range, all out-of-window binomial terms vanish and the same
`C(j,m) · coeff_j · α₀^(j-m)` sum collapses to `hasseEvalAtRoot`.

It is a theorem-level wrapper around `P2KeystoneReindex.taylorCollapse`, exposed here alongside the
other reabsorption bricks so the remaining cleared-vs-uncleared comparison can cite the exact
`Q`-range form without importing the keystone module directly. -/
theorem hasseEvalAtRoot_eq_QDegreeBinomReindex (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    hasseEvalAtRoot H x₀ R i1 m
      = ∑ j ∈ Finset.range ((Q x₀ R H).natDegree + 1),
          (j.choose m)
            • (liftToFunctionField (H := H)
                  ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff j)
                * (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
                    ^ (j - m)) := by
  rw [← taylorCollapse (H := H) x₀ R i1 m]
  simp [α₀]

/-- **Y-degree reabsorption over a fixed range (PROVEN, char-independent).**  For any range
`{0, …, N}` wide enough to contain the Y-degrees of `Δ_X^{i₁}(Δ_Y^m R)|_{x₀}` (shifted by `m`),

  `hasseEvalAtRoot i₁ m
     = ∑_{j ∈ range (N+1)} C(j,m) · (lift((Δ_X^{i₁}R)|_{x₀}).coeff j) · (T/W)^{j-m}`.

This is exactly the LHS inner sum of `RestrictedFaaDiBrunoMatch`
(`restrictedFaaDiBrunoSum_eq_partitionForm`, at a partition with `m = |λ|` parts, summed over the
Y-degree `j ∈ range (Q.natDegree + 1)`): the whole Y-degree sum collapses, term for term, into the
single embedding object `hasseEvalAtRoot`.  The out-of-window terms vanish char-independently — the
low terms `j < m` by `C(j,m) = 0`, the high terms `j - m > deg` because
`C(j,m) • coeff_j = (Δ_Y^m object).coeff (j-m)` (the binomial sits *inside* the Hasse coefficient
via `evalX_hasseDeriv_Y_coeff`) which is `0` past the degree. -/
theorem hasseEvalAtRoot_eq_fixedRange (x₀ : F) (R : F[X][X][Y]) (i1 m N : ℕ)
    (hN : (Bivariate.evalX (Polynomial.C x₀)
            (hasseDerivX i1 (hasseDerivY m R))).natDegree + m ≤ N) :
    hasseEvalAtRoot H x₀ R i1 m
      = ∑ j ∈ Finset.range (N + 1),
          (j.choose m)
            • (liftToFunctionField (H := H)
                  ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff j)
                * (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
                    ^ (j - m)) := by
  rw [hasseEvalAtRoot_eq_binomReindex]
  refine Finset.sum_subset ?_ ?_
  · -- the `binomReindex` window `{m, …, deg + m}` sits inside `range (N+1)`.
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_range] at hi ⊢
    rw [addRightEmbedding_apply]
    omega
  · -- the terms of `range (N+1)` outside the window vanish.
    intro j _ hjnot
    by_cases hjm : j < m
    · rw [Nat.choose_eq_zero_of_lt hjm, zero_smul]
    · have hjm' : m ≤ j := not_lt.mp hjm
      have hgap : (Bivariate.evalX (Polynomial.C x₀)
          (hasseDerivX i1 (hasseDerivY m R))).natDegree < j - m := by
        by_contra h
        rw [Nat.not_lt] at h
        exact hjnot (Finset.mem_map.mpr
          ⟨j - m, Finset.mem_range.mpr (by omega), by rw [addRightEmbedding_apply]; omega⟩)
      have hjmm : j - m + m = j := by omega
      have hcoeff := evalX_hasseDeriv_Y_coeff x₀ R i1 m (j - m)
      rw [hjmm] at hcoeff
      rw [← smul_mul_assoc, ← map_nsmul, ← hcoeff,
        Polynomial.coeff_eq_zero_of_natDegree_lt hgap, map_zero, zero_mul]

/-- **Order-zero LHS reabsorption.**  After the order-zero branch collapse in `P2Assembly`,
the surviving LHS power sum is exactly the cleared root evaluation `hasseEvalAtRoot ... 1 0`. -/
theorem restrictedFaaDiBrunoPartitionZeroPowerSum_eq_hasseEvalAtRoot
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
      hasseEvalAtRoot H x₀ R 1 0 := by
  unfold restrictedFaaDiBrunoPartitionZeroPowerSum
  rw [hasseEvalAtRoot_eq_QDegreeBinomReindex H x₀ R 1 0,
    coeff_zero_βHenselAssembled H x₀ R hHyp]
  simp

/-- At order zero, the normalized partition residual is equivalent to the reabsorbed LHS
`hasseEvalAtRoot` equaling the single surviving RHS `B_coeff` term. -/
theorem restrictedPartitionMatchAt_zero_iff_hasseEvalAtRoot_eq_singleBcoeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      hasseEvalAtRoot H x₀ R 1 0 =
        restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp := by
  rw [restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_singleBcoeff H x₀ R hHyp,
    restrictedFaaDiBrunoPartitionZeroPowerSum_eq_hasseEvalAtRoot H x₀ R hHyp]

/-- Build the fixed order-zero partition residual from the reabsorbed LHS equality. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_hasseEvalAtRoot_eq_singleBcoeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero :
      hasseEvalAtRoot H x₀ R 1 0 =
        restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  (restrictedPartitionMatchAt_zero_iff_hasseEvalAtRoot_eq_singleBcoeff H x₀ R hHyp).2 hzero

/-- Project the reabsorbed LHS equality from the fixed order-zero partition residual. -/
theorem hasseEvalAtRoot_eq_singleBcoeff_of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    hasseEvalAtRoot H x₀ R 1 0 =
      restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp :=
  (restrictedPartitionMatchAt_zero_iff_hasseEvalAtRoot_eq_singleBcoeff H x₀ R hHyp).1 hpart

/-- The carved order-zero P2 core is equivalent to the reabsorbed LHS `hasseEvalAtRoot` equaling
the single surviving RHS `B_coeff` term. -/
theorem restrictedMatchAt_zero_iff_hasseEvalAtRoot_eq_singleBcoeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      hasseEvalAtRoot H x₀ R 1 0 =
        restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp :=
  (restrictedMatchAt_iff_partitionMatchAt H x₀ R hHyp 0).trans
    (restrictedPartitionMatchAt_zero_iff_hasseEvalAtRoot_eq_singleBcoeff H x₀ R hHyp)

/-- Build the carved order-zero P2 core from the reabsorbed LHS equality. -/
theorem RestrictedFaaDiBrunoMatchAt.zero_of_hasseEvalAtRoot_eq_singleBcoeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero :
      hasseEvalAtRoot H x₀ R 1 0 =
        restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 :=
  (restrictedMatchAt_zero_iff_hasseEvalAtRoot_eq_singleBcoeff H x₀ R hHyp).2 hzero

/-- Project the reabsorbed LHS equality from the carved order-zero P2 core. -/
theorem hasseEvalAtRoot_eq_singleBcoeff_of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    hasseEvalAtRoot H x₀ R 1 0 =
      restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp :=
  (restrictedMatchAt_zero_iff_hasseEvalAtRoot_eq_singleBcoeff H x₀ R hHyp).1 hmatch

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- For the empty partition, the surviving `B_coeff` is just the bare un-cleared
iterated-Hasse representative. -/
theorem B_coeff_indiscrete_zero_eq_hasseCoeffRepr𝒪
    (x₀ : F) (R : F[X][X][Y]) :
    B_coeff H x₀ R 1 (Nat.Partition.indiscrete 0)
      = hasseCoeffRepr𝒪 H x₀ R 1 0 := by
  simp [B_coeff, prefactor, sigmaLambda]

/-- The surviving order-zero RHS target with the empty-partition `B_coeff` numerator unfolded. -/
theorem restrictedMatchRecursionPartitionZeroSingleBcoeff_eq_unclearedHasseCoeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp
      = ClaimA2.ζ R x₀ H
        * (embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / ((liftToFunctionField (H := H) H.leadingCoeff) ^ 2
              * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp))) := by
  simp [restrictedMatchRecursionPartitionZeroSingleBcoeff,
    B_coeff_indiscrete_zero_eq_hasseCoeffRepr𝒪]

/-- The surviving order-zero RHS target with both the `B_coeff` numerator and the `ξ`
denominator expanded, without cancelling the `ζ` factor. -/
theorem restrictedMatchRecursionPartitionZeroSingleBcoeff_eq_unclearedHasseCoeff_div_ζ
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp
      = ClaimA2.ζ R x₀ H
        * (embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / ((liftToFunctionField (H := H) H.leadingCoeff) ^ 2
              * ((liftToFunctionField (H := H) H.leadingCoeff) ^ (R.natDegree - 2)
                  * ClaimA2.ζ R x₀ H))) := by
  rw [restrictedMatchRecursionPartitionZeroSingleBcoeff_eq_unclearedHasseCoeff,
    ClaimA2.embeddingOf𝒪Into𝕃_ξ]

/-- If `ζ` is nonzero and `R` has degree at least two, the surviving order-zero RHS target
cancels to the un-cleared Hasse representative divided by `W ^ R.natDegree`. -/
theorem restrictedMatchRecursionPartitionZeroSingleBcoeff_eq_unclearedHasseCoeff_div_W_natDegree
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0) :
    restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp
      = embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree := by
  rw [restrictedMatchRecursionPartitionZeroSingleBcoeff_eq_unclearedHasseCoeff_div_ζ]
  have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hpow :
      (liftToFunctionField (H := H) H.leadingCoeff) ^ 2
        * ((liftToFunctionField (H := H) H.leadingCoeff) ^ (R.natDegree - 2)
          * ClaimA2.ζ R x₀ H)
        =
      (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree
        * ClaimA2.ζ R x₀ H := by
    rw [← mul_assoc, ← pow_add]
    have hnat : 2 + (R.natDegree - 2) = R.natDegree := by omega
    rw [hnat]
  rw [hpow]
  field_simp [hζ, hW]

/-- The canonical single-`B_coeff` RHS target with the empty-partition numerator unfolded. -/
theorem restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp
      = ClaimA2.ζ R x₀ H
        * (embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / ((liftToFunctionField (H := H) H.leadingCoeff) ^ 2
              * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp))) := by
  exact restrictedMatchRecursionPartitionZeroSingleBcoeff_eq_unclearedHasseCoeff H x₀ R hHyp

/-- The canonical single-`B_coeff` RHS target with both the numerator and `ξ` denominator
expanded, without cancelling the `ζ` factor. -/
theorem restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff_div_ζ
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp
      = ClaimA2.ζ R x₀ H
        * (embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / ((liftToFunctionField (H := H) H.leadingCoeff) ^ 2
              * ((liftToFunctionField (H := H) H.leadingCoeff) ^ (R.natDegree - 2)
                  * ClaimA2.ζ R x₀ H))) := by
  rw [restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff,
    ClaimA2.embeddingOf𝒪Into𝕃_ξ]

/-- If `ζ` is nonzero and `R` has degree at least two, the canonical single-`B_coeff` RHS
target cancels to the un-cleared Hasse representative divided by `W ^ R.natDegree`. -/
theorem restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff_div_W_natDegree
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0) :
    restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp
      = embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree := by
  rw [restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff_div_ζ]
  have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hpow :
      (liftToFunctionField (H := H) H.leadingCoeff) ^ 2
        * ((liftToFunctionField (H := H) H.leadingCoeff) ^ (R.natDegree - 2)
          * ClaimA2.ζ R x₀ H)
        =
      (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree
        * ClaimA2.ζ R x₀ H := by
    rw [← mul_assoc, ← pow_add]
    have hnat : 2 + (R.natDegree - 2) = R.natDegree := by omega
    rw [hnat]
  rw [hpow]
  field_simp [hζ, hW]

/-- At order zero, the normalized partition residual is equivalent to the reabsorbed LHS
`hasseEvalAtRoot` equaling the canonical single surviving RHS `B_coeff` term. -/
theorem restrictedPartitionMatchAt_zero_iff_hasseEvalAtRoot_eq_single_B_coeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      hasseEvalAtRoot H x₀ R 1 0 =
        restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp := by
  rw [restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_single_B_coeff H x₀ R hHyp,
    restrictedFaaDiBrunoPartitionZeroPowerSum_eq_hasseEvalAtRoot H x₀ R hHyp]

/-- Build the fixed order-zero partition residual from the canonical reabsorbed LHS equality. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_hasseEvalAtRoot_eq_single_B_coeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero :
      hasseEvalAtRoot H x₀ R 1 0 =
        restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  (restrictedPartitionMatchAt_zero_iff_hasseEvalAtRoot_eq_single_B_coeff H x₀ R hHyp).2 hzero

/-- Project the canonical reabsorbed LHS equality from the fixed order-zero partition residual. -/
theorem hasseEvalAtRoot_eq_single_B_coeff_of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    hasseEvalAtRoot H x₀ R 1 0 =
      restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp :=
  (restrictedPartitionMatchAt_zero_iff_hasseEvalAtRoot_eq_single_B_coeff H x₀ R hHyp).1 hpart

/-- The carved order-zero P2 core is equivalent to the canonical reabsorbed LHS equality. -/
theorem restrictedMatchAt_zero_iff_hasseEvalAtRoot_eq_single_B_coeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      hasseEvalAtRoot H x₀ R 1 0 =
        restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp :=
  (restrictedMatchAt_iff_partitionMatchAt H x₀ R hHyp 0).trans
    (restrictedPartitionMatchAt_zero_iff_hasseEvalAtRoot_eq_single_B_coeff H x₀ R hHyp)

/-- Build the carved order-zero P2 core from the canonical reabsorbed LHS equality. -/
theorem RestrictedFaaDiBrunoMatchAt.zero_of_hasseEvalAtRoot_eq_single_B_coeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero :
      hasseEvalAtRoot H x₀ R 1 0 =
        restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 :=
  (restrictedMatchAt_zero_iff_hasseEvalAtRoot_eq_single_B_coeff H x₀ R hHyp).2 hzero

/-- Project the canonical reabsorbed LHS equality from the carved order-zero P2 core. -/
theorem hasseEvalAtRoot_eq_single_B_coeff_of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    hasseEvalAtRoot H x₀ R 1 0 =
      restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp :=
  (restrictedMatchAt_zero_iff_hasseEvalAtRoot_eq_single_B_coeff H x₀ R hHyp).1 hmatch

/-- Under the legitimate nonzero/degree hypotheses, any carved order-zero match exposes the
cleared-vs-uncleared comparison as the only remaining target. -/
theorem hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    hasseEvalAtRoot H x₀ R 1 0 =
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree := by
  calc
    hasseEvalAtRoot H x₀ R 1 0
        = restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp :=
      hasseEvalAtRoot_eq_single_B_coeff_of_restrictedMatchAt_zero H x₀ R hHyp hmatch
    _ = embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree :=
      restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff_div_W_natDegree
        H x₀ R hHyp hd hζ

/-- The cleared-vs-uncleared equality is enough to build the carved order-zero match once the
canonical RHS has been cancelled under the explicit degree/nonzero hypotheses. -/
theorem RestrictedFaaDiBrunoMatchAt.zero_of_unclearedHasseCoeff_div_W_natDegree
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hzero :
      hasseEvalAtRoot H x₀ R 1 0 =
        embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 := by
  apply RestrictedFaaDiBrunoMatchAt.zero_of_hasseEvalAtRoot_eq_single_B_coeff
  calc
    hasseEvalAtRoot H x₀ R 1 0
        = embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
            / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree := hzero
    _ = restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp :=
      (restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff_div_W_natDegree
        H x₀ R hHyp hd hζ).symm

/-- Fixed order-zero P2 is exactly the isolated cleared-vs-uncleared equality under the explicit
degree/nonzero cancellation hypotheses. -/
theorem restrictedMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      hasseEvalAtRoot H x₀ R 1 0 =
        embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree :=
  ⟨hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_restrictedMatchAt_zero
      H x₀ R hHyp hd hζ,
    RestrictedFaaDiBrunoMatchAt.zero_of_unclearedHasseCoeff_div_W_natDegree
      H x₀ R hHyp hd hζ⟩

/-- Under the legitimate nonzero/degree hypotheses, any normalized partition order-zero match
exposes the un-cleared-over-`W ^ R.natDegree` target. -/
theorem hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    hasseEvalAtRoot H x₀ R 1 0 =
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree :=
  hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_restrictedMatchAt_zero
    H x₀ R hHyp hd hζ
    (RestrictedFaaDiBrunoMatchAt.of_partitionMatchAt H x₀ R hHyp 0 hpart)

/-- The un-cleared-over-`W ^ R.natDegree` target builds the normalized partition order-zero match
under the same explicit cancellation hypotheses. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_unclearedHasseCoeff_div_W_natDegree
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hzero :
      hasseEvalAtRoot H x₀ R 1 0 =
        embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  RestrictedFaaDiBrunoPartitionMatchAt.of_restrictedMatchAt H x₀ R hHyp 0
    (RestrictedFaaDiBrunoMatchAt.zero_of_unclearedHasseCoeff_div_W_natDegree
      H x₀ R hHyp hd hζ hzero)

/-- The normalized partition order-zero P2 residual is exactly the isolated
un-cleared-over-`W ^ R.natDegree` target under the explicit degree/nonzero hypotheses. -/
theorem restrictedPartitionMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      hasseEvalAtRoot H x₀ R 1 0 =
        embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree :=
  ⟨hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_partitionMatchAt_zero
      H x₀ R hHyp hd hζ,
    RestrictedFaaDiBrunoPartitionMatchAt.zero_of_unclearedHasseCoeff_div_W_natDegree
      H x₀ R hHyp hd hζ⟩


end BCIKS20.HenselNumerator

-- Axiom audit.
#print axioms BCIKS20.HenselNumerator.coeff_zero_βHenselAssembled
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_binomReindex
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_QDegreeBinomReindex
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_fixedRange
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoPartitionZeroPowerSum_eq_hasseEvalAtRoot
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedPartitionMatchAt_zero_iff_hasseEvalAtRoot_eq_singleBcoeff
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_hasseEvalAtRoot_eq_singleBcoeff
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_singleBcoeff_of_partitionMatchAt_zero
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_hasseEvalAtRoot_eq_singleBcoeff
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchAt.zero_of_hasseEvalAtRoot_eq_singleBcoeff
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_singleBcoeff_of_restrictedMatchAt_zero
#print axioms BCIKS20.HenselNumerator.B_coeff_indiscrete_zero_eq_hasseCoeffRepr𝒪
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchRecursionPartitionZeroSingleBcoeff_eq_unclearedHasseCoeff
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchRecursionPartitionZeroSingleBcoeff_eq_unclearedHasseCoeff_div_ζ
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchRecursionPartitionZeroSingleBcoeff_eq_unclearedHasseCoeff_div_W_natDegree
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff_div_ζ
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff_div_W_natDegree
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedPartitionMatchAt_zero_iff_hasseEvalAtRoot_eq_single_B_coeff
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_hasseEvalAtRoot_eq_single_B_coeff
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_single_B_coeff_of_partitionMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_hasseEvalAtRoot_eq_single_B_coeff
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchAt.zero_of_hasseEvalAtRoot_eq_single_B_coeff
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_single_B_coeff_of_restrictedMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_restrictedMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchAt.zero_of_unclearedHasseCoeff_div_W_natDegree
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_partitionMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_unclearedHasseCoeff_div_W_natDegree
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedPartitionMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree
