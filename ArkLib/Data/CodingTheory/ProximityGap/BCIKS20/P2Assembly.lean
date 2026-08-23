/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2BijectionApply
import ArkLib.ToMathlib.Polynomial.HasseDerivEval

/-!
# BCIKS20 Appendix A.4 — P2 assembly partition-form frontier (issue #139)

Both sides of the carved core `RestrictedFaaDiBrunoMatch` are now explicit partition sums, all
proven in `P2BijectionApply`:

* LHS — `restrictedFaaDiBrunoSum_eq_partitionForm`;
* RHS — `coeff_succ_βHenselAssembled_partitionForm` / `restrictedMatch_rhs_eq_recursionPartitionForm`
  (`-ζ · coeff(t+1)(βHenselAssembled) = ζ · recSum / den`);
* α₀-Taylor identity — `hasseEvalAtRoot_eq_taylorSum`;
* Y-Hasse commutation — `evalX_hasseDeriv_Y_coeff`.

The genuine combinatorial core of the per-term identification — the order-`k` Hasse-derivative
evaluation `(hasseDeriv k p).eval a = ∑_i C(i,k)·p.coeff i·a^{i-k}` — is proven independently as
`Polynomial.hasseDeriv_eval_eq_sum` (`ArkLib/ToMathlib/Polynomial/HasseDerivEval.lean`).

The remaining P2 obligation is the per-`(i₁,λ)` term-level equality assembling these into
`RestrictedFaaDiBrunoMatch`.  This file names the final partition-form residual and proves it is
equivalent to the carved core, so downstream work can target the exact normalized statement.
See issue #139.
-/

noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **`hasseEvalAtRoot` in LHS partition shape (PROVEN).** Composing the proven
`hasseEvalAtRoot_eq_taylorSum` (`∑_i C(i+m,m)·(lift((Δ_X^{i₁}R)|x₀).coeff(i+m))·(T/W)^i`) with the
`+m` reindex `Polynomial.sum_choose_shift_reindex` gives `hasseEvalAtRoot` directly in the binomial,
`α₀`-shifted shape that appears (per Y-degree `j`) on the LHS of the carved restricted match — the
left-side identification feeding the per-`(i₁,λ)` term equality. -/
theorem hasseEvalAtRoot_eq_partitionShape (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    hasseEvalAtRoot H x₀ R i1 m
      = ∑ j ∈ Finset.range ((Bivariate.evalX (Polynomial.C x₀)
              (hasseDerivX i1 (hasseDerivY m R))).natDegree + m + 1),
          (j.choose m)
            • ((liftToFunctionField (H := H)
                  ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff j))
                * (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
                    ^ (j - m)) := by
  rw [hasseEvalAtRoot_eq_taylorSum]
  exact Polynomial.sum_choose_shift_reindex
    (fun j => liftToFunctionField (H := H)
      ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff j))
    (fun i => (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) ^ i)
    m _

/-- The already-reindexed left side of the carved restricted Faà-di-Bruno match. -/
def restrictedFaaDiBrunoPartitionForm (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
    ∑ ab ∈ Finset.antidiagonal (t + 1),
      (liftToFunctionField (H := H)
          ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
      * ∑ lam ∈ (Finset.univ : Finset (Nat.Partition ab.2)).filter
                  (fun lam => lam.parts.card ≤ i ∧ (t + 1) ∉ lam.parts),
          ((i.choose lam.parts.card) * lam.parts.countPerms)
            • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
                * (lam.parts.map (fun j =>
                    PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)

/-- The already-normalized recursion-side right side of the carved restricted match. -/
def restrictedMatchRecursionPartitionForm (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  let recSum : 𝕃 H :=
    ∑ i1 ∈ Finset.range (t + 2),
      ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                (fun lam => (t + 1) ∉ lam.parts),
        embeddingOf𝒪Into𝕃 H (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
          * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
          * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
          * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
  let den : 𝕃 H :=
    (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
      * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)
  ClaimA2.ζ R x₀ H * (recSum / den)

/-- The final P2 partition-form residual: both sides of `RestrictedFaaDiBrunoMatch` after the
proven Faà-di-Bruno and recursion-side partition normalizations. -/
def RestrictedFaaDiBrunoPartitionMatchAt (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : Prop :=
  restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t
    = restrictedMatchRecursionPartitionForm H x₀ R hHyp t

/-- **Order-zero LHS branch collapse.**  At `t = 0`, the `ab = (0,1)` branch is killed by
the `1 ∉ λ.parts` filter on `Nat.Partition 1`, and the `ab = (1,0)` branch has only the empty
partition.  The left side of the final P2 residual is therefore the single surviving Taylor
power-sum indexed by the `Y`-degree of `Q`. -/
theorem restrictedFaaDiBrunoPartitionForm_zero_eq_powerSum
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp 0 =
      ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        (liftToFunctionField (H := H)
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i))
        * (PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ i := by
  unfold restrictedFaaDiBrunoPartitionForm
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.Nat.sum_antidiagonal_succ]
  simp

/-- The explicit surviving `t = 0` LHS target after the partition branches collapse. -/
def restrictedFaaDiBrunoPartitionZeroPowerSum
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) : 𝕃 H :=
  ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
    (liftToFunctionField (H := H)
        ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i))
    * (PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ i

/-- The order-zero LHS collapse, phrased through the named surviving power-sum target. -/
theorem restrictedFaaDiBrunoPartitionForm_zero_eq_zeroPowerSum
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp 0 =
      restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp := by
  simpa [restrictedFaaDiBrunoPartitionZeroPowerSum] using
    restrictedFaaDiBrunoPartitionForm_zero_eq_powerSum H x₀ R hHyp

/-- The explicit surviving `t = 0` RHS target after the recursion partition branches collapse. -/
def restrictedMatchRecursionPartitionZeroSingleBcoeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) : 𝕃 H :=
  ClaimA2.ζ R x₀ H
    * (embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R 1 (Nat.Partition.indiscrete 0))
      / ((liftToFunctionField (H := H) H.leadingCoeff) ^ 2
          * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)))

/-- The order-zero RHS collapse, phrased through the named surviving single-`B_coeff` target. -/
theorem restrictedMatchRecursionPartitionForm_zero_eq_singleBcoeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedMatchRecursionPartitionForm H x₀ R hHyp 0 =
      restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp := by
  unfold restrictedMatchRecursionPartitionForm restrictedMatchRecursionPartitionZeroSingleBcoeff
  have hrange2 : Finset.range 2 = ({0, 1} : Finset ℕ) := by
    ext n
    simp
    omega
  rw [hrange2]
  have hdefault : (default : Nat.Partition 0) = Nat.Partition.indiscrete 0 :=
    ArkLib.Nat.Partition.eq_indiscrete_zero default
  simp [deltaSave, sigmaLambda, hdefault]

/-- At order zero, the normalized partition residual is exactly the surviving power-sum target
against the recursion-side partition form. -/
theorem restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_recursion
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
        restrictedMatchRecursionPartitionForm H x₀ R hHyp 0 := by
  unfold RestrictedFaaDiBrunoPartitionMatchAt
  rw [restrictedFaaDiBrunoPartitionForm_zero_eq_zeroPowerSum H x₀ R hHyp]

/-- At order zero, the normalized partition residual is exactly the surviving power-sum target
against the single surviving recursion `B_coeff` term. -/
theorem restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_singleBcoeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
        restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp := by
  rw [restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_recursion H x₀ R hHyp,
    restrictedMatchRecursionPartitionForm_zero_eq_singleBcoeff H x₀ R hHyp]

/-- Build the fixed order-zero partition residual from the surviving power-sum equality. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_zeroPowerSum_eq_recursion
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero :
      restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
        restrictedMatchRecursionPartitionForm H x₀ R hHyp 0) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  (restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_recursion H x₀ R hHyp).2 hzero

/-- Project the surviving power-sum equality from the fixed order-zero partition residual. -/
theorem zeroPowerSum_eq_recursion_of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
      restrictedMatchRecursionPartitionForm H x₀ R hHyp 0 :=
  (restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_recursion H x₀ R hHyp).1 hpart

/-- Build the fixed order-zero partition residual from the canonical single-`B_coeff` RHS
equality. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_zeroPowerSum_eq_singleBcoeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero :
      restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
        restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  (restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_singleBcoeff H x₀ R hHyp).2 hzero

/-- Project the canonical single-`B_coeff` RHS equality from the fixed order-zero partition
residual. -/
theorem zeroPowerSum_eq_singleBcoeff_of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
      restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp :=
  (restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_singleBcoeff H x₀ R hHyp).1 hpart

/-- The explicit surviving `t = 0` RHS target after the recursion partition branches collapse:
only `i₁ = 1` and the unique partition of `0` remain. -/
def restrictedMatchRecursionPartitionFormZeroSingleBCoeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) : 𝕃 H :=
  ClaimA2.ζ R x₀ H *
    (embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R 1 (Nat.Partition.indiscrete 0)) /
      ((liftToFunctionField (H := H) H.leadingCoeff) ^ 2 *
        embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)))

/-- **Order-zero RHS branch collapse.**  At `t = 0`, the `i₁ = 0` branch ranges over
partitions of `1` excluding the part `1`, hence vanishes. The `i₁ = 1` branch ranges over the
singleton partition of `0`; its partition product is `1`, `Σλ = 0`, and the powers reduce to the
single `B_coeff` numerator over `leadingCoeff^2 * ξ`. -/
theorem restrictedMatchRecursionPartitionForm_zero_eq_single_B_coeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedMatchRecursionPartitionForm H x₀ R hHyp 0 =
      restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp := by
  unfold restrictedMatchRecursionPartitionForm
  unfold restrictedMatchRecursionPartitionFormZeroSingleBCoeff
  apply congrArg (fun z : 𝕃 H => ClaimA2.ζ R x₀ H * z)
  congr 1
  · simp [Finset.sum_range_succ, ArkLib.Nat.Partition.eq_indiscrete_zero,
      partitionProd_zero, deltaSave, sigmaLambda]
  · norm_num

/-- At order zero, the normalized partition residual is equivalent to the surviving LHS
power-sum equaling the single surviving RHS `B_coeff` term. -/
theorem restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_single_B_coeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
        restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp := by
  rw [restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_recursion H x₀ R hHyp,
    restrictedMatchRecursionPartitionForm_zero_eq_single_B_coeff H x₀ R hHyp]

/-- Build the fixed order-zero partition residual from the single-`B_coeff` RHS equality. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_zeroPowerSum_eq_single_B_coeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero :
      restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
        restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  (restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_single_B_coeff H x₀ R hHyp).2 hzero

/-- Project the single-`B_coeff` RHS equality from the fixed order-zero partition residual. -/
theorem zeroPowerSum_eq_single_B_coeff_of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
      restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp :=
  (restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_single_B_coeff H x₀ R hHyp).1 hpart

/-- The final all-orders P2 partition-form residual.  This is packaged as a family of
single-order residuals so the remaining term-level proof can be attacked order by order. -/
def RestrictedFaaDiBrunoPartitionMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  ∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t

/-- The all-orders partition residual is exactly the family of single-order residuals. -/
theorem restrictedPartitionMatch_iff_forall_at (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp ↔
      ∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t :=
  Iff.rfl

/-- Projection from the all-orders normalized residual to a fixed order. -/
theorem RestrictedFaaDiBrunoPartitionMatch.at
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp) (t : ℕ) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t :=
  hpart t

/-- Assemble the all-orders normalized residual from its single-order family. -/
theorem RestrictedFaaDiBrunoPartitionMatch.of_forallAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hat : ∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) :
    RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp :=
  hat

/-- Restatement of the proven left-side partition normalization using the named form. -/
theorem restrictedFaaDiBrunoSum_eq_restrictedPartitionForm (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoSum H x₀ R hHyp t
      = restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t :=
  restrictedFaaDiBrunoSum_eq_partitionForm H x₀ R hHyp t

/-- Restatement of the proven right-side recursion normalization using the named form. -/
theorem restrictedMatch_rhs_eq_restrictedRecursionPartitionForm
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    - (ClaimA2.ζ R x₀ H
        * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp))
      = restrictedMatchRecursionPartitionForm H x₀ R hHyp t :=
  restrictedMatch_rhs_eq_recursionPartitionForm H x₀ R hHyp t

/-- Fixed-order equivalence between the carved P2 core and the normalized partition residual. -/
theorem restrictedMatchAt_iff_partitionMatchAt (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t ↔
      RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t := by
  constructor
  · intro hmatch
    unfold RestrictedFaaDiBrunoMatchAt at hmatch
    unfold RestrictedFaaDiBrunoPartitionMatchAt
    rw [← restrictedFaaDiBrunoSum_eq_restrictedPartitionForm H x₀ R hHyp t,
      ← restrictedMatch_rhs_eq_restrictedRecursionPartitionForm H x₀ R hHyp t]
    exact hmatch
  · intro hpart
    unfold RestrictedFaaDiBrunoPartitionMatchAt at hpart
    unfold RestrictedFaaDiBrunoMatchAt
    rw [restrictedFaaDiBrunoSum_eq_restrictedPartitionForm H x₀ R hHyp t,
      restrictedMatch_rhs_eq_restrictedRecursionPartitionForm H x₀ R hHyp t]
    exact hpart

/-- Directional adapter from the fixed-order carved core to the fixed-order partition residual. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.of_restrictedMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t :=
  (restrictedMatchAt_iff_partitionMatchAt H x₀ R hHyp t).1 hmatch

/-- Directional adapter from the fixed-order partition residual back to the fixed-order core. -/
theorem RestrictedFaaDiBrunoMatchAt.of_partitionMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t :=
  (restrictedMatchAt_iff_partitionMatchAt H x₀ R hHyp t).2 hpart

/-- The carved order-zero P2 core is equivalent to the surviving power-sum target. -/
theorem restrictedMatchAt_zero_iff_zeroPowerSum_eq_recursion
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
        restrictedMatchRecursionPartitionForm H x₀ R hHyp 0 :=
  (restrictedMatchAt_iff_partitionMatchAt H x₀ R hHyp 0).trans
    (restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_recursion H x₀ R hHyp)

/-- Build the carved order-zero P2 core from the surviving power-sum equality. -/
theorem RestrictedFaaDiBrunoMatchAt.zero_of_zeroPowerSum_eq_recursion
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero :
      restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
        restrictedMatchRecursionPartitionForm H x₀ R hHyp 0) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 :=
  (restrictedMatchAt_zero_iff_zeroPowerSum_eq_recursion H x₀ R hHyp).2 hzero

/-- Project the surviving power-sum equality from the carved order-zero P2 core. -/
theorem zeroPowerSum_eq_recursion_of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
      restrictedMatchRecursionPartitionForm H x₀ R hHyp 0 :=
  (restrictedMatchAt_zero_iff_zeroPowerSum_eq_recursion H x₀ R hHyp).1 hmatch

/-- The carved order-zero P2 core is equivalent to the surviving LHS power-sum equaling the
canonical single surviving RHS `B_coeff` term. -/
theorem restrictedMatchAt_zero_iff_zeroPowerSum_eq_singleBcoeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
        restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp :=
  (restrictedMatchAt_iff_partitionMatchAt H x₀ R hHyp 0).trans
    (restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_singleBcoeff H x₀ R hHyp)

/-- Build the carved order-zero P2 core from the canonical single-`B_coeff` RHS equality. -/
theorem RestrictedFaaDiBrunoMatchAt.zero_of_zeroPowerSum_eq_singleBcoeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero :
      restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
        restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 :=
  (restrictedMatchAt_zero_iff_zeroPowerSum_eq_singleBcoeff H x₀ R hHyp).2 hzero

/-- Project the canonical single-`B_coeff` RHS equality from the carved order-zero P2 core. -/
theorem zeroPowerSum_eq_singleBcoeff_of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
      restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp :=
  (restrictedMatchAt_zero_iff_zeroPowerSum_eq_singleBcoeff H x₀ R hHyp).1 hmatch

/-- The carved order-zero P2 core is equivalent to the surviving LHS power-sum equaling the single
surviving RHS `B_coeff` term. -/
theorem restrictedMatchAt_zero_iff_zeroPowerSum_eq_single_B_coeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
        restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp :=
  (restrictedMatchAt_iff_partitionMatchAt H x₀ R hHyp 0).trans
    (restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_single_B_coeff H x₀ R hHyp)

/-- Build the carved order-zero P2 core from the single-`B_coeff` RHS equality. -/
theorem RestrictedFaaDiBrunoMatchAt.zero_of_zeroPowerSum_eq_single_B_coeff
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero :
      restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
        restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 :=
  (restrictedMatchAt_zero_iff_zeroPowerSum_eq_single_B_coeff H x₀ R hHyp).2 hzero

/-- Project the single-`B_coeff` RHS equality from the carved order-zero P2 core. -/
theorem zeroPowerSum_eq_single_B_coeff_of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    restrictedFaaDiBrunoPartitionZeroPowerSum H x₀ R hHyp =
      restrictedMatchRecursionPartitionFormZeroSingleBCoeff H x₀ R hHyp :=
  (restrictedMatchAt_zero_iff_zeroPowerSum_eq_single_B_coeff H x₀ R hHyp).1 hmatch

/-- Fixed-order truncated-defect cancellation from the partition-form residual. -/
theorem trunc_defect_cancel_assembled_of_partitionMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselTrunc H x₀ R hHyp t) (Q x₀ R H))
      + ClaimA2.ζ R x₀ H * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
        = 0 :=
  trunc_defect_cancel_assembled_at H x₀ R hHyp t
    (RestrictedFaaDiBrunoMatchAt.of_partitionMatchAt H x₀ R hHyp t hpart)

/-- A fixed-order partition residual vanishes the corresponding assembled-root coefficient. -/
theorem coeff_succ_eval_zero_of_partitionMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) :
    PowerSeries.coeff (t + 1)
      (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0 :=
  coeff_succ_eval_of_trunc_defect_cancel H x₀ R hHyp t
    (trunc_defect_cancel_assembled_of_partitionMatchAt H x₀ R hHyp t hpart)

/-- Fixed-order assembled-series coefficient vanishing from the normalized partition residual. -/
theorem coeff_succ_eval_βHenselAssembled_of_partitionMatchAt
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) :
    PowerSeries.coeff (t + 1)
        (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0 :=
  coeff_succ_eval_zero_of_partitionMatchAt H x₀ R hHyp t hpart

/-- Coefficient vanishing from an all-orders family of fixed-order partition residuals. -/
theorem coeff_succ_eval_zero_of_forall_partitionMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hat : ∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) (t : ℕ) :
    PowerSeries.coeff (t + 1)
      (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H)) = 0 :=
  coeff_succ_eval_zero_of_partitionMatchAt H x₀ R hHyp t (hat t)

/-- The fixed-order partition residual family supplies the legacy successor-sum residual. -/
theorem faaDiBrunoSuccSumZeroResidual_of_forall_partitionMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hat : ∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) :
    FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp := by
  intro t
  rw [← coeff_eval_Q_faaDiBruno H x₀ R (βHenselAssembled H x₀ R hHyp) (t + 1)]
  exact coeff_succ_eval_zero_of_forall_partitionMatchAt H x₀ R hHyp hat t

/-- The carved core is equivalent to the final partition-form residual. -/
theorem restrictedMatch_iff_partitionMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp
      ↔ RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp := by
  constructor
  · intro hmatch t
    unfold RestrictedFaaDiBrunoPartitionMatchAt
    rw [← restrictedFaaDiBrunoSum_eq_restrictedPartitionForm H x₀ R hHyp t,
      ← restrictedMatch_rhs_eq_restrictedRecursionPartitionForm H x₀ R hHyp t]
    exact hmatch t
  · intro hpart t
    rw [restrictedFaaDiBrunoSum_eq_restrictedPartitionForm H x₀ R hHyp t,
      restrictedMatch_rhs_eq_restrictedRecursionPartitionForm H x₀ R hHyp t]
    exact hpart t

/-- The carved P2 core is equivalent to proving the final partition-form residual at every fixed
order. This is the direct per-order target surface for the remaining term-level proof. -/
theorem restrictedMatch_iff_forall_partitionMatchAt (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp ↔
      ∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t :=
  (restrictedMatch_iff_partitionMatch H x₀ R hHyp).trans
    (restrictedPartitionMatch_iff_forall_at H x₀ R hHyp)

/-- Directional adapter from the carved restricted match to the normalized partition residual. -/
theorem RestrictedFaaDiBrunoPartitionMatch.of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp :=
  (restrictedMatch_iff_partitionMatch H x₀ R hHyp).1 hmatch

/-- Directional adapter from the normalized partition residual back to the carved core. -/
theorem RestrictedFaaDiBrunoMatch.of_partitionMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp :=
  (restrictedMatch_iff_partitionMatch H x₀ R hHyp).2 hpart

/-- Directional adapter from a fixed-order partition residual family to the carved core. -/
theorem RestrictedFaaDiBrunoMatch.of_forall_partitionMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hat : ∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp :=
  (restrictedMatch_iff_forall_partitionMatchAt H x₀ R hHyp).2 hat

/-- Project fixed-order partition residuals from the carved core. -/
theorem RestrictedFaaDiBrunoMatch.forall_partitionMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    ∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t :=
  (restrictedMatch_iff_forall_partitionMatchAt H x₀ R hHyp).1 hmatch

/-- The normalized partition residual supplies the full P2 vanishing identity. -/
theorem fullVanishes_of_partitionMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp :=
  fullVanishes_of_restrictedMatch H x₀ R hHyp
    (RestrictedFaaDiBrunoMatch.of_partitionMatch H x₀ R hHyp hpart)

/-- The fixed-order partition residual family supplies the full P2 vanishing identity. -/
theorem fullVanishes_of_forall_partitionMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hat : ∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp :=
  fullVanishes_of_partitionMatch H x₀ R hHyp
    (RestrictedFaaDiBrunoPartitionMatch.of_forallAt H x₀ R hHyp hat)

/-- The normalized partition residual supplies the legacy successor-sum residual. -/
theorem faaDiBrunoSuccSumZeroResidual_of_partitionMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp) :
    FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp :=
  faaDiBrunoSuccSumZeroResidual_of_restrictedMatch H x₀ R hHyp
    (RestrictedFaaDiBrunoMatch.of_partitionMatch H x₀ R hHyp hpart)

/-- The normalized partition residual closes the existing conditional P2 endpoint. -/
theorem P2_closed_of_partitionMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  P2_closed_of_restrictedMatch H x₀ R hHyp
    (RestrictedFaaDiBrunoMatch.of_partitionMatch H x₀ R hHyp hpart)

/-- The assembled numerator series is a root of `Q` from the normalized partition residual. -/
theorem assembledSeries_isRoot_of_partitionMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp) :
    Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 :=
  (P2_closed_of_partitionMatch H x₀ R hHyp hpart).1

/-- The repaired P2 lift identity, exposed per order, from the normalized partition residual. -/
theorem βHensel_lift_identity_of_partitionMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = αGenuine H x₀ R hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
  (P2_closed_of_partitionMatch H x₀ R hHyp hpart).2 t

/-- The fixed-order partition residual family closes the existing conditional P2 endpoint. -/
theorem P2_closed_of_forall_partitionMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hat : ∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0)
    ∧ (∀ t : ℕ, embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1)) :=
  P2_closed_of_partitionMatch H x₀ R hHyp
    (RestrictedFaaDiBrunoPartitionMatch.of_forallAt H x₀ R hHyp hat)

/-- The assembled numerator series is a root from fixed-order partition residuals. -/
theorem assembledSeries_isRoot_of_forall_partitionMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hat : ∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) :
    Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0 :=
  (P2_closed_of_forall_partitionMatchAt H x₀ R hHyp hat).1

/-- The repaired P2 lift identity from fixed-order partition residuals. -/
theorem βHensel_lift_identity_of_forall_partitionMatchAt
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hat : ∀ t : ℕ, RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = αGenuine H x₀ R hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) :=
  (P2_closed_of_forall_partitionMatchAt H x₀ R hHyp hat).2 t

-- In-file axiom audit for the named P2 partition residual and its equivalence to the carved core.
section AxiomAudit
#print axioms restrictedFaaDiBrunoPartitionForm
#print axioms restrictedMatchRecursionPartitionForm
#print axioms RestrictedFaaDiBrunoPartitionMatchAt
#print axioms restrictedFaaDiBrunoPartitionForm_zero_eq_powerSum
#print axioms restrictedFaaDiBrunoPartitionZeroPowerSum
#print axioms restrictedFaaDiBrunoPartitionForm_zero_eq_zeroPowerSum
#print axioms restrictedMatchRecursionPartitionZeroSingleBcoeff
#print axioms restrictedMatchRecursionPartitionForm_zero_eq_singleBcoeff
#print axioms restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_recursion
#print axioms restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_singleBcoeff
#print axioms RestrictedFaaDiBrunoPartitionMatchAt.zero_of_zeroPowerSum_eq_recursion
#print axioms zeroPowerSum_eq_recursion_of_partitionMatchAt_zero
#print axioms restrictedMatchAt_zero_iff_zeroPowerSum_eq_recursion
#print axioms RestrictedFaaDiBrunoMatchAt.zero_of_zeroPowerSum_eq_recursion
#print axioms zeroPowerSum_eq_recursion_of_restrictedMatchAt_zero
#print axioms RestrictedFaaDiBrunoPartitionMatchAt.zero_of_zeroPowerSum_eq_singleBcoeff
#print axioms zeroPowerSum_eq_singleBcoeff_of_partitionMatchAt_zero
#print axioms restrictedMatchAt_zero_iff_zeroPowerSum_eq_singleBcoeff
#print axioms RestrictedFaaDiBrunoMatchAt.zero_of_zeroPowerSum_eq_singleBcoeff
#print axioms zeroPowerSum_eq_singleBcoeff_of_restrictedMatchAt_zero
#print axioms restrictedMatchRecursionPartitionFormZeroSingleBCoeff
#print axioms restrictedMatchRecursionPartitionForm_zero_eq_single_B_coeff
#print axioms restrictedPartitionMatchAt_zero_iff_zeroPowerSum_eq_single_B_coeff
#print axioms RestrictedFaaDiBrunoPartitionMatchAt.zero_of_zeroPowerSum_eq_single_B_coeff
#print axioms zeroPowerSum_eq_single_B_coeff_of_partitionMatchAt_zero
#print axioms restrictedMatchAt_zero_iff_zeroPowerSum_eq_single_B_coeff
#print axioms RestrictedFaaDiBrunoMatchAt.zero_of_zeroPowerSum_eq_single_B_coeff
#print axioms zeroPowerSum_eq_single_B_coeff_of_restrictedMatchAt_zero
#print axioms RestrictedFaaDiBrunoPartitionMatch
#print axioms restrictedPartitionMatch_iff_forall_at
#print axioms RestrictedFaaDiBrunoPartitionMatch.at
#print axioms RestrictedFaaDiBrunoPartitionMatch.of_forallAt
#print axioms restrictedFaaDiBrunoSum_eq_restrictedPartitionForm
#print axioms restrictedMatch_rhs_eq_restrictedRecursionPartitionForm
#print axioms restrictedMatchAt_iff_partitionMatchAt
#print axioms RestrictedFaaDiBrunoPartitionMatchAt.of_restrictedMatchAt
#print axioms RestrictedFaaDiBrunoMatchAt.of_partitionMatchAt
#print axioms trunc_defect_cancel_assembled_of_partitionMatchAt
#print axioms coeff_succ_eval_zero_of_partitionMatchAt
#print axioms coeff_succ_eval_βHenselAssembled_of_partitionMatchAt
#print axioms coeff_succ_eval_zero_of_forall_partitionMatchAt
#print axioms faaDiBrunoSuccSumZeroResidual_of_forall_partitionMatchAt
#print axioms P2_closed_of_forall_partitionMatchAt
#print axioms assembledSeries_isRoot_of_forall_partitionMatchAt
#print axioms βHensel_lift_identity_of_forall_partitionMatchAt
#print axioms restrictedMatch_iff_partitionMatch
#print axioms restrictedMatch_iff_forall_partitionMatchAt
#print axioms RestrictedFaaDiBrunoPartitionMatch.of_restrictedMatch
#print axioms RestrictedFaaDiBrunoMatch.of_partitionMatch
#print axioms RestrictedFaaDiBrunoMatch.of_forall_partitionMatchAt
#print axioms RestrictedFaaDiBrunoMatch.forall_partitionMatchAt
#print axioms fullVanishes_of_partitionMatch
#print axioms fullVanishes_of_forall_partitionMatchAt
#print axioms faaDiBrunoSuccSumZeroResidual_of_partitionMatch
#print axioms P2_closed_of_partitionMatch
#print axioms assembledSeries_isRoot_of_partitionMatch
#print axioms βHensel_lift_identity_of_partitionMatch
end AxiomAudit

end BCIKS20.HenselNumerator
