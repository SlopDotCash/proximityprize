/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Bijection
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Vanish
import ArkLib.ToMathlib.PartitionRecursion

/-!
# BCIKS20 Appendix A.4 — `restrictedFaaDiBrunoSum` in partition form (toward `RestrictedFaaDiBrunoMatch`)

Applies the proven combinatorial reindex `innerSum_reindex` (`P2Bijection.lean`) to the actual
`restrictedFaaDiBrunoSum` (`P2Close.lean`): each guarded value-multiset inner sum becomes a sum over
partitions `λ` of `ab.2` with `≤ i` parts and no part `= t+1`.  This is the entropy-free half of
`RestrictedFaaDiBrunoMatch`; what remains is the algebraic identification of the partition-indexed
factors with the `(A.1)` recursion `βHensel_succ` (the `B_coeff` / Y-Hasse / `W`/`ξ`/`ζ` clearing).
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

/-- **`restrictedFaaDiBrunoSum` in partition form.**  Rewrites the restricted Faà-di-Bruno defect
sum, term by term, into a sum over the Y-degree `i`, the `X`-Taylor split `ab`, and the partitions
`λ ⊢ ab.2` with `|λ| ≤ i` and `(t+1) ∉ λ`:

  `restrictedFaaDiBrunoSum t
     = ∑_i ∑_{ab} lift((Δ_X^{ab.1} R)|_{x₀}).coeff i ·
         ∑_{λ ⊢ ab.2, |λ|≤i, (t+1)∉λ} (C(i,|λ|)·countPerms λ) · (α₀^{i-|λ|} · ∏_{l∈λ} coeff l βHenselAssembled)`,

where `α₀ = coeff 0 βHenselAssembled`.  Pure application of `innerSum_reindex`. -/
theorem restrictedFaaDiBrunoSum_eq_partitionForm (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoSum H x₀ R hHyp t
      = ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
          ∑ ab ∈ Finset.antidiagonal (t + 1),
            (liftToFunctionField (H := H)
                ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX ab.1 R)).coeff i))
            * ∑ lam ∈ (Finset.univ : Finset (Nat.Partition ab.2)).filter
                        (fun lam => lam.parts.card ≤ i ∧ (t + 1) ∉ lam.parts),
                ((i.choose lam.parts.card) * lam.parts.countPerms)
                  • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
                      * (lam.parts.map (fun j =>
                          PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod) := by
  unfold restrictedFaaDiBrunoSum
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun ab _ => ?_))
  rw [innerSum_reindex i ab.2 (t + 1) (Nat.succ_pos t)
    (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))]

/-- **The `βHensel_succ` guard is vacuous on valid `(i₁,λ)`.**  In the `(A.1)` recursion the
partition product is `partitionProd λ (fun l => if l < t+1 then βHensel l else 0)`.  For `λ ⊢ (t+1−i₁)`
with `(t+1) ∉ λ`, every part `l` satisfies `l ≤ t+1−i₁` and `l ≠ t+1`, hence `l < t+1`, so the guard
is always taken and the product equals the plain `partitionProd λ (βHensel …)`. -/
theorem partitionProd_guard_eq (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t i1 : ℕ) (lam : Nat.Partition (t + 1 - i1)) (hT : (t + 1) ∉ lam.parts) :
    partitionProd lam (fun l => if _h : l < t + 1 then βHensel H x₀ R hHyp l else 0)
      = partitionProd lam (βHensel H x₀ R hHyp) := by
  unfold partitionProd
  congr 1
  apply Multiset.map_congr rfl
  intro l hl
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem hl
  have hle : l ≤ t + 1 - i1 := by
    have hsum : lam.parts.sum = l + rest.sum := by rw [hrest, Multiset.sum_cons]
    have : l ≤ lam.parts.sum := by rw [hsum]; exact Nat.le_add_right l rest.sum
    rwa [lam.parts_sum] at this
  have hne : l ≠ t + 1 := fun h => hT (h ▸ hl)
  rw [dif_pos (show l < t + 1 by omega)]

/-- **Positive outer index automatically satisfies the recursion exclusion.**  If `0 < i₁`, then
`λ ⊢ t+1-i₁` partitions a total strictly smaller than `t+1`, so `(t+1)` cannot occur as a part. -/
theorem partition_notMem_succ_of_pos_i1 (t i1 : ℕ) (hi1 : 0 < i1)
    (lam : Nat.Partition (t + 1 - i1)) :
    (t + 1) ∉ lam.parts :=
  ArkLib.Nat.Partition.notMem_parts_of_lt lam (by omega)

/-- **Positive outer index makes the recursion partition filter vacuous.**  In the `i₁ > 0` branch
of `(A.1)`, every partition of `t+1-i₁` automatically avoids the forbidden part `t+1`. -/
theorem partition_filter_notMem_succ_eq_univ_of_pos_i1 (t i1 : ℕ) (hi1 : 0 < i1) :
    ((Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
        (fun lam => (t + 1) ∉ lam.parts))
      = Finset.univ := by
  classical
  ext lam
  simp [partition_notMem_succ_of_pos_i1 t i1 hi1 lam]

/-- **Positive outer index collapses the `βHensel_succ` product guard.**  This is
`partitionProd_guard_eq` with the `(t+1) ∉ λ.parts` side condition discharged by
`Nat.Partition.notMem_parts_of_lt`. -/
theorem partitionProd_guard_eq_of_pos_i1 (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t i1 : ℕ) (hi1 : 0 < i1)
    (lam : Nat.Partition (t + 1 - i1)) :
    partitionProd lam (fun l => if _h : l < t + 1 then βHensel H x₀ R hHyp l else 0)
      = partitionProd lam (βHensel H x₀ R hHyp) :=
  partitionProd_guard_eq H x₀ R hHyp t i1 lam
    (partition_notMem_succ_of_pos_i1 t i1 hi1 lam)

/-- **Zero outer index exclusion is exactly non-indiscreteness.**  For `λ ⊢ t+1`, the forbidden
part `(t+1)` occurs iff `λ` is the one-part partition `indiscrete (t+1)`. -/
theorem partition_notMem_succ_iff_ne_indiscrete (t : ℕ)
    (lam : Nat.Partition (t + 1)) :
    (t + 1) ∉ lam.parts ↔ lam ≠ Nat.Partition.indiscrete (t + 1) :=
  not_congr (ArkLib.Nat.Partition.mem_self_iff_eq_indiscrete (Nat.succ_pos t) (p := lam))

/-- **Zero outer index filter removes exactly the indiscrete partition.**  The `i₁ = 0` branch of
the `(A.1)` recursion ranges over all partitions of `t+1` except the single part `[t+1]`. -/
theorem partition_filter_notMem_succ_eq_univ_erase_indiscrete (t : ℕ) :
    ((Finset.univ : Finset (Nat.Partition (t + 1))).filter
        (fun lam => (t + 1) ∉ lam.parts))
      = Finset.univ.erase (Nat.Partition.indiscrete (t + 1)) := by
  classical
  ext lam
  simp [partition_notMem_succ_iff_ne_indiscrete t lam]

/-- **Non-indiscrete zero outer index collapses the `βHensel_succ` product guard.**  This is the
`i₁ = 0` complement to `partitionProd_guard_eq_of_pos_i1`. -/
theorem partitionProd_guard_eq_of_ne_indiscrete (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) (lam : Nat.Partition (t + 1))
    (hne : lam ≠ Nat.Partition.indiscrete (t + 1)) :
    partitionProd lam (fun l => if _h : l < t + 1 then βHensel H x₀ R hHyp l else 0)
      = partitionProd lam (βHensel H x₀ R hHyp) :=
  partitionProd_guard_eq H x₀ R hHyp t 0 lam
    ((partition_notMem_succ_iff_ne_indiscrete t lam).2 hne)

/-- **Embedding of the `(A.1)` recursion `βHensel (t+1)` into `𝕃 H`.**  Pushes the ring
homomorphism `embeddingOf𝒪Into𝕃` through `βHensel_succ` (sum, negation, products, powers) and
discharges the guard via `partitionProd_guard_eq`, giving the `(i₁,λ)` sum with the partition
product over the plain `βHensel`. -/
theorem embed_βHensel_succ (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
      = - ∑ i1 ∈ Finset.range (t + 2),
          ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                    (fun lam => (t + 1) ∉ lam.parts),
            embeddingOf𝒪Into𝕃 H (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
              * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
              * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
              * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp)) := by
  rw [βHensel_succ, RingHom.map_neg]
  rw [show
    (embeddingOf𝒪Into𝕃 H)
        (∑ i1 ∈ Finset.range (t + 2),
          ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                    (fun lam => (t + 1) ∉ lam.parts),
            (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
              * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
              * B_coeff H x₀ R i1 lam
              * partitionProd lam
                  (fun l => if _h : l < t + 1 then βHensel H x₀ R hHyp l else 0))
      = ∑ i1 ∈ Finset.range (t + 2),
          (embeddingOf𝒪Into𝕃 H)
            (∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                      (fun lam => (t + 1) ∉ lam.parts),
              (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
                * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
                * B_coeff H x₀ R i1 lam
                * partitionProd lam
                    (fun l => if _h : l < t + 1 then βHensel H x₀ R hHyp l else 0)) by
    change (embeddingOf𝒪Into𝕃 H).toAddMonoidHom
        (∑ i1 ∈ Finset.range (t + 2),
          ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                    (fun lam => (t + 1) ∉ lam.parts),
            (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
              * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
              * B_coeff H x₀ R i1 lam
              * partitionProd lam
                  (fun l => if _h : l < t + 1 then βHensel H x₀ R hHyp l else 0))
      = _
    simp]
  refine congrArg Neg.neg (Finset.sum_congr rfl (fun i1 _ => ?_))
  rw [show
    (embeddingOf𝒪Into𝕃 H)
        (∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                  (fun lam => (t + 1) ∉ lam.parts),
          (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
            * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
            * B_coeff H x₀ R i1 lam
            * partitionProd lam
                (fun l => if _h : l < t + 1 then βHensel H x₀ R hHyp l else 0))
      = ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                  (fun lam => (t + 1) ∉ lam.parts),
          (embeddingOf𝒪Into𝕃 H)
            ((W𝒪 H) ^ (i1 + deltaSave i1 - 1)
              * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
              * B_coeff H x₀ R i1 lam
              * partitionProd lam
                  (fun l => if _h : l < t + 1 then βHensel H x₀ R hHyp l else 0)) by
    change (embeddingOf𝒪Into𝕃 H).toAddMonoidHom
        (∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                  (fun lam => (t + 1) ∉ lam.parts),
          (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
            * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
            * B_coeff H x₀ R i1 lam
            * partitionProd lam
                (fun l => if _h : l < t + 1 then βHensel H x₀ R hHyp l else 0))
      = _
    simp]
  refine Finset.sum_congr rfl (fun lam hlam => ?_)
  rw [partitionProd_guard_eq H x₀ R hHyp t i1 lam (Finset.mem_filter.mp hlam).2]
  simp only [map_mul, map_pow]

/-- **`coeff (t+1) βHenselAssembled` in `(i₁,λ)` partition form.**  Combines the definitional
`coeff_mk` unfolding of `βHenselAssembled` with `embed_βHensel_succ`: the order-`(t+1)` coefficient
is the embedded `(A.1)` recursion sum over `W^{t+2}·ξ^{2t+1}`.  Dual to
`restrictedFaaDiBrunoSum_eq_partitionForm`; together both sides of `RestrictedFaaDiBrunoMatch` are
now explicit partition sums, reducing the residual to a per-`(i₁,λ)` algebraic identity. -/
theorem coeff_succ_βHenselAssembled_partitionForm (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
      = (- ∑ i1 ∈ Finset.range (t + 2),
            ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                      (fun lam => (t + 1) ∉ lam.parts),
              embeddingOf𝒪Into𝕃 H (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
                * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
                * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
                * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp)))
        / ((liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)) := by
  unfold βHenselAssembled
  rw [PowerSeries.coeff_mk, embed_βHensel_succ]

/-- **Right-hand side of `RestrictedFaaDiBrunoMatch` in recursion partition form.**
The carved P2 match has right-hand side
`-ζ · coeff(t+1)(βHenselAssembled)`.  After
`coeff_succ_βHenselAssembled_partitionForm`, this is exactly `ζ` times the positive
`(A.1)` recursion partition sum over the global denominator.  This helper is only RHS
normalization; the remaining P2 work is still the term-level equality with the restricted
Faà-di-Bruno LHS. -/
theorem restrictedMatch_rhs_eq_recursionPartitionForm (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    let recSum : 𝕃 H :=
      ∑ i1 ∈ Finset.range (t + 2),
        ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                  (fun lam => (t + 1) ∉ lam.parts),
          embeddingOf𝒪Into𝕃 H (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
            * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
            * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
            * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp));
    let den : 𝕃 H :=
      (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
        * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1);
    - (ClaimA2.ζ R x₀ H
        * PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp))
      = ClaimA2.ζ R x₀ H * (recSum / den) := by
  dsimp
  rw [coeff_succ_βHenselAssembled_partitionForm]
  ring

/-- **Y-Hasse coefficient commutation.**  The middle-`X` Hasse derivative `Δ_X^{i₁}` and the
evaluation `X ↦ x₀` commute past the outer-`Y` Hasse derivative `Δ_Y^m`, which only contributes the
Taylor binomial via `hasseDerivY_coeff`:

  `(evalX(C x₀)(Δ_X^{i₁}(Δ_Y^m R))).coeff i = C(i+m, m) · (evalX(C x₀)(Δ_X^{i₁} R)).coeff (i+m)`.

This is the polynomial heart of the α₀-Taylor identity: it turns the order-`(i+m)` `Y`-coefficient of
`Δ_X^{i₁} R` (with its Hasse weight) into the order-`i` coefficient of the Hasse-`Y`-shifted object. -/
theorem evalX_hasseDeriv_Y_coeff (x₀ : F) (R : F[X][X][Y]) (i1 m i : ℕ) :
    (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))).coeff i
      = (i + m).choose m
          • (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff (i + m) := by
  rw [evalX_C_coeff, hasseDerivX_coeff, hasseDerivY_coeff, evalX_C_coeff, hasseDerivX_coeff,
    map_nsmul (Polynomial.hasseDeriv i1), Polynomial.eval_smul]

/-- **The α₀-Taylor identity.**  Evaluating the iterated Hasse coefficient at the generic root
`α₀ = T/W` (`hasseEvalAtRoot`) is the Hasse-Taylor sum: by `eval₂_eq_sum_range` and the Y-Hasse
commutation (brick 9), each order-`i` term is the order-`(i+m)` coefficient of `Δ_X^{i₁} R` weighted
by `C(i+m, m)` and `α₀^i`:

  `hasseEvalAtRoot i₁ m = ∑_i C(i+m, m) · (lift((Δ_X^{i₁}R)|_{x₀}).coeff(i+m)) · α₀^i`.

This is exactly the (reindexed) α₀-Taylor shape appearing on the LHS of `RestrictedFaaDiBrunoMatch`
(`restrictedFaaDiBrunoSum_eq_partitionForm`), now identified with the embedding-side
`hasseEvalAtRoot` / `B_coeff` object. -/
theorem hasseEvalAtRoot_eq_taylorSum (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    hasseEvalAtRoot H x₀ R i1 m
      = ∑ i ∈ Finset.range ((Bivariate.evalX (Polynomial.C x₀)
              (hasseDerivX i1 (hasseDerivY m R))).natDegree + 1),
          (i + m).choose m
            • (liftToFunctionField (H := H)
                  ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff (i + m))
                * (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) ^ i) := by
  unfold hasseEvalAtRoot
  rw [Polynomial.eval₂_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [evalX_hasseDeriv_Y_coeff, map_nsmul (liftToFunctionField (H := H)), smul_mul_assoc]

/-- **Embedding of the leading-coefficient unit `W𝒪`.**  `W𝒪 = ⟦C(lc H)⟧` embeds to the
function-field leading coefficient `W = liftToFunctionField (lc H)`.  A W-telescope ingredient. -/
theorem embed_W𝒪 : embeddingOf𝒪Into𝕃 H (W𝒪 H) = liftToFunctionField (H := H) H.leadingCoeff := by
  unfold W𝒪
  rw [embeddingOf𝒪Into𝕃_mk, liftBivariate_C]

end BCIKS20.HenselNumerator

-- Axiom audit.
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoSum_eq_partitionForm
#print axioms BCIKS20.HenselNumerator.partitionProd_guard_eq
#print axioms BCIKS20.HenselNumerator.partition_notMem_succ_of_pos_i1
#print axioms BCIKS20.HenselNumerator.partition_filter_notMem_succ_eq_univ_of_pos_i1
#print axioms BCIKS20.HenselNumerator.partitionProd_guard_eq_of_pos_i1
#print axioms BCIKS20.HenselNumerator.partition_notMem_succ_iff_ne_indiscrete
#print axioms BCIKS20.HenselNumerator.partition_filter_notMem_succ_eq_univ_erase_indiscrete
#print axioms BCIKS20.HenselNumerator.partitionProd_guard_eq_of_ne_indiscrete
#print axioms BCIKS20.HenselNumerator.embed_βHensel_succ
#print axioms BCIKS20.HenselNumerator.coeff_succ_βHenselAssembled_partitionForm
#print axioms BCIKS20.HenselNumerator.restrictedMatch_rhs_eq_recursionPartitionForm
#print axioms BCIKS20.HenselNumerator.evalX_hasseDeriv_Y_coeff
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_taylorSum
#print axioms BCIKS20.HenselNumerator.embed_W𝒪
