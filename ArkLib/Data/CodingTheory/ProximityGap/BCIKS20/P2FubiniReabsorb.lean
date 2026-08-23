/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reabsorb
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2FilterDrop
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2KeystoneReindex

/-!
# BCIKS20 Appendix A.4 — per-partition Y-degree reabsorption (the Fubini core)

After `partitionSum_drop_card_filter` removes the `i`-dependent `|λ| ≤ i` constraint and the `i`/`λ`
sums are Fubini-swapped, the inner object — for a *fixed* partition `λ` with `m = |λ|` parts,
multiplicity `cp = countPerms λ`, and coefficient product `Plam` — is the Y-degree sum

  `∑_{i ∈ range (Q.natDegree+1)} lift((Δ_X^{i₁}R)|_{x₀}).coeff i · ((C(i,m)·cp) • (α₀^{i-m} · Plam))`.

`inner_Ydegree_sum_eq_countPerms_hasseEvalAtRoot` collapses this to `cp • (hasseEvalAtRoot i₁ m · Plam)`
using `coeff_zero_βHenselAssembled` (`α₀ = T/W`) and `hasseEvalAtRoot_eq_QDegreeBinomReindex`
(the Y-degree reabsorption). The remaining manipulation is pure `CommSemiring` `ℕ`-scalar algebra
(`nsmul_eq_mul` + `ring`), term by term — this is the genuine algebraic content of the Fubini step.

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

/-- **Per-partition Y-degree reabsorption (PROVEN).**  For a fixed partition datum `(m, cp, Plam)`,
the inner Y-degree sum of the LHS partition form collapses to `cp • (hasseEvalAtRoot i₁ m · Plam)`.

Route: rewrite the base `α₀ = coeff 0 βHenselAssembled` to `T/W` (`coeff_zero_βHenselAssembled`),
expand `hasseEvalAtRoot i₁ m` over the same `Q`-degree range (`hasseEvalAtRoot_eq_QDegreeBinomReindex`),
push the `cp •` and `· Plam` through the sum (`Finset.sum_mul`/`Finset.smul_sum`), and close term by
term with `nsmul_eq_mul` + `ring`. -/
theorem inner_Ydegree_sum_eq_countPerms_hasseEvalAtRoot
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (i1 m cp : ℕ) (Plam : 𝕃 H) :
    (∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        liftToFunctionField (H := H)
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i)
          * ((i.choose m * cp) •
              ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - m) * Plam)))
      = cp • (hasseEvalAtRoot H x₀ R i1 m * Plam) := by
  have hα0 : PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp) = α₀ H := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, βHenselAssembled_constantCoeff]
  rw [hα0, ← taylorCollapse (H := H) x₀ R i1 m]
  simp only [nsmul_eq_mul, Nat.cast_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **Per-`ab` Fubini assembly (PROVEN).**  Combining the two cores: for a fixed `ab` (with X-Taylor
order `i₁` and Y-composition order `c`), the LHS partition-form block

  `∑_{i} lift((Δ_X^{i₁}R)|_{x₀}).coeff i · ∑_{λ⊢c, |λ|≤i, T∉λ} (C(i,|λ|)·countPerms λ)•(α₀^{i-|λ|}·Pλ)`

equals `∑_{λ⊢c, T∉λ} countPerms λ • (hasseEvalAtRoot i₁ |λ| · Pλ)`.  Route: drop the `|λ|≤i` filter
(`partitionSum_drop_card_filter`), distribute the lift factor (`Finset.mul_sum`), swap the `i`/`λ`
sums (`Finset.sum_comm`), and reabsorb each partition's Y-degree sum
(`inner_Ydegree_sum_eq_countPerms_hasseEvalAtRoot`).  This is the full LHS reabsorption of one
antidiagonal block of `RestrictedFaaDiBrunoMatch`. -/
theorem restrictedInner_eq_countPerms_hasseEvalAtRoot_sum
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (i1 c T : ℕ) :
    (∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        liftToFunctionField (H := H)
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff i)
          * (∑ lam ∈ (Finset.univ : Finset (Nat.Partition c)).filter
                      (fun lam => lam.parts.card ≤ i ∧ T ∉ lam.parts),
              ((i.choose lam.parts.card) * lam.parts.countPerms)
                • ((PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ (i - lam.parts.card)
                    * (lam.parts.map
                        (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod)))
      = ∑ lam ∈ (Finset.univ : Finset (Nat.Partition c)).filter (fun lam => T ∉ lam.parts),
          lam.parts.countPerms
            • (hasseEvalAtRoot H x₀ R i1 lam.parts.card
                * (lam.parts.map
                    (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod) := by
  simp only [partitionSum_drop_card_filter]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  exact inner_Ydegree_sum_eq_countPerms_hasseEvalAtRoot H x₀ R hHyp i1
      lam.parts.card lam.parts.countPerms _

/-- **Full LHS reabsorption of `restrictedFaaDiBrunoSum` (PROVEN).**  Summing the per-`ab` block
over the antidiagonal: the entire restricted Faà-di-Bruno defect sum equals

  `∑_{ab ∈ antidiagonal (t+1)} ∑_{λ⊢ab.2, (t+1)∉λ} countPerms λ • (hasseEvalAtRoot ab.1 |λ| · Pλ)`.

This is the complete entropy-free (LHS) half of `RestrictedFaaDiBrunoMatch`: every Y-degree sum has
been reabsorbed into `hasseEvalAtRoot`.  Route: `restrictedFaaDiBrunoSum_eq_partitionForm`, swap the
Y-degree and antidiagonal sums (`Finset.sum_comm`), then apply the per-`ab` reabsorption
`restrictedInner_eq_countPerms_hasseEvalAtRoot_sum` block by block.

What remains to close `RestrictedFaaDiBrunoMatch` is the reconciliation of this `hasseEvalAtRoot`
double sum against the RHS recursion form (`coeff_succ_βHenselAssembled_partitionForm`): the
`B_coeff = prefactor·hasseCoeffRepr𝒪` identity, `prefactor = countPerms`, the
`partitionProd_coeff_assembled` `W`/`ξ` telescope, and the `ζ` denominator — i.e. the
cleared-vs-uncleared root-relation core (the `t = 0` obstruction, generalized). -/
theorem restrictedFaaDiBrunoSum_eq_hasseDoubleSum
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoSum H x₀ R hHyp t
      = ∑ ab ∈ Finset.antidiagonal (t + 1),
          ∑ lam ∈ (Finset.univ : Finset (Nat.Partition ab.2)).filter
                    (fun lam => (t + 1) ∉ lam.parts),
            lam.parts.countPerms
              • (hasseEvalAtRoot H x₀ R ab.1 lam.parts.card
                  * (lam.parts.map
                      (fun j => PowerSeries.coeff j (βHenselAssembled H x₀ R hHyp))).prod) := by
  rw [restrictedFaaDiBrunoSum_eq_partitionForm, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ab _ => ?_)
  exact restrictedInner_eq_countPerms_hasseEvalAtRoot_sum H x₀ R hHyp ab.1 ab.2 (t + 1)

end BCIKS20.HenselNumerator

-- Axiom audit.
#print axioms BCIKS20.HenselNumerator.inner_Ydegree_sum_eq_countPerms_hasseEvalAtRoot
#print axioms BCIKS20.HenselNumerator.restrictedInner_eq_countPerms_hasseEvalAtRoot_sum
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoSum_eq_hasseDoubleSum
