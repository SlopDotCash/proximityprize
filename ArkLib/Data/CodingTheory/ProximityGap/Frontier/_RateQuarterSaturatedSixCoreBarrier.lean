/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterPrimitiveFactorRecursion

/-!
# Rate-quarter saturated endpoint: six-core Plotkin barrier

At the common-factor endpoint, write `n=16m` and

```text
6z = 53m-8,
```

so `z` is the amplified core size.  Six distinct degree-`<4m` primitive
factor lines cannot all have cores of size at least `z` while every pair core
stays below the polynomial root cap `4m-1`: the exact-diagonal constant-weight
Johnson inequality is already contradictory.

Consequently any six-core attempt at this agreement scale forces one pair
intersection to have at least `4m-1` coordinates.  For primitive direction
degree at least one, distinct factor differences have degree at most `4m-2`,
so the algebraic root bound would then identify the two lines.  This file
records the set-system half of that closure; the five-core case remains
arithmetically possible and is the sharp next multi-line frontier.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.RateQuarterSaturatedSixCoreBarrier

open ConstantWeightPlotkinBound
open HalfPredecessorLineCoreGeometry
open HalfPredecessorRateQuarterDeterminantCollapse
open HalfPredecessorRateQuarterPrimitiveDirection
open HalfPredecessorRateQuarterPrimitiveFactorRecursion

attribute [local instance] Classical.propDecidable

variable {U : Type} [Fintype U] [DecidableEq U]

/-- Six saturated-size cores in a `16m`-point universe force a pair
intersection strictly above the degree-`4m-2` root cap. -/
theorem exists_pair_inter_card_ge_four_mul_sub_one
    {m z : Nat} (hm : 0 < m) (hz : 6 * z = 53 * m - 8)
    (hU : Fintype.card U = 16 * m)
    (S : Fin 6 → Finset U)
    (hsize : ∀ i, z ≤ (S i).card) :
    ∃ i j : Fin 6, i ≠ j ∧ 4 * m - 1 ≤ (S i ∩ S j).card := by
  by_contra hnot
  push Not at hnot
  let T : Fin 6 → Finset U := fun i =>
    Classical.choose (Finset.exists_subset_card_eq (hsize i))
  have hTsub : ∀ i, T i ⊆ S i := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).1
  have hTcard : ∀ i, (T i).card = z := by
    intro i
    exact (Classical.choose_spec
      (Finset.exists_subset_card_eq (hsize i))).2
  have hTpair : ∀ i j, i ≠ j → (T i ∩ T j).card ≤ 4 * m - 2 := by
    intro i j hij
    have hsmall := hnot i j hij
    have hS : (S i ∩ S j).card ≤ 4 * m - 2 := by omega
    exact (Finset.card_le_card
      (Finset.inter_subset_inter (hTsub i) (hTsub j))).trans hS
  have hplot := constantWeight_johnson T z (4 * m - 2) hTcard hTpair
  rw [Fintype.card_fin, hU] at hplot
  have hm8 : 8 ≤ 53 * m := by omega
  have hz' : 6 * z + 8 = 53 * m := by omega
  have hfour : 2 ≤ 4 * m := by omega
  have hsub : (4 * m - 2) + 2 = 4 * m := Nat.sub_add_cancel hfour
  norm_num at hplot
  nlinarith [hsub]

section PrimitiveCluster

open Polynomial

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **Six-line primitive-cluster closure at the saturated endpoint.**  A
nonconstant primitive direction leaves factor degree `<4m-1`; hence distinct
factors have pair-core size at most `4m-2`.  The six-core Plotkin barrier
forces a pair of size at least `4m-1`, a contradiction.

Thus a primitive collapsed cluster can contain at most five distinct factors
whose received-word cores all reach the saturated P1 agreement core size. -/
theorem not_six_saturated_cores_in_primitive_cluster
    (dom : I ↪ F) (u0 u1 : I → F)
    {m z : Nat} (hm : 0 < m) (hz : 6 * z = 53 * m - 8)
    (hI : Fintype.card I = 16 * m)
    (line0 line1 : PolynomialLine F) (hne : line0 ≠ line1)
    (source : Fin 6 → PolynomialLine F)
    (factor : Fin 6 → F[X]) (hfactor : Function.Injective factor)
    (hfactorDeg : ∀ i, (factor i).natDegree < 4 * m - 1)
    (hA : ∀ i, (source i).1 - line0.1 =
      primitiveIntercept line0 line1 * factor i)
    (hR : ∀ i, (source i).2 - line0.2 =
      primitiveSlope line0 line1 * factor i)
    (hcore : ∀ i, z ≤
      (jointCore dom u0 u1 (source i).1 (source i).2).card) :
    False := by
  let S : Fin 6 → Finset I := fun i =>
    jointCore dom u0 u1 (source i).1 (source i).2
  obtain ⟨i, j, hij, hlarge⟩ :=
    exists_pair_inter_card_ge_four_mul_sub_one hm hz hI S hcore
  have hcap := core_intersection_card_le_factor_dimension_pred
    dom u0 u1 line0 line1 (source i) (source j)
      (factor i) (factor j) (ell := 4 * m - 1)
      hne (hfactor.ne hij) (hfactorDeg i) (hfactorDeg j)
      (hA i) (hR i) (hA j) (hR j)
  change (S i ∩ S j).card ≤ (4 * m - 1) - 1 at hcap
  have hfour : 2 ≤ 4 * m := by omega
  have hpred : (4 * m - 1) - 1 = 4 * m - 2 := by omega
  rw [hpred] at hcap
  omega

end PrimitiveCluster

end ArkLib.ProximityGap.Frontier.RateQuarterSaturatedSixCoreBarrier

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.RateQuarterSaturatedSixCoreBarrier
#print axioms exists_pair_inter_card_ge_four_mul_sub_one
#print axioms not_six_saturated_cores_in_primitive_cluster
