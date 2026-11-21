/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSectionResultant
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeTerminalKernel
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCoordinateWeight
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge

/-! # The coordinate-weight bound for an actual terminal cubic -/

open Polynomial Finset
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.SecondPrimeCubicWeightBound

open SecondPrimeQuarticInterpolation SecondPrimeDegreeSevenDimension SecondPrimeSectionResultant
open SecondPrimeCoordinateWeight SecondPrimeTerminalKernel

variable {K F ι : Type} [Field K] [Field F] [Fintype ι]

/-- Every sufficiently populated irreducible cubic component of the genuine terminal
interpolation problem has coordinate/value weight at most 290805098. -/
theorem weight_bound (φ : F →+* K) (dom : ι ↪ K) (u₀ u₁ : ι → K)
    (hn : Fintype.card ι = 1073741824) (f : Surface K) (hi : Irreducible f)
    (hb : f.natDegree = 3) (hf : WeightedSylvesterDegree.TotalDegreeLe f 34)
    (G : Finset F) (w : F → K[X]) (hlarge : 100663466 < G.card)
    (hfit : ∀ z ∈ G, (w z).natDegree ≤ 67108863 ∧ ∃ S : Finset ι, 357913943 ≤ S.card ∧
      ∀ i ∈ S, (w z).eval (dom i) = u₀ i + φ z * u₁ i)
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (w z) = 0) :
    weight 67108863 f ≤ 290805098 := by
  classical
  by_contra! hweight
  obtain ⟨c, hc, hesc⟩ := escapes_quotient_window dom u₀ u₁ hn f
  have hdiv := divides_interpolation_kernel (s := 33554432) (v := 5) φ dom u₀ u₁ f hi
    (by omega) (by decide : 0 < 357913943) hf G w hfit hroot (by simpa [hb] using hlarge) c hc
  obtain ⟨H, hH⟩ := hdiv
  have hne : surface c ≠ 0 := by
    intro hz
    apply hesc 0
    rw [hz]
    change 0 = f * surfaceLinear 0
    rw [map_zero, mul_zero]
  have hHne : H ≠ 0 := right_ne_zero_of_mul (hH ▸ hne)
  have hW : weight 67108863 (surface c) ≤ 357913942 :=
    weight_le_of_coeff _ _ fun j i a h => by have hh := (surface_support c h).2.2; omega
  rw [hH, weight_mul _ _ _ hi.ne_zero hHne] at hW
  have hQt : Bivariate.totalDegree (surface c) ≤ 33554432 := by
    apply Finset.sup_le
    intro j hj
    have hi' := leadingCoeff_ne_zero.mpr (mem_support_iff.mp hj)
    exact (surface_support c (leadingCoeff_ne_zero.mpr hi')).2.1
  rw [hH, Bivariate.totalDegree_mul hi.ne_zero hHne] at hQt
  have hFt := Bivariate.coeff_totalDegree_le f
    (mem_support_iff.mpr (leadingCoeff_ne_zero.mpr hi.ne_zero))
  have hY : (surface c).natDegree ≤ 5 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (surface_support c h).1
  rw [hH, natDegree_mul hi.ne_zero hHne, hb] at hY
  obtain ⟨v, hv⟩ := exists_coefficients_of_support (s := 33554429) (v := 2)
    (d := 67108863) (t := 67108844) H (fun j i a h => by
      have hj : H.coeff j ≠ 0 := fun hz => h (by simp [hz])
      have hii : (H.coeff j).coeff i ≠ 0 := fun hz => h (by simp [hz])
      have hY' := le_natDegree_of_ne_zero hj
      have hi' := le_natDegree_of_ne_zero hii
      have hT := Bivariate.coeff_totalDegree_le H (mem_support_iff.mpr hj)
      have hC := coeff_weight_le 67108863 H h
      exact ⟨by omega, by omega, by omega⟩)
  exact hesc v (hH.trans (congrArg (fun B => f * B) hv.symm))

open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry in
/-- Direct form for genuine bad-scalar witnesses over a finite evaluation domain, over any
coefficient-field extension used for the component factorization. -/
theorem actual_cubic_weight [DecidableEq F] (φ : F →+* K) (dom : ι ↪ F) (δ : ℝ≥0)
    (u : Code.WordStack F (Fin 2) ι) (hn : Fintype.card ι = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 67108864 δ u)
    (Q f : Surface K) (hQ : Q ≠ 0) (hdiv : f ∣ Q) (hi : Irreducible f)
    (hb : f.natDegree = 3)
    (htri : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 34)
    (G : Finset F) (hG : G ⊆ fam.G) (hlarge : 100663466 < G.card)
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
    weight 67108863 f ≤ 290805098 := by
  classical
  apply weight_bound φ (dom.trans ⟨φ, φ.injective⟩) (fun i => φ (u 0 i)) (fun i => φ (u 1 i))
    hn f hi hb (factor_triangle hQ hdiv htri) G (fun z => (fam.q z).map φ) hlarge _ hroot
  intro z hz
  refine ⟨natDegree_map_le.trans (by have hh := fam.degree_lt z (hG hz); omega),
    fullAgreement dom (u 0) (u 1) z (fam.q z), ht.trans (fam.threshold_le z (hG hz)), ?_⟩
  intro i hi
  have h := (mem_filter.mp hi).2
  simpa only [Function.Embedding.trans_apply, Function.Embedding.coeFn_mk, eval_map_apply,
    map_add, map_mul] using congrArg φ h

#print axioms weight_bound
#print axioms actual_cubic_weight
end ArkLib.ProximityGap.Frontier.SecondPrimeCubicWeightBound
