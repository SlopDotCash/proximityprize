/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.IntrinsicQuarticSectionCap
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSelectedSectionChart
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeActualPopulations
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticWeightBound

/-! # Actual selected-scalar counts on the proper quartic branch

The lifted evaluation points and scalar labels retain their cardinalities under the
field embedding. Each original agreement set then supplies exactly the selected section
required by the intrinsic quartic resultant.
-/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeActualQuarticCap

open Finset Polynomial
open SecondPrimeCoordinateWeight SecondPrimeScalarChart SecondPrimeSelectedSectionChart
open SecondPrimeActualPopulations HalfPredecessorBadEventRichPointBridge
open HalfPredecessorLineCoreGeometry
open MovingCubicVanishingBranch CanonicalQuarticSiteOrder
open scoped NNReal

variable {I F K : Type} [Fintype I] [Field F] [DecidableEq F] [Field K]
  {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- Every collection of selected labels lying on a proper irreducible quartic has the
intrinsic section cap, for the true domain and the original received rows. -/
theorem label_cap (fam : BadScalarRichPointFamily dom 67108864 δ u) (φ : F →+* K)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (Q f : Surface K) (hQ : Q ≠ 0) (hdiv : f ∣ Q) (hi : Irreducible f) (hfour : f.natDegree = 4)
    (htri : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 34)
    (hnd : ¬ genericEquation (scalarChart f) ∣
      genericEquation (scalarFieldHessian (scalarChart f)))
    (G : Finset F) (hG : G ⊆ fam.G)
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
    G.card ≤ 268435546 := by
  classical
  by_cases hlarge : 646 < G.card
  · have w := SecondPrimeQuarticWeightBound.actual_quartic_weight φ dom δ u hn ht fam
      Q f hQ hdiv hi hfour htri G hG hlarge hroot
    have hd : 0 < f.natDegree := by omega
    have hc := (value_degree f).trans hfour
    have hprim := (SecondPrimeReceivedJetColumns.chart_irreducible f hi hd).isPrimitive
      (by omega : (scalarChart f).natDegree ≠ 0)
    let e : F ↪ K := ⟨φ, φ.injective⟩
    let d := dom.trans e
    let D := univ.map d
    let row (j : Fin 2) := Function.extend d (fun i => φ (u j i)) (fun _ => 0)
    let q := Function.extend φ (fun z => (fam.q z).map φ) (fun _ => 0)
    have hrow (j : Fin 2) (i : I) : row j (d i) = φ (u j i) := d.injective.extend_apply _ _ i
    have hq (z : F) : q (e z) = (fam.q z).map φ := φ.injective.extend_apply _ _ z
    have hnD : D.card = 1073741824 := by simpa only [D, card_map, card_univ] using hn
    have hcap := IntrinsicQuarticSectionCap.secondPrime_proper_quartic_label_cap
      (f.map Bivariate.swap.toRingHom) D hnD (row 0) (row 1)
      (original_scalar_bound f (SecondPrimeSectionResultant.factor_triangle hQ hdiv htri))
      hprim hc (generic_irreducible f hi hd) hnd ((chart_weight f _).trans w) (G.map e) q
    rw [← card_map (f := e)]
    apply hcap
    intro z hz
    obtain ⟨g, hg, rfl⟩ := mem_map.mp hz
    rw [hq]
    refine ⟨natDegree_map_le.trans (by have hh := fam.degree_lt g (hG hg); omega),
      (section_identity f _ _).trans (hroot g hg), ?_⟩
    let S := fullAgreement dom (u 0) (u 1) g (fam.q g)
    refine ⟨S.map d, map_subset_map.mpr (subset_univ _), ?_, ?_⟩
    · rw [card_map]
      exact ht.trans (fam.threshold_le g (hG hg))
    · intro a ha
      obtain ⟨i, hiS, rfl⟩ := mem_map.mp ha
      rw [hrow, hrow]
      have hh := (mem_filter.mp hiS).2
      simpa only [d, e, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
        eval_map_apply, map_add, map_mul] using congrArg φ hh
  · omega

/-- The proper quartic cannot realize the large population produced by the actual
factorization of the received-word interpolant. -/
theorem population_cap (fam : Family dom δ u) (φ : F →+* K)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (Q f : Surface K) (hQ : Q ≠ 0) (hdiv : f ∣ Q) (hi : Irreducible f) (hfour : f.natDegree = 4)
    (htri : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 34)
    (hnd : ¬ genericEquation (scalarChart f) ∣
      genericEquation (scalarFieldHessian (scalarChart f))) :
    (population fam φ f).card ≤ 268435546 := by
  classical
  exact label_cap fam φ hn ht Q f hQ hdiv hi hfour htri hnd _ (filter_subset _ _)
    (fun _ hz => (mem_filter.mp hz).2)

#print axioms label_cap
#print axioms population_cap
end ArkLib.ProximityGap.Frontier.SecondPrimeActualQuarticCap
