/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeMobiusSections
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSmallCubic

/-! # Bounding the original population from a change of coordinate

Simple sections keep all their original agreements under the common change of coordinate.
The interpolation and Hessian tests can therefore be performed on the changed surface
without identifying its Taylor multiplicities with those of the original surface.
-/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeChartPopulation
open Polynomial Finset SecondPrimeCoordinateWeight SecondPrimeScalarChart
open SecondPrimeActualPopulations
open SecondPrimeMobiusSections IntrinsicReceivedSections JetMultiplierGraph
open CanonicalQuarticSiteOrder MovingCubicVanishingBranch WeightedSylvesterDegree
open HalfPredecessorLineCoreGeometry SecondPrimeCubicWindowCount
open scoped NNReal

variable {F K I : Type} [Fintype I] [Nonempty I] [Field F]
  [Field K] {p : ℕ} [CharP K p] {dom : I ↪ F} {δ : ℝ≥0}
  {u : Code.WordStack F (Fin 2) I}

/-- The sites in the common coordinate centered at r form an injective domain. -/
noncomputable def coordinate (D : I ↪ K) (r : K) : I ↪ K where
  toFun i := (D i - r)⁻¹
  inj' _ _ h := D.injective (sub_left_inj.mp (inv_injective h))

/-- Sum of exact orders in the chart, on the two transformed received rows. -/
noncomputable def orders (D : I ↪ K) (a b : I → K) (g : Surface K) : ℕ :=
  ∑ i : I, siteOrder (scalarChart g) (RatFunc.C (D i))
    (C (RatFunc.C (a i) + RatFunc.X * RatFunc.C (b i)))

/-- A transformed set of sections with genuine agreements is small. A component
that divides its Hessian is excluded directly in the changed coordinates. -/
theorem cap (φ : F →+* K) (D : I ↪ K) (a b : I → K) (g : Surface K)
    (hi : Irreducible g) (hb : g.natDegree = 3) (tri : TotalDegreeLe g 34)
    (hn : Fintype.card I = 1073741824) (hw : weight 67108863 g ≤ 290805098)
    (hp : 276 < p)
    (hcharge : (¬ genericEquation (scalarChart g) ∣
      genericEquation (scalarFieldHessian (scalarChart g))) →
      SufficientCharge (orders D a b g) (weight 67108863 g))
    (G : Finset F) (w : F → K[X])
    (hroot : ∀ z ∈ G, g.eval₂ (evalRingHom (C (φ z))) (w z) = 0)
    (hfit : ∀ z ∈ G, (w z).natDegree ≤ 67108863 ∧ ∃ T : Finset I, 357913943 ≤ T.card ∧
      ∀ i ∈ T, (w z).eval (D i) = a i + φ z * b i) : G.card ≤ 1200005270 := by
  classical
  by_cases hdiv : genericEquation (scalarChart g) ∣
      genericEquation (scalarFieldHessian (scalarChart g))
  · exact (SecondPrimeReverseChart.divisible_label_cap φ hp g hi (by omega) (by omega)
      tri hdiv G w hroot).trans (by decide)
  let inv := Function.invFun D
  have hinv (i : I) : inv (D i) = i := Function.leftInverse_invFun D.injective i
  refine SecondPrimeCubicIntrinsicEscape.section_cap φ (univ.map D) (a ∘ inv) (b ∘ inv) g hi hb tri
    (by simpa using hn) hw ?_ G w hroot ?_
  · have hline (x y : K) : algebraMap K[X] (RatFunc K) (received x y) =
        RatFunc.C x + RatFunc.X * RatFunc.C y := by rw [received, map_add, map_mul]; rfl
    simpa only [sum_map, Function.comp_apply, hinv, receivedOrder, hline, mapPlane,
      scalarChart, orders] using hcharge hdiv
  · intro z hz
    obtain ⟨hd, T, ht, hT⟩ := hfit z hz
    refine ⟨hd, T.map D, map_subset_map.mpr (subset_univ T), by simpa using ht, ?_⟩
    rintro _ hj
    obtain ⟨i, hit, rfl⟩ := mem_map.mp hj
    simpa only [Function.comp_apply, hinv] using hT i hit

/-- Bound the original label population using the transformed simple sections. At most
161 multiple sections were discarded when choosing the common coordinate. -/
theorem population_cap [DecidableEq F] (fam : Family dom δ u) (φ : F →+* K) (f : Surface K)
    (r : K) (S : Finset F) (hS : S ⊆ population fam φ f)
    (hcount : (population fam φ f).card ≤ S.card + 161)
    (hn : Fintype.card I = 1073741824) (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hp : 276 < p) :
    let W := weight 67108863 f
    let g := surfaceChart r W 67108863 f
    let D := coordinate (dom.trans (⟨φ, φ.injective⟩ : F ↪ K)) r
    let row := fun j i => (D i) ^ 67108863 * φ (u j i)
    let w := fun z => chart r 67108863 ((fam.q z).map φ)
    Irreducible g → g.natDegree = 3 → TotalDegreeLe g 34 → weight 67108863 g ≤ 290805098 →
    ((¬ genericEquation (scalarChart g) ∣ genericEquation (scalarFieldHessian (scalarChart g))) →
      SufficientCharge (orders D (row 0) (row 1) g) (weight 67108863 g)) →
    (∀ z ∈ S, (w z).natDegree ≤ 67108863 ∧ g.eval₂ (evalRingHom (C (φ z))) (w z) = 0 ∧
      ∀ i ∈ fullAgreement dom (u 0) (u 1) z (fam.q z),
        (w z).eval (D i) = row 0 i + φ z * row 1 i) →
    (population fam φ f).card ≤ 1200005431 := by
  classical
  intro W g D row w hi hb htri hw hcharge hsections
  have hsmall := cap φ D (row 0) (row 1) g hi hb htri hn hw hp hcharge S w
    (fun z hz => (hsections z hz).2.1) (fun z hz => ⟨(hsections z hz).1, _,
      ht.trans (fam.threshold_le z (mem_filter.mp (hS hz)).1), (hsections z hz).2.2⟩)
  omega

#print axioms population_cap
end ArkLib.ProximityGap.Frontier.SecondPrimeChartPopulation
