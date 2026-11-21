/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCubicWindowCount
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSelectedSectionChart
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCubicWeightBound

/-! # Unrestricted cubic interpolation outside the subspace of all multiples -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeCubicIntrinsicEscape

open Finset Polynomial
open SecondPrimeQuarticInterpolation SecondPrimeDegreeSevenDimension SecondPrimeCoordinateWeight
open SecondPrimeSectionResultant SecondPrimeCubicWindowCount SecondPrimeSelectedSectionChart
open SecondPrimeScalarChart SecondPrimeReceivedJetColumns
open IntrinsicReceivedSections JetMultiplierGraph
open WeightedSylvesterDegree

set_option maxRecDepth 4096

variable {K : Type} [Field K]
private abbrev Source := SecondPrimeCubicWindowCount.Vars 11453246176
private abbrev Small (w : ℕ) := SecondPrimeCubicWindowCount.Vars (11453246176 - w)

private noncomputable def allowedMultiples (f : Surface K) (w : ℕ) :
    Submodule K (Source → K) :=
  (LinearMap.range ((LinearMap.mulLeft K f).comp
    (surfaceLinear (F := K) (s := 400000000) (v := 170) (d := 67108863)
      (t := 11453246176 - w)))).comap surfaceLinear

private theorem allowed_rank (f : Surface K) (w : ℕ) :
    Module.finrank K (allowedMultiples f w) ≤ Fintype.card (Small w) := by
  let L := allowedMultiples f w
  let P : L →ₗ[K] Surface K := surfaceLinear.comp L.subtype
  let T : (Small w → K) →ₗ[K] Surface K := (LinearMap.mulLeft K f).comp surfaceLinear
  have hi : Function.Injective P := by
    intro x y h
    apply Subtype.ext
    by_contra hn
    apply surface_ne_zero (sub_ne_zero.mpr hn)
    change surfaceLinear (s := 400000000) (v := 170) (d := 67108863) (t := 11453246176)
      (x.val-y.val) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr h
  have hinc : LinearMap.range P ≤ LinearMap.range T := by
    rintro _ ⟨c, rfl⟩
    exact c.property
  have h := (Submodule.finrank_mono hinc).trans (LinearMap.finrank_range_le T)
  rw [LinearMap.finrank_range_of_inj hi, Module.finrank_fintype_fun_eq_card] at h
  exact h

private theorem source_value (c : Source → K) : (surface c).natDegree ≤ 170 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  ext i a
  simp only [coeff_zero]
  by_contra hn
  exact hj.not_ge (surface_support c hn).1

private theorem source_triangle (c : Source → K) : TotalDegreeLe (surface c) 400000000 := by
  by_cases h : surface c = 0
  · simp [h, TotalDegreeLe]
  exact factor_triangle h dvd_rfl (fun _ _ _ hn => (surface_support c hn).2.1)

private theorem all_multiples (f : Surface K) (c : Source → K) (hf : f ≠ 0)
    (hd : f ∣ surface c) : c ∈ allowedMultiples f (weight 67108863 f) := by
  obtain ⟨H, hh⟩ := hd
  by_cases hzero : surface c = 0
  · refine ⟨0, ?_⟩
    change f * surfaceLinear (s := 400000000) (v := 170) (d := 67108863)
      (t := 11453246176-weight 67108863 f) 0 = surface c
    rw [hzero, map_zero, mul_zero]
  have hH : H ≠ 0 := right_ne_zero_of_mul (hh ▸ hzero)
  have hW : weight 67108863 (surface c) ≤ 11453246175 :=
    weight_le_of_coeff _ _ fun j i a h => by have hh' := (surface_support c h).2.2; omega
  rw [hh, weight_mul _ _ _ hf hH] at hW
  have hT : Bivariate.totalDegree (surface c) ≤ 400000000 := by
    apply Finset.sup_le
    exact fun j hj => source_triangle c _ (mem_support_iff.mp hj)
  rw [hh, Bivariate.totalDegree_mul hf hH] at hT
  have hY := source_value c
  rw [hh, natDegree_mul hf hH] at hY
  obtain ⟨v, hv⟩ := exists_coefficients_of_support (s := 400000000) (v := 170)
    (d := 67108863) (t := 11453246176-weight 67108863 f) H (fun j i a h => by
      have hj : H.coeff j ≠ 0 := fun hz => h (by simp [hz])
      have hii : (H.coeff j).coeff i ≠ 0 := fun hz => h (by simp [hz])
      have hval := le_natDegree_of_ne_zero hj
      have hscalar := le_natDegree_of_ne_zero hii
      have htotal := Bivariate.coeff_totalDegree_le H (mem_support_iff.mpr hj)
      have hcoord := coeff_weight_le 67108863 H h
      exact ⟨by omega, by omega, by omega⟩)
  exact ⟨v, (congrArg (fun A => f*A) hv).trans hh.symm⟩

/-- A cubic with the ordinary-polar received-order charge admits an auxiliary on the actual
domain that contains every sufficiently rich section and escapes every multiple of the cubic. -/
theorem exists_auxiliary (D : Finset K) (u v : K → K) (f : Surface K)
    (hi : Irreducible f) (hb : f.natDegree = 3) (hf : TotalDegreeLe f 34)
    (hn : D.card = 1073741824) (hl : 201326589 ≤ weight 67108863 f)
    (hu : weight 67108863 f ≤ 290805098)
    (hcharge : SufficientCharge
      (∑ a ∈ D, receivedOrder (f.map Bivariate.swap.toRingHom) a (u a) (v a)) (weight 67108863 f)) :
    ∃ c : Source → K, ¬f ∣ surface c ∧ ∀ (z : K) (q : K[X]) (S : Finset K), S ⊆ D →
      357913943 ≤ S.card → q.natDegree ≤ 67108863 → f.eval₂ (evalRingHom (C z)) q = 0 →
      (∀ a ∈ S, q.eval a = u a+z*v a) → (surface c).eval₂ (evalRingHom (C z)) q = 0 := by
  classical
  let G := f.map Bivariate.swap.toRingHom
  let r (a : K) := receivedOrder G a (u a) (v a)
  let W := weight 67108863 f
  let E := Source → K
  let realized : E →ₗ[K] Surface K :=
    (mapAlgHom Bivariate.swap.toAlgHom).toLinearMap.comp surfaceLinear
  have hthree (a : K) : r a ≤ 3 := by
    apply (CanonicalQuarticSiteOrder.siteOrder_le _ _ _).trans
    exact (value_degree f).trans hb |>.le
  have hcount := dimension_surplus (fun a : D => r a.val) W hl hu (by simpa using hn)
    (fun a => hthree a.val) (by simpa only [D.sum_coe_sort (f := r)] using hcharge)
  let cap (a : K) := ((32-r a)*(32-r a+1)/2)*399999967
  change Fintype.card D * (528*400000001) + Fintype.card (Small W) <
    Fintype.card Source + ∑ a : D, cap a.val at hcount
  rw [D.sum_coe_sort (f := cap), Fintype.card_coe] at hcount
  have hcap := allowed_rank f W
  have hp : (scalarChart f).IsPrimitive :=
    (chart_irreducible f hi (by omega)).isPrimitive (by rw [value_degree, hb]; decide)
  obtain ⟨c, hc, hsel⟩ := exists_section_outside (μ := 32) D u v G hp
    (original_scalar_bound f hf) (fun a _ => (hthree a).trans (by decide))
    (by decide : 34 ≤ 400000000+1) realized (fun c => original_scalar_bound _ (source_triangle c))
    (allowedMultiples f W) (by
      rw [Module.finrank_fintype_fun_eq_card]
      exact (Nat.add_le_add_left hcap _).trans_lt hcount)
  refine ⟨c, fun h => hc (all_multiples f c hi.ne_zero h), ?_⟩
  intro z q S hS hs hd hroot hfit
  rw [← section_identity]
  apply hsel z q S hS ((section_identity _ _ _).trans hroot) hfit
  change ((mapPlane (evalRingHom z)
    ((surface c).map Bivariate.swap.toRingHom)).eval q).natDegree < _
  rw [section_identity, surface_eval]
  exact (specialize_degree c z q hd (by decide)).trans_le (by omega)

private theorem weight_lower (f : Surface K) (hi : Irreducible f) (hb : f.natDegree = 3) :
    201326589 ≤ weight 67108863 f := by
  have h₁ : f.coeff f.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hi.ne_zero
  have h₂ := leadingCoeff_ne_zero.mpr h₁
  have h := coeff_weight_le 67108863 f (leadingCoeff_ne_zero.mpr h₂)
  rw [hb] at h
  omega

/-- The genuine polynomial jet construction and nonzero resultant cap the total number of
rich selected labels by 1200005270 whenever the received orders satisfy either charge. -/
theorem section_cap {F : Type} [Field F] (φ : F →+* K)
    (D : Finset K) (u v : K → K) (f : Surface K) (hi : Irreducible f)
    (hb : f.natDegree = 3) (hf : TotalDegreeLe f 34) (hn : D.card = 1073741824)
    (hu : weight 67108863 f ≤ 290805098)
    (hcharge : SufficientCharge
      (∑ a ∈ D, receivedOrder (f.map Bivariate.swap.toRingHom) a (u a) (v a)) (weight 67108863 f))
    (G : Finset F) (w : F → K[X])
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) (w z) = 0)
    (hfit : ∀ z ∈ G, (w z).natDegree ≤ 67108863 ∧ ∃ S ⊆ D, 357913943 ≤ S.card ∧
      ∀ a ∈ S, (w z).eval a = u a + φ z * v a) : G.card ≤ 1200005270 := by
  classical
  obtain ⟨c, hnd, hall⟩ := exists_auxiliary D u v f hi hb hf hn (weight_lower f hi hb) hu hcharge
  by_contra! hlarge
  apply hnd
  apply divides_of_many_sections φ f (surface c) hi (by omega) hf (source_triangle c) G w
  · intro z hz
    obtain ⟨hd, S, hS, ht, ha⟩ := hfit z hz
    exact ⟨hroot z hz, hall _ _ _ hS ht hd (hroot z hz) ha⟩
  · rw [hb]
    have h := source_value c
    omega

open scoped NNReal in
open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry in
/-- On an actual bad-scalar family the only remaining premise is the received-order charge
of the indicated component on the original domain. -/
theorem actual_cubic_cap {F ι : Type} [Field F] [Fintype ι] [DecidableEq F]
    (φ : F →+* K) (dom : ι ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) ι)
    (hn : Fintype.card ι = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊)
    (fam : BadScalarRichPointFamily dom 67108864 δ u)
    (Q f : Surface K) (hQ : Q ≠ 0) (hdiv : f ∣ Q) (hi : Irreducible f)
    (hb : f.natDegree = 3)
    (htri : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 34)
    (G : Finset F) (hG : G ⊆ fam.G)
    (hroot : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0)
    (hcharge : SufficientCharge
      (∑ i : ι, CanonicalQuarticSiteOrder.siteOrder (scalarChart f) (RatFunc.C (φ (dom i)))
        (C (RatFunc.C (φ (u 0 i)) + RatFunc.X * RatFunc.C (φ (u 1 i))))) (weight 67108863 f)) :
    G.card ≤ 1200005270 := by
  classical
  by_cases hlarge : 100663466 < G.card
  swap
  · omega
  let D := dom.trans (⟨φ, φ.injective⟩ : F ↪ K)
  have : Nonempty ι := Fintype.card_pos_iff.mp (hn ▸ by decide)
  let inv := Function.invFun D
  have hinv (i : ι) : inv (D i) = i := Function.leftInverse_invFun D.injective i
  have hw := SecondPrimeCubicWeightBound.actual_cubic_weight φ dom δ u hn ht fam Q f hQ hdiv hi hb
    htri G hG hlarge hroot
  refine section_cap φ (univ.map D) (fun a => φ (u 0 (inv a))) (fun a => φ (u 1 (inv a))) f hi hb
    (factor_triangle hQ hdiv htri) (by simpa using hn) hw ?_ G (fun z => (fam.q z).map φ) hroot ?_
  · simp only [sum_map, hinv]
    have hline (a b : K) : algebraMap K[X] (RatFunc K) (received a b) =
        RatFunc.C a + RatFunc.X * RatFunc.C b := by rw [received, map_add, map_mul]; rfl
    simpa only [receivedOrder, hline, mapPlane, scalarChart, D, Function.Embedding.trans_apply,
      Function.Embedding.coeFn_mk] using hcharge
  · intro z hz
    let S := fullAgreement dom (u 0) (u 1) z (fam.q z)
    refine ⟨natDegree_map_le.trans (by have hh := fam.degree_lt z (hG hz); omega),
      S.map D, map_subset_map.mpr (subset_univ S), ?_, ?_⟩
    · simpa only [card_map] using ht.trans (fam.threshold_le z (hG hz))
    · rintro a ha
      obtain ⟨i, hS, rfl⟩ := mem_map.mp ha
      have h := (mem_filter.mp hS).2
      change ((fam.q z).map φ).eval (D i) = φ (u 0 (inv (D i))) + φ z * φ (u 1 (inv (D i)))
      rw [hinv]
      simpa only [D, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
        eval_map_apply, map_add, map_mul] using congrArg φ h

#print axioms actual_cubic_cap
#print axioms exists_auxiliary
end ArkLib.ProximityGap.Frontier.SecondPrimeCubicIntrinsicEscape
