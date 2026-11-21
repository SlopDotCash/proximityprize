/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.UnconditionalCubicPopulation
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCubicOnly

/-! # A cubic and a quartic on the same five-eighth predecessor sections

The smaller interpolation window bounds the total value-degree budget by three.
A sufficiently populated component also divides the common terminal quartic,
bringing its uniform label counts and affine-head recognition to this cubic.
-/
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.FiveEighthCubicFactors
open SecondPrimeQuarticInterpolation SecondPrimeSectionResultant SecondPrimeActualPopulations
open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry HalfPredecessorSecantLines
open _root_.ProximityGap
variable {F I K : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] [DecidableEq I] [Field K]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

private theorem factor_sum {A : Type} [DecidableEq A] (U : Multiset A) (D : A → ℕ) :
    ∑ f ∈ U.toFinset, D f ≤ (U.map D).sum := by
  change (U.dedup.map D).sum ≤ _
  obtain ⟨R,h⟩ := Multiset.le_iff_exists_add.mp (Multiset.dedup_le U)
  calc _ ≤ (U.dedup.map D).sum+(R.map D).sum := Nat.le_add_right _ _
       _ = _ := by conv_rhs => rw [h,Multiset.map_add,Multiset.sum_add]

/-- Every selected label outside thirteen exceptions lies on an irreducible
component in a total ordinate budget of three. Every component above 512 labels
has the terminal quartic's bounds and its actual base-field head in degree one. -/
theorem components [Infinite K] (fam : Family dom δ u) (φ : F →+* K) {p : ℕ} [CharP K p]
    (hp : 1744830589<p) (hn : Fintype.card I=1073741824)
    (ht : 402653185≤⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊) :
    ∃ (U : Finset (Factor K)) (E : Finset F),
      E.card≤13 ∧ U.card≤3 ∧ (∑ f ∈ U, f.natDegree)≤3 ∧
      fam.G ⊆ E ∪ U.biUnion (population fam φ) ∧
      ∀ f ∈ U, 0<f.natDegree ∧
        (f.natDegree=3 → (population fam φ f).card≤1200005270) ∧
        (f.natDegree=2 → (population fam φ f).card≤512) ∧
        (f.natDegree=1 → 512<(population fam φ f).card →
          ∃ L ∈ lineParameters fam, population fam φ f ⊆ pointsOn fam L) := by
  classical
  let dom' := dom.trans (⟨φ,φ.injective⟩ : F ↪ K)
  let u₀ (i : I) := φ (u 0 i)
  let u₁ (i : I) := φ (u 1 i)
  have fit (z : F) (hz : z∈fam.G) :
      ((fam.q z).map φ).natDegree≤67108863 ∧
      ∃ S : Finset I, 402653185≤S.card ∧ ∀ i∈S, ((fam.q z).map φ).eval (dom' i) = u₀ i + φ z*u₁ i := by
    refine ⟨natDegree_map_le.trans (by have := fam.degree_lt z hz; omega),
      fullAgreement dom (u 0) (u 1) z (fam.q z),ht.trans (fam.threshold_le z hz),?_⟩
    intro i hi
    change ((fam.q z).map φ).eval (φ (dom i)) = _
    rw [eval_map_apply]
    simpa only [u₀,u₁,map_add,map_mul] using congrArg φ (mem_filter.mp hi).2
  obtain ⟨c,hc,_,hcurve⟩ := exists_curve (s:=13) (v:=3) (d:=67108863) (t:=402653185) dom' u₀ u₁
    (by decide) (by rw [hn]; simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]; norm_num [Fin.sum_univ_succ])
  let C₀ := surface c
  have hc0 : C₀≠0 := surface_ne_zero hc
  have htotal := factor_triangle hc0 dvd_rfl (fun j i a h => (surface_support c h).2.1)
  have hy : C₀.natDegree≤3 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (surface_support c h).1
  have hdeg (j : ℕ) : (C₀.coeff j).natDegree≤13 := by
    by_cases hj : C₀.coeff j=0
    · simp [hj]
    · have hh := htotal j hj; omega
  have h₀ (z : F) (hz : z∈fam.G) : C₀.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ)=0 := by
    obtain ⟨hdeg,S,hS,ha⟩ := fit z hz
    exact (surface_eval c ..).trans (hcurve _ _ hdeg _ hS ha)
  obtain ⟨P,E,hP,hprim,hdiv,hde,_,exc,hcov⟩ := SecondPrimePrimitiveSurface.primitive_surface φ hc0 fam.G
    (fun z => (fam.q z).map φ) 13 hdeg h₀
  obtain ⟨T,hT,hs,hnT,cover⟩ := SecondPrimePrimitiveSurface.factor_cover P hP hprim
  let U := T.toFinset
  have hyT : P.natDegree≤3 := hde.le.trans hy
  have ht0 : 357913943 ≤ ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊ := by omega
  obtain ⟨Q,hQ,hshape,hquart⟩ := secondPrime_predecessor_surface dom' u₀ u₁ hn
  have hQdeg : Q.natDegree≤4 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (hshape j i a h).1
  have hQtri := fun j i a h => (hshape j i a h).2.1
  have hQtot := factor_triangle hQ dvd_rfl hQtri
  have hQroot (z : F) (hz : z∈fam.G) : Q.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ)=0 := by
    obtain ⟨hdeg,S,hS,ha⟩ := fit z hz
    exact hquart _ _ hdeg S (by omega) ha
  refine ⟨U,E,exc,T.toFinset_card_le.trans (hnT.trans hyT),(factor_sum T _).trans (hs.le.trans hyT),?_,?_⟩
  · intro z hz
    by_cases he : z∈E
    · exact mem_union_left _ he
    obtain ⟨f,hf,hh⟩ := cover _ _ (hcov z hz he)
    exact mem_union_right _ (mem_biUnion.mpr ⟨f,Multiset.mem_toFinset.mpr hf,mem_filter.mpr ⟨hz,hh⟩⟩)
  · intro f hf
    obtain ⟨hi,hpos,hfP⟩ := hT f (Multiset.mem_toFinset.mp hf)
    have hdegf := (natDegree_le_of_dvd hfP hP).trans hyT
    have hft := factor_triangle hc0 (hfP.trans hdiv) (fun j i a h => (surface_support c h).2.1)
    let G := population fam φ f
    have hsub : G⊆fam.G := filter_subset ..
    have root (z : F) (hz : z∈G) : f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ)=0 := (mem_filter.mp hz).2
    have divides (hbig : 512<G.card) : f∣Q := by
      apply divides_of_many_sections φ f Q hi hpos hft hQtot G (fun z => (fam.q z).map φ)
        (fun z hz => ⟨root z hz,hQroot z (hsub hz)⟩)
      have hh := Nat.add_le_add (Nat.mul_le_mul_right 34 hdegf) (Nat.mul_le_mul_right 13 hQdeg)
      omega
    refine ⟨hpos,?_,?_,?_⟩
    · intro h3
      by_cases hb : 100663466 < G.card
      · have hd := divides (by omega)
        have hw := SecondPrimeCubicWeightBound.actual_cubic_weight φ dom δ u hn ht0 fam Q f hQ hd hi h3
          hQtri G hsub hb root
        exact UnconditionalCubicPopulation.cap fam φ p hp hn ht0 Q f hQ hi hd h3 hQtri hw
      · exact (le_of_not_gt hb).trans (by decide)
    · intro h2
      by_contra! hb
      have h := SecondPrimeQuadraticFactor.quadratic_population_le fam φ Q f hQ (divides hb) hi h2 (by
        intro j i a he
        obtain ⟨_,hh,hc⟩ := hshape j i a he
        exact ⟨hh,by omega⟩) (by
          intro i hi hj hz
          exact (show ¬ p ≤ i by omega) (Nat.le_of_dvd hi ((CharP.cast_eq_zero_iff K p i).mp hz))) hn ht0
      omega
    · intro h1 hbig
      change 512<G.card at hbig
      exact TerminalLinearComponent.actual_linear φ fam hn ht0 Q f hQ hi (divides hbig) h1 hshape G hsub (by omega) root

#print axioms components
end ArkLib.ProximityGap.Frontier.FiveEighthCubicFactors
