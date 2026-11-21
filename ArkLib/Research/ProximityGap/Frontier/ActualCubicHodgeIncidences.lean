/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCubicOnly
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSectionResultant
import ArkLib.Research.ProximityGap.Frontier.HodgeSectionIncidence

/-! # Ordinary received incidences on the actual terminal cubic -/

open Finset Polynomial Code
open ArkLib.ProximityGap.Frontier
open HalfPredecessorLineCoreGeometry HalfPredecessorBadEventRichPointBridge SecondPrimeActualPopulations SecondPrimeCoordinateWeight
open scoped NNReal

namespace ProximityGap.ActualCubicHodgeIncidences

variable {K : Type} [Field K]

/-- Substitute a coordinate and then its affine received value, keeping the
scalar parameter as a polynomial variable. -/
noncomputable def received (f : Factor K) (x a b : K) : K[X] :=
  f.eval₂ (mapRingHom (evalRingHom x)) (C a+Polynomial.X*C b)

/-- The coordinate polynomial obtained by evaluating a surface on a section. -/
noncomputable def sectionValue (f : Factor K) (z : K) (q : K[X]) : K[X] :=
  f.eval₂ (evalRingHom (C z)) q

private theorem received_degree (f : Factor K) {h : ℕ}
    (hf : WeightedSylvesterDegree.TotalDegreeLe f h) (x a b : K) :
    (received f x a b).natDegree ≤ h := by
  classical
  let L : K[X] := C a+Polynomial.X*C b
  have hL : L.natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact natDegree_mul_le.trans (by simp)
  rw [received,eval₂_eq_sum,Polynomial.sum]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hs := hf j (mem_support_iff.mp hj)
  have hc : ((f.coeff j).map (evalRingHom x)).natDegree ≤ (f.coeff j).natDegree := natDegree_map_le
  have hpow : (L^j).natDegree ≤ j*L.natDegree := natDegree_pow_le
  have hle := Nat.mul_le_mul_left j hL
  change (((f.coeff j).map (evalRingHom x))*L^j).natDegree ≤ h
  exact natDegree_mul_le.trans (by omega)

private theorem scalar_spec_degree (P : Polynomial K[X]) (z : K) :
    (P.eval (C z)).natDegree ≤ Bivariate.degreeX P := by
  have h := Bivariate.evalY_eq_evalX_swap z P
  simp only [Bivariate.evalY,Bivariate.evalX_eq_map] at h
  rw [h]
  exact natDegree_map_le.trans_eq (Bivariate.natDegreeY_swap P)

private theorem derivative_section_degree (f : Factor K) {z : K} {q : K[X]} {d W : ℕ}
    (hq : q.natDegree ≤ d) (hw : weight d f ≤ W) :
    (sectionValue f.derivative z q).natDegree ≤ W-d := by
  classical
  rw [sectionValue,eval₂_eq_sum,Polynomial.sum]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj' := mem_support_iff.mp hj
  have hc0 : f.coeff (j+1) ≠ 0 := by
    intro hc; exact hj' (by simp [coeff_derivative,hc])
  obtain ⟨i,hi,heq,_⟩ := Bivariate.exists_max_index_degreeX (f.coeff (j+1)) hc0
  have hc := coeff_weight_le d f (j := j+1) (i := i)
    (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi))
  rw [Nat.add_mul,one_mul] at hc
  have h1 := scalar_spec_degree (f.coeff (j+1)) z
  have hp : (q^j).natDegree ≤ j*q.natDegree := natDegree_pow_le
  have hqj := Nat.mul_le_mul_left j hq
  simp only [coeff_derivative,coe_evalRingHom,eval_mul,eval_natCast,← Nat.cast_succ,Nat.succ_eq_add_one]
  have hm : ((f.coeff (j+1)).eval (C z)*(j+1 : ℕ)).natDegree ≤
      ((f.coeff (j+1)).eval (C z)).natDegree := by
    exact natDegree_mul_le.trans (by rw [natDegree_natCast,Nat.add_zero])
  exact natDegree_mul_le.trans (by omega)

private theorem same_value (f : Factor K) (x z a b : K) (q : K[X])
    (h : q.eval x = a+z*b) :
    (sectionValue f z q).eval x = (received f x a b).eval z := by
  induction f using Polynomial.induction_on' with
  | add _ _ hp hq =>
    simpa only [sectionValue,received,eval₂_add,eval_add] using congrArg₂ (·+·) hp hq
  | monomial j r =>
    simp only [sectionValue,received,eval₂_monomial,coe_evalRingHom,eval_mul,eval_pow,
      eval_add,eval_C,eval_X,h]
    rw [SecondPrimeLinearFactor.at_site]
    rfl

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

open Classical in
/-- Ordinary incidences are actual folded-row agreements on a received line
contained in the surface, with nonzero value derivative at the intersection. -/
noncomputable def ordinarySites (fam : Family dom δ u) (φ : F →+* K)
    (f : Factor K) (z : F) : Finset I :=
  (fullAgreement dom (u 0) (u 1) z (fam.q z)).filter fun i =>
    received f (φ (dom i)) (φ (u 0 i)) (φ (u 1 i)) = 0 ∧
    (received f.derivative (φ (dom i)) (φ (u 0 i)) (φ (u 1 i))).eval (φ z) ≠ 0

private theorem roots_bound {α : Type} (s : Finset α) (v : α → K) (hv : Function.Injective v)
    (g : K[X]) (hg : g ≠ 0) (hs : ∀ a ∈ s, g.eval (v a) = 0) : s.card ≤ g.natDegree := by
  by_contra! h
  apply hg
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun a : s => v a.val)
    (hv.comp Subtype.val_injective)
  · exact fun a => hs a.val a.property
  · simpa using h

private theorem agreement_arithmetic {M J B : ℕ}
    (h : M*357913943 ≤ J+B+M*223696235) (hb : B ≤ 34*1073741824) :
    M*134217708 ≤ J+34*1073741824 := by
  rw [show 357913943 = 134217708 + 223696235 by decide,Nat.mul_add] at h
  exact (Nat.le_of_add_le_add_right h).trans (Nat.add_le_add_left hb _)

/-- Every simple subpopulation on the actual cubic forces ordinary incidences,
after paying at most its coordinate derivative degree per section and the
scalar degree per domain site. -/
theorem ordinary_agreement_count (fam : Family dom δ u) (φ : F →+* K) (f : Factor K)
    (hf : WeightedSylvesterDegree.TotalDegreeLe f 34) (hw : weight 67108863 f ≤ 290805098)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊)
    (S : Finset F) (hS : S ⊆ population fam φ f)
    (hsimp : ∀ z ∈ S, sectionValue f.derivative (φ z) ((fam.q z).map φ) ≠ 0) :
    S.card*134217708 ≤ (∑ z ∈ S, (ordinarySites fam φ f z).card)+34*1073741824 := by
  classical
  let A (z : F) := fullAgreement dom (u 0) (u 1) z (fam.q z)
  let R (i : I) := received f (φ (dom i)) (φ (u 0 i)) (φ (u 1 i))
  let V (z : F) := sectionValue f.derivative (φ z) ((fam.q z).map φ)
  let zeroSites (z : F) := univ.filter fun i => (V z).eval (φ (dom i)) = 0
  let off (z : F) := univ.filter fun i => i ∈ A z ∧ R i ≠ 0
  have hfam (z : F) (hz : z ∈ S) : z ∈ fam.G := (mem_filter.mp (hS hz)).1
  have hfit (i : I) (z : F) (hi : i ∈ A z) :
      ((fam.q z).map φ).eval (φ (dom i)) = φ (u 0 i) + φ z*φ (u 1 i) := by
    rw [eval_map_apply, (mem_filter.mp hi).2, map_add,map_mul]
  have hzcap (z : F) (hz : z ∈ S) : (zeroSites z).card ≤ 223696235 := by
    have hg : ((fam.q z).map φ).natDegree ≤ 67108863 :=
      natDegree_map_le.trans (by have := fam.degree_lt z (hfam z hz); omega)
    apply (roots_bound _ _ (φ.injective.comp dom.injective) (V z) (hsimp z hz)
      (fun _ hi => (mem_filter.mp hi).2)).trans
    have hdeg := derivative_section_degree f (z := φ z) (d := 67108863) (W := 290805098) hg hw
    exact hdeg
  have hoff (i : I) : (S.filter fun z => i ∈ off z).card ≤ 34 := by
    by_cases hi : R i = 0
    · simp [off,hi]
    apply (roots_bound _ φ φ.injective (R i) hi ?_).trans (received_degree f hf _ _ _)
    intro z hz
    obtain ⟨hzS,hzo⟩ := mem_filter.mp hz
    have hfa := (mem_filter.mp hzo).2.1
    have hroot := (mem_filter.mp (hS hzS)).2
    have he := same_value f _ _ _ _ _ (hfit i z hfa)
    change sectionValue f (φ z) ((fam.q z).map φ) = 0 at hroot
    simpa only [hroot,eval_zero] using he.symm
  have hsumOff : ∑ z ∈ S, (off z).card ≤ 34*1073741824 := by
    have hre : ∑ z ∈ S, (off z).card = ∑ i : I, (S.filter fun z => i ∈ off z).card := by
      have hcard (z : F) : (off z).card = ∑ i : I, if i ∈ off z then 1 else 0 := by simp
      simp_rw [hcard,card_filter]; rw [sum_comm]
    rw [hre]
    exact (sum_le_sum (fun i _ => hoff i)).trans_eq (by simp [hn])
  have hrow (z : F) (hz : z ∈ S) :
      357913943 ≤ (ordinarySites fam φ f z).card+(off z).card+223696235 := by
    have hc : A z ⊆ ordinarySites fam φ f z ∪ off z ∪ zeroSites z := by
      intro i hi
      by_cases hR : R i = 0
      · by_cases hV : (V z).eval (φ (dom i)) = 0
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hV⟩)
        apply mem_union_left
        apply mem_union_left
        apply mem_filter.mpr
        refine ⟨hi,hR,?_⟩
        have he := same_value f.derivative _ _ _ _ _ (hfit i z hi)
        exact fun hh => hV (he.trans hh)
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hi,hR⟩))
    have h1 := (ht.trans (fam.threshold_le z (hfam z hz))).trans (card_le_card hc)
    have h2 := card_union_le (ordinarySites fam φ f z) (off z)
    have h3 := card_union_le (ordinarySites fam φ f z ∪ off z) (zeroSites z)
    have hz' := hzcap z hz
    omega
  have hs := sum_le_sum hrow
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,sum_add_distrib] at hs
  exact agreement_arithmetic hs hsumOff

/-- The full cubic derivative resultant, before choosing a particular section. -/
noncomputable def cubicResultant (f : Factor K) : Polynomial K[X] := resultant f f.derivative 3 2

/-- The scalar-specialized polynomial in the value variable over the coordinate
fraction field. -/
noncomputable def genericFiber (f : Factor K) (z : K) : Polynomial (FractionRing K[X]) :=
  f.map ((algebraMap K[X] (FractionRing K[X])).comp (evalRingHom (C z)))

/-- A retained scalar has a full-degree separable generic fiber. -/
theorem regular_fiber (f : Factor K) (hd : f.natDegree = 3) (z : K)
    (hz : (cubicResultant f).eval (C z) ≠ 0) :
    (genericFiber f z).natDegree = 3 ∧ (genericFiber f z).Separable := by
  let ψ := (algebraMap K[X] (FractionRing K[X])).comp (evalRingHom (C z))
  have hres : ψ (resultant f f.derivative 3 2) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (FractionRing K[X]))).mpr hz
  refine ⟨?_,separable_map_of_resultant_derivative_padded_ne_zero ψ f hd.le (by decide) hres⟩
  have hle : (genericFiber f z).natDegree ≤ 3 := natDegree_map_le.trans hd.le
  by_contra hlt
  have hl : (f.map ψ).natDegree < 3 := by change (genericFiber f z).natDegree < 3; omega
  have hder := natDegree_derivative_le (f.map ψ)
  rw [derivative_map] at hder
  have hr := resultant_eq_zero_of_lt_lt (f := f.map ψ) (g := f.derivative.map ψ) (m := 3) (n := 2) hl (show (f.derivative.map ψ).natDegree < 2 by omega)
  rw [resultant_map_map] at hr
  exact hres hr

/-- The projected branch resultant has scalar degree at most 161 for actual
terminal cubics, so the bound counts generic degeneracies even on unselected sheets. -/
theorem cubic_resultant_bounds (f : Factor K) (hi : Irreducible f) (hd : f.natDegree = 3)
    (hchar : (3 : K) ≠ 0) (hf : WeightedSylvesterDegree.TotalDegreeLe f 34) :
    cubicResultant f ≠ 0 ∧ (cubicResultant f).natDegree ≤ 161 := by
  classical
  have hval : (3 : Polynomial K[X]) ≠ 0 := by
    simpa only [map_ofNat] using C_ne_zero.mpr (C_ne_zero.mpr hchar)
  have hlead : f.coeff 3 ≠ 0 := hd ▸ leadingCoeff_ne_zero.mpr hi.ne_zero
  have hc : f.derivative.coeff 2 ≠ 0 := by
    rw [coeff_derivative]
    convert mul_ne_zero hlead hval using 1
    norm_num
  have hg : f.derivative ≠ 0 := fun h => hc (by simp [h])
  have hg2 : f.derivative.natDegree = 2 := by
    have hle := natDegree_derivative_le f
    have hlo := le_natDegree_of_ne_zero hc
    omega
  have ht : WeightedSylvesterDegree.TotalDegreeLe f.derivative 33 := by
    intro j h
    have hcoeff : f.coeff (j+1) ≠ 0 := fun he => h (by simp [coeff_derivative,he])
    have ha := hf (j+1) hcoeff
    have hb := coeff_derivative_natDegree_le f j
    omega
  constructor
  · have hnot : ¬ f ∣ f.derivative := fun h => by
      have := natDegree_le_of_dvd h hg
      omega
    simpa only [cubicResultant,hd,hg2] using
      SecondPrimeSectionResultant.resultant_ne_zero f f.derivative hi (by omega) hnot
  · exact WeightedSylvesterDegree.natDegree_resultant_le f f.derivative hf ht

open Classical in
/-- Selected labels whose entire generic cubic fiber is regular. -/
noncomputable def regularSections (fam : Family dom δ u) (φ : F →+* K) (f : Factor K) :
    Finset F := (population fam φ f).filter fun z => (cubicResultant f).eval (C (φ z)) ≠ 0

/-- At most 161 selected labels are lost, and every retained selected section is simple. -/
theorem regular_sections (fam : Family dom δ u) (φ : F →+* K) (f : Factor K)
    (hi : Irreducible f) (hd : f.natDegree = 3) (hchar : (3 : K) ≠ 0)
    (hf : WeightedSylvesterDegree.TotalDegreeLe f 34) :
    (population fam φ f).card ≤ (regularSections fam φ f).card+161 ∧
    ∀ z ∈ regularSections fam φ f, sectionValue f.derivative (φ z) ((fam.q z).map φ) ≠ 0 := by
  classical
  let G := regularSections fam φ f
  let T := population fam φ f
  let bad := T \ G
  obtain ⟨hR,hr⟩ := cubic_resultant_bounds f hi hd hchar hf
  constructor
  · have hx : (T \ G).card ≤ (cubicResultant f).natDegree := by
      by_contra! hbig
      apply hR
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun z : bad => C (φ (z:F)))
        (C_injective.comp (φ.injective.comp Subtype.val_injective))
      · intro z
        obtain ⟨hzT,hzG⟩ := mem_sdiff.mp z.property
        by_contra h
        exact hzG (mem_filter.mpr ⟨hzT,h⟩)
      · simpa only [Fintype.card_coe] using hbig
    have hc := card_sdiff_add_card_eq_card (show G ⊆ T from filter_subset _ _)
    change T.card ≤ G.card+161
    omega
  · intro z hz h
    obtain ⟨hzT,hzR⟩ := mem_filter.mp hz
    apply hzR
    apply map_resultant_eq_zero_of_common_root (evalRingHom (C (φ z))) f f.derivative hd.le
      ((natDegree_derivative_le f).trans (by omega)) (Or.inl (by decide)) ((fam.q z).map φ)
    · rw [eval_map]; exact (mem_filter.mp hzT).2
    · rw [eval_map]; exact h

/-- An actual counterexample forces at least this many ordinary incidence pairs
on one irreducible cubic, after every generically ramified scalar fiber is discarded. -/
theorem actual_ordinary_mass (fam : Family dom δ u) (φ : F →+* K)
    {p : ℕ} [CharP K p] (hp : 715827884 < p) (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = 357913943)
    (hbig : 2147483648 < fam.G.card) :
    ∃ Q : Factor K, Q ≠ 0 ∧ TerminalFactorCoverage.Supported Q ∧
      ∃ f : Factor K, Irreducible f ∧ f ∣ Q ∧ f.natDegree = 3 ∧
        weight 67108863 f ≤ 290805098 ∧
        1431655572 ≤ (regularSections fam φ f).card ∧
        (∀ z ∈ regularSections fam φ f, (genericFiber f (φ z)).natDegree = 3 ∧
          (genericFiber f (φ z)).Separable) ∧
        192153493012046960 ≤ ∑ z ∈ regularSections fam φ f, (ordinarySites fam φ f z).card := by
  classical
  obtain ⟨Q,hQ,hs,f,hi,hd,hy,hpop,hw⟩ :=
    SecondPrimeCubicOnly.actual_cubic fam φ hp hn ht hbig
  have htri := SecondPrimeSectionResultant.factor_triangle hQ hd (fun j i a h => (hs j i a h).2.1)
  have hchar : (3:K) ≠ 0 := by
    intro hz
    have hle := Nat.le_of_dvd (by decide : 0 < 3) ((CharP.cast_eq_zero_iff K p 3).mp hz)
    omega
  obtain ⟨hremoved,hsimp⟩ := regular_sections fam φ f hi hy hchar htri
  have hG : 1431655572 ≤ (regularSections fam φ f).card := by omega
  refine ⟨Q,hQ,hs,f,hi,hd,hy,hw,hG,fun z hz => regular_fiber f hy (φ z) (mem_filter.mp hz).2,?_⟩
  have hfit := ordinary_agreement_count fam φ f htri hw hn ht.ge
    (regularSections fam φ f) (filter_subset _ _) hsimp
  omega

open ArkLib.ProximityGap.KKH26 ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open TerminalCollinearHeadCount

private abbrev prizeP := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
private abbrev prizeG := ArkLib.ProximityGap.PrizeShapePrimeP30Second.g
local instance : Fact prizeP.Prime := ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- A bound for the literal ordinary-incidence pairs alone suffices for the
exact second-prime operational threshold. The projected resultant, agreement
losses and population transfer have already been discharged. -/
theorem secondPrime_threshold_of_ordinary_incidence_bound
    (h : ∀ u : WordStack (ZMod prizeP) (Fin 2) (Fin (2^30)),
      let fam := canonicalBadScalarRichPointFamily secondDomain (k := 2^26)
        ((715827881 : ℝ≥0)/1073741824) u (by decide)
      let φ := algebraMap (ZMod prizeP) (AlgebraicClosure (ZMod prizeP))
      ∀ Q f : Factor (AlgebraicClosure (ZMod prizeP)), Q ≠ 0 → TerminalFactorCoverage.Supported Q →
        Irreducible f → f ∣ Q → f.natDegree = 3 → weight 67108863 f ≤ 290805098 →
        (∑ z ∈ regularSections fam φ f, (ordinarySites fam φ f z).card) < 192153493012046960) :
    MCAThresholdLedger.mcaDeltaStar (F := ZMod prizeP) (evalCode prizeG (2^30) (2^26-1))
      (epsStar : ℝ≥0∞) = (715827882 : ℝ≥0)/1073741824 := by
  apply secondPrime_threshold_of_head_cover
  intro u fam G hG hN
  have ht := TwoCorePackingThreshold.agreement_ceiling 715827881 (by decide)
  have hbig : 2147483648 < fam.G.card := by have := card_le_card hG; omega
  obtain ⟨Q,hQ,hs,f,hi,hd,hy,hw,_,_,hmass⟩ :=
    actual_ordinary_mass fam (algebraMap (ZMod prizeP) (AlgebraicClosure (ZMod prizeP)))
      (p := prizeP) (by decide) (Fintype.card_fin _) ht hbig
  exact False.elim ((h u Q f hQ hs hi hd hy hw).not_ge hmass)

#print axioms ordinary_agreement_count
#print axioms regular_fiber
#print axioms regular_sections
#print axioms actual_ordinary_mass
#print axioms secondPrime_threshold_of_ordinary_incidence_bound

end ProximityGap.ActualCubicHodgeIncidences
