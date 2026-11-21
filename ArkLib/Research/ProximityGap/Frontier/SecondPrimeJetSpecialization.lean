/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.BivariateVanishing
import ArkLib.Research.ProximityGap.Frontier.SecondPrimePolynomialJetColumns
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSectionResultant
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeActualPopulations
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSylvesterFiberMass

/-! # Polynomial jet constraints on actual selected sections -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeJetSpecialization

open Polynomial Finset SecondPrimeJetMultiplication SecondPrimePolynomialJetColumns
open SecondPrimeActualPopulations SecondPrimeQuarticInterpolation
open scoped NNReal

variable {K : Type} [Field K]

private noncomputable def shift {R : Type} [CommRing R] (p : R[X][X]) (a w : R) : R[X][X] :=
  (p.taylor (C w)).map (taylorAlgHom a).toRingHom

/-- The integral Taylor expansion at a received line, before fixing any scalar. -/
noncomputable abbrev localExpansion (p : K[X][X][X]) (a u v : K) : K[X][X][X] :=
  shift (p.map Bivariate.swap.toRingHom) (C a) (C u + Polynomial.X * C v)

/-- Membership of the auxiliary's truncated Taylor jet in the polynomial image of
multiplication by the component. The same witnesses specialize at every scalar. -/
def LocalMembership (f p : K[X][X][X]) (μ : ℕ) (a u v : K) : Prop :=
  ∃ ν, ∃ h : Jet ν → K[X], ∀ y : Jet μ,
    ((localExpansion p a u v).coeff y.val.1).coeff y.val.2 =
      ∑ x : Jet ν, h x * entry (localExpansion f a u v) x.val y.val

private theorem fiber_local (p : K[X][X][X]) (a u v z : K) :
    (localExpansion p a u v).map (mapRingHom (evalRingHom z)) =
      shift (p.map (evalRingHom (C z))) a (u + z * v) := by
  have hf : (p.map Bivariate.swap.toRingHom).map (mapRingHom (evalRingHom z)) =
      p.map (evalRingHom (C z)) := by
    ext1 i
    simp only [coeff_map, coe_mapRingHom]
    change (Bivariate.swap (p.coeff i)).map (evalRingHom z) = (p.coeff i).eval (C z)
    simpa only [Bivariate.evalY, Bivariate.evalX_eq_map] using
      (Bivariate.evalY_eq_evalX_swap z (p.coeff i)).symm
  have ht := map_taylor (p.map Bivariate.swap.toRingHom)
    (C (C u + Polynomial.X * C v)) (mapRingHom (evalRingHom z))
  rw [hf] at ht
  simp only [coe_mapRingHom, Polynomial.map_C, coe_evalRingHom, eval_add, eval_mul, eval_C,
    eval_X] at ht
  ext1 i
  have hi := congrArg (fun q : K[X][X] => q.coeff i) ht
  simp only [coeff_map, coe_mapRingHom] at hi
  simp only [localExpansion, shift, coeff_map, coe_mapRingHom, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, taylorAlgHom_apply]
  rw [map_taylor, hi]
  simp

private theorem eval_entry (p : K[X][X][X]) (z : K) (x y : ℕ × ℕ) :
    (entry p x y).eval z = entry (p.map (mapRingHom (evalRingHom z))) x y := by
  unfold entry
  split_ifs <;> simp [coeff_map]

private theorem zero_jet_graph (P : K[X][X]) (q : K[X]) (hq : q.eval 0 = 0) {μ : ℕ}
    (h : ∀ i j, i + j < μ → (P.coeff j).coeff i = 0) :
    (Polynomial.X : K[X]) ^ μ ∣ P.eval q := by
  have hv : ArkLib.GS.vanishesToOrder μ P 0 0 := by
    rw [ArkLib.GS.vanishesToOrder_iff_hasseCoeff]
    intro i j hij
    simpa only [ArkLib.GS.hasseCoeff_eq_innerTaylorCoeff_taylor, ArkLib.GS.innerTaylorCoeff,
      map_zero, taylor_zero, LinearMap.id_coe, id_eq] using h i j hij
  simpa only [map_zero, sub_zero] using hv.dvd_eval q hq

private theorem shift_graph (p : K[X][X]) (a w : K) (q : K[X]) :
    (shift p a w).eval ((q - C w).taylor a) = (p.eval q).taylor a := by
  change ((p.taylor (C w)).map (taylorAlgHom a).toRingHom).eval
    ((taylorAlgHom a).toRingHom (q - C w)) = _
  rw [eval_map_apply, taylor_eval_sub]
  rfl

/-- At a genuine agreement, integral local membership gives a root of multiplicity
μ after restricting the auxiliary to the actual component section. -/
theorem site (f p : K[X][X][X]) (μ : ℕ) (a u v z : K) (q : K[X])
    (hf : f.eval₂ (evalRingHom (C z)) q = 0) (hq : q.eval a = u + z * v)
    (h : LocalMembership f p μ a u v) :
    (Polynomial.X - C a) ^ μ ∣ p.eval₂ (evalRingHom (C z)) q := by
  classical
  obtain ⟨ν, b, hb⟩ := h
  let F := f.map (evalRingHom (C z))
  let P := p.map (evalRingHom (C z))
  let w := u + z * v
  let b' (i : Jet ν) := (b i).eval z
  let B := jetPolynomial ν b'
  let R := shift P a w - shift F a w * B
  have hlow (i j) (hij : i + j < μ) : (R.coeff j).coeff i = 0 := by
    let y : Jet μ := ⟨(j, i), GSMultInterp.mem_multIdx.mpr (by omega)⟩
    have hm := congrArg (Polynomial.eval z) (hb y)
    simp only [eval_finsetSum, eval_mul, eval_entry] at hm
    rw [fiber_local] at hm
    have hp := congrArg (fun U : K[X][X] => (U.coeff j).coeff i) (fiber_local p a u v z)
    simp only [coeff_map, coe_mapRingHom, coe_evalRingHom] at hp
    change (((localExpansion p a u v).coeff j).coeff i).eval z = _ at hm
    rw [hp] at hm
    rw [show (∑ x : Jet ν, (b x).eval z * entry (shift F a w) x.val y.val) =
      multiplyJet (shift F a w) ν μ b' y from (multiplyJet_apply _ _ _ _ _).symm] at hm
    change ((shift P a w).coeff j).coeff i = ((shift F a w * B).coeff j).coeff i at hm
    simpa only [R, coeff_sub, sub_eq_zero] using hm
  have hq' : ((q - C w).taylor a).eval 0 = 0 := by
    rw [← coeff_zero_eq_eval_zero, taylor_coeff_zero, eval_sub, eval_C, sub_eq_zero]
    exact hq
  have hd := zero_jet_graph R _ hq' hlow
  have hf' : F.eval q = 0 := by simpa only [F, eval_map] using hf
  change (Polynomial.X : K[X]) ^ μ ∣ (shift P a w - shift F a w * B).eval ((q - C w).taylor a) at hd
  rw [eval_sub, eval_mul, shift_graph, shift_graph, hf', map_zero, zero_mul, sub_zero] at hd
  have hh := map_dvd (taylorAlgHom (-a)) hd
  simpa only [map_pow, taylorAlgHom_apply, taylor_X, C_neg, ← sub_eq_add_neg, taylor_taylor,
    neg_add_cancel, taylor_zero, P, eval_map, LinearMap.id_coe, id_eq] using hh

private theorem surface_degree {s v d t : ℕ} (c : Monomials s v d t → K) (z : K) (q : K[X])
    (hq : q.natDegree ≤ d) (ht : 0 < t) :
    ((surface c).eval₂ (evalRingHom (C z)) q).natDegree < t := by
  rw [surface_eval]
  apply Nat.lt_of_le_pred ht
  rw [Nat.pred_eq_sub_one]
  apply natDegree_sum_le_of_forall_le
  intro m _
  have hj := (natDegree_pow_le (p := q) (n := m.1.val)).trans (Nat.mul_le_mul_left _ hq)
  have hi := m.2.2.isLt
  exact (natDegree_mul_le.trans (Nat.add_le_add (natDegree_monomial_le _) hj)).trans (by omega)

variable {I F : Type} [Fintype I] [Field F] [DecidableEq F]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- The full-multiplicity substitution at the actual coordinates forces every selected
section on the component to vanish on the supported auxiliary. -/
theorem selected_section (fam : Family dom δ u) (σ : F →+* K)
    (f : K[X][X][X]) {s v μ t : ℕ} (c : Monomials s v 67108863 (μ * t) → K)
    (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) (hpos : 0 < μ * t)
    (hloc : ∀ i, LocalMembership f (surface c) μ (σ (dom i)) (σ (u 0 i)) (σ (u 1 i)))
    (z : F) (hz : z ∈ population fam σ f) :
    (surface c).eval₂ (evalRingHom (C (σ z))) ((fam.q z).map σ) = 0 := by
  classical
  let P := (surface c).eval₂ (evalRingHom (C (σ z))) ((fam.q z).map σ)
  let A := HalfPredecessorLineCoreGeometry.fullAgreement dom (u 0) (u 1) z (fam.q z)
  let e : I ↪ K := dom.trans ⟨σ, σ.injective⟩
  let S := A.map e
  obtain ⟨hzG, hroot⟩ := mem_filter.mp hz
  have hdeg := fam.degree_lt z hzG
  have hd : P.natDegree < μ * t :=
    surface_degree c (σ z) ((fam.q z).map σ) (natDegree_map_le.trans (by omega)) hpos
  by_contra hn
  have h := SecondPrimeSylvesterFiberMass.fiber_mass_le (show P ≠ 0 from hn) S μ (fun a ha => by
    obtain ⟨i, hi, rfl⟩ := mem_map.mp ha
    apply site f (surface c) μ (σ (dom i)) (σ (u 0 i)) (σ (u 1 i)) (σ z) ((fam.q z).map σ)
      hroot _ (hloc i)
    simpa only [eval_map_apply, map_add, map_mul] using congrArg σ (mem_filter.mp hi).2)
  have hag : t ≤ S.card := (ht.trans (fam.threshold_le z hzG)).trans_eq (card_map e).symm
  have hsmall := Nat.mul_le_mul_right μ hag
  rw [Nat.mul_comm t μ] at hsmall
  omega

/-- Any sufficiently populous component divides every supported auxiliary satisfying the
polynomial local conditions at the actual sites. Together with a nonmultiple from the
global constraint system this gives a contradiction. -/
theorem divides_of_membership (fam : Family dom δ u) (σ : F →+* K)
    (f : K[X][X][X]) (hi : Irreducible f) (hb : 0 < f.natDegree)
    {s v μ t m : ℕ} (c : Monomials s v 67108863 (μ * t) → K) (hc : c ≠ 0)
    (hf : WeightedSylvesterDegree.TotalDegreeLe f m)
    (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) (hpos : 0 < μ * t)
    (hloc : ∀ i, LocalMembership f (surface c) μ (σ (dom i)) (σ (u 0 i)) (σ (u 1 i)))
    (hlarge : f.natDegree * s + (surface c).natDegree * m - f.natDegree * (surface c).natDegree
      < (population fam σ f).card) : f ∣ surface c := by
  classical
  have hs := SecondPrimeSectionResultant.factor_triangle (surface_ne_zero hc) (dvd_refl (surface c))
    (fun j i a h => (surface_support c h).2.1)
  exact SecondPrimeSectionResultant.divides_of_many_sections σ f (surface c) hi hb hf hs
    (population fam σ f) (fun z => (fam.q z).map σ) (fun z hz =>
      ⟨(mem_filter.mp hz).2, selected_section fam σ f c ht hpos hloc z hz⟩) hlarge

/-- The intrinsic cubic auxiliary with the written production parameters rules out the
entire 1431655733-label cubic: the resultant permits at most 1200000062 labels. -/
theorem cubic_population_le (fam : Family dom δ u) (σ : F →+* K)
    (f : K[X][X][X]) (hi : Irreducible f) (h3 : f.natDegree = 3)
    (hf : WeightedSylvesterDegree.TotalDegreeLe f 34)
    (c : Monomials 400000000 2 67108863 (64 * 357913943) → K) (hc : c ≠ 0)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hloc : ∀ i, LocalMembership f (surface c) 64 (σ (dom i)) (σ (u 0 i)) (σ (u 1 i))) :
    (population fam σ f).card ≤ 1200000062 := by
  classical
  have hy : (surface c).natDegree ≤ 2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i a
    simp only [coeff_zero]
    by_contra h
    exact hj.not_ge (surface_support c h).1
  by_contra! hlarge
  have hbound : f.natDegree * 400000000 + (surface c).natDegree * 34 -
      f.natDegree * (surface c).natDegree < (population fam σ f).card := by
    rw [h3]
    omega
  have hd := divides_of_membership fam σ f hi (by omega) c hc hf ht (by decide) hloc hbound
  have := natDegree_le_of_dvd hd (surface_ne_zero hc)
  omega

end ArkLib.ProximityGap.Frontier.SecondPrimeJetSpecialization
