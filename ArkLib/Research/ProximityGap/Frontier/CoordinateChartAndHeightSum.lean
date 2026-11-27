/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DiscriminantFactorSplit
import ArkLib.Research.ProximityGap.Frontier.PlaneBranchRegularity
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeMobiusSections
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeMobiusIrreducible
import ArkLib.Research.ProximityGap.Frontier.LogarithmicSectionHeights
import ArkLib.Research.ProximityGap.Frontier.RepeatedSectionSpecialization
import ArkLib.Research.ProximityGap.Frontier.SquarefreeCoordinateResultant
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCoordinateWeight
import ArkLib.Research.ProximityGap.Frontier.WeightedSylvesterDegree
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.SetTheory.Cardinal.Order

/-! # Coordinate charting, tangent height budget, and lost-agreement budget

This module implements Worker Packet L1c for the purely algebraic logarithmic section-height
engine:
1. Discarding singular fibers (`≤ G + 2 * b * m` labels) and applying a common Möbius coordinate
   chart `T = 1 / (X - r), Y ↦ T^d Y` (`SecondPrimeMobiusSections.surfaceChart`) preserving
   irreducibility (`SecondPrimeMobiusIrreducible.irreducible_surfaceChart`), total degree `≤ m`,
   weighted degree `≤ W₀ ≤ W`, and all received-line agreements.
2. Numerator degree bound `(tangentPair F' z q'_z).1.natDegree ≤ d + (tangentPair F' z q'_z).2.natDegree`
   from `SecondPrimeMobiusSections.derivative_graph_degree`.
3. Existence of coprime constant anchors `a, a' ∈ K` and the total denominator height bound
   `∑ z ∈ S_ret, (den z).natDegree ≤ 2 * A * G + 2 * W * m` via `PlaneBranchRegularity` (`D₁, D₂`)
   and `LogarithmicSectionHeights.two_resultant_height_budget`.
4. Per-site fiber factorization and `RepeatedSectionSpecialization.received_tangent` giving the
   total lost-agreement bound `≤ (G + m) * n`.
-/

set_option autoImplicit false
noncomputable section

open Finset Polynomial
open scoped BigOperators
open ArkLib.ProximityGap.NormalizedSectionSpecialization
open ArkLib.ProximityGap.HeightOneNormalization
open ArkLib.ProximityGap.RepeatedSectionSpecialization
open ArkLib.ProximityGap.Frontier.DiscriminantFactorSplit
open ArkLib.ProximityGap.Frontier.PlaneBranchRegularity
open ArkLib.ProximityGap.Frontier.SecondPrimeMobiusSections
open ArkLib.ProximityGap.Frontier.SecondPrimeMobiusIrreducible
open ArkLib.ProximityGap.Frontier.LogarithmicSectionHeights
open ArkLib.ProximityGap.Frontier.SecondPrimeCoordinateWeight
open ArkLib.ProximityGap.Frontier.WeightedSylvesterDegree

namespace ArkLib.ProximityGap.Frontier.CoordinateChartAndHeightSum

/-! ## Section 1: Elementary bivariate and resultant helpers -/

section BivariateHelpers

variable {K : Type} [Field K]

private lemma coeff_swap_coeff (P : K[X][X]) (a i : ℕ) :
    ((Bivariate.swap P).coeff a).coeff i = (P.coeff i).coeff a := by
  induction P using Polynomial.induction_on' generalizing a i with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n u =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, Bivariate.swap_C]
    have hswapX : Bivariate.swap (Polynomial.X : K[X][X]) = C Polynomial.X := Bivariate.swap_Y
    rw [hswapX, ← C_pow, mul_comm, coeff_C_mul, coeff_map, coeff_C_mul_X_pow]
    by_cases h : i = n
    · subst h; simp [coeff_X_pow]
    · simp [h, coeff_X_pow]

private lemma swap_map_evalRingHom (P : K[X][X]) (z : K) :
    (Bivariate.swap P).map (evalRingHom z) = P.eval (C z) := by
  simpa only [Bivariate.evalY, Bivariate.evalX_eq_map] using
    (Bivariate.evalY_eq_evalX_swap z P).symm

private lemma swap_coeff_natDegree_le (P : K[X][X]) (a : ℕ) :
    ((Bivariate.swap P).coeff a).natDegree ≤ P.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_swap_coeff, coeff_eq_zero_of_natDegree_lt hi, coeff_zero]

private lemma eval_map_C (V : K[X]) (z : K) : (V.map C).eval (C z) = C (V.eval z) := by
  simp [eval_map]

/-- A nonzero bivariate polynomial `P : K[X][X]` vanishes on at most `P.natDegree` fibers `Z = z`. -/
theorem card_eval_C_eq_zero_le [DecidableEq K] (P : K[X][X]) (hP : P ≠ 0) (S : Finset K) :
    (S.filter fun z => P.eval (C z) = 0).card ≤ P.natDegree := by
  have hsw : Bivariate.swap P ≠ 0 :=
    (map_ne_zero_iff _ Bivariate.swap.injective).mpr hP
  let a := (Bivariate.swap P).natDegree
  let g : K[X] := (Bivariate.swap P).coeff a
  have hg : g ≠ 0 := leadingCoeff_ne_zero.mpr hsw
  have hsub : S.filter (fun z => P.eval (C z) = 0) ⊆ g.roots.toFinset := by
    intro z hz
    have hev : P.eval (C z) = 0 := (Finset.mem_filter.mp hz).2
    rw [← swap_map_evalRingHom] at hev
    have hga : g.eval z = 0 := by
      have := congrArg (fun p : K[X] => p.coeff a) hev
      simpa [g, coeff_map, coe_evalRingHom] using this
    exact Multiset.mem_toFinset.mpr ((mem_roots hg).mpr hga)
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans ((card_roots' g).trans (swap_coeff_natDegree_le P a)))

/-- Away from `F.leadingCoeff * F.discr = 0`, any section `(z, q)` of `F` is simple (`F_Y(z, q) ≠ 0`). -/
theorem eval_deriv_ne_zero_of_discr_ne_zero (F : K[X][X][X]) (hb : 2 ≤ F.natDegree)
    (z : K) (q : K[X])
    (h₀ : (F.map (evalRingHom (C z))).eval q = 0)
    (hne : (F.leadingCoeff * F.discr).eval (C z) ≠ 0) :
    (F.derivative.map (evalRingHom (C z))).eval q ≠ 0 := by
  set b := F.natDegree
  obtain ⟨P, Q, _, _, hbez⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    (m := b) (n := b - 1) F F.derivative le_rfl (natDegree_derivative_le F) (by omega)
  have hres : resultant F F.derivative b (b - 1) =
      (-1) ^ (b * (b - 1) / 2) * (F.leadingCoeff * F.discr) := by
    have hpos : 0 < F.degree := natDegree_pos_iff_degree_pos.mp (by omega)
    rw [Polynomial.resultant_deriv hpos]
    ring
  rw [hres] at hbez
  have hev := congrArg (fun p : K[X][X][X] => (p.map (evalRingHom (C z))).eval q) hbez
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, eval_add, eval_mul, eval_C,
    h₀, zero_mul, zero_add, coe_evalRingHom, eval_pow, eval_neg, eval_one] at hev
  intro hdz
  rw [hdz, zero_mul] at hev
  rw [eval_mul] at hne
  have hsign : ((-1 : K[X]) ^ (b * (b - 1) / 2)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  exact mul_ne_zero hsign hne hev.symm

private lemma chart_ne_zero' (r : K) (D : ℕ) {p : K[X]} (hp : p ≠ 0) :
    SecondPrimeMobiusSections.chart r D p ≠ 0 := by
  change (p.taylor r).reflect D ≠ 0
  exact fun h => hp ((taylorEquiv r).injective (by simpa using reflect_eq_zero_iff.mp h))

/-- In `K[Z][X]`, relatively prime nonzero polynomials remain coprime over `FractionRing K[Z]`. -/
theorem isCoprime_map_fractionRing_of_isRelPrime {P Q : K[X][X]}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hrel : IsRelPrime P Q) :
    IsCoprime (P.map (algebraMap K[X] (FractionRing K[X])))
      (Q.map (algebraMap K[X] (FractionRing K[X]))) := by
  classical
  let L := FractionRing K[X]
  let φ := algebraMap K[X] L
  have hinj : Function.Injective φ := IsFractionRing.injective K[X] L
  have hP' : P.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hP
  have hQ' : Q.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hQ
  by_contra hnot
  have hgne : EuclideanDomain.gcd (P.map φ) (Q.map φ) ≠ 0 :=
    fun hz => hP' (zero_dvd_iff.mp (hz ▸ EuclideanDomain.gcd_dvd_left _ _))
  have hgnu : ¬ IsUnit (EuclideanDomain.gcd (P.map φ) (Q.map φ)) := by
    intro hu
    apply hnot
    obtain ⟨u, hu'⟩ := hu
    refine ⟨EuclideanDomain.gcdA (P.map φ) (Q.map φ) * (↑u⁻¹ : L[X]),
      EuclideanDomain.gcdB (P.map φ) (Q.map φ) * (↑u⁻¹ : L[X]), ?_⟩
    have hbez := EuclideanDomain.gcd_eq_gcd_ab (P.map φ) (Q.map φ)
    rw [← hu'] at hbez
    calc (EuclideanDomain.gcdA (P.map φ) (Q.map φ) * (↑u⁻¹ : L[X])) * P.map φ +
          (EuclideanDomain.gcdB (P.map φ) (Q.map φ) * (↑u⁻¹ : L[X])) * Q.map φ
        = (P.map φ * EuclideanDomain.gcdA (P.map φ) (Q.map φ) +
            Q.map φ * EuclideanDomain.gcdB (P.map φ) (Q.map φ)) * (↑u⁻¹ : L[X]) := by ring
      _ = (u : L[X]) * (↑u⁻¹ : L[X]) := by rw [← hbez]
      _ = 1 := Units.mul_inv u
  obtain ⟨f, hfirr, hfgcd⟩ := WfDvdMonoid.exists_irreducible_factor hgnu hgne
  have hfP : f ∣ P.map φ := hfgcd.trans (EuclideanDomain.gcd_dvd_left _ _)
  have hfQ : f ∣ Q.map φ := hfgcd.trans (EuclideanDomain.gcd_dvd_right _ _)
  have hfdeg : 0 < f.natDegree := by
    by_contra h0
    have hdeg0 : f.natDegree = 0 := by omega
    have hfne : f ≠ 0 := hfirr.ne_zero
    rw [eq_C_of_natDegree_eq_zero hdeg0] at hfne hfirr
    exact hfirr.not_isUnit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (C_ne_zero.mp hfne)))
  -- Clear denominators of `f` into `K[X][X]` and take primitive part
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors K[X])
    (f.support.image f.coeff)
  let g : K[X][X] := ∑ j ∈ f.support,
    if hj : j ∈ f.support then
      monomial j (Classical.choose (hd (f.coeff j) (Finset.mem_image_of_mem _ hj)))
    else 0
  have hgmap : g.map φ = C (φ d) * f := by
    ext j
    rw [coeff_map, coeff_C_mul]
    by_cases hj : j ∈ f.support
    · have hspec := Classical.choose_spec (hd (f.coeff j) (Finset.mem_image_of_mem _ hj))
      simp only [g, finsetSum_coeff]
      rw [Finset.sum_eq_single j]
      · simp only [hj, ↓reduceDIte, coeff_monomial, ↓reduceIte]
        simpa only [Algebra.smul_def] using hspec
      · intro k hk hne
        simp only [hk, ↓reduceDIte, coeff_monomial, hne, ↓reduceIte]
      · intro hnot'; exact absurd hj hnot'
    · have hfj : f.coeff j = 0 := notMem_support_iff.mp hj
      simp only [g, finsetSum_coeff, hfj, mul_zero]
      rw [Finset.sum_eq_zero, map_zero]
      intro k hk
      have hne : k ≠ j := fun heq => hj (heq ▸ hk)
      simp only [hk, ↓reduceDIte, coeff_monomial, hne, ↓reduceIte]
  have hd0 : φ d ≠ 0 :=
    (map_ne_zero_iff φ hinj).mpr (nonZeroDivisors.ne_zero d.2)
  have hgne' : g ≠ 0 := by
    intro hz
    rw [hz, Polynomial.map_zero] at hgmap
    exact mul_ne_zero (C_ne_zero.mpr hd0) hfirr.ne_zero hgmap.symm
  let r : K[X][X] := g.primPart
  have hrprim : r.IsPrimitive := isPrimitive_primPart g
  have hrg : C g.content * r = g := g.eq_C_content_mul_primPart.symm
  have hgc0 : g.content ≠ 0 := content_eq_zero_iff.not.mpr hgne'
  have hrmap_dvd_f : r.map φ ∣ f := by
    refine ⟨C ((φ d)⁻¹ * φ g.content), ?_⟩
    have hm := congrArg (Polynomial.map φ) hrg
    rw [Polynomial.map_mul, map_C, hgmap] at hm
    have hmul : C (φ d) * f = C (φ g.content) * r.map φ := hm.symm
    have h1 := congrArg (fun p : L[X] => C (φ d)⁻¹ * p) hmul
    simp only [← mul_assoc, ← C_mul, inv_mul_cancel₀ hd0, C_1, one_mul] at h1
    rw [h1, mul_comm (r.map φ)]
  have hf_dvd_rmap : f ∣ r.map φ := by
    refine ⟨C (φ d * (φ g.content)⁻¹), ?_⟩
    have hm := congrArg (Polynomial.map φ) hrg
    rw [Polynomial.map_mul, map_C, hgmap] at hm
    have hgcL : φ g.content ≠ 0 := (map_ne_zero_iff φ hinj).mpr hgc0
    have h1 := congrArg (fun p : L[X] => C (φ g.content)⁻¹ * p) hm
    simp only [← mul_assoc, ← C_mul, inv_mul_cancel₀ hgcL, C_1, one_mul] at h1
    rw [h1, mul_comm (φ g.content)⁻¹, mul_comm]
  have hrP : r ∣ P :=
    (hrprim.dvd_iff_fraction_map_dvd_fraction_map L).mpr (hrmap_dvd_f.trans hfP)
  have hrQ : r ∣ Q :=
    (hrprim.dvd_iff_fraction_map_dvd_fraction_map L).mpr (hrmap_dvd_f.trans hfQ)
  have hrunit : IsUnit r := hrel hrP hrQ
  have hrmap_unit : IsUnit (r.map φ) := hrunit.map (Polynomial.mapRingHom φ)
  exact hfirr.not_isUnit (isUnit_of_dvd_unit hf_dvd_rmap hrmap_unit)

/-- Relatively prime nonzero polynomials in `K[Z][X]` have nonzero resultant. -/
theorem resultant_ne_zero_of_isRelPrime {P Q : K[X][X]}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hrel : IsRelPrime P Q) :
    resultant P Q P.natDegree Q.natDegree ≠ 0 := by
  let L := FractionRing K[X]
  let φ := algebraMap K[X] L
  have hinj : Function.Injective φ := IsFractionRing.injective K[X] L
  have hcop := isCoprime_map_fractionRing_of_isRelPrime hP hQ hrel
  have hr := Polynomial.resultant_ne_zero _ _ hcop
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
    resultant_map_map] at hr
  exact fun hz => hr (by rw [hz, map_zero])

/-- GCD factoring lemma in `K[X]`: if `d` divides `a₁*b₁, a₂*b₁, a₁*b₂, a₂*b₂`, then
`d ∣ EuclideanDomain.gcd a₁ a₂ * EuclideanDomain.gcd b₁ b₂`. -/
theorem dvd_gcd_mul_gcd [DecidableEq K] {d a₁ a₂ b₁ b₂ : K[X]}
    (h11 : d ∣ a₁ * b₁) (h21 : d ∣ a₂ * b₁)
    (h12 : d ∣ a₁ * b₂) (h22 : d ∣ a₂ * b₂) :
    d ∣ EuclideanDomain.gcd a₁ a₂ * EuclideanDomain.gcd b₁ b₂ := by
  rw [EuclideanDomain.gcd_eq_gcd_ab a₁ a₂, EuclideanDomain.gcd_eq_gcd_ab b₁ b₂]
  have heq : (a₁ * EuclideanDomain.gcdA a₁ a₂ + a₂ * EuclideanDomain.gcdB a₁ a₂) *
      (b₁ * EuclideanDomain.gcdA b₁ b₂ + b₂ * EuclideanDomain.gcdB b₁ b₂) =
      (a₁ * b₁) * (EuclideanDomain.gcdA a₁ a₂ * EuclideanDomain.gcdA b₁ b₂) +
      (a₂ * b₁) * (EuclideanDomain.gcdB a₁ a₂ * EuclideanDomain.gcdA b₁ b₂) +
      (a₁ * b₂) * (EuclideanDomain.gcdA a₁ a₂ * EuclideanDomain.gcdB b₁ b₂) +
      (a₂ * b₂) * (EuclideanDomain.gcdB a₁ a₂ * EuclideanDomain.gcdB b₁ b₂) := by ring
  rw [heq]
  exact dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_left h11 _) (dvd_mul_of_dvd_left h21 _))
    (dvd_mul_of_dvd_left h12 _)) (dvd_mul_of_dvd_left h22 _)

end BivariateHelpers

/-! ## Section 2: Coprime constant anchors and denominator height sum -/

section AnchorsAndHeight

variable {K : Type} [Field K]

/-- Existence of coprime constant anchors `a, a' ∈ K` for an irreducible surface `F : K[X][X][X]`
with `2 ≤ F.natDegree`, avoiding all section fibers `z ∈ S`. -/
theorem exists_coprime_anchors [Infinite K] (F : K[X][X][X])
    (hFirr : Irreducible F) (hb : 2 ≤ F.natDegree)
    (S : Finset K) (hFlead : ∀ z ∈ S, F.leadingCoeff.eval (C z) ≠ 0) :
    ∃ a a' : K,
      F.eval (C (C a)) ≠ 0 ∧ F.eval (C (C a')) ≠ 0 ∧
      (∀ z ∈ S, (F.eval (C (C a))).eval (C z) ≠ 0) ∧
      (∀ z ∈ S, (F.eval (C (C a'))).eval (C z) ≠ 0) ∧
      IsRelPrime (F.eval (C (C a))) (F.eval (C (C a'))) := by
  classical
  have hFne : F ≠ 0 := hFirr.ne_zero
  have hprim : F.IsPrimitive := hFirr.isPrimitive (by omega)
  have hFz_ne : ∀ z ∈ S, F.map (evalRingHom (C z)) ≠ 0 := by
    intro z hz h0
    have := congrArg (fun p : K[X][X] => p.coeff F.natDegree) h0
    rw [coeff_map, coeff_zero] at this
    exact hFlead z hz this
  let cToBase : K →+* K[X] := C
  have hc_inj : Function.Injective cToBase := C_injective
  let cToPlane : K →+* K[X][X] := C.comp C
  have hcp_inj : Function.Injective cToPlane := C_injective.comp C_injective
  let badS : Finset K :=
    S.biUnion (fun z => ((F.map (evalRingHom (C z))).roots.toFinset).preimage cToBase hc_inj.injOn) ∪
    (F.roots.toFinset).preimage cToPlane hcp_inj.injOn
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset badS
  have ha_ne : F.eval (C (C a)) ≠ 0 := by
    intro hz
    exact ha (Finset.mem_union_right _ (Finset.mem_preimage.mpr
      (Multiset.mem_toFinset.mpr ((mem_roots hFne).mpr hz))))
  have ha_S : ∀ z ∈ S, (F.eval (C (C a))).eval (C z) ≠ 0 := by
    intro z hz hev
    have hev' : (F.map (evalRingHom (C z))).eval (C a) = 0 := by
      have hcomm := Polynomial.hom_eval₂ F (RingHom.id _) (evalRingHom (C z)) (C (C a))
      simpa [eval_map, eval₂_id] using hcomm.symm.trans hev
    exact ha (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨z, hz,
      Finset.mem_preimage.mpr (Multiset.mem_toFinset.mpr ((mem_roots (hFz_ne z hz)).mpr hev'))⟩))
  -- Avoid every irreducible factor `p` of `F.eval (C (C a))`
  let facs : Finset K[X][X] := (UniqueFactorizationMonoid.factors (F.eval (C (C a)))).toFinset
  have hbad_fac : ∀ p : K[X][X], Irreducible p →
      ∃ T : Finset K, ∀ a' : K, p ∣ F.eval (C (C a')) → a' ∈ T := by
    intro p hp
    have hprime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
    let I : Ideal K[X][X] := Ideal.span {p}
    have hIprime : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hprime
    let Q := K[X][X] ⧸ I
    let mk : K[X][X] →+* Q := Ideal.Quotient.mk I
    have hFmap_ne : F.map mk ≠ 0 := by
      intro hz
      have hpall : ∀ j, p ∣ F.coeff j := by
        intro j
        have h0 := congrArg (fun g : Q[X] => g.coeff j) hz
        rw [coeff_map, coeff_zero] at h0
        exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
      exact hprime.not_isUnit (hprim p ((C_dvd_iff_dvd_coeff p F).mpr hpall))
    let kToQ : K →+* Q := mk.comp cToPlane
    have hkQ_inj : Function.Injective kToQ := by
      have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hIprime.ne_top
      exact kToQ.injective
    refine ⟨((F.map mk).roots.toFinset).preimage kToQ hkQ_inj.injOn, fun a' hdvd => ?_⟩
    refine Finset.mem_preimage.mpr (Multiset.mem_toFinset.mpr ((mem_roots hFmap_ne).mpr ?_))
    have h0 : mk (F.eval (C (C a'))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdvd)
    have hcomm := Polynomial.hom_eval₂ F (RingHom.id _) mk (C (C a'))
    simpa [kToQ, cToPlane, eval_map, eval₂_id] using hcomm.symm.trans h0
  let badFac : Finset K :=
    facs.biUnion (fun p => if hp : Irreducible p then Classical.choose (hbad_fac p hp) else ∅)
  obtain ⟨a', ha'⟩ := Infinite.exists_notMem_finset (badS ∪ badFac)
  have ha'S_not : a' ∉ badS := fun h => ha' (Finset.mem_union_left _ h)
  have ha'F_not : a' ∉ badFac := fun h => ha' (Finset.mem_union_right _ h)
  have ha'_ne : F.eval (C (C a')) ≠ 0 := by
    intro hz
    exact ha'S_not (Finset.mem_union_right _ (Finset.mem_preimage.mpr
      (Multiset.mem_toFinset.mpr ((mem_roots hFne).mpr hz))))
  have ha'_S : ∀ z ∈ S, (F.eval (C (C a'))).eval (C z) ≠ 0 := by
    intro z hz hev
    have hev' : (F.map (evalRingHom (C z))).eval (C a') = 0 := by
      have hcomm := Polynomial.hom_eval₂ F (RingHom.id _) (evalRingHom (C z)) (C (C a'))
      simpa [eval_map, eval₂_id] using hcomm.symm.trans hev
    exact ha'S_not (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨z, hz,
      Finset.mem_preimage.mpr (Multiset.mem_toFinset.mpr ((mem_roots (hFz_ne z hz)).mpr hev'))⟩))
  refine ⟨a, a', ha_ne, ha'_ne, ha_S, ha'_S, ?_⟩
  intro d hd1 hd2
  by_contra hdu
  obtain ⟨p, hpirr, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hdu
    (ne_zero_of_dvd_ne_zero ha_ne hd1)
  have hp1 : p ∣ F.eval (C (C a)) := hpd.trans hd1
  have hp2 : p ∣ F.eval (C (C a')) := hpd.trans hd2
  obtain ⟨q, hqmem, hqassoc⟩ :=
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd ha_ne hpirr hp1
  have hqirr : Irreducible q := UniqueFactorizationMonoid.irreducible_of_factor q hqmem
  have hq2 : q ∣ F.eval (C (C a')) := hqassoc.symm.dvd.trans hp2
  have ha'_in : a' ∈ Classical.choose (hbad_fac q hqirr) :=
    Classical.choose_spec (hbad_fac q hqirr) a' hq2
  exact ha'F_not (Finset.mem_biUnion.mpr ⟨q, Multiset.mem_toFinset.mpr hqmem, by
    simp [hqirr, ha'_in]⟩)

/-- **Total tangent-denominator height bound**: for an irreducible surface `F : K[X][X][X]`
of value degree `b ≥ 2`, total degree `≤ m`, weighted degree `≤ W`, and simple sections
`(z, q z)` on `S` where `(F.leadingCoeff * F.discr)(X, z) ≠ 0`, the sum of reduced denominator
degrees satisfies `∑ z ∈ S, (den z).natDegree ≤ 2 * A * G + 2 * W * m`. -/
theorem total_denominator_height_le [Infinite K]
    (F : K[X][X][X]) {d W m : ℕ}
    (hFirr : Irreducible F) (hb : 2 ≤ F.natDegree)
    (hTot : ∀ j i a, ((F.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ m)
    (hWt : ∀ j i a, ((F.coeff j).coeff i).coeff a ≠ 0 → a + j * d ≤ W)
    (hchar : ∀ r : ℕ, 0 < r →
      r ≤ max ((2 * F.natDegree - 2) * W - F.natDegree * (F.natDegree - 1) * d) F.natDegree →
      (r : K) ≠ 0)
    (S : Finset K) (q : K → K[X])
    (hF0 : ∀ z ∈ S, (F.map (evalRingHom (C z))).eval (q z) = 0)
    (hFgood : ∀ z ∈ S, (F.leadingCoeff * F.discr).eval (C z) ≠ 0) :
    let L := FractionRing K[X]
    let A := (2 * F.natDegree - 2) * W - F.natDegree * (F.natDegree - 1) * d
    let G := (2 * F.natDegree - 2) * m - F.natDegree * (F.natDegree - 1)
    ∑ z ∈ S, ((tangentPair (L := L) F z (q z)).2).natDegree ≤ 2 * A * G + 2 * W * m := by
  classical
  let L := FractionRing K[X]
  set b := F.natDegree
  set A := (2 * b - 2) * W - b * (b - 1) * d
  set G := (2 * b - 2) * m - b * (b - 1)
  have hchar_b : ∀ r : ℕ, 0 < r → r ≤ b → (r : K) ≠ 0 :=
    fun r hr hle => hchar r hr (hle.trans (le_max_right _ _))
  have hchar_A : ∀ r : ℕ, 0 < r → r ≤ A → (r : K) ≠ 0 :=
    fun r hr hle => hchar r hr (hle.trans (le_max_left _ _))
  have hdiscr_ne : F.discr ≠ 0 := discr_ne_zero F hFirr hb (hchar_b b (by omega) le_rfl)
  have hdiscr_Z : F.discr.natDegree ≤ G := discr_natDegree_le F hb hTot
  have hdiscr_X : Bivariate.degreeX F.discr ≤ A := discr_degreeX_le F hb hWt
  obtain ⟨V, U, H, hV0, hU0, hH0, hsq_all, hdvd_all, hsplit, hVZ_le, hUX_le,
      hHprim, _, hHz_all⟩ := factor_split F.discr hdiscr_ne
  have hHsq : Squarefree H := hsq_all.of_mul_right
  have hVdvd : V.map C ∣ F.discr := (dvd_mul_right _ _).trans ((dvd_mul_right _ _).trans hdvd_all)
  have hHdvd : H ∣ F.discr := (dvd_mul_left _ _).trans hdvd_all
  have : Fact (Irreducible (F.map (genericCoeffs (R := K[X]) (L := L)))) :=
    ⟨irreducible_map_genericCoeffs F hFirr (by omega)⟩
  obtain ⟨D₁, hδ₁, hD₁⟩ := exists_regular_logDerivZ (L := L) F hFirr hb hchar_b hU0 hsplit
  obtain ⟨D₂, hδ₂, hD₂⟩ := exists_regular_logDerivJac (L := L) F hFirr hb hchar_b hsplit
  have hFlead : ∀ z ∈ S, F.leadingCoeff.eval (C z) ≠ 0 := fun z hz h0 =>
    hFgood z hz (by rw [eval_mul, h0, zero_mul])
  have hFdiscr_z : ∀ z ∈ S, F.discr.eval (C z) ≠ 0 := fun z hz h0 =>
    hFgood z hz (by rw [eval_mul, h0, mul_zero])
  have hFder : ∀ z ∈ S, (F.derivative.map (evalRingHom (C z))).eval (q z) ≠ 0 :=
    fun z hz => eval_deriv_ne_zero_of_discr_ne_zero F hb z (q z) (hF0 z hz) (hFgood z hz)
  obtain ⟨a, a', ha_ne, ha'_ne, ha_S, ha'_S, hrel_aa'⟩ :=
    exists_coprime_anchors F hFirr hb S hFlead
  have hroot_ne : ∀ c : K, F.eval (C (C c)) ≠ 0 →
      AdjoinRoot.root (F.map (genericCoeffs (R := K[X]) (L := L))) ≠
        planeBase (L := L) F (C (C c)) := by
    intro c hc heq
    have hY0 : F.eval₂ (planeBase (L := L) F)
        (AdjoinRoot.root (F.map (genericCoeffs (R := K[X]) (L := L)))) = 0 := by
      change F.eval₂ ((AdjoinRoot.of _).comp _) _ = 0
      rw [← eval₂_map]
      exact AdjoinRoot.eval₂_root _
    rw [heq, eval₂_at_apply] at hY0
    have hinj : Function.Injective (planeBase (L := L) F) := by
      change Function.Injective ((algebraMap (FractionRing L[X]) (Curve (L := L) F)).comp
        (genericCoeffs (R := K[X]) (L := L)))
      refine (algebraMap (FractionRing L[X]) (Curve (L := L) F)).injective.comp ?_
      change Function.Injective ((algebraMap L[X] (FractionRing L[X])).comp
        (Polynomial.mapRingHom (algebraMap K[X] L)))
      exact (IsFractionRing.injective L[X] (FractionRing L[X])).comp
        (Polynomial.map_injective _ (IsFractionRing.injective K[X] L))
    exact hc (hinj (hY0.trans (map_zero _).symm))
  let Aa : K[X][X] := F.eval (C (C a))
  let Aa' : K[X][X] := F.eval (C (C a'))
  let P : K[X][X] := Bivariate.swap Aa
  let Q : K[X][X] := Bivariate.swap Aa'
  have hPne : P ≠ 0 := (map_ne_zero_iff _ Bivariate.swap.injective).mpr ha_ne
  have hQne : Q ≠ 0 := (map_ne_zero_iff _ Bivariate.swap.injective).mpr ha'_ne
  have hPQ_rel : IsRelPrime P Q := by
    intro r hr1 hr2
    have h1 : Bivariate.swap.symm r ∣ Aa := by
      simpa [P, Bivariate.swap_swap_apply] using map_dvd Bivariate.swap.symm.toRingHom hr1
    have h2 : Bivariate.swap.symm r ∣ Aa' := by
      simpa [Q, Bivariate.swap_swap_apply] using map_dvd Bivariate.swap.symm.toRingHom hr2
    have hu : IsUnit (Bivariate.swap.symm r) := hrel_aa' h1 h2
    simpa using hu.map Bivariate.swap.toRingHom
  have hPQ_res : resultant P Q P.natDegree Q.natDegree ≠ 0 :=
    resultant_ne_zero_of_isRelPrime hPne hQne hPQ_rel
  -- Degree bounds for `Aa` and `Aa'` (hence `P` and `Q`)
  have hEval_bounds : ∀ c : K,
      Bivariate.degreeX (F.eval (C (C c))) ≤ W ∧ (F.eval (C (C c))).natDegree ≤ m := by
    intro c
    have hcoeff_X : ∀ i k, ((F.eval (C (C c))).coeff i).coeff k ≠ 0 → k ≤ W ∧ i ≤ m := by
      intro i k hne
      rw [eval_eq_sum_range, finsetSum_coeff, finsetSum_coeff] at hne
      obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      rw [← C_pow, ← C_pow, coeff_mul_C, coeff_mul_C] at hj
      have h0 : ((F.coeff j).coeff i).coeff k ≠ 0 := left_ne_zero_of_mul hj
      have h1 := hWt j i k h0
      have h2 := hTot j i k h0
      omega
    refine ⟨?_, ?_⟩
    · by_cases hz : F.eval (C (C c)) = 0
      · simp [hz, Bivariate.degreeX]
      · obtain ⟨i, hi, heq, _⟩ := Bivariate.exists_max_index_degreeX _ hz
        rw [← heq]
        exact (hcoeff_X i _ (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi))).1
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro i hi
      by_contra hne
      exact absurd (hcoeff_X i _ (leadingCoeff_ne_zero.mpr hne)).2 (by omega)
  have hP_deg : P.natDegree ≤ W := by
    rw [show P.natDegree = Bivariate.degreeX Aa from Bivariate.natDegreeY_swap Aa]
    exact (hEval_bounds a).1
  have hQ_deg : Q.natDegree ≤ W := by
    rw [show Q.natDegree = Bivariate.degreeX Aa' from Bivariate.natDegreeY_swap Aa']
    exact (hEval_bounds a').1
  have hP_coeff : ∀ j, (P.coeff j).natDegree ≤ m :=
    fun j => (swap_coeff_natDegree_le Aa j).trans (hEval_bounds a).2
  have hQ_coeff : ∀ j, (Q.coeff j).natDegree ≤ m :=
    fun j => (swap_coeff_natDegree_le Aa' j).trans (hEval_bounds a').2
  -- Cancel `V(z) ≠ 0` on every `z ∈ S`
  have hVz : ∀ z ∈ S, V.eval z ≠ 0 := by
    intro z hz hvz
    obtain ⟨qV, hqV⟩ := hVdvd
    have h0 := congrArg (fun p : K[X][X] => p.eval (C z)) hqV
    rw [eval_mul, eval_map_C, hvz, C_0, zero_mul] at h0
    exact hFdiscr_z z hz h0
  have hHz_ne : ∀ z ∈ S, H.eval (C z) ≠ 0 := by
    intro z hz hhz
    obtain ⟨qH, hqH⟩ := hHdvd
    have h0 := congrArg (fun p : K[X][X] => p.eval (C z)) hqH
    rw [eval_mul, hhz, zero_mul] at h0
    exact hFdiscr_z z hz h0
  let den : K → K[X] := fun z => (tangentPair (L := L) F z (q z)).2
  have hdvd_H : ∀ z ∈ S, ∀ c : K, F.eval (C (C c)) ≠ 0 →
      den z ∣ (F.eval (C (C c))).eval (C z) * H.eval (C z) := by
    intro z hz c hc
    have h1 := tangentPair_den_dvd_of_logDerivZ (L := L) F (V.map C * H) D₁ hD₁ hδ₁ z (q z)
      (hFlead z hz) (hF0 z hz) (hFder z hz) (C (C c)) (hroot_ne c hc)
    rw [eval_mul, eval_map_C] at h1
    have hu : IsUnit (C (V.eval z) : K[X]) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr (hVz z hz))
    have h2 : den z ∣ C (V.eval z) * ((F.eval (C (C c))).eval (C z) * H.eval (C z)) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h1
    exact (hu.dvd_mul_left).mp h2
  have hdvd_J : ∀ z ∈ S, ∀ c : K, F.eval (C (C c)) ≠ 0 →
      den z ∣ (F.eval (C (C c))).eval (C z) * (U * (partialX K H).eval (C z)) := by
    intro z hz c hc
    have h1 := tangentPair_den_dvd_of_logDerivJac (L := L) F U (V.map C * H) D₂ hD₂ hδ₂ z (q z)
      (hFlead z hz) (hF0 z hz) (hFder z hz) (C (C c)) (hroot_ne c hc)
    have hpx : partialX K (V.map C * H) = V.map C * partialX K H := by
      rw [(partialX K).leibniz, partialX_map_C]
      simp [smul_eq_mul]
    rw [hpx, eval_mul, eval_map_C] at h1
    have hu : IsUnit (C (V.eval z) : K[X]) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr (hVz z hz))
    have h2 : den z ∣ C (V.eval z) * ((F.eval (C (C c))).eval (C z) * (U * (partialX K H).eval (C z))) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h1
    exact (hu.dvd_mul_left).mp h2
  -- Case split on `Bivariate.degreeX H = 0` vs `0 < Bivariate.degreeX H`
  by_cases hHdeg0 : Bivariate.degreeX H = 0
  · -- `H` is a nonzero constant in `K`, so `H.eval (C z)` is a unit in `K[X]`!
    have hH_const_unit : ∀ z ∈ S, IsUnit (H.eval (C z)) := by
      intro z hz
      have hdeg0 : (H.eval (C z)).natDegree = 0 := by
        rw [← swap_map_evalRingHom]
        refine Nat.eq_zero_of_le_zero (natDegree_map_le.trans ?_)
        rw [show (Bivariate.swap H).natDegree = Bivariate.degreeX H from Bivariate.natDegreeY_swap H,
          hHdeg0]
      rw [eq_C_of_natDegree_eq_zero hdeg0]
      exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr fun h0 =>
        hHz_ne z hz (by rw [eq_C_of_natDegree_eq_zero hdeg0, h0, C_0]))
    have hdiv_PQ : ∀ z ∈ S, den z ∣ P.map (evalRingHom z) ∧ den z ∣ Q.map (evalRingHom z) := by
      intro z hz
      rw [swap_map_evalRingHom, swap_map_evalRingHom]
      exact ⟨((hH_const_unit z hz).dvd_mul_right).mp (hdvd_H z hz a ha_ne),
        ((hH_const_unit z hz).dvd_mul_right).mp (hdvd_H z hz a' ha'_ne)⟩
    have hP_S : ∀ z ∈ S, P.map (evalRingHom z) ≠ 0 := by
      intro z hz; rw [swap_map_evalRingHom]; exact ha_S z hz
    have hsum := total_common_factor_degree P Q hPQ_res S den hP_S hdiv_PQ
    have hres_deg := natDegree_resultant_le_of_coeff_natDegree_le P Q P.natDegree Q.natDegree m m
      hP_coeff hQ_coeff
    have hle : Q.natDegree * m + P.natDegree * m ≤ 2 * W * m := by
      have h1 := Nat.mul_le_mul_right m hP_deg
      have h2 := Nat.mul_le_mul_right m hQ_deg
      have h2Wm : 2 * W * m = W * m + W * m := by ring
      omega
    exact (hsum.trans (hres_deg.trans hle)).trans (Nat.le_add_left _ _)
  · -- Main case: `0 < Bivariate.degreeX H`, apply `two_resultant_height_budget`
    have hHpos : 0 < Bivariate.degreeX H := Nat.pos_of_ne_zero hHdeg0
    let Hsw : K[X][X] := Bivariate.swap H
    let Ksw : K[X][X] := Bivariate.swap (C U * partialX K H)
    have hHsw_deg : Hsw.natDegree = Bivariate.degreeX H := Bivariate.natDegreeY_swap H
    have hHsw_le : Hsw.natDegree ≤ A := hHsw_deg ▸ (Nat.le_add_left _ _).trans (hUX_le.trans hdiscr_X)
    have hKsw_eq : Ksw = U.map C * Hsw.derivative := by
      dsimp [Ksw, Hsw]
      rw [map_mul, Bivariate.swap_C, swap_partialX]
    have hHsw_sq : Squarefree Hsw := by
      intro x hx
      have h' : Bivariate.swap.symm x * Bivariate.swap.symm x ∣ H := by
        simpa [Hsw, map_mul, Bivariate.swap_swap_apply] using map_dvd Bivariate.swap.symm.toRingHom hx
      have hu := hHsq (Bivariate.swap.symm x) h'
      simpa using hu.map Bivariate.swap.toRingHom
    have hHsw_der_res :
        resultant Hsw Hsw.derivative Hsw.natDegree (Hsw.natDegree - 1) ≠ 0 :=
      ProximityGap.SquarefreeCoordinateResultant.squarefree_resultant_ne_zero Hsw hHsw_sq
        (hHsw_deg ▸ hHpos) (fun i hi hle => hchar_A i hi (hle.trans hHsw_le))
    -- `Hsw` and `Ksw = U.map C * Hsw.derivative` are coprime over `FractionRing K[Z]`
    have hHsw_U_rel : IsRelPrime Hsw (U.map C) := by
      intro r hr1 hr2
      have h1 : Bivariate.swap.symm r ∣ H := by
        simpa [Hsw, Bivariate.swap_swap_apply] using map_dvd Bivariate.swap.symm.toRingHom hr1
      have h2 : Bivariate.swap.symm r ∣ C U := by
        have hswapU : Bivariate.swap (C U) = U.map C := Bivariate.swap_C U
        simpa [← hswapU, Bivariate.swap_swap_apply] using map_dvd Bivariate.swap.symm.toRingHom hr2
      by_contra hru
      have hru' : ¬ IsUnit (Bivariate.swap.symm r) := fun hu =>
        hru (by simpa using hu.map Bivariate.swap.toRingHom)
      obtain ⟨p, hpirr, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hru'
        (ne_zero_of_dvd_ne_zero hH0 h1)
      have hpC : p ∣ C U := hpd.trans h2
      have hpH : p ∣ H := hpd.trans h1
      have hpdeg : p.natDegree = 0 := by
        have := natDegree_le_of_dvd hpC (C_ne_zero.mpr hU0)
        rw [natDegree_C] at this
        omega
      exact (hHprim p (UniqueFactorizationMonoid.irreducible_iff_prime.mp hpirr) hpH).1 hpdeg
    have hHsw_ne : Hsw ≠ 0 := (map_ne_zero_iff _ Bivariate.swap.injective).mpr hH0
    have hUmap_ne : U.map (C : K →+* K[X]) ≠ 0 := (Polynomial.map_ne_zero_iff C_injective).mpr hU0
    have hHsw_der_ne : Hsw.derivative ≠ 0 := by
      intro hz
      have hlead : Hsw.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hHsw_ne
      have hcoeff := congrArg (fun g : K[X][X] => g.coeff (Hsw.natDegree - 1)) hz
      rw [coeff_derivative, coeff_zero, show Hsw.natDegree - 1 + 1 = Hsw.natDegree by omega] at hcoeff
      have hcast : ((Hsw.natDegree - 1 : ℕ) + 1 : K[X]) = C (Hsw.natDegree : K) := by
        rw [← Nat.cast_add_one, show Hsw.natDegree - 1 + 1 = Hsw.natDegree by omega]; simp
      rw [hcast] at hcoeff
      exact mul_ne_zero hlead (C_ne_zero.mpr (hchar_A Hsw.natDegree (by omega) hHsw_le)) hcoeff
    have hKsw_res : resultant Hsw Ksw Hsw.natDegree Ksw.natDegree ≠ 0 := by
      let φ := algebraMap K[X] L
      have hinj : Function.Injective φ := IsFractionRing.injective K[X] L
      have hcop1 : IsCoprime (Hsw.map φ) ((U.map C).map φ) :=
        isCoprime_map_fractionRing_of_isRelPrime hHsw_ne hUmap_ne hHsw_U_rel
      have hcop2 : IsCoprime (Hsw.map φ) (Hsw.derivative.map φ) := by
        have hresL : resultant (Hsw.map φ) (Hsw.derivative.map φ)
            (Hsw.map φ).natDegree (Hsw.derivative.map φ).natDegree ≠ 0 := by
          have hder_deg : Hsw.derivative.natDegree = Hsw.natDegree - 1 := by
            apply le_antisymm (natDegree_derivative_le Hsw)
            apply le_natDegree_of_ne_zero
            rw [coeff_derivative, show Hsw.natDegree - 1 + 1 = Hsw.natDegree by omega]
            have hcast : ((Hsw.natDegree - 1 : ℕ) + 1 : K[X]) = C (Hsw.natDegree : K) := by
              rw [← Nat.cast_add_one, show Hsw.natDegree - 1 + 1 = Hsw.natDegree by omega]; simp
            rw [hcast]
            exact mul_ne_zero (leadingCoeff_ne_zero.mpr hHsw_ne)
              (C_ne_zero.mpr (hchar_A Hsw.natDegree (by omega) hHsw_le))
          rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj, hder_deg,
            resultant_map_map]
          exact (map_ne_zero_iff φ hinj).mpr hHsw_der_res
        by_contra hnot
        exact hresL (Polynomial.resultant_eq_zero_iff.mpr
          ⟨Or.inl ((Polynomial.map_ne_zero_iff hinj).mpr hHsw_ne), hnot⟩)
      have hcop : IsCoprime (Hsw.map φ) (Ksw.map φ) := by
        rw [hKsw_eq, Polynomial.map_mul]
        exact hcop1.mul_right hcop2
      have hr := Polynomial.resultant_ne_zero _ _ hcop
      rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
        resultant_map_map] at hr
      exact fun hz => hr (by rw [hz, map_zero])
    have hKsw_le : Ksw.natDegree ≤ A := by
      rw [hKsw_eq]
      refine natDegree_mul_le.trans ?_
      have h1 : (U.map (C : K →+* K[X])).natDegree = U.natDegree :=
        natDegree_map_eq_of_injective C_injective U
      have h2 : Hsw.derivative.natDegree ≤ Hsw.natDegree :=
        (natDegree_derivative_le Hsw).trans (Nat.sub_le _ _)
      rw [hHsw_deg] at h2
      rw [h1]
      have := hUX_le.trans hdiscr_X
      omega
    have hHsw_coeff : ∀ j, (Hsw.coeff j).natDegree ≤ G :=
      fun j => (swap_coeff_natDegree_le H j).trans ((Nat.le_add_left _ _).trans (hVZ_le.trans hdiscr_Z))
    have hKsw_coeff : ∀ j, (Ksw.coeff j).natDegree ≤ G := by
      intro j
      refine (swap_coeff_natDegree_le (C U * partialX K H) j).trans ?_
      have h1 : (C U * partialX K H).natDegree ≤ H.natDegree := by
        refine natDegree_mul_le.trans ?_
        rw [natDegree_C, zero_add]
        rw [natDegree_le_iff_coeff_eq_zero]
        intro i hi
        rw [coeff_partialX, coeff_eq_zero_of_natDegree_lt hi, derivative_zero]
      exact h1.trans ((Nat.le_add_left _ _).trans (hVZ_le.trans hdiscr_Z))
    let a_gcd : K → K[X] := fun z => EuclideanDomain.gcd (Aa.eval (C z)) (Aa'.eval (C z))
    let b_gcd : K → K[X] := fun z => EuclideanDomain.gcd (H.eval (C z)) (U * (partialX K H).eval (C z))
    have hbudget := two_resultant_height_budget P Q Hsw Ksw S a_gcd b_gcd den W m A G
      hPQ_res hKsw_res
      (fun z hz => by rw [swap_map_evalRingHom]; exact ha_S z hz)
      (fun z hz => by rw [swap_map_evalRingHom]; exact hHz_ne z hz)
      (fun z hz => by
        rw [swap_map_evalRingHom, swap_map_evalRingHom]
        exact ⟨EuclideanDomain.gcd_dvd_left _ _, EuclideanDomain.gcd_dvd_right _ _⟩)
      (fun z hz => by
        rw [swap_map_evalRingHom, swap_map_evalRingHom, eval_mul, eval_C]
        exact ⟨EuclideanDomain.gcd_dvd_left _ _, EuclideanDomain.gcd_dvd_right _ _⟩)
      (fun z hz => dvd_gcd_mul_gcd (hdvd_H z hz a ha_ne) (hdvd_H z hz a' ha'_ne)
        (hdvd_J z hz a ha_ne) (hdvd_J z hz a' ha'_ne))
      ⟨hP_deg, hQ_deg, hHsw_le, hKsw_le⟩
      (fun j => ⟨hP_coeff j, hQ_coeff j, hHsw_coeff j, hKsw_coeff j⟩)
    linarith [hbudget]

end AnchorsAndHeight

/-! ## Section 3: Per-site fiber factorization and total lost agreements -/

section FiberLoss

variable {K : Type} [Field K]

/-- Dividing a polynomial `P : K[X][X]` of total degree `≤ M` by a linear factor `Polynomial.X - C L` with
`L.natDegree ≤ 1` drops the total degree by `1`. -/
theorem totalDegreeLe_of_mul_linear {P Q : K[X][X]} {L : K[X]} {M : ℕ}
    (hL : L.natDegree ≤ 1) (hTot : TotalDegreeLe P M) (hfac : P = (Polynomial.X - C L) * Q) :
    TotalDegreeLe Q (M - 1) := by
  by_cases hQ0 : Q = 0
  · intro j hj; exact absurd rfl (hQ0 ▸ hj)
  have hPdeg : P.natDegree = Q.natDegree + 1 := by
    have hmon : (Polynomial.X - C L).Monic := monic_X_sub_C L
    rw [hfac, hmon.natDegree_mul' hQ0, natDegree_X_sub_C, add_comm]
  have hPne : P ≠ 0 := by
    rw [hfac]; exact mul_ne_zero (X_sub_C_ne_zero L) hQ0
  have hM_ge : Q.natDegree + 1 ≤ M := by
    have hlc := hTot P.natDegree (leadingCoeff_ne_zero.mpr hPne)
    omega
  have hstep : ∀ s : ℕ, ∀ k : ℕ, k + s = Q.natDegree →
      Q.coeff k ≠ 0 → (Q.coeff k).natDegree + k ≤ M - 1 := by
    intro s
    induction s with
    | zero =>
      intro k hk hne
      have hEq : P.coeff (k + 1) = Q.coeff k := by
        rw [hfac, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul,
          coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < k + 1), mul_zero, sub_zero]
      have hP1 := hTot (k + 1) (hEq.symm ▸ hne)
      rw [hEq] at hP1
      omega
    | succ s ih =>
      intro k hk hne
      have hEq : Q.coeff k = P.coeff (k + 1) + L * Q.coeff (k + 1) := by
        have h := congrArg (fun p : K[X][X] => p.coeff (k + 1)) hfac
        rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul] at h
        linear_combination -h
      have h1 : (P.coeff (k + 1)).natDegree + k ≤ M - 1 := by
        by_cases h0 : P.coeff (k + 1) = 0
        · rw [h0, natDegree_zero, zero_add]; omega
        · have := hTot (k + 1) h0; omega
      have h2 : (L * Q.coeff (k + 1)).natDegree + k ≤ M - 1 := by
        by_cases h0 : Q.coeff (k + 1) = 0
        · rw [h0, mul_zero, natDegree_zero, zero_add]; omega
        · have hih := ih (k + 1) (by omega) h0
          have hmul := natDegree_mul_le (p := L) (q := Q.coeff (k + 1))
          omega
      rw [hEq]
      have hadd := natDegree_add_le (P.coeff (k + 1)) (L * Q.coeff (k + 1))
      omega
  intro k hk
  have hkle : k ≤ Q.natDegree := le_natDegree_of_ne_zero hk
  exact hstep (Q.natDegree - k) k (by omega) hk

/-- Factor out the maximal power of `Polynomial.X - C L` from a nonzero polynomial `P : K[X][X]`. -/
theorem exists_max_linear_factor (P : K[X][X]) (hP : P ≠ 0) (L : K[X]) :
    ∃ (j : ℕ) (B : K[X][X]),
      j ≤ P.natDegree ∧ B ≠ 0 ∧ B.eval L ≠ 0 ∧ P = (Polynomial.X - C L) ^ j * B := by
  induction hdeg : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hroot : P.eval L = 0
    · obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hroot
      have hQ0 : Q ≠ 0 := fun hz => hP (by rw [hQ, hz, mul_zero])
      have hQdeg : Q.natDegree < n := by
        have hmon : (Polynomial.X - C L).Monic := monic_X_sub_C L
        have := congrArg Polynomial.natDegree hQ
        rw [hdeg, hmon.natDegree_mul' hQ0, natDegree_X_sub_C] at this
        omega
      obtain ⟨j, B, hjle, hB0, hBeval, hQfac⟩ := ih Q.natDegree hQdeg Q hQ0 rfl
      refine ⟨j + 1, B, by omega, hB0, hBeval, ?_⟩
      rw [hQ, hQfac, pow_succ', mul_assoc]
    · exact ⟨0, P, Nat.zero_le _, hP, hroot, by simp⟩

/-- Evaluating a polynomial `B : K[X][X]` of total degree `≤ m` at `L : K[X]` of degree `≤ 1`
gives a polynomial of degree `≤ m`. -/
theorem natDegree_eval_linear_le {B : K[X][X]} {L : K[X]} {m : ℕ}
    (hL : L.natDegree ≤ 1) (hTot : TotalDegreeLe B m) :
    (B.eval L).natDegree ≤ m := by
  rw [eval_eq_sum, sum_def]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have h1 := hTot j (mem_support_iff.mp hj)
  have h2 := natDegree_mul_le (p := B.coeff j) (q := L ^ j)
  have h3 := natDegree_pow_le (p := L) (n := j)
  have h4 : j * L.natDegree ≤ j := by simpa using Nat.mul_le_mul_left j hL
  omega

/-- **Complete L1c Coordinate Chart + Height + Loss Package**:
Given an irreducible surface `F : K[X][X][X]` and sections `(z, q z)` for `z ∈ S`, returns a
retained subset `S_ret ⊆ S` with `(S \ S_ret).card ≤ G + 2 * b * m`, transformed coordinates
`dom' : I ↪ K`, transformed received rows `u₀', u₁'`, transformed surface `F'` (irreducible,
same `b`, total degree `≤ m`), transformed sections `q'`, reduced tangent pairs `(s₁, s₂)`, and
good agreement sets `J'` satisfying all hypotheses of `TangentHeadCount.tangent_head_population_of_loss`
with `Cs = 2 * A * G + 2 * W * m` and `loss = (G + m) * Fintype.card I`. -/
theorem coordinate_chart_height_and_loss
    {I : Type} [Infinite K] [DecidableEq K] [Fintype I] [DecidableEq I]
    (dom : I ↪ K) (u₀ u₁ : I → K)
    {d t W m : ℕ} (F : K[X][X][X])
    (hFirr : Irreducible F) (hb : 2 ≤ F.natDegree)
    (hTot : ∀ j i a, ((F.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ m)
    (hWt : ∀ j i a, ((F.coeff j).coeff i).coeff a ≠ 0 → a + j * d ≤ W)
    (hchar : ∀ r : ℕ, 0 < r →
      r ≤ max ((2 * F.natDegree - 2) * W - F.natDegree * (F.natDegree - 1) * d) F.natDegree →
      (r : K) ≠ 0)
    (S : Finset K) (q : K → K[X])
    (hq : ∀ z ∈ S, (q z).natDegree ≤ d)
    (hF0 : ∀ z ∈ S, F.eval₂ (evalRingHom (C z)) (q z) = 0)
    (hAgree : ∀ z ∈ S, t ≤ (Finset.univ.filter fun x => (q z).eval (dom x) = u₀ x + z * u₁ x).card) :
    let b := F.natDegree
    let A := (2 * b - 2) * W - b * (b - 1) * d
    let G := (2 * b - 2) * m - b * (b - 1)
    ∃ (S_ret : Finset K) (dom' : I ↪ K) (u₀' u₁' : I → K)
      (F' : K[X][X][X]) (q' s₁ s₂ : K → K[X]) (J' : K → Finset I),
      S_ret ⊆ S ∧
      (S \ S_ret).card ≤ G + 2 * b * m ∧
      Irreducible F' ∧
      F'.natDegree = b ∧
      TotalDegreeLe F' m ∧
      (∀ z ∈ S_ret, (q' z).natDegree ≤ d) ∧
      (∀ z ∈ S_ret, (F'.map (evalRingHom (C z))).eval (q' z) = 0) ∧
      (∀ z ∈ S_ret, s₁ z ≠ 0) ∧
      (∀ z ∈ S_ret, (s₂ z).natDegree ≤ d + (s₁ z).natDegree) ∧
      (∀ z ∈ S_ret, ∀ x ∈ J' z, (s₁ z).eval (dom' x) ≠ 0) ∧
      (∀ z ∈ S_ret, ∀ x ∈ J' z, (s₂ z).eval (dom' x) = u₁' x * (s₁ z).eval (dom' x)) ∧
      (∀ z ∈ S_ret, ∀ x ∈ J' z,
        (q' z).eval (dom' x) * (s₁ z).eval (dom' x) - z * (s₂ z).eval (dom' x) =
          u₀' x * (s₁ z).eval (dom' x)) ∧
      (∑ z ∈ S_ret, (s₁ z).natDegree ≤ 2 * A * G + 2 * W * m) ∧
      (S_ret.card * t ≤ ∑ z ∈ S_ret, (J' z).card + (G + m) * Fintype.card I) := by
  classical
  let L := FractionRing K[X]
  set b := F.natDegree
  set A := (2 * b - 2) * W - b * (b - 1) * d
  set G := (2 * b - 2) * m - b * (b - 1)
  have hchar_b : ∀ r : ℕ, 0 < r → r ≤ b → (r : K) ≠ 0 :=
    fun r hr hle => hchar r hr (hle.trans (le_max_right _ _))
  -- Step 1: Total degree & weight of `F`, and initial singular-fiber discard `S₁`
  have hTotF : TotalDegreeLe F m := by
    intro j hj
    have hlc := leadingCoeff_ne_zero.mpr hj
    have hlc2 := leadingCoeff_ne_zero.mpr hlc
    have h := hTot j _ _ hlc2
    omega
  set W₀ := SecondPrimeCoordinateWeight.weight d F
  have hW₀_le : W₀ ≤ W := SecondPrimeCoordinateWeight.weight_le_of_coeff d F hWt
  have hbd_le : b * d ≤ W₀ := by
    have hlc : F.coeff b ≠ 0 := leadingCoeff_ne_zero.mpr hFirr.ne_zero
    have hlc2 := leadingCoeff_ne_zero.mpr hlc
    have hlc3 := leadingCoeff_ne_zero.mpr hlc2
    have hw := SecondPrimeCoordinateWeight.coeff_weight_le d F hlc3
    omega
  have hd_le_W₀ : d ≤ W₀ := by
    calc d = 1 * d := (one_mul d).symm
      _ ≤ b * d := Nat.mul_le_mul_right d (by omega)
      _ ≤ W₀ := hbd_le
  have hdiscr_ne : F.discr ≠ 0 := discr_ne_zero F hFirr hb (hchar_b b (by omega) le_rfl)
  have hlead_ne : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFirr.ne_zero
  let S₁ : Finset K := S.filter fun z => (F.leadingCoeff * F.discr).eval (C z) ≠ 0
  have hS₁_sub : S₁ ⊆ S := Finset.filter_subset _ _
  have hS₁_disc : (S \ S₁).card ≤ G + m := by
    have hEq : S \ S₁ = S.filter fun z => (F.leadingCoeff * F.discr).eval (C z) = 0 := by
      ext z
      simp only [S₁, Finset.mem_sdiff, Finset.mem_filter, not_and, not_not]
      tauto
    rw [hEq]
    have h1 := card_eval_C_eq_zero_le (F.leadingCoeff * F.discr) (mul_ne_zero hlead_ne hdiscr_ne) S
    have h2 : (F.leadingCoeff * F.discr).natDegree ≤ F.leadingCoeff.natDegree + F.discr.natDegree :=
      natDegree_mul_le
    have h3 : F.leadingCoeff.natDegree ≤ m := by
      have := hTotF F.natDegree hlead_ne
      rw [leadingCoeff]
      omega
    have h4 : F.discr.natDegree ≤ G := discr_natDegree_le F hb hTot
    omega
  have hF0_map : ∀ z ∈ S, (F.map (evalRingHom (C z))).eval (q z) = 0 := by
    intro z hz; simpa [eval_map] using hF0 z hz
  have hFder_S₁ : ∀ z ∈ S₁, (F.derivative.map (evalRingHom (C z))).eval (q z) ≠ 0 :=
    fun z hz => eval_deriv_ne_zero_of_discr_ne_zero F hb z (q z) (hF0_map z (hS₁_sub hz))
      (Finset.mem_filter.mp hz).2
  -- Step 2: Choose common Möbius chart center `r`
  obtain ⟨r, hr_dom, hr_der⟩ := SecondPrimeMobiusSections.common_center S₁
    (Finset.univ.image dom) (fun z => (F.derivative.map (evalRingHom (C z))).eval (q z)) hFder_S₁
  have hr_ne : ∀ x : I, dom x ≠ r := fun x hx =>
    hr_dom (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)
  let F' : K[X][X][X] := surfaceChart r W₀ d F
  have hF'irr : Irreducible F' := irreducible_surfaceChart r d F hFirr (by omega)
  have hF'deg : F'.natDegree = b := surface_value_degree r W₀ d F
  have hF'Tot : TotalDegreeLe F' m := surface_triangle r W₀ d F m hTotF
  have hF'Wt_le : SecondPrimeCoordinateWeight.weight d F' ≤ W₀ := surface_weight_le r d F
  have hF'Tot_c : ∀ j i a, ((F'.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ m := by
    intro j i a hne
    have hi : (F'.coeff j).coeff i ≠ 0 := fun hz => hne (by simp [hz])
    have hj : F'.coeff j ≠ 0 := fun hz => hi (by simp [hz])
    have h1 := le_natDegree_of_ne_zero hi
    have h2 := hF'Tot j hj
    omega
  have hF'Wt_c : ∀ j i a, ((F'.coeff j).coeff i).coeff a ≠ 0 → a + j * d ≤ W₀ := by
    intro j i a hne
    have hw := SecondPrimeCoordinateWeight.coeff_weight_le d F' hne
    exact hw.trans hF'Wt_le
  have hF'Wt_W : ∀ j i a, ((F'.coeff j).coeff i).coeff a ≠ 0 → a + j * d ≤ W :=
    fun j i a hne => (hF'Wt_c j i a hne).trans hW₀_le
  -- Transformed domain, received rows, and sections
  let dom' : I ↪ K :=
    ⟨fun x => (dom x - r)⁻¹, fun x y hxy => by
      have h1 : dom x - r = dom y - r := inv_injective hxy
      exact dom.injective (sub_left_inj.mp h1)⟩
  let u₀' : I → K := fun x => ((dom x - r)⁻¹) ^ d * u₀ x
  let u₁' : I → K := fun x => ((dom x - r)⁻¹) ^ d * u₁ x
  let q' : K → K[X] := fun z => SecondPrimeMobiusSections.chart r d (q z)
  -- Second discard: `(F'.discr).eval (C z) = 0`
  have hF'discr_ne : F'.discr ≠ 0 :=
    discr_ne_zero F' hF'irr (by omega) (hF'deg ▸ hchar_b b (by omega) le_rfl)
  let S_ret : Finset K := S₁.filter fun z => (F'.discr).eval (C z) ≠ 0
  have hS_ret_S₁ : S_ret ⊆ S₁ := Finset.filter_subset _ _
  have hS_ret_S : S_ret ⊆ S := hS_ret_S₁.trans hS₁_sub
  have hS_disc : (S \ S_ret).card ≤ G + 2 * b * m := by
    have hsub : S \ S_ret ⊆ (S \ S₁) ∪ (S₁.filter fun z => (F'.discr).eval (C z) = 0) := by
      intro z hz
      obtain ⟨hzS, hzNot⟩ := Finset.mem_sdiff.mp hz
      by_cases hz1 : z ∈ S₁
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz1, ?_⟩)
        by_contra hne
        exact hzNot (Finset.mem_filter.mpr ⟨hz1, hne⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hzS, hz1⟩)
    have h2 : (S₁.filter fun z => (F'.discr).eval (C z) = 0).card ≤ G := by
      have h := card_eval_C_eq_zero_le F'.discr hF'discr_ne S₁
      have hd := discr_natDegree_le F' (by omega) hF'Tot_c
      rw [hF'deg] at hd
      exact h.trans hd
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hG_le : G ≤ (2 * b - 2) * m := Nat.sub_le _ _
    have hmul : (2 * b - 2) * m + m ≤ 2 * b * m := by
      have hle : 2 * b - 2 + 1 ≤ 2 * b := by omega
      calc (2 * b - 2) * m + m = (2 * b - 2 + 1) * m := by ring
        _ ≤ 2 * b * m := Nat.mul_le_mul_right m hle
    omega
  -- Section properties on `S_ret`
  have hq'_deg : ∀ z ∈ S_ret, (q' z).natDegree ≤ d :=
    fun z hz => chart_degree_le r d (q z) (hq z (hS_ret_S hz))
  have hF'0 : ∀ z ∈ S_ret, (F'.map (evalRingHom (C z))).eval (q' z) = 0 := by
    intro z hz
    rw [surface_fiber, plane_graph r W₀ d _ (q z) (hq z (hS_ret_S hz)) (section_weight d F z),
      hF0_map z (hS_ret_S hz), map_zero]
  have hF'lead : ∀ z ∈ S_ret, F'.leadingCoeff.eval (C z) ≠ 0 := by
    intro z hz
    have hfl : F.leadingCoeff.eval (C z) ≠ 0 := fun h0 =>
      (Finset.mem_filter.mp (hS_ret_S₁ hz)).2 (by rw [eval_mul, h0, zero_mul])
    have hcoeff : F'.leadingCoeff.eval (C z) =
        ((F'.map (evalRingHom (C z))).coeff b) := by
      rw [coeff_map, leadingCoeff, hF'deg]; rfl
    rw [hcoeff, surface_fiber, plane_coeff, coeff_map]
    exact chart_ne_zero' r (W₀ - b * d) hfl
  have hF'good : ∀ z ∈ S_ret, (F'.leadingCoeff * F'.discr).eval (C z) ≠ 0 := by
    intro z hz
    rw [eval_mul]
    exact mul_ne_zero (hF'lead z hz) (Finset.mem_filter.mp hz).2
  have hF'der_deg : ∀ z ∈ S_ret,
      ((F'.derivative.map (evalRingHom (C z))).eval (q' z)).natDegree = W₀ - d := by
    intro z hz
    rw [← derivative_map, surface_fiber]
    exact derivative_graph_degree r W₀ d (F.map (evalRingHom (C z))) (q z)
      (hq z (hS_ret_S hz)) (section_weight d F z) (by
        simpa [derivative_map] using hr_der z (hS_ret_S₁ hz))
  have hF'der_ne : ∀ z ∈ S_ret, (F'.derivative.map (evalRingHom (C z))).eval (q' z) ≠ 0 :=
    fun z hz => eval_deriv_ne_zero_of_discr_ne_zero F' (by omega) z (q' z) (hF'0 z hz) (hF'good z hz)
  -- Step 3: Reduced tangent pairs `(s₁, s₂)` and numerator degree bound
  let s₁ : K → K[X] := fun z => (tangentPair (L := L) F' z (q' z)).2
  let s₂ : K → K[X] := fun z => (tangentPair (L := L) F' z (q' z)).1
  have hs₁_ne : ∀ z ∈ S_ret, s₁ z ≠ 0 := fun z _ =>
    nonZeroDivisors.ne_zero (IsFractionRing.den K[X] _).property
  have hs₂_deg : ∀ z ∈ S_ret, (s₂ z).natDegree ≤ d + (s₁ z).natDegree := by
    intro z hz
    by_cases h0 : s₂ z = 0
    · rw [h0, natDegree_zero]; exact Nat.zero_le _
    · let t_z := (F'.derivative.map (evalRingHom (C z))).eval (q' z)
      let w_z := ((coefficientDerivative (scalarDerivative K[X]) F').map (evalRingHom (C z))).eval (q' z)
      have hrel : t_z * s₂ z = -w_z * s₁ z := by
        let v := -algebraMap K[X] L w_z / algebraMap K[X] L t_z
        apply IsFractionRing.injective K[X] L
        change algebraMap K[X] L (t_z * IsFractionRing.num K[X] v) =
          algebraMap K[X] L (-w_z * (IsFractionRing.den K[X] v : K[X]))
        have h := (IsFractionRing.num_mul_den_eq_num_iff_eq (A := K[X]) (x := v) (y := v)).mpr rfl
        have htL : algebraMap K[X] L t_z ≠ 0 := by
          simpa using (IsFractionRing.injective K[X] L).ne (hF'der_ne z hz)
        rw [map_mul, map_mul, map_neg, ← h]
        dsimp only [v]
        rw [← mul_assoc, mul_div_cancel₀ _ htL]
      have hw_deg : w_z.natDegree ≤ W₀ := by
        dsimp [w_z]
        rw [eval_eq_sum, sum_def]
        apply natDegree_sum_le_of_forall_le
        intro j hj
        rw [mem_support_iff, coeff_map] at hj
        rw [coeff_map]
        have hcj : (F'.coeff j).derivative ≠ 0 := fun h0 => hj (by
          change ((F'.coeff j).derivative).eval (C z) = 0
          rw [h0, eval_zero])
        have hj' : F'.coeff j ≠ 0 := fun h0 => hcj (by simp [h0])
        have hdeg_coeff : ((F'.coeff j).derivative.eval (C z)).natDegree + j * d ≤ W₀ := by
          have h1 : ((F'.coeff j).derivative.eval (C z)).natDegree ≤
              Bivariate.degreeX (F'.coeff j).derivative := by
            rw [← swap_map_evalRingHom, ← Bivariate.natDegreeY_swap]
            exact natDegree_map_le
          have h2 : Bivariate.degreeX (F'.coeff j).derivative ≤ Bivariate.degreeX (F'.coeff j) := by
            by_cases hd0 : (F'.coeff j).derivative = 0
            · simp [hd0, Bivariate.degreeX]
            · obtain ⟨i, hi, heq, _⟩ := Bivariate.exists_max_index_degreeX _ hd0
              rw [← heq]
              have hne : (F'.coeff j).coeff (i + 1) ≠ 0 := by
                intro h0
                exact (mem_support_iff.mp hi) (by rw [coeff_derivative, h0, zero_mul])
              have h3 : ((F'.coeff j).derivative.coeff i).natDegree ≤
                  ((F'.coeff j).coeff (i + 1)).natDegree := by
                rw [coeff_derivative, show (↑i + 1 : K[X]) = C ((i : K) + 1) from by simp,
                  mul_comm]
                exact natDegree_C_mul_le _ _
              exact h3.trans (Bivariate.coeff_natDegree_le_degreeX (F'.coeff j) (i + 1))
          obtain ⟨i₀, hi₀, heq₀, _⟩ := Bivariate.exists_max_index_degreeX (F'.coeff j) hj'
          have h3 := hF'Wt_c j i₀ _ (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi₀))
          rw [heq₀] at h3
          omega
        have hqpow := (natDegree_pow_le (p := q' z) (n := j)).trans
          (Nat.mul_le_mul_left j (hq'_deg z hz))
        change ((F'.coeff j).derivative.eval (C z) * q' z ^ j).natDegree ≤ W₀
        exact natDegree_mul_le.trans (by omega)
      have hw_ne : w_z ≠ 0 := by
        intro hw0
        rw [hw0, neg_zero, zero_mul] at hrel
        exact mul_ne_zero (hF'der_ne z hz) h0 hrel
      have hdeg_eq := congrArg Polynomial.natDegree hrel
      rw [natDegree_mul (hF'der_ne z hz) h0,
        natDegree_mul (neg_ne_zero.mpr hw_ne) (hs₁_ne z hz), natDegree_neg,
        hF'der_deg z hz] at hdeg_eq
      omega
  -- Step 4: Denominator height sum bound
  have hheight : ∑ z ∈ S_ret, (s₁ z).natDegree ≤ 2 * A * G + 2 * W * m := by
    have h := total_denominator_height_le F' hF'irr (by omega) hF'Tot_c hF'Wt_W
      (by rwa [hF'deg]) S_ret q' hF'0 hF'good
    rwa [hF'deg] at h
  -- Step 5: Per-site fiber factorization and lost-agreement bound via `received_tangent`
  obtain ⟨V, U, H, hV0, hU0, hH0, _, hdvd_all, hsplit, hVZ_le, _, _, hHx_all, _⟩ :=
    factor_split F'.discr hF'discr_ne
  have hVdvd : V.map C ∣ F'.discr := (dvd_mul_right _ _).trans ((dvd_mul_right _ _).trans hdvd_all)
  have : Fact (Irreducible (F'.map (genericCoeffs (R := K[X]) (L := L)))) :=
    ⟨irreducible_map_genericCoeffs F' hF'irr (by omega)⟩
  obtain ⟨D₁, hδ₁, hD₁⟩ := exists_regular_logDerivZ (L := L) F' hF'irr (by omega)
    (by rwa [hF'deg]) hU0 hsplit
  have hF'x_ne : ∀ x : I, F'.map (mapRingHom (evalRingHom (dom' x))) ≠ 0 := by
    intro x hx
    have hprim : F'.IsPrimitive := hF'irr.isPrimitive (by omega)
    have hdvd_all_x : ∀ j, C (Polynomial.X - C (dom' x)) ∣ F'.coeff j := by
      intro j
      have h0 := congrArg (fun g : K[X][X] => g.coeff j) hx
      rw [coeff_map, coeff_zero] at h0
      refine (C_dvd_iff_dvd_coeff _ _).mpr fun i => dvd_iff_isRoot.mpr ?_
      have h1 := congrArg (fun g : K[X] => g.coeff i) h0
      simpa [coe_mapRingHom, coeff_map, coe_evalRingHom] using h1
    have hu := hprim (C (Polynomial.X - C (dom' x))) ((C_dvd_iff_dvd_coeff _ _).mpr hdvd_all_x)
    have hux : IsUnit (Polynomial.X - C (dom' x) : K[X]) := isUnit_C.mp hu
    exact (by simp : (Polynomial.X - C (dom' x) : K[X]).natDegree ≠ 0)
      (natDegree_eq_zero_of_isUnit hux)
  have hHx_ne : ∀ x : I, H.map (evalRingHom (dom' x)) ≠ 0 := fun x => hHx_all (dom' x)
  let L_line : I → K[X] := fun x => C (u₀' x) + C (u₁' x) * Polynomial.X
  have hL_deg : ∀ x : I, (L_line x).natDegree ≤ 1 := by
    intro x
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_C]; exact Nat.zero_le 1
    · exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X])
  have hfac_site : ∀ x : I,
      ∃ (j : ℕ) (B : K[X][X]),
        j ≤ b ∧ B ≠ 0 ∧ B.eval (L_line x) ≠ 0 ∧ (B.eval (L_line x)).natDegree ≤ m ∧
        F'.map (mapRingHom (evalRingHom (dom' x))) = (Polynomial.X - C (L_line x)) ^ j * B := by
    intro x
    let Fx := F'.map (mapRingHom (evalRingHom (dom' x)))
    obtain ⟨j, B, hjle, hB0, hBeval, hfac⟩ := exists_max_linear_factor Fx (hF'x_ne x) (L_line x)
    have hFx_tot : TotalDegreeLe Fx m := by
      intro k hk
      rw [coeff_map] at hk ⊢
      have hk' : F'.coeff k ≠ 0 := fun h0 => hk (by simp [h0])
      exact (Nat.add_le_add_right natDegree_map_le k).trans (hF'Tot k hk')
    have hB_tot : TotalDegreeLe B m := by
      have hgen : ∀ r : ℕ, ∀ P Q : K[X][X], TotalDegreeLe P m →
          P = (Polynomial.X - C (L_line x)) ^ r * Q → TotalDegreeLe Q m := by
        intro r
        induction r with
        | zero => intro P Q hP hPQ; simp at hPQ; exact hPQ ▸ hP
        | succ r ih =>
          intro P Q hP hPQ
          have hstep1 := totalDegreeLe_of_mul_linear (hL_deg x) hP
            (by rw [hPQ, pow_succ', mul_assoc])
          exact ih _ Q (fun k hk => (hstep1 k hk).trans (Nat.sub_le m 1)) rfl
      exact hgen j Fx B hFx_tot hfac
    exact ⟨j, B, hjle.trans (natDegree_map_le.trans (by omega)), hB0, hBeval,
      natDegree_eval_linear_le (hL_deg x) hB_tot, hfac⟩
  let j_site : I → ℕ := fun x => Classical.choose (hfac_site x)
  let B_site : I → K[X][X] := fun x => Classical.choose (Classical.choose_spec (hfac_site x))
  have hsite_spec : ∀ x : I,
      j_site x ≤ b ∧ B_site x ≠ 0 ∧ (B_site x).eval (L_line x) ≠ 0 ∧
      ((B_site x).eval (L_line x)).natDegree ≤ m ∧
      F'.map (mapRingHom (evalRingHom (dom' x))) =
        (Polynomial.X - C (L_line x)) ^ j_site x * B_site x :=
    fun x => Classical.choose_spec (Classical.choose_spec (hfac_site x))
  let badSite : I → Finset K := fun x =>
    S_ret.filter fun z =>
      ((B_site x).eval (L_line x)).eval z = 0 ∨ (H.map (evalRingHom (dom' x))).eval z = 0
  have hbad_card : ∀ x : I, (badSite x).card ≤ G + m := by
    intro x
    have hsub : badSite x ⊆
        (((B_site x).eval (L_line x)).roots.toFinset) ∪
          ((H.map (evalRingHom (dom' x))).roots.toFinset) := by
      intro z hz
      rcases (Finset.mem_filter.mp hz).2 with h1 | h2
      · exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
          ((mem_roots (hsite_spec x).2.2.1).mpr h1))
      · exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr
          ((mem_roots (hHx_ne x)).mpr h2))
    have hc1 : (((B_site x).eval (L_line x)).roots.toFinset).card ≤ m :=
      (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (hsite_spec x).2.2.2.1)
    have hc2 : ((H.map (evalRingHom (dom' x))).roots.toFinset).card ≤ G := by
      have hH_Z : H.natDegree ≤ G := by
        have hFd := discr_natDegree_le F' (by omega) hF'Tot_c
        rw [hF'deg] at hFd
        exact (Nat.le_add_left _ _).trans (hVZ_le.trans hFd)
      exact (Multiset.toFinset_card_le _).trans
        ((card_roots' _).trans (natDegree_map_le.trans hH_Z))
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  let J' : K → Finset I := fun z =>
    Finset.univ.filter fun x =>
      (q' z).eval (dom' x) = u₀' x + z * u₁' x ∧ z ∉ badSite x
  -- Every site in `J' z` satisfies `received_tangent`
  have hJ'_tan : ∀ z ∈ S_ret, ∀ x ∈ J' z,
      (s₁ z).eval (dom' x) ≠ 0 ∧
      (s₂ z).eval (dom' x) = u₁' x * (s₁ z).eval (dom' x) ∧
      (q' z).eval (dom' x) * (s₁ z).eval (dom' x) - z * (s₂ z).eval (dom' x) =
        u₀' x * (s₁ z).eval (dom' x) := by
    intro z hz x hx
    obtain ⟨_, hqx, hnotbad⟩ := Finset.mem_filter.mp hx
    have hnot_or : ¬ (((B_site x).eval (L_line x)).eval z = 0 ∨
        (H.map (evalRingHom (dom' x))).eval z = 0) :=
      fun h => hnotbad (Finset.mem_filter.mpr ⟨hz, h⟩)
    push Not at hnot_or
    obtain ⟨hBz_ne, hHz_ne⟩ := hnot_or
    have hB_eval : ((B_site x).map (evalRingHom z)).eval ((q' z).eval (dom' x)) ≠ 0 := by
      have hEq : ((B_site x).eval (L_line x)).eval z =
          ((B_site x).map (evalRingHom z)).eval (u₀' x + z * u₁' x) := by
        have h := Polynomial.hom_eval₂ (B_site x) (RingHom.id K[X]) (evalRingHom z) (L_line x)
        simpa [L_line, eval_map, eval₂_id, mul_comm (u₁' x) z] using h
      rwa [hqx, ← hEq]
    have hj_pos : 0 < j_site x := by
      by_contra h0
      have hj0 : j_site x = 0 := by omega
      have hfac := (hsite_spec x).2.2.2.2
      rw [hj0, pow_zero, one_mul] at hfac
      have hFxz0 : ((F'.map (mapRingHom (evalRingHom (dom' x)))).map (evalRingHom z)).eval
          ((q' z).eval (dom' x)) = 0 := by
        have hcomm : (evalRingHom z).comp (mapRingHom (evalRingHom (dom' x))) =
            (evalRingHom (dom' x)).comp (evalRingHom (C z)) := by
          ext <;> simp
        rw [Polynomial.map_map, hcomm, ← Polynomial.map_map, eval_map]
        have h := Polynomial.hom_eval₂ (F'.map (evalRingHom (C z))) (RingHom.id K[X])
          (evalRingHom (dom' x)) (q' z)
        have h0 := congrArg (evalRingHom (dom' x)) (hF'0 z hz)
        simpa [eval₂_id] using h.symm.trans h0
      rw [hfac] at hFxz0
      exact hB_eval hFxz0
    have hfact : ((j_site x).factorial : K) ≠ 0 := by
      have hgen : ∀ n : ℕ, n ≤ b → (n.factorial : K) ≠ 0 := by
        intro n
        induction n with
        | zero => intro _; simp
        | succ n ih =>
          intro hle
          rw [Nat.factorial_succ, Nat.cast_mul]
          exact mul_ne_zero (hchar_b (n + 1) (by omega) hle) (ih (by omega))
      exact hgen (j_site x) (hsite_spec x).1
    have hVz : V.eval z ≠ 0 := by
      intro hvz
      obtain ⟨qV, hqV⟩ := hVdvd
      have h0 := congrArg (fun p : K[X][X] => p.eval (C z)) hqV
      rw [eval_mul, eval_map_C, hvz, C_0, zero_mul] at h0
      exact (Finset.mem_filter.mp hz).2 h0
    have hHtilde_ne : ((V.map C * H).eval (C z)).eval (dom' x) ≠ 0 := by
      rw [eval_mul, eval_map_C, eval_mul, eval_C]
      have hHev : (H.eval (C z)).eval (dom' x) = (H.map (evalRingHom (dom' x))).eval z := by
        rw [eval_map]
        have h := Polynomial.hom_eval₂ H (RingHom.id K[X]) (evalRingHom (dom' x)) (C z)
        simpa [eval₂_id] using h
      rw [hHev]
      exact mul_ne_zero hVz hHz_ne
    have hcard : (F'.natDegree : Cardinal) < Cardinal.mk K :=
      (Cardinal.natCast_lt_aleph0 (n := F'.natDegree)).trans_le (Cardinal.aleph0_le_mk K)
    exact received_tangent (L := L) F' (dom' x) z (u₀' x) (u₁' x) (q' z)
      (hF'lead z hz) (hF'0 z hz) (hF'der_ne z hz) D₁ hD₁ (V.map C * H) hδ₁
      hHtilde_ne hqx (j_site x) hj_pos hfact hcard (B_site x) hB_eval (hsite_spec x).2.2.2.2
  -- Step 6: Agreement count transfer and double-counting loss bound
  have hlow : S_ret.card * t ≤ ∑ z ∈ S_ret, (J' z).card + (G + m) * Fintype.card I := by
    let Agree' : K → Finset I := fun z =>
      Finset.univ.filter fun x => (q' z).eval (dom' x) = u₀' x + z * u₁' x
    have hAg_eq : ∀ z ∈ S_ret,
        (Finset.univ.filter fun x => (q z).eval (dom x) = u₀ x + z * u₁ x) = Agree' z := by
      intro z hz
      ext x
      simp only [Agree', Finset.mem_filter, Finset.mem_univ, true_and]
      have hscale : ((dom x - r)⁻¹) ^ d ≠ 0 := pow_ne_zero d (inv_ne_zero (sub_ne_zero.mpr (hr_ne x)))
      have hev := chart_eval r (dom x) (hr_ne x) d (q z) (hq z (hS_ret_S hz))
      change (q' z).eval (dom' x) = ((dom x - r)⁻¹) ^ d * (q z).eval (dom x) at hev
      rw [hev]
      dsimp only [u₀', u₁']
      rw [show ((dom x - r)⁻¹) ^ d * u₀ x + z * (((dom x - r)⁻¹) ^ d * u₁ x) =
        ((dom x - r)⁻¹) ^ d * (u₀ x + z * u₁ x) by ring]
      exact (mul_right_inj' hscale).symm
    have h1 : S_ret.card * t ≤ ∑ z ∈ S_ret, (Agree' z).card := by
      calc S_ret.card * t = ∑ _z ∈ S_ret, t := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ z ∈ S_ret, (Agree' z).card := Finset.sum_le_sum fun z hz => by
            rw [← hAg_eq z hz]; exact hAgree z (hS_ret_S hz)
    have h2 : ∑ z ∈ S_ret, (Agree' z).card ≤
        ∑ z ∈ S_ret, (J' z).card + ∑ z ∈ S_ret, (Finset.univ.filter fun x => z ∈ badSite x).card := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun z _ => ?_
      have hsub : Agree' z ⊆ J' z ∪ (Finset.univ.filter fun x => z ∈ badSite x) := by
        intro x hx
        by_cases hb : z ∈ badSite x
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hb⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2, hb⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hswap : ∑ z ∈ S_ret, (Finset.univ.filter fun x => z ∈ badSite x).card =
        ∑ x : I, (badSite x).card := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hsub : badSite x ⊆ S_ret := Finset.filter_subset _ _
      rw [← Finset.card_filter, show S_ret.filter (fun z => z ∈ badSite x) = badSite x from by
        ext z; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩]
    have h3 : ∑ x : I, (badSite x).card ≤ (G + m) * Fintype.card I := by
      calc ∑ x : I, (badSite x).card ≤ ∑ _x : I, (G + m) := Finset.sum_le_sum fun x _ => hbad_card x
        _ = Fintype.card I * (G + m) := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        _ = (G + m) * Fintype.card I := Nat.mul_comm _ _
    omega
  exact ⟨S_ret, dom', u₀', u₁', F', q', s₁, s₂, J', hS_ret_S, hS_disc, hF'irr, hF'deg, hF'Tot,
    hq'_deg, hF'0, hs₁_ne, hs₂_deg,
    fun z hz x hx => (hJ'_tan z hz x hx).1,
    fun z hz x hx => (hJ'_tan z hz x hx).2.1,
    fun z hz x hx => (hJ'_tan z hz x hx).2.2,
    hheight, hlow⟩

end FiberLoss

#print axioms card_eval_C_eq_zero_le
#print axioms eval_deriv_ne_zero_of_discr_ne_zero
#print axioms isCoprime_map_fractionRing_of_isRelPrime
#print axioms resultant_ne_zero_of_isRelPrime
#print axioms exists_coprime_anchors
#print axioms total_denominator_height_le
#print axioms coordinate_chart_height_and_loss

end ArkLib.ProximityGap.Frontier.CoordinateChartAndHeightSum
