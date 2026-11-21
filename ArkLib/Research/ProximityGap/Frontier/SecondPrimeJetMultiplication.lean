/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CanonicalQuarticSiteOrder
import Mathlib.RingTheory.Polynomial.GaussLemma
import ArkLib.Data.CodingTheory.GuruswamiSudan.MultiplicityInterpolation
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

/-! # Rank of multiplication on the truncated two-variable jet -/

open Polynomial Finset
namespace ArkLib.ProximityGap.Frontier.SecondPrimeJetMultiplication

variable {K : Type} [Field K]

private noncomputable def scaleAxis (F : K[X][X]) : K[X][X] :=
  F.comp (Polynomial.C (Polynomial.X : Polynomial K) * Polynomial.X)

private theorem scale_coeff (F : K[X][X]) (i : ℕ) :
    (scaleAxis F).coeff i = F.coeff i * Polynomial.X ^ i :=
  comp_C_mul_X_coeff

private theorem scale_ne (F : K[X][X]) (hF : F ≠ 0) : scaleAxis F ≠ 0 := by
  intro h
  have hj : F.coeff F.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hF
  apply mul_ne_zero hj (pow_ne_zero F.natDegree X_ne_zero)
  rw [← scale_coeff, h, coeff_zero]

/-- The least total degree of a nonzero monomial. The coordinate content after replacing
V by TV computes the minimum common T-adic order of all value coefficients. -/
noncomputable def jetOrder (F : K[X][X]) : ℕ := by
  classical
  exact (scaleAxis F).content.natTrailingDegree

/-- Multiplicity at the translated origin is additive on products of nonzero polynomials. -/
theorem jetOrder_mul (F H : K[X][X]) (hF : F ≠ 0) (hH : H ≠ 0) :
    jetOrder (F * H) = jetOrder F + jetOrder H := by
  classical
  have hmul : scaleAxis (F * H) = scaleAxis F * scaleAxis H := mul_comp _ _ _
  simp only [jetOrder, hmul, content_mul]
  exact natTrailingDegree_mul (content_eq_zero_iff.not.mpr (scale_ne _ hF))
    (content_eq_zero_iff.not.mpr (scale_ne _ hH))

/-- The order bound is precisely vanishing of all jets below its total degree. -/
theorem le_jetOrder_iff (F : K[X][X]) (hF : F ≠ 0) (r : ℕ) :
    r ≤ jetOrder F ↔ ∀ i j, i + j < r → (F.coeff i).coeff j = 0 := by
  classical
  have hnon : (scaleAxis F).content ≠ 0 := content_eq_zero_iff.not.mpr (scale_ne _ hF)
  rw [jetOrder, ← rootMultiplicity_eq_natTrailingDegree', le_rootMultiplicity_iff hnon]
  simp only [map_zero, sub_zero, dvd_content_iff_C_dvd, C_dvd_iff_dvd_coeff, scale_coeff,
    X_pow_dvd_iff]
  constructor
  · intro h i j hj
    have hh := h i (j + i) (by omega)
    simpa only [coeff_mul_X_pow] using hh
  · intro h i j hj
    rw [coeff_mul_X_pow']
    split_ifs with hi
    · exact h _ _ (by omega)
    · rfl

/-- Reference the received-site order from the actual canonical quartic theorem. -/
theorem jetOrder_at_site (F : K[X][X]) (hF : F.IsPrimitive) (a : K) (w : K[X]) :
    jetOrder ((F.taylor w).map (taylorAlgHom a).toRingHom) =
      CanonicalQuarticSiteOrder.siteOrder F a w := by
  let P := (F.taylor w).map (taylorAlgHom a).toRingHom
  have hP : P ≠ 0 := by
    intro h
    have hinj : Function.Injective (taylorAlgHom a : K[X] →ₐ[K] K[X]) := by
      intro x y he
      have e := congrArg (taylor (-a)) he
      simpa [taylorAlgHom_apply, taylor_taylor] using e
    have ht := (map_injective (taylorAlgHom a).toRingHom hinj).ne
      (show F.taylor w ≠ 0 by simpa using hF.ne_zero)
    exact ht (h.trans (Polynomial.map_zero _).symm)
  have he (r : ℕ) : r ≤ jetOrder P ↔ r ≤ CanonicalQuarticSiteOrder.siteOrder F a w := by
    rw [le_jetOrder_iff P hP, CanonicalQuarticSiteOrder.le_siteOrder_iff_jet F hF]
    simp only [P, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, taylorAlgHom_apply]
  exact le_antisymm ((he _).mp le_rfl) ((he _).mpr le_rfl)

/-- Multiplication by a polynomial of order r is injective on the multipliers of total
degree below μ−r when the resulting product is observed through all degrees below μ. -/
theorem multiplier_eq_zero (f : K[X][X]) (hf : f ≠ 0) (H : K[X][X]) {μ : ℕ}
    (hdegree : ∀ i j, (H.coeff i).coeff j ≠ 0 → i + j < μ - jetOrder f)
    (hvanish : ∀ i j, i + j < μ → ((f * H).coeff i).coeff j = 0) : H = 0 := by
  by_contra hH
  have hfg := (le_jetOrder_iff _ (mul_ne_zero hf hH) μ).mpr hvanish
  rw [jetOrder_mul f H hf hH] at hfg
  have htop : H.coeff H.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hH
  let i := H.natDegree
  let j := (H.coeff i).natDegree
  have hcoeff : (H.coeff i).coeff j ≠ 0 := leadingCoeff_ne_zero.mpr htop
  have hsmall := hdegree i j hcoeff
  have hleast : jetOrder H ≤ i + j := by
    by_contra! hlt
    exact hcoeff ((le_jetOrder_iff H hH _).mp le_rfl i j hlt)
  omega

/-- Pairs of nonnegative exponents of total degree strictly below the cutoff. -/
abbrev Jet (n : ℕ) := ↥(GSMultInterp.multIdx n)

/-- Project a bivariate polynomial onto its truncated Taylor coefficients. -/
noncomputable def readJet (n : ℕ) : K[X][X] →ₗ[K] (Jet n → K) where
  toFun p x := (p.coeff x.val.1).coeff x.val.2
  map_add' p q := by ext x; simp
  map_smul' c p := by ext x; simp [coeff_smul]

/-- Polynomial whose monomial coefficients are the supplied jet. -/
noncomputable def jetPolynomial (n : ℕ) : (Jet n → K) →ₗ[K] K[X][X] where
  toFun v := ∑ x : Jet n, v x • monomial x.val.1 (monomial x.val.2 1)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, mul_smul]

private theorem monomial_coeff (x : ℕ × ℕ) (i j : ℕ) (a : K) :
    (((a • monomial x.1 (monomial x.2 (1 : K))).coeff i).coeff j) =
      if x = (i, j) then a else 0 := by
  rcases x with ⟨u, v⟩
  by_cases h : u = i <;> by_cases h' : v = j <;> simp [coeff_smul, coeff_monomial, h, h']

private theorem jetPolynomial_coeff (n : ℕ) (v : Jet n → K) (i j : ℕ) :
    (((jetPolynomial n) v).coeff i).coeff j =
      if h : (i, j) ∈ GSMultInterp.multIdx n then v ⟨(i, j), h⟩ else 0 := by
  classical
  change ((∑ x : Jet n, v x • monomial x.val.1 (monomial x.val.2 (1 : K))).coeff i).coeff j = _
  simp only [finsetSum_coeff, monomial_coeff]
  split_ifs with h
  · let x : Jet n := ⟨(i, j), h⟩
    rw [Finset.sum_eq_single x]
    · simp [x]
    · intro y _ hy
      have hn : y.val ≠ (i, j) := fun he => hy (Subtype.ext he)
      simp [hn]
    · simp
  · apply Finset.sum_eq_zero
    intro x _
    have hn : x.val ≠ (i, j) := fun he => h (he ▸ x.property)
    simp [hn]

/-- Multiply a truncated polynomial representative and retain the first μ jet diagonals. -/
noncomputable def multiplyJet (f : K[X][X]) (n μ : ℕ) : (Jet n → K) →ₗ[K] (Jet μ → K) :=
  (readJet μ).comp ((LinearMap.mulLeft K f).comp (jetPolynomial n))

/-- Low-degree multipliers remain independent after multiplying in the truncated jet. -/
theorem multiplyJet_injective (f : K[X][X]) (hf : f ≠ 0) (μ : ℕ) :
    Function.Injective (multiplyJet f (μ - jetOrder f) μ) := by
  classical
  apply (LinearMap.ker_eq_bot.mp ·)
  rw [LinearMap.ker_eq_bot']
  intro v hv
  let n := μ - jetOrder f
  have hz : jetPolynomial n v = 0 := by
    apply multiplier_eq_zero f hf (μ := μ)
    · intro i j hne
      by_contra! hneg
      exact hne (by simp [jetPolynomial_coeff, GSMultInterp.mem_multIdx, n, hneg])
    · intro i j hij
      exact congrFun hv (⟨(i, j), GSMultInterp.mem_multIdx.mpr hij⟩ : Jet μ)
  ext x
  have h := congrArg (fun p : K[X][X] => (p.coeff x.val.1).coeff x.val.2) hz
  have hx : x.val ∈ GSMultInterp.multIdx n := x.property
  simpa only [jetPolynomial_coeff, Prod.eta, hx, dite_true, coeff_zero, Pi.zero_apply] using h

/-- Exact rank of the independent multiplier subspace, in triangular-number form. -/
theorem multiplier_rank (f : K[X][X]) (hf : f ≠ 0) (μ : ℕ) :
    Module.finrank K (LinearMap.range (multiplyJet f (μ - jetOrder f) μ)) =
      (μ - jetOrder f) * (μ - jetOrder f + 1) / 2 := by
  rw [LinearMap.finrank_range_of_inj (multiplyJet_injective f hf μ)]
  simp [Jet, GSMultInterp.card_multIdx]

/-- The full space of truncated multiples in the jet target. -/
noncomputable def jetIdeal (f : K[X][X]) (μ : ℕ) : Submodule K (Jet μ → K) :=
  LinearMap.range ((readJet μ).comp (LinearMap.mulLeft K f))

/-- The independent monomial multiples span the entire ideal in the truncated jet. -/
theorem range_multiplyJet (f : K[X][X]) (hf : f ≠ 0) (μ : ℕ) :
    LinearMap.range (multiplyJet f (μ - jetOrder f) μ) = jetIdeal f μ := by
  classical
  let n := μ - jetOrder f
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨jetPolynomial n v, rfl⟩
  · rintro _ ⟨p, rfl⟩
    refine ⟨readJet n p, ?_⟩
    let q := jetPolynomial n (readJet n p)
    have hlow : ∀ i j, i + j < n → ((p - q).coeff i).coeff j = 0 := by
      intro i j hij
      have hm : (i, j) ∈ GSMultInterp.multIdx n := GSMultInterp.mem_multIdx.mpr hij
      simp only [q, coeff_sub, jetPolynomial_coeff, hm, dite_true, readJet, LinearMap.coe_mk,
        AddHom.coe_mk, sub_self]
    change readJet μ (f * q) = readJet μ (f * p)
    by_cases h : p - q = 0
    · rw [sub_eq_zero.mp h]
    have ho := (le_jetOrder_iff _ h n).mpr hlow
    have hp : μ ≤ jetOrder (f * (p - q)) := by rw [jetOrder_mul f _ hf h]; dsimp [n] at ho; omega
    ext x
    have hx := (le_jetOrder_iff _ (mul_ne_zero hf h) μ).mp hp x.val.1 x.val.2
      (GSMultInterp.mem_multIdx.mp x.property)
    simp only [mul_sub, coeff_sub] at hx
    exact (sub_eq_zero.mp hx).symm

/-- The intrinsic number of independent vanishing requirements at one site. -/
theorem codimension (f : K[X][X]) (hf : f ≠ 0) (μ : ℕ) :
    Module.finrank K ((Jet μ → K) ⧸ jetIdeal f μ) =
      μ * (μ + 1) / 2 - (μ - jetOrder f) * (μ - jetOrder f + 1) / 2 := by
  have h := Submodule.finrank_quotient_add_finrank (jetIdeal f μ)
  have hr := multiplier_rank f hf μ
  rw [range_multiplyJet f hf μ] at hr
  rw [hr] at h
  simp only [Module.finrank_fintype_fun_eq_card, Jet, Fintype.card_coe,
    GSMultInterp.card_multIdx] at h
  exact Nat.eq_sub_of_add_eq h

/-- A uniform linear bound on the number of scalar constraints per received site. -/
theorem codimension_le (f : K[X][X]) (hf : f ≠ 0) (μ : ℕ) :
    Module.finrank K ((Jet μ → K) ⧸ jetIdeal f μ) ≤ μ * jetOrder f := by
  rw [codimension f hf μ]
  set r := jetOrder f
  suffices hh : μ * (μ + 1) ≤ (μ-r) * (μ-r+1) + μ*r*2 by omega
  rcases le_total r μ with hr | hr
  · have h := Nat.sub_add_cancel hr
    generalize μ-r = z at h ⊢
    rw [← h]
    rcases r with _ | r <;> nlinarith
  · rw [Nat.sub_eq_zero_of_le hr]
    obtain rfl | hμ := Nat.eq_zero_or_pos μ
    · simp
    · nlinarith [Nat.mul_le_mul_left μ hr, Nat.mul_le_mul_left μ hμ]

#print axioms codimension_le
#print axioms multiplier_rank
#print axioms jetOrder_mul
#print axioms le_jetOrder_iff
#print axioms jetOrder_at_site
#print axioms multiplier_eq_zero
end ArkLib.ProximityGap.Frontier.SecondPrimeJetMultiplication
