/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.Polynomial.Bivariate
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.CharP.Lemmas

/-! # Geometric irreducibility of a plane curve from a smooth rational point

An irreducible bivariate polynomial `F : L[X][X]` (inner variable `Z`, outer variable `Y`)
admitting a simple `L`-point `(z₀, y₀)` remains irreducible over `AlgebraicClosure L`, in every
characteristic including imperfect fields such as `L = k(X)` in positive characteristic.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset

namespace ArkLib.ProximityGap.Frontier.GeometricIrreducibilitySmoothPoint

private theorem aeval_expand_eq {L K : Type*} [CommRing L] [CommRing K] [Algebra L K]
    (n : ℕ) (g : L[X]) (x : K) :
    aeval x (expand L n g) = aeval (x ^ n) g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial k a =>
    simp [expand_monomial, aeval_monomial, pow_mul, mul_comm]

private theorem expChar_pos_of {R : Type*} [CommRing R] [Nontrivial R] (q : ℕ) [ExpChar R q] :
    0 < q := by
  cases ‹ExpChar R q› with
  | zero => exact Nat.zero_lt_one
  | prime hp => exact hp.pos

private theorem expChar_of_injective_hom {R S : Type*} [CommRing R] [CommRing S]
    (q : ℕ) [ExpChar R q] (φ : R →+* S) (hφ : Function.Injective φ) : ExpChar S q := by
  cases ‹ExpChar R q› with
  | zero =>
    have : CharZero S := ⟨fun a b h => Nat.cast_injective (hφ (by simpa only [map_natCast] using h))⟩
    exact ExpChar.zero
  | prime hp =>
    have : CharP S q := ⟨fun n => by
      rw [← map_natCast φ, map_eq_zero_iff φ hφ, CharP.cast_eq_zero_iff R q n]⟩
    exact ExpChar.prime hp

private theorem expChar_polynomial {R : Type*} [CommRing R] (q : ℕ) [ExpChar R q] :
    ExpChar R[X] q :=
  expChar_of_injective_hom q Polynomial.C Polynomial.C_injective

private theorem sum_pow_expChar_pow_eq {R ι : Type*} [CommRing R] (q : ℕ) [ExpChar R q]
    (s : Finset ι) (f : ι → R) (e : ℕ) :
    (∑ i ∈ s, f i) ^ (q ^ e) = ∑ i ∈ s, (f i) ^ (q ^ e) := by
  classical
  nontriviality R
  have hpos : 0 < q ^ e := pow_pos (expChar_pos_of (R := R) q) e
  induction s using Finset.induction_on with
  | empty => simp [zero_pow hpos.ne']
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_expChar_pow (p := q), ih]

/-- An element of `AlgebraicClosure L` fixed by every `L`-automorphism is purely inseparable
over `L`: some `q^e`-th power (where `q` is the exponential characteristic of `L`) lies in `L`. -/
theorem fixed_by_algEquiv_pow_mem_range {L : Type*} [Field L] (q : ℕ) [ExpChar L q]
    (x : AlgebraicClosure L) (hfix : ∀ σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L, σ x = x) :
    ∃ (e : ℕ) (a : L), algebraMap L (AlgebraicClosure L) a = x ^ (q ^ e) := by
  classical
  let K := AlgebraicClosure L
  have halg : IsIntegral L x := Algebra.IsIntegral.isIntegral x
  let μ : L[X] := minpoly L x
  have hμ_irr : Irreducible μ := minpoly.irreducible halg
  have hμ_monic : μ.Monic := minpoly.monic halg
  have hμ_root : ∀ y : K, aeval y μ = 0 → y = x := by
    intro y hy
    have hconj : IsConjRoot L x y := minpoly.eq_of_irreducible_of_monic hμ_irr hy hμ_monic
    obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
    exact σ.injective (hσ.trans (hfix σ).symm)
  have hmem_of_deg_one : ∀ (g : L[X]) (y : K), g.natDegree = 1 → aeval y g = 0 →
      ∃ a : L, algebraMap L K a = y := by
    intro g y hdeg hroot
    have hg : g = C (g.coeff 1) * X + C (g.coeff 0) :=
      eq_X_add_C_of_natDegree_le_one (le_of_eq hdeg)
    have hg_ne : g ≠ 0 := ne_zero_of_natDegree_gt (by rw [hdeg]; exact Nat.zero_lt_one)
    have hc1 : g.coeff 1 ≠ 0 := by
      rw [← hdeg]
      exact leadingCoeff_ne_zero.mpr hg_ne
    rw [hg, map_add, map_mul, aeval_C, aeval_C, aeval_X] at hroot
    refine ⟨-(g.coeff 0) / g.coeff 1, ?_⟩
    have hc1K : algebraMap L K (g.coeff 1) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap L K).injective).mpr hc1
    rw [map_div₀, map_neg, div_eq_iff hc1K]
    linear_combination -hroot
  cases ‹ExpChar L q› with
  | zero =>
    have hsep : μ.Separable := hμ_irr.separable
    have hsplit : (μ.map (algebraMap L K)).Splits := IsAlgClosed.splits _
    have hnodup : (μ.map (algebraMap L K)).roots.Nodup :=
      Polynomial.nodup_roots hsep.map
    have hmem_x : x ∈ (μ.map (algebraMap L K)).roots :=
      (mem_roots (Polynomial.map_ne_zero hμ_irr.ne_zero)).mpr
        (by rw [IsRoot, eval_map, ← aeval_def]; exact minpoly.aeval L x)
    have hcard : (μ.map (algebraMap L K)).roots.card = 1 := by
      have hle : (μ.map (algebraMap L K)).roots.card ≤ 1 := by
        calc (μ.map (algebraMap L K)).roots.card
            = (μ.map (algebraMap L K)).roots.toFinset.card :=
              (Multiset.toFinset_card_of_nodup hnodup).symm
          _ ≤ ({x} : Finset K).card := Finset.card_le_card (fun y hy => by
              have hy0 : aeval y μ = 0 := by
                rw [aeval_def, ← eval_map]
                exact (mem_roots (Polynomial.map_ne_zero hμ_irr.ne_zero)).mp
                  (Multiset.mem_toFinset.mp hy)
              exact Finset.mem_singleton.mpr (hμ_root y hy0))
          _ = 1 := Finset.card_singleton x
      have hge : 1 ≤ (μ.map (algebraMap L K)).roots.card :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨x, hmem_x⟩
      omega
    have hdeg1 : μ.natDegree = 1 := by
      have := hsplit.natDegree_eq_card_roots
      rw [natDegree_map_eq_of_injective (algebraMap L K).injective] at this
      omega
    obtain ⟨a, ha⟩ := hmem_of_deg_one μ x hdeg1 (minpoly.aeval L x)
    exact ⟨0, a, by simpa using ha⟩
  | prime hp =>
    obtain ⟨n, g, hg_sep, hgf⟩ := Polynomial.exists_separable_of_irreducible q hμ_irr hp.ne_zero
    have hg_ne : g ≠ 0 := hg_sep.ne_zero
    have hroot_g : aeval (x ^ (q ^ n)) g = 0 := by
      have h1 : aeval x (expand L (q ^ n) g) = 0 := by rw [hgf]; exact minpoly.aeval L x
      rwa [aeval_expand_eq] at h1
    have hsplit : (g.map (algebraMap L K)).Splits := IsAlgClosed.splits _
    have hnodup : (g.map (algebraMap L K)).roots.Nodup :=
      Polynomial.nodup_roots hg_sep.map
    have hmem_xq : x ^ (q ^ n) ∈ (g.map (algebraMap L K)).roots :=
      (mem_roots (Polynomial.map_ne_zero hg_ne)).mpr
        (by rw [IsRoot, eval_map, ← aeval_def]; exact hroot_g)
    have huniq_g : ∀ y : K, aeval y g = 0 → y = x ^ (q ^ n) := by
      intro y hy
      have hpos : 0 < q ^ n := pow_pos hp.pos n
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y hpos
      have hμz : aeval z μ = 0 := by
        rw [← hgf, aeval_expand_eq, hz, hy]
      rw [← hz, hμ_root z hμz]
    have hcard : (g.map (algebraMap L K)).roots.card = 1 := by
      have hle : (g.map (algebraMap L K)).roots.card ≤ 1 := by
        calc (g.map (algebraMap L K)).roots.card
            = (g.map (algebraMap L K)).roots.toFinset.card :=
              (Multiset.toFinset_card_of_nodup hnodup).symm
          _ ≤ ({x ^ (q ^ n)} : Finset K).card := Finset.card_le_card (fun y hy => by
              have hy0 : aeval y g = 0 := by
                rw [aeval_def, ← eval_map]
                exact (mem_roots (Polynomial.map_ne_zero hg_ne)).mp
                  (Multiset.mem_toFinset.mp hy)
              exact Finset.mem_singleton.mpr (huniq_g y hy0))
          _ = 1 := Finset.card_singleton _
      have hge : 1 ≤ (g.map (algebraMap L K)).roots.card :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨x ^ (q ^ n), hmem_xq⟩
      omega
    have hdeg1 : g.natDegree = 1 := by
      have := hsplit.natDegree_eq_card_roots
      rw [natDegree_map_eq_of_injective (algebraMap L K).injective] at this
      omega
    obtain ⟨a, ha⟩ := hmem_of_deg_one g (x ^ (q ^ n)) hdeg1 hroot_g
    exact ⟨n, a, ha⟩

/-- Lifting a ring homomorphism to bivariate polynomials `R[X][X]`. -/
def mapBiv {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) : R[X][X] →+* S[X][X] :=
  mapRingHom (mapRingHom φ)

@[simp]
theorem coeff_coeff_mapBiv {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (P : R[X][X]) (j i : ℕ) :
    ((mapBiv φ P).coeff j).coeff i = φ ((P.coeff j).coeff i) := by
  simp [mapBiv]

theorem mapBiv_injective {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) : Function.Injective (mapBiv φ) :=
  Polynomial.map_injective _ (Polynomial.map_injective _ hφ)

theorem mapBiv_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (ψ : S →+* T) (φ : R →+* S) (P : R[X][X]) :
    mapBiv ψ (mapBiv φ P) = mapBiv (ψ.comp φ) P := by
  ext j i
  simp [mapBiv]

theorem eval_mapBiv {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (P : R[X][X]) (z y : R) :
    ((mapBiv φ P).map (evalRingHom (φ z))).eval (φ y) =
      φ ((P.map (evalRingHom z)).eval y) := by
  have h1 : (evalRingHom (φ z)).comp (mapRingHom φ) = φ.comp (evalRingHom z) := by
    ext <;> simp
  calc ((mapBiv φ P).map (evalRingHom (φ z))).eval (φ y)
      = (P.map ((evalRingHom (φ z)).comp (mapRingHom φ))).eval (φ y) := by
        simp [mapBiv, Polynomial.map_map]
    _ = (P.map (φ.comp (evalRingHom z))).eval (φ y) := by rw [h1]
    _ = ((P.map (evalRingHom z)).map φ).eval (φ y) := by rw [Polynomial.map_map]
    _ = φ ((P.map (evalRingHom z)).eval y) := eval_map_apply φ _

theorem derivative_mapBiv {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (P : R[X][X]) :
    (mapBiv φ P).derivative = mapBiv φ P.derivative := by
  simp [mapBiv, Polynomial.derivative_map]

/-- If every coefficient of a univariate polynomial `p : K[X]` lies in `range φ` for `φ : L →+* K`,
then `p` is the image of some `q : L[X]` under `Polynomial.map φ`. -/
private theorem exists_map_eq_of_coeff_mem_range {L K : Type*} [CommRing L] [CommRing K]
    (φ : L →+* K) (p : K[X]) (h : ∀ i, p.coeff i ∈ Set.range φ) :
    ∃ q : L[X], q.map φ = p := by
  classical
  choose c hc using h
  refine ⟨∑ i ∈ p.support, Polynomial.monomial i (c i), ?_⟩
  rw [Polynomial.map_sum]
  ext k
  rw [finsetSum_coeff]
  by_cases hk : k ∈ p.support
  · rw [Finset.sum_eq_single k]
    · simp [hc k]
    · intro b _ hbk
      simp [Polynomial.map_monomial, Polynomial.coeff_monomial, hbk]
    · intro h'
      exact absurd hk h'
  · rw [Polynomial.notMem_support_iff.mp hk]
    apply Finset.sum_eq_zero
    intro b hb
    have hbk : b ≠ k := fun he => hk (he ▸ hb)
    simp [Polynomial.map_monomial, Polynomial.coeff_monomial, hbk]

/-- In a ring of exponential characteristic `q`, raising a polynomial to `q^e` raises every
coefficient to `q^e` and multiplies exponents by `q^e`. -/
private theorem poly_pow_expChar_pow_coeff_mem_range {R S : Type*} [CommRing R] [CommRing S]
    (q : ℕ) [ExpChar S q] (φ : R →+* S) (p : S[X]) (e : ℕ)
    (h : ∀ i, p.coeff i ^ (q ^ e) ∈ Set.range φ) :
    ∀ k, (p ^ (q ^ e)).coeff k ∈ Set.range φ := by
  classical
  have : ExpChar S[X] q := expChar_polynomial q
  have hsum : p ^ (q ^ e) =
      ∑ i ∈ p.support, Polynomial.monomial (i * q ^ e) (p.coeff i ^ (q ^ e)) := by
    conv_lhs => rw [p.as_sum_support]
    rw [sum_pow_expChar_pow_eq q]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.monomial_pow]
  intro k
  rw [hsum, finsetSum_coeff]
  have hmem : ∀ i ∈ p.support,
      (Polynomial.monomial (i * q ^ e) (p.coeff i ^ (q ^ e))).coeff k ∈ Set.range φ := by
    intro i _
    rw [Polynomial.coeff_monomial]
    split_ifs
    · exact h i
    · exact ⟨0, map_zero φ⟩
  exact Subring.sum_mem φ.range hmem

/-- A bivariate polynomial over `AlgebraicClosure L` fixed by all `L`-automorphisms has a
`(q^e)`-th power descending to `L[X][X]`. -/
theorem biv_fixed_pow_descends {L : Type*} [Field L] (q : ℕ) [ExpChar L q]
    (P : (AlgebraicClosure L)[X][X])
    (hfix : ∀ σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L, mapBiv σ.toRingHom P = P) :
    ∃ (e : ℕ) (R : L[X][X]), mapBiv (algebraMap L (AlgebraicClosure L)) R = P ^ (q ^ e) := by
  classical
  let K := AlgebraicClosure L
  let φ := algebraMap L K
  have : ExpChar K q := expChar_of_injective_hom q φ φ.injective
  have hcoeff_fix : ∀ j i (σ : K ≃ₐ[L] K), σ ((P.coeff j).coeff i) = (P.coeff j).coeff i := by
    intro j i σ
    have h := congrArg (fun Q : K[X][X] => (Q.coeff j).coeff i) (hfix σ)
    simpa [coeff_coeff_mapBiv] using h
  have hcoeff_pow : ∀ j i, ∃ e : ℕ, ((P.coeff j).coeff i) ^ (q ^ e) ∈ Set.range φ := by
    intro j i
    obtain ⟨e, a, ha⟩ := fixed_by_algEquiv_pow_mem_range q ((P.coeff j).coeff i) (hcoeff_fix j i)
    exact ⟨e, a, ha⟩
  choose expf hexpf using hcoeff_pow
  let pairs : Finset (ℕ × ℕ) := P.support.biUnion fun j => (P.coeff j).support.image (fun i => (j, i))
  let E : ℕ := pairs.sup fun ji => expf ji.1 ji.2
  have hqpos : 0 < q ^ E := pow_pos (expChar_pos_of (R := L) q) E
  have hpow_all : ∀ j i, ((P.coeff j).coeff i) ^ (q ^ E) ∈ Set.range φ := by
    intro j i
    by_cases hj : j ∈ P.support
    · by_cases hi : i ∈ (P.coeff j).support
      · have hmem : (j, i) ∈ pairs :=
          Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
        have hle : expf j i ≤ E := Finset.le_sup (f := fun ji : ℕ × ℕ => expf ji.1 ji.2) hmem
        obtain ⟨a, ha⟩ := hexpf j i
        refine ⟨a ^ (q ^ (E - expf j i)), ?_⟩
        rw [map_pow, ha, ← pow_mul, ← pow_add, Nat.add_sub_of_le hle]
      · have hz : (P.coeff j).coeff i = 0 := Polynomial.notMem_support_iff.mp hi
        rw [hz, zero_pow hqpos.ne']
        exact ⟨0, map_zero φ⟩
    · have hz : P.coeff j = 0 := Polynomial.notMem_support_iff.mp hj
      rw [hz, coeff_zero, zero_pow hqpos.ne']
      exact ⟨0, map_zero φ⟩
  have hinner : ∀ j, (P.coeff j) ^ (q ^ E) ∈ Set.range (mapRingHom φ) := by
    intro j
    obtain ⟨r, hr⟩ := exists_map_eq_of_coeff_mem_range φ ((P.coeff j) ^ (q ^ E))
      (poly_pow_expChar_pow_coeff_mem_range q φ (P.coeff j) E (hpow_all j))
    exact ⟨r, hr⟩
  have : ExpChar K[X] q := expChar_polynomial q
  obtain ⟨R, hR⟩ := exists_map_eq_of_coeff_mem_range (mapRingHom φ) (P ^ (q ^ E))
    (poly_pow_expChar_pow_coeff_mem_range q (mapRingHom φ) P E hinner)
  exact ⟨E, R, hR⟩

/-- If `F : L[X][X]` is irreducible with `0 < F.natDegree` and `R : L[X][X]` satisfies that
`F` and `R` share a positive-`Y`-degree common divisor over `K`, then `F ∣ R` in `L[X][X]`. -/
private theorem dvd_of_common_factor_over_extension {L K : Type*} [Field L] [Field K]
    (φ : L →+* K) (F R : L[X][X]) (hF : Irreducible F) (hFdeg : 0 < F.natDegree)
    (P : K[X][X]) (hPdeg : 0 < P.natDegree)
    (hPF : P ∣ mapBiv φ F) (hPR : P ∣ mapBiv φ R) :
    F ∣ R := by
  classical
  by_contra hndvd
  let ιL : L[X] →+* FractionRing L[X] := algebraMap L[X] (FractionRing L[X])
  let FL : (FractionRing L[X])[X] := F.map ιL
  let RL : (FractionRing L[X])[X] := R.map ιL
  have hFprim : F.IsPrimitive := hF.isPrimitive hFdeg.ne'
  have hFL_irr : Irreducible FL :=
    (hFprim.irreducible_iff_irreducible_map_fraction_map (K := FractionRing L[X])).mp hF
  have hFL_ndvd : ¬ FL ∣ RL := by
    intro hdiv
    exact hndvd ((hFprim.dvd_iff_fraction_map_dvd_fraction_map (K := FractionRing L[X])).mpr hdiv)
  have hcop : IsCoprime FL RL :=
    (hFL_irr.coprime_iff_not_dvd).mpr hFL_ndvd
  have hres_ne : resultant F R F.natDegree R.natDegree ≠ 0 := by
    have hresL := Polynomial.resultant_ne_zero FL RL hcop
    dsimp only [FL, RL] at hresL
    rw [natDegree_map_eq_of_injective (IsFractionRing.injective L[X] (FractionRing L[X])),
      natDegree_map_eq_of_injective (IsFractionRing.injective L[X] (FractionRing L[X])),
      resultant_map_map] at hresL
    exact fun h0 => hresL (by simp [h0])
  obtain ⟨A, B, -, -, hAB⟩ :=
    exists_mul_add_mul_eq_C_resultant F R le_rfl le_rfl (Or.inl hFdeg.ne')
  have hABK := congrArg (mapBiv φ) hAB
  rw [map_add, map_mul, map_mul] at hABK
  have hCeq : mapBiv φ (C (resultant F R F.natDegree R.natDegree)) =
      C ((resultant F R F.natDegree R.natDegree).map φ) := by
    simp [mapBiv]
  rw [hCeq] at hABK
  have hPdvd : P ∣ C ((resultant F R F.natDegree R.natDegree).map φ) := by
    rw [← hABK]
    exact dvd_add (dvd_mul_of_dvd_left hPF _) (dvd_mul_of_dvd_left hPR _)
  have hresK_ne : (resultant F R F.natDegree R.natDegree).map φ ≠ 0 :=
    (Polynomial.map_ne_zero_iff φ.injective).mpr hres_ne
  have hPdeg0 : P.natDegree ≤ 0 := by
    have := natDegree_le_of_dvd hPdvd (C_ne_zero.mpr hresK_ne)
    simpa [natDegree_C] using this
  omega

/-- Units of `K[X][X]` are nonzero double-constant polynomials `C (C c)`. -/
private theorem eq_C_C_of_isUnit {K : Type*} [Field K] {u : K[X][X]} (hu : IsUnit u) :
    ∃ c : K, c ≠ 0 ∧ u = C (C c) := by
  obtain ⟨p, hp_unit, rfl⟩ := Polynomial.isUnit_iff.mp hu
  obtain ⟨c, hc_unit, rfl⟩ := Polynomial.isUnit_iff.mp hp_unit
  exact ⟨c, hc_unit.ne_zero, rfl⟩

/-- **Geometric irreducibility from a smooth `Y`-point (`L2a`).**
If `F : L[X][X]` is irreducible over `L` and has an `L`-point `(z₀, y₀)` where `F(z₀, y₀) = 0`
and `∂_Y F(z₀, y₀) ≠ 0`, then `F` remains irreducible over `AlgebraicClosure L`. -/
theorem irreducible_algebraicClosure_of_smooth_y {L : Type*} [Field L]
    (F : L[X][X]) (hF : Irreducible F) (z₀ y₀ : L)
    (hroot : (F.map (evalRingHom z₀)).eval y₀ = 0)
    (hsmooth : (F.derivative.map (evalRingHom z₀)).eval y₀ ≠ 0) :
    Irreducible (mapBiv (algebraMap L (AlgebraicClosure L)) F) := by
  classical
  let K := AlgebraicClosure L
  let φ := algebraMap L K
  let FK := mapBiv φ F
  have hFdeg : 0 < F.natDegree := by
    by_contra h
    have h0 : F.natDegree = 0 := by omega
    rw [eq_C_of_natDegree_eq_zero h0, derivative_C, Polynomial.map_zero, eval_zero] at hsmooth
    exact hsmooth rfl
  have hFK_ne : FK ≠ 0 := by
    simpa [FK] using (mapBiv_injective φ.injective).ne hF.ne_zero
  have hFK_root : (FK.map (evalRingHom (φ z₀))).eval (φ y₀) = 0 := by
    rw [eval_mapBiv, hroot, map_zero]
  have hFK_smooth : (FK.derivative.map (evalRingHom (φ z₀))).eval (φ y₀) ≠ 0 := by
    rw [derivative_mapBiv, eval_mapBiv]
    exact (map_ne_zero_iff φ φ.injective).mpr hsmooth
  obtain ⟨factors, hfactors_prime, hfactors_assoc⟩ :=
    UniqueFactorizationMonoid.exists_prime_factors FK hFK_ne
  obtain ⟨u, hu⟩ := hfactors_assoc
  let ev : K[X][X] →+* K := (evalRingHom (φ y₀)).comp (mapRingHom (evalRingHom (φ z₀)))
  have hev_apply (G : K[X][X]) : ev G = (G.map (evalRingHom (φ z₀))).eval (φ y₀) := rfl
  have hev_CC (a : K) : ev (C (C a)) = a := by simp [hev_apply]
  have hprod_zero : ev factors.prod = 0 := by
    have h0 : ev (factors.prod * (u : K[X][X])) = 0 := by rw [hu]; exact hFK_root
    rw [map_mul] at h0
    obtain ⟨c, hc, huc⟩ := eq_C_C_of_isUnit u.isUnit
    have hu_ev : ev (u : K[X][X]) ≠ 0 := by rw [huc, hev_CC]; exact hc
    exact (mul_eq_zero.mp h0).resolve_right hu_ev
  obtain ⟨P₀, hP₀_mem, hP₀_zero⟩ : ∃ P₀ ∈ factors, ev P₀ = 0 := by
    have h0 : (factors.map ev).prod = 0 := by rw [← map_multiset_prod]; exact hprod_zero
    exact Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h0)
  have hP₀_irr : Irreducible P₀ := (hfactors_prime P₀ hP₀_mem).irreducible
  have hP₀_dvd : P₀ ∣ FK := by
    rw [← hu]
    exact dvd_mul_of_dvd_left (Multiset.dvd_prod hP₀_mem) _
  obtain ⟨Q₀, hPQ₀⟩ := hP₀_dvd
  have hder_prod : ev FK.derivative = ev P₀.derivative * ev Q₀ + ev P₀ * ev Q₀.derivative := by
    rw [hPQ₀, derivative_mul, map_add, map_mul, map_mul]
  rw [hP₀_zero, zero_mul, add_zero] at hder_prod
  have hFK_sm_ev : ev FK.derivative ≠ 0 := hFK_smooth
  rw [hder_prod] at hFK_sm_ev
  have hP₀_der_ne : ev P₀.derivative ≠ 0 := left_ne_zero_of_mul hFK_sm_ev
  have hQ₀_ev_ne : ev Q₀ ≠ 0 := right_ne_zero_of_mul hFK_sm_ev
  let c₀ : K := (ev P₀.derivative)⁻¹
  have hc₀_ne : c₀ ≠ 0 := inv_ne_zero hP₀_der_ne
  let P : K[X][X] := C (C c₀) * P₀
  let Q : K[X][X] := C (C (ev P₀.derivative)) * Q₀
  have hP_irr : Irreducible P := by
    have hu : IsUnit (C (C c₀) : K[X][X]) := isUnit_C.mpr (isUnit_C.mpr hc₀_ne.isUnit)
    exact (Associated.irreducible_iff ⟨hu.unit, mul_comm _ _⟩).mp hP₀_irr
  have hPQ : FK = P * Q := by
    rw [hPQ₀]
    have hmul : C (C c₀) * C (C (ev P₀.derivative)) = (1 : K[X][X]) := by
      rw [← C_mul, ← C_mul, inv_mul_cancel₀ hP₀_der_ne, C_1, C_1]
    calc P₀ * Q₀ = 1 * (P₀ * Q₀) := (one_mul _).symm
      _ = (C (C c₀) * C (C (ev P₀.derivative))) * (P₀ * Q₀) := by rw [hmul]
      _ = P * Q := by dsimp [P, Q]; ring
  have hP_zero : ev P = 0 := by simp [P, hP₀_zero]
  have hP_der : ev P.derivative = 1 := by
    change ev (C (C c₀) * P₀).derivative = 1
    rw [derivative_C_mul, map_mul, hev_CC, inv_mul_cancel₀ hP₀_der_ne]
  have hQ_ev_ne : ev Q ≠ 0 := by
    change ev (C (C (ev P₀.derivative)) * Q₀) ≠ 0
    rw [map_mul, hev_CC]
    exact mul_ne_zero hP₀_der_ne hQ₀_ev_ne
  have hP_deg : 0 < P.natDegree := by
    by_contra h
    have h0 : P.natDegree = 0 := by omega
    rw [eq_C_of_natDegree_eq_zero h0, derivative_C, map_zero] at hP_der
    exact zero_ne_one hP_der
  have hP_unique : ∀ P' : K[X][X], Irreducible P' → P' ∣ FK → ev P' = 0 →
      ev P'.derivative = 1 → P' = P := by
    intro P' hP'_irr hP'_dvd hP'_zero hP'_der
    have hP'_prime : Prime P' := UniqueFactorizationMonoid.irreducible_iff_prime.mp hP'_irr
    rw [hPQ] at hP'_dvd
    rcases hP'_prime.dvd_or_dvd hP'_dvd with hdvdP | hdvdQ
    · obtain ⟨w, hw⟩ := hP'_irr.associated_of_dvd hP_irr hdvdP
      obtain ⟨c, _, hwc⟩ := eq_C_C_of_isUnit w.isUnit
      have hP_eq : P = C (C c) * P' := by rw [← hw, hwc, mul_comm]
      have hc1 : c = 1 := by
        have h := congrArg (fun G : K[X][X] => ev G.derivative) hP_eq
        rw [hP_der, derivative_C_mul, map_mul, hev_CC, hP'_der, mul_one] at h
        exact h.symm
      rw [hP_eq, hc1, C_1, C_1, one_mul]
    · obtain ⟨W, hW⟩ := hdvdQ
      have h0 : ev Q = 0 := by rw [hW, map_mul, hP'_zero, zero_mul]
      exact absurd h0 hQ_ev_ne
  have hP_fix : ∀ σ : K ≃ₐ[L] K, mapBiv σ.toRingHom P = P := by
    intro σ
    let eBiv : K[X][X] ≃+* K[X][X] :=
      Polynomial.mapEquiv (Polynomial.mapEquiv σ.toRingEquiv)
    have heBiv : ∀ G, mapBiv σ.toRingHom G = eBiv G := fun _ => rfl
    have hσ_FK : mapBiv σ.toRingHom FK = FK := by
      rw [mapBiv_comp]
      have hcomp : σ.toRingHom.comp φ = φ := RingHom.ext fun a => σ.commutes a
      rw [hcomp]
    have hσ_irr : Irreducible (mapBiv σ.toRingHom P) := by
      rw [heBiv]
      exact (MulEquiv.irreducible_iff eBiv.toMulEquiv).mpr hP_irr
    have hσ_dvd : mapBiv σ.toRingHom P ∣ FK := by
      rw [← hσ_FK]
      exact map_dvd (mapBiv σ.toRingHom) ⟨Q, hPQ⟩
    have hσ_ev (G : K[X][X]) : ev (mapBiv σ.toRingHom G) = σ (ev G) := by
      have hz : σ (φ z₀) = φ z₀ := σ.commutes z₀
      have hy : σ (φ y₀) = φ y₀ := σ.commutes y₀
      rw [hev_apply, ← hz, ← hy]
      exact eval_mapBiv σ.toRingHom G (φ z₀) (φ y₀)
    have hσ_zero : ev (mapBiv σ.toRingHom P) = 0 := by rw [hσ_ev, hP_zero, map_zero]
    have hσ_der : ev (mapBiv σ.toRingHom P).derivative = 1 := by
      rw [derivative_mapBiv, hσ_ev, hP_der, map_one]
    exact hP_unique _ hσ_irr hσ_dvd hσ_zero hσ_der
  obtain ⟨q, hq⟩ := ExpChar.exists L
  obtain ⟨e, R, hR⟩ := biv_fixed_pow_descends q P hP_fix
  have hqpos : 0 < q ^ e := pow_pos (expChar_pos_of (R := L) q) e
  have hP_dvd_R : P ∣ mapBiv φ R := by
    rw [hR]
    exact dvd_pow_self P hqpos.ne'
  have hF_dvd_R : F ∣ R :=
    dvd_of_common_factor_over_extension φ F R hF hFdeg P hP_deg ⟨Q, hPQ⟩ hP_dvd_R
  have hFK_dvd_Ppow : FK ∣ P ^ (q ^ e) := by
    rw [← hR]
    exact map_dvd (mapBiv φ) hF_dvd_R
  have hQ_unit : IsUnit Q := by
    by_contra hQ_not_unit
    have hQ_ne : Q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hPQ
      exact hFK_ne hPQ
    obtain ⟨qfac, hqfac_prime, hqfac_assoc⟩ :=
      UniqueFactorizationMonoid.exists_prime_factors Q hQ_ne
    have hqfac_ne : qfac ≠ 0 := by
      intro h0
      rw [h0, Multiset.prod_zero] at hqfac_assoc
      exact hQ_not_unit (hqfac_assoc.isUnit_iff.mp isUnit_one)
    obtain ⟨P', hP'_mem⟩ := Multiset.exists_mem_of_ne_zero hqfac_ne
    have hP'_prime : Prime P' := hqfac_prime P' hP'_mem
    have hP'_irr : Irreducible P' := hP'_prime.irreducible
    have hP'_dvd_Q : P' ∣ Q := (Multiset.dvd_prod hP'_mem).trans hqfac_assoc.dvd
    have hP'_dvd_Ppow : P' ∣ P ^ (q ^ e) :=
      (hP'_dvd_Q.trans (dvd_mul_left Q P)).trans (hPQ ▸ hFK_dvd_Ppow)
    have hP'_dvd_P : P' ∣ P := hP'_prime.dvd_of_dvd_pow hP'_dvd_Ppow
    obtain ⟨w, hw⟩ := hP'_irr.associated_of_dvd hP_irr hP'_dvd_P
    have hP'_zero : ev P' = 0 := by
      obtain ⟨c, hc, hwc⟩ := eq_C_C_of_isUnit w.isUnit
      have h0 : ev P' * c = 0 := by
        have h := congrArg ev hw
        rw [map_mul, hwc, hev_CC, hP_zero] at h
        exact h
      exact (mul_eq_zero.mp h0).resolve_right hc
    obtain ⟨W, hW⟩ := hP'_dvd_Q
    exact hQ_ev_ne (by rw [hW, map_mul, hP'_zero, zero_mul])
  change Irreducible FK
  rw [hPQ]
  exact (Associated.irreducible_iff ⟨hQ_unit.unit, rfl⟩).mp hP_irr

private theorem swap_monomial_monomial {R : Type*} [CommRing R] (j i : ℕ) (c : R) :
    Bivariate.swap (Polynomial.monomial j (Polynomial.monomial i c)) =
      Polynomial.monomial i (Polynomial.monomial j c) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
    ← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
  have hCC : Bivariate.swap (Polynomial.C (Polynomial.C c)) = Polynomial.C (Polynomial.C c) := by
    simp [Bivariate.swap]
  have hCX : Bivariate.swap (Polynomial.C (Polynomial.X : R[X])) = (Polynomial.X : R[X][X]) := by
    simp [Bivariate.swap]
  have hX : Bivariate.swap (Polynomial.X : R[X][X]) = Polynomial.C (Polynomial.X : R[X]) := by
    simp [Bivariate.swap]
  rw [map_mul, map_mul, map_pow, map_pow, map_mul, map_pow, hCC, hCX, hX]
  simp only [C_mul, C_pow]
  ring

private theorem eval_swap_eq {R : Type*} [CommRing R] (F : R[X][X]) (z y : R) :
    ((Bivariate.swap F).map (evalRingHom y)).eval z = (F.map (evalRingHom z)).eval y := by
  induction F using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial j p =>
    induction p using Polynomial.induction_on' with
    | add a b ha hb =>
      rw [map_add (Polynomial.monomial j)]
      simp [map_add, ha, hb]
    | monomial i c =>
      rw [swap_monomial_monomial]
      simp only [Polynomial.map_monomial, coe_evalRingHom, eval_monomial]
      ring

private theorem mapBiv_swap {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (F : R[X][X]) :
    mapBiv φ (Bivariate.swap F) = Bivariate.swap (mapBiv φ F) := by
  induction F using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial j p =>
    induction p using Polynomial.induction_on' with
    | add a b ha hb =>
      rw [map_add (Polynomial.monomial j)]
      simp [map_add, ha, hb]
    | monomial i c =>
      simp only [mapBiv, coe_mapRingHom, Polynomial.map_monomial, swap_monomial_monomial]

/-- **Geometric irreducibility from any smooth `L`-point (`L2a`, full version).**
Allows either partial derivative `∂_Y F` or `∂_Z F` to be nonzero at `(z₀, y₀)`. -/
theorem irreducible_algebraicClosure_of_smooth {L : Type*} [Field L]
    (F : L[X][X]) (hF : Irreducible F) (z₀ y₀ : L)
    (hroot : (F.map (evalRingHom z₀)).eval y₀ = 0)
    (hsmooth : (F.derivative.map (evalRingHom z₀)).eval y₀ ≠ 0 ∨
      ((Bivariate.swap F).derivative.map (evalRingHom y₀)).eval z₀ ≠ 0) :
    Irreducible (mapBiv (algebraMap L (AlgebraicClosure L)) F) := by
  rcases hsmooth with hy | hz
  · exact irreducible_algebraicClosure_of_smooth_y F hF z₀ y₀ hroot hy
  · let K := AlgebraicClosure L
    let φ := algebraMap L K
    have hswap_irr : Irreducible (Bivariate.swap F) :=
      (MulEquiv.irreducible_iff Bivariate.swap.toMulEquiv).mpr hF
    have hswap_root : ((Bivariate.swap F).map (evalRingHom y₀)).eval z₀ = 0 := by
      rw [eval_swap_eq, hroot]
    have hirr := irreducible_algebraicClosure_of_smooth_y (Bivariate.swap F) hswap_irr y₀ z₀
      hswap_root hz
    rw [mapBiv_swap] at hirr
    exact (MulEquiv.irreducible_iff Bivariate.swap.toMulEquiv).mp hirr

#print axioms fixed_by_algEquiv_pow_mem_range
#print axioms biv_fixed_pow_descends
#print axioms irreducible_algebraicClosure_of_smooth_y
#print axioms irreducible_algebraicClosure_of_smooth

end ArkLib.ProximityGap.Frontier.GeometricIrreducibilitySmoothPoint
