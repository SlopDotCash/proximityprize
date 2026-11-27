/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PlaneCurveLinearAlgebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # Function-field derivations and constant-extension irreducibility for plane curves -/

set_option autoImplicit false
noncomputable section

open Polynomial MvPolynomial Finset Module
open ArkLib.ProximityGap.Frontier.PlaneBezoutWithMultiplicity
open ArkLib.ProximityGap.Frontier.PlaneCurveLinearAlgebra

namespace ArkLib.ProximityGap.Frontier.PlaneCurveFunctionField

section AlgebraAndDerivations

variable {K : Type*} [Field K]

/-- Convenience helper: `p.totalDegree ≤ d` if every monomial in `p.support` has weight `≤ d`. -/
theorem totalDegree_le_of_forall_mem_support {σ R : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} {d : ℕ} (h : ∀ e ∈ p.support, (e.sum fun _ v => v) ≤ d) :
    p.totalDegree ≤ d :=
  Finset.sup_le h

/-- Convenience helper: `MvPolynomial.map` does not increase `totalDegree`. -/
theorem totalDegree_map_le' {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (p : MvPolynomial σ R) :
    (MvPolynomial.map φ p).totalDegree ≤ p.totalDegree :=
  Finset.sup_le fun _ he =>
    Finset.le_sup (f := fun s : σ →₀ ℕ => s.sum fun _ e => e) (MvPolynomial.support_map_subset φ p he)

/-- Dehomogenization of an irreducible homogeneous polynomial `F` of degree `m ≥ 2` is irreducible
in `MvPolynomial (Fin 2) K`. -/
theorem irreducible_dehom {F : MvPolynomial (Fin 3) K} {m : ℕ}
    (hF_irr : Irreducible F) (hF_hom : F.IsHomogeneous m) (hm : 2 ≤ m) :
    Irreducible (dehom F) := by
  have hX2_ndvd : ¬ (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ F := by
    intro ⟨Q, hQ⟩
    rcases hF_irr.isUnit_or_isUnit hQ with hu | hQu
    · obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
      have h := congrArg (fun p : MvPolynomial (Fin 3) K => p.coeff (Finsupp.single 2 1)) hc
      have hne : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single 2 1 :=
        Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
      simp [MvPolynomial.coeff_X, MvPolynomial.coeff_C, hne] at h
    · obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hQu
      have hdeg : F.IsHomogeneous 1 := by
        rw [hQ, hc]
        simpa using (MvPolynomial.isHomogeneous_X K (2 : Fin 3)).mul (MvPolynomial.isHomogeneous_C (Fin 3) c)
      obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hF_irr.ne_zero
      have h1 := hF_hom (MvPolynomial.mem_support_iff.mp he)
      have h2 := hdeg (MvPolynomial.mem_support_iff.mp he)
      omega
  have hf_deg : (dehom F).totalDegree = m := by
    apply le_antisymm
    · refine totalDegree_le_of_forall_mem_support fun e he => ?_
      rw [MvPolynomial.mem_support_iff, F.as_sum, map_sum, MvPolynomial.coeff_sum] at he
      obtain ⟨n, hn, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
      rw [dehom_monomial, MvPolynomial.coeff_monomial] at hne
      split_ifs at hne with hpn
      · rw [← hpn, m2_sum, proj2_apply_0, proj2_apply_1]
        have h := hF_hom (MvPolynomial.mem_support_iff.mp hn)
        rw [weight_one_eq_sum, m3_sum] at h
        omega
      · exact absurd rfl hne
    · by_contra hlt
      have hlt' : (dehom F).totalDegree < m := not_le.mp hlt
      -- Then every term of `F` has `e 0 + e 1 < m`, so `e 2 ≥ 1`, so `X 2 ∣ F`.
      have hX2 : (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ F := by
        have hF_eq : F = homog m (dehom F) :=
          dehom_inj_on_homogeneous m hF_hom (homog_isHomogeneous m _ (le_of_lt hlt')) (dehom_homog m _).symm
        rw [hF_eq]
        refine ⟨∑ e ∈ (dehom F).support,
            MvPolynomial.monomial (ext3 e (m - (e 0 + e 1) - 1)) ((dehom F).coeff e), ?_⟩
        rw [Finset.mul_sum]; unfold homog
        refine Finset.sum_congr rfl fun e he => ?_
        have hle : e 0 + e 1 ≤ (dehom F).totalDegree := by
          have := Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum fun _ v => v) he
          rwa [m2_sum] at this
        rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
        exact congrArg (fun d => MvPolynomial.monomial d ((dehom F).coeff e))
          (by ext i; fin_cases i <;> simp; omega)
      exact hX2_ndvd hX2
  have hf_not_unit : ¬ IsUnit (dehom F) := by
    intro hu
    obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
    rw [hc, MvPolynomial.totalDegree_C] at hf_deg
    omega
  refine ⟨hf_not_unit, ?_⟩
  intro a b hab
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; rw [hab, MvPolynomial.totalDegree_zero] at hf_deg; omega
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab; rw [hab, MvPolynomial.totalDegree_zero] at hf_deg; omega
  let da := a.totalDegree
  let db := b.totalDegree
  have hsum_deg : da + db = m := by
    have hmul : (homog da a * homog db b).IsHomogeneous (da + db) :=
      (homog_isHomogeneous da a le_rfl).mul (homog_isHomogeneous db b le_rfl)
    have hdehom_mul : dehom (homog da a * homog db b) = dehom F := by
      rw [map_mul, dehom_homog, dehom_homog, hab]
    have hmul_ne : homog da a * homog db b ≠ 0 := by
      intro h0
      have := congrArg dehom h0
      rw [hdehom_mul, map_zero] at this
      rw [this, MvPolynomial.totalDegree_zero] at hf_deg; omega
    have hle : m ≤ da + db := by
      rw [← hf_deg, hab]
      exact MvPolynomial.totalDegree_mul a b
    -- If `da + db > m`, `homog da a * homog db b` would equal `X 2 ^ (da + db - m) * F`, impossible
    -- since `X 2` divides neither `homog da a` nor `homog db b`.
    have hF_mul : homog da a * homog db b = MvPolynomial.X 2 ^ (da + db - m) * F := by
      apply dehom_inj_on_homogeneous (da + db) hmul
      · have := ((MvPolynomial.isHomogeneous_X K (2 : Fin 3)).pow (da + db - m)).mul hF_hom
        rwa [one_mul, Nat.sub_add_cancel hle] at this
      · rw [hdehom_mul, map_mul, map_pow, dehom]; simp
    by_contra hne
    have hgt : m < da + db := by omega
    have hX2_dvd_prod : (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ homog da a * homog db b := by
      rw [hF_mul]
      exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
    have hX2_prime : Prime (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) := by
      -- `X 2` is prime because `MvPolynomial (Fin 3) K ⧸ (X 2) ≅ MvPolynomial (Fin 2) K` is a domain.
      have hker : RingHom.ker (MvPolynomial.aeval (R := K) ![MvPolynomial.X 0, MvPolynomial.X 1, (0 : MvPolynomial (Fin 2) K)]) =
          Ideal.span {MvPolynomial.X 2} := by
        apply le_antisymm
        · intro p hp
          rw [RingHom.mem_ker] at hp
          rw [Ideal.mem_span_singleton]
          refine ⟨∑ e ∈ p.support, MvPolynomial.monomial (e - Finsupp.single 2 1) (p.coeff e), ?_⟩
          rw [Finset.mul_sum]; conv_lhs => rw [p.as_sum]
          refine Finset.sum_congr rfl fun e he => ?_
          have he2 : 1 ≤ e 2 := by
            by_contra h2
            have he20 : e 2 = 0 := by omega
            have hcoeff : ((MvPolynomial.aeval (R := K) ![MvPolynomial.X 0, MvPolynomial.X 1, (0 : MvPolynomial (Fin 2) K)]) p).coeff (proj2 e) = p.coeff e := by
              conv_lhs => rw [p.as_sum, map_sum, MvPolynomial.coeff_sum]
              rw [Finset.sum_eq_single e]
              · rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq,
                  Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
                have h0v : (![MvPolynomial.X 0, MvPolynomial.X 1, (0 : MvPolynomial (Fin 2) K)] :
                    Fin 3 → MvPolynomial (Fin 2) K) 0 = MvPolynomial.X 0 := rfl
                have h1v : (![MvPolynomial.X 0, MvPolynomial.X 1, (0 : MvPolynomial (Fin 2) K)] :
                    Fin 3 → MvPolynomial (Fin 2) K) 1 = MvPolynomial.X 1 := rfl
                have h2v : (![MvPolynomial.X 0, MvPolynomial.X 1, (0 : MvPolynomial (Fin 2) K)] :
                    Fin 3 → MvPolynomial (Fin 2) K) 2 = 0 := rfl
                rw [h0v, h1v, h2v, he20, pow_zero, mul_one, MvPolynomial.X, MvPolynomial.X,
                  MvPolynomial.monomial_pow, MvPolynomial.monomial_pow,
                  MvPolynomial.monomial_mul_monomial, MvPolynomial.C_mul_monomial,
                  MvPolynomial.coeff_monomial]
                have hpe : Finsupp.single (0 : Fin 2) (e 0) + Finsupp.single 1 (e 1) = proj2 e := by
                  ext i; fin_cases i <;> simp [proj2]
                simp [hpe]
              · intro n _ hne
                rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq,
                  Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
                have h0v : (![MvPolynomial.X 0, MvPolynomial.X 1, (0 : MvPolynomial (Fin 2) K)] :
                    Fin 3 → MvPolynomial (Fin 2) K) 0 = MvPolynomial.X 0 := rfl
                have h1v : (![MvPolynomial.X 0, MvPolynomial.X 1, (0 : MvPolynomial (Fin 2) K)] :
                    Fin 3 → MvPolynomial (Fin 2) K) 1 = MvPolynomial.X 1 := rfl
                have h2v : (![MvPolynomial.X 0, MvPolynomial.X 1, (0 : MvPolynomial (Fin 2) K)] :
                    Fin 3 → MvPolynomial (Fin 2) K) 2 = 0 := rfl
                rw [h0v, h1v, h2v]
                by_cases hn2 : n 2 = 0
                · rw [hn2, pow_zero, mul_one, MvPolynomial.X, MvPolynomial.X,
                    MvPolynomial.monomial_pow, MvPolynomial.monomial_pow,
                    MvPolynomial.monomial_mul_monomial, MvPolynomial.C_mul_monomial,
                    MvPolynomial.coeff_monomial]
                  split_ifs with heq
                  · exfalso; apply hne; ext i; fin_cases i
                    · change n 0 = e 0
                      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq; simpa [proj2] using this
                    · change n 1 = e 1
                      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) heq; simpa [proj2] using this
                    · simp [he20, hn2]
                  · rfl
                · simp [zero_pow hn2]
              · intro hnot; exact absurd he hnot
            rw [hp] at hcoeff
            exact MvPolynomial.mem_support_iff.mp he (by simpa using hcoeff.symm)
          rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
          exact congrArg (fun d => MvPolynomial.monomial d (p.coeff e))
            (by ext i; fin_cases i <;> simp; omega)
        · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]; simp
      have hisprime : (Ideal.span {(MvPolynomial.X 2 : MvPolynomial (Fin 3) K)}).IsPrime := by
        rw [← hker]
        exact RingHom.ker_isPrime _
      exact (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero 2)).mp hisprime
    have hndvd_homog (g : MvPolynomial (Fin 2) K) (hg : g ≠ 0) :
        ¬ (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ homog g.totalDegree g := by
      intro ⟨Q, hQ⟩
      obtain ⟨e, he, he_max⟩ :=
        Finset.exists_mem_eq_sup g.support (MvPolynomial.support_nonempty.mpr hg)
          (fun s : Fin 2 →₀ ℕ => s.sum fun _ v => v)
      have hdeg_eq : e 0 + e 1 = g.totalDegree := by rw [← m2_sum]; exact he_max.symm
      have h1 : (homog g.totalDegree g).coeff (ext3 e 0) = g.coeff e := by
        simp only [homog, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
        rw [Finset.sum_eq_single e]
        · simp [hdeg_eq]
        · intro n _ hne
          split_ifs with heq
          · exfalso; exact hne (by simpa [proj2_ext3] using congrArg proj2 heq)
          · rfl
        · intro hnot; exact absurd he hnot
      have h2 : (MvPolynomial.X 2 * Q).coeff (ext3 e 0) = 0 := by
        rw [MvPolynomial.coeff_mul]
        apply Finset.sum_eq_zero; rintro ⟨u, v⟩ huv
        have hu2 : u 2 + v 2 = 0 := by
          have := congrArg (fun f : Fin 3 →₀ ℕ => f 2) (Finset.mem_antidiagonal.mp huv)
          simpa using this
        have hu : (MvPolynomial.X 2 : MvPolynomial (Fin 3) K).coeff u = 0 := by
          rw [MvPolynomial.coeff_X]
          split_ifs with heq
          · exfalso; have := congrArg (fun f : Fin 3 →₀ ℕ => f 2) heq; simp at this; omega
          · rfl
        rw [hu, zero_mul]
      rw [← hQ, h1] at h2
      exact MvPolynomial.mem_support_iff.mp he h2
    rcases hX2_prime.dvd_or_dvd hX2_dvd_prod with h1 | h2
    · exact hndvd_homog a ha0 h1
    · exact hndvd_homog b hb0 h2
  have hF_fac : F = homog da a * homog db b := by
    apply dehom_inj_on_homogeneous m hF_hom
    · rw [← hsum_deg]
      exact (homog_isHomogeneous da a le_rfl).mul (homog_isHomogeneous db b le_rfl)
    · rw [map_mul, dehom_homog, dehom_homog, hab]
  rcases hF_irr.isUnit_or_isUnit hF_fac with hua | hub
  · left
    have := hua.map dehom.toRingHom
    rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dehom_homog] at this
  · right
    have := hub.map dehom.toRingHom
    rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dehom_homog] at this

/-- An irreducible polynomial `f : MvPolynomial (Fin 2) K` remains irreducible after base change
to `FractionRing K[X]`. -/
theorem irreducible_map_fractionRing_poly (f : MvPolynomial (Fin 2) K) (hf : Irreducible f) :
    Irreducible (MvPolynomial.map (algebraMap K (FractionRing K[X])) f) := by
  classical
  let R := MvPolynomial (Fin 2) K
  let L := FractionRing K[X]
  let ιK : K →+* K[X] := Polynomial.C
  let ι : K[X] →+* L := algebraMap K[X] L
  have hcomp : algebraMap K L = ι.comp ιK := by
    ext a; rfl
  -- Equivalence `MvPolynomial (Fin 2) K[X] ≃+* R[X]`.
  let eRX : MvPolynomial (Fin 2) K[X] →+* R[X] :=
    MvPolynomial.eval₂Hom (Polynomial.mapRingHom MvPolynomial.C)
      (fun i => Polynomial.C (MvPolynomial.X i))
  let eBack : R[X] →+* MvPolynomial (Fin 2) K[X] :=
    Polynomial.eval₂RingHom (MvPolynomial.map Polynomial.C) (MvPolynomial.C Polynomial.X)
  have he_left : ∀ p, eBack (eRX p) = p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C q =>
      induction q using Polynomial.induction_on' with
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
      | monomial k a =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        have hC : eBack (eRX (MvPolynomial.C (Polynomial.C a))) = MvPolynomial.C (Polynomial.C a) := by
          simp [eRX, eBack]
          exact MvPolynomial.map_C Polynomial.C a
        have hX : eBack (eRX (MvPolynomial.C Polynomial.X)) = MvPolynomial.C Polynomial.X := by
          simp [eRX, eBack]
        rw [map_mul, map_pow, map_mul, map_pow, map_mul, map_pow, hC, hX]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | mul_X p i hp =>
      rw [map_mul, map_mul, hp]
      have hXi : eBack (eRX (MvPolynomial.X i)) = MvPolynomial.X i := by
        simp [eRX, eBack]
        exact MvPolynomial.map_X Polynomial.C i
      rw [hXi]
  have he_right : ∀ q, eRX (eBack q) = q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | monomial k p =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      have hC : eRX (MvPolynomial.map Polynomial.C p) = Polynomial.C p := by
        induction p using MvPolynomial.induction_on with
        | C a => simp [eRX]
        | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
        | mul_X a i ha =>
          rw [map_mul, map_mul, ha]
          have hXi : eRX (MvPolynomial.map Polynomial.C (MvPolynomial.X i)) = Polynomial.C (MvPolynomial.X i) := by
            simp [eRX]
          rw [hXi, ← map_mul]
      have hCp : eBack (Polynomial.C p) = MvPolynomial.map Polynomial.C p := by simp [eBack]
      have hX : eBack Polynomial.X = MvPolynomial.C Polynomial.X := by simp [eBack]
      have heX : eRX (MvPolynomial.C Polynomial.X) = Polynomial.X := by simp [eRX]
      rw [map_mul, map_pow, hCp, hX, map_mul, map_pow, hC, heX]
  have hf_map_eq_all : ∀ g : MvPolynomial (Fin 2) K, eRX (MvPolynomial.map ιK g) = Polynomial.C g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [eRX, ιK]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
    | mul_X a i ha =>
      rw [map_mul, map_mul, ha]
      have hXi : eRX (MvPolynomial.map ιK (MvPolynomial.X i)) = Polynomial.C (MvPolynomial.X i) := by
        simp [eRX]
      rw [hXi, ← map_mul]
  have hf_map_eq : eRX (MvPolynomial.map ιK f) = Polynomial.C f := hf_map_eq_all f
  -- `Polynomial.C f` is prime in `R[X]`.
  have hCf_prime : Prime (Polynomial.C f : R[X]) := by
    have hf_prime : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf
    have : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr hf_prime
    let π : R →+* R ⧸ Ideal.span {f} := Ideal.Quotient.mk (Ideal.span {f})
    have hker : RingHom.ker (Polynomial.mapRingHom π) = Ideal.span {Polynomial.C f} := by
      apply le_antisymm
      · intro p hp
        rw [RingHom.mem_ker] at hp
        rw [Ideal.mem_span_singleton]
        have hcoeff : ∀ j, f ∣ p.coeff j := by
          intro j
          have := congrArg (fun q : (R ⧸ Ideal.span {f})[X] => q.coeff j) hp
          simp only [coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_zero] at this
          exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp this)
        choose q hq using hcoeff
        refine ⟨∑ j ∈ p.support, Polynomial.monomial j (q j), ?_⟩
        apply Polynomial.ext; intro j
        rw [Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff]
        by_cases hj : j ∈ p.support
        · rw [Finset.sum_eq_single j]
          · simp [hq j]
          · intro i _ hij; simp [Polynomial.coeff_monomial, hij]
          · intro h; exact absurd hj h
        · rw [Polynomial.notMem_support_iff.mp hj]
          symm; rw [mul_eq_zero]; right
          apply Finset.sum_eq_zero; intro i hi
          have hij : i ≠ j := fun h => hj (h ▸ hi)
          simp [Polynomial.coeff_monomial, hij]
      · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
        apply Polynomial.ext; intro j
        simp only [coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_C, Polynomial.coeff_zero]
        split_ifs
        · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
        · exact map_zero π
    have hisprime : (Ideal.span {(Polynomial.C f : R[X])}).IsPrime := by
      rw [← hker]; exact RingHom.ker_isPrime _
    exact (Ideal.span_singleton_prime (Polynomial.C_ne_zero.mpr hf.ne_zero)).mp hisprime
  have hclear (g : MvPolynomial (Fin 2) L) :
      ∃ (c : K[X]) (g₀ : MvPolynomial (Fin 2) K[X]), c ≠ 0 ∧
        MvPolynomial.map ι g₀ = MvPolynomial.C (ι c) * g := by
    have hrep : ∀ e, ∃ a b : K[X], b ≠ 0 ∧ g.coeff e = ι a / ι b := by
      intro e
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := K[X]) (g.coeff e)
      exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, hab.symm⟩
    choose a b hb hab using hrep
    let c : K[X] := ∏ e ∈ g.support, b e
    have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun e _ => hb e
    let g₀ : MvPolynomial (Fin 2) K[X] :=
      ∑ e ∈ g.support, MvPolynomial.monomial e (a e * ∏ e' ∈ g.support.erase e, b e')
    refine ⟨c, g₀, hc, ?_⟩
    ext e
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]
    by_cases he : e ∈ g.support
    · have hprod : c = b e * ∏ e' ∈ g.support.erase e, b e' :=
        (Finset.mul_prod_erase g.support b he).symm
      have hcoeff : g₀.coeff e = a e * ∏ e' ∈ g.support.erase e, b e' := by
        simp only [g₀, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
        rw [Finset.sum_eq_single e]
        · simp
        · intro e' _ hne; simp [hne]
        · intro h; exact absurd he h
      rw [hcoeff, map_mul, hab e, hprod, map_mul]
      have hbe : ι (b e) ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective K[X] L)).mpr (hb e)
      dsimp only [ι, L] at hbe ⊢
      field_simp [hbe]
    · have hge : g.coeff e = 0 := MvPolynomial.notMem_support_iff.mp he
      have hg0e : g₀.coeff e = 0 := by
        simp only [g₀, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
        apply Finset.sum_eq_zero; intro e' he'
        have hne : e' ≠ e := fun h => he (h ▸ he')
        simp [hne]
      simp [hge, hg0e]
  have hf_not_unit : ¬ IsUnit (MvPolynomial.map (algebraMap K L) f) := by
    intro hu
    obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
    have hf_deg0 : f.totalDegree = 0 := by
      have hdeg := congrArg MvPolynomial.totalDegree hc
      rw [MvPolynomial.totalDegree_C] at hdeg
      have heq : (MvPolynomial.map (algebraMap K L) f).totalDegree = f.totalDegree := by
        apply le_antisymm (totalDegree_map_le' _ _)
        refine totalDegree_le_of_forall_mem_support fun e he => ?_
        have he' : (MvPolynomial.map (algebraMap K L) f).coeff e ≠ 0 := by
          rw [MvPolynomial.coeff_map]
          exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr (MvPolynomial.mem_support_iff.mp he)
        exact Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum fun _ v => v)
          (MvPolynomial.mem_support_iff.mpr he')
      omega
    have ha : f = MvPolynomial.C (f.coeff 0) := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hf_deg0
    have ha_ne : f.coeff 0 ≠ 0 := by intro h0; rw [h0, map_zero] at ha; exact hf.ne_zero ha
    exact hf.not_isUnit (ha ▸ ha_ne.isUnit.map MvPolynomial.C)
  refine ⟨hf_not_unit, ?_⟩
  intro A B hAB
  obtain ⟨cA, A₀, hcA, hA₀⟩ := hclear A
  obtain ⟨cB, B₀, hcB, hB₀⟩ := hclear B
  have hmul_eq : MvPolynomial.C (cA * cB) * MvPolynomial.map ιK f = A₀ * B₀ := by
    apply MvPolynomial.map_injective ι (IsFractionRing.injective K[X] L)
    rw [map_mul (MvPolynomial.map ι), MvPolynomial.map_C, MvPolynomial.map_map, ← hcomp,
      map_mul (MvPolynomial.map ι), hA₀, hB₀, hAB, map_mul, map_mul]
    ring
  have hdiv_prod : Polynomial.C f ∣ eRX A₀ * eRX B₀ := by
    refine ⟨eRX (MvPolynomial.C (cA * cB)), ?_⟩
    rw [← map_mul, ← hmul_eq, map_mul, hf_map_eq, mul_comm]
  -- Helper: if `C f ∣ eRX G₀` in `R[X]` and `C c * f.map ιK = G₀ * H₀`, then `H₀` is a constant in `K[X]`.
  have hunit_of_dvd (G₀ H₀ : MvPolynomial (Fin 2) K[X]) (H : MvPolynomial (Fin 2) L) (cH : K[X])
      (hcH : cH ≠ 0) (hH₀ : MvPolynomial.map ι H₀ = MvPolynomial.C (ι cH) * H)
      (hmul : MvPolynomial.C (cA * cB) * MvPolynomial.map ιK f = G₀ * H₀)
      (hdvd : Polynomial.C f ∣ eRX G₀) : IsUnit H := by
    obtain ⟨Q', hQ'⟩ := hdvd
    let Q := eBack Q'
    have hG₀ : G₀ = MvPolynomial.map ιK f * Q := by
      rw [← he_left G₀, hQ', map_mul, ← hf_map_eq, he_left]
    have hcancel : MvPolynomial.C (cA * cB) = Q * H₀ := by
      have hf_ne : MvPolynomial.map ιK f ≠ 0 :=
        (map_ne_zero_iff _ (MvPolynomial.map_injective ιK Polynomial.C_injective)).mpr hf.ne_zero
      apply mul_left_cancel₀ hf_ne
      rw [mul_comm, hmul, hG₀]; ring
    -- Since `Q * H₀ = C (cA * cB)` over the domain `K[X]`, `H₀` has totalDegree 0!
    have hH₀_deg0 : H₀.totalDegree = 0 := by
      by_contra hpos
      -- Map to `MvPolynomial (Fin 2) L` where `Q * H₀ = C (ι (cA * cB))` is a unit!
      have hcAB : cA * cB ≠ 0 := mul_ne_zero hcA hcB
      have huL : IsUnit (MvPolynomial.map ι H₀) := by
        have h1 : MvPolynomial.map ι Q * MvPolynomial.map ι H₀ =
            MvPolynomial.C (ι (cA * cB)) := by
          rw [← map_mul, ← hcancel, MvPolynomial.map_C]
        have huC : IsUnit (MvPolynomial.C (ι (cA * cB)) : MvPolynomial (Fin 2) L) :=
          ((map_ne_zero_iff ι (IsFractionRing.injective K[X] L)).mpr hcAB).isUnit.map MvPolynomial.C
        exact isUnit_of_mul_isUnit_right (h1.symm ▸ huC)
      obtain ⟨d, _, hd⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp huL
      apply hpos
      have hdeg := congrArg MvPolynomial.totalDegree hd
      rw [MvPolynomial.totalDegree_C] at hdeg
      have heq : (MvPolynomial.map ι H₀).totalDegree = H₀.totalDegree := by
        apply le_antisymm (totalDegree_map_le' _ _)
        refine totalDegree_le_of_forall_mem_support fun e he => ?_
        have he' : (MvPolynomial.map ι H₀).coeff e ≠ 0 := by
          rw [MvPolynomial.coeff_map]
          exact (map_ne_zero_iff ι (IsFractionRing.injective K[X] L)).mpr (MvPolynomial.mem_support_iff.mp he)
        exact Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum fun _ v => v)
          (MvPolynomial.mem_support_iff.mpr he')
      omega
    have hb₀ : H₀ = MvPolynomial.C (H₀.coeff 0) := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hH₀_deg0
    have hb₀_ne : H₀.coeff 0 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hb₀
      rw [hb₀, mul_zero] at hcancel
      have h0' := congrArg (fun p : MvPolynomial (Fin 2) K[X] => p.coeff 0) hcancel
      simp [mul_ne_zero hcA hcB] at h0'
    have hH_eq : H = MvPolynomial.C (ι (H₀.coeff 0) / ι cH) := by
      have hcHL : ι cH ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective K[X] L)).mpr hcH
      apply mul_left_cancel₀ (MvPolynomial.C_ne_zero.mpr hcHL)
      rw [← hH₀]
      conv_lhs => rw [hb₀]
      rw [MvPolynomial.map_C, ← map_mul, mul_div_cancel₀ _ hcHL]
    rw [hH_eq]
    have hb₀L : ι (H₀.coeff 0) ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective K[X] L)).mpr hb₀_ne
    have hcHL : ι cH ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective K[X] L)).mpr hcH
    exact (div_ne_zero hb₀L hcHL).isUnit.map MvPolynomial.C
  rcases hCf_prime.dvd_or_dvd hdiv_prod with hA | hB
  · right; exact hunit_of_dvd A₀ B₀ B cB hcB hB₀ hmul_eq hA
  · left; exact hunit_of_dvd B₀ A₀ A cA hcA hA₀ (by rw [hmul_eq, mul_comm]) hB

/-- Existence of fraction representation in `FractionRing D`. -/
private theorem exists_div_rep {D : Type*} [CommRing D] [IsDomain D] (x : FractionRing D) :
    ∃ a b : D, b ≠ 0 ∧ x = algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := D) x
  exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, hab.symm⟩

/-- Underlying function of the fraction-field derivation extension. -/
private def fracDerivAux {D : Type*} [CommRing D] [IsDomain D] [Algebra K D]
    (δ : Derivation K D D) (x : FractionRing D) : FractionRing D :=
  let a := (exists_div_rep x).choose
  let b := (exists_div_rep x).choose_spec.choose
  (algebraMap D (FractionRing D) b * algebraMap D (FractionRing D) (δ a) -
    algebraMap D (FractionRing D) a * algebraMap D (FractionRing D) (δ b)) /
    (algebraMap D (FractionRing D) b) ^ 2

private theorem fracDerivAux_div {D : Type*} [CommRing D] [IsDomain D] [Algebra K D]
    (δ : Derivation K D D) (a b : D) (hb : b ≠ 0) :
    fracDerivAux δ (algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b) =
      (algebraMap D (FractionRing D) b * algebraMap D (FractionRing D) (δ a) -
        algebraMap D (FractionRing D) a * algebraMap D (FractionRing D) (δ b)) /
        (algebraMap D (FractionRing D) b) ^ 2 := by
  have hwd : ∀ a₁ b₁ a₂ b₂ : D, b₁ ≠ 0 → b₂ ≠ 0 →
      algebraMap D (FractionRing D) a₁ / algebraMap D (FractionRing D) b₁ =
        algebraMap D (FractionRing D) a₂ / algebraMap D (FractionRing D) b₂ →
      (algebraMap D (FractionRing D) b₁ * algebraMap D (FractionRing D) (δ a₁) -
          algebraMap D (FractionRing D) a₁ * algebraMap D (FractionRing D) (δ b₁)) /
          (algebraMap D (FractionRing D) b₁) ^ 2 =
      (algebraMap D (FractionRing D) b₂ * algebraMap D (FractionRing D) (δ a₂) -
          algebraMap D (FractionRing D) a₂ * algebraMap D (FractionRing D) (δ b₂)) /
          (algebraMap D (FractionRing D) b₂) ^ 2 := by
    intro a₁ b₁ a₂ b₂ hb₁ hb₂ heq
    have hb₁E : algebraMap D (FractionRing D) b₁ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective D (FractionRing D))).mpr hb₁
    have hb₂E : algebraMap D (FractionRing D) b₂ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective D (FractionRing D))).mpr hb₂
    have hcrossE : algebraMap D (FractionRing D) (a₁ * b₂) =
        algebraMap D (FractionRing D) (a₂ * b₁) := by
      rw [map_mul, map_mul]
      exact (div_eq_div_iff hb₁E hb₂E).mp heq
    have hcross : a₁ * b₂ = a₂ * b₁ := IsFractionRing.injective D (FractionRing D) hcrossE
    have hder := congrArg δ hcross
    simp only [δ.leibniz, smul_eq_mul] at hder
    have hderE := congrArg (algebraMap D (FractionRing D)) hder
    simp only [map_add, map_mul] at hderE
    rw [div_eq_div_iff (pow_ne_zero 2 hb₁E) (pow_ne_zero 2 hb₂E)]
    have hcE : algebraMap D (FractionRing D) a₁ * algebraMap D (FractionRing D) b₂ =
        algebraMap D (FractionRing D) a₂ * algebraMap D (FractionRing D) b₁ := by
      simpa only [map_mul] using hcrossE
    linear_combination
      algebraMap D (FractionRing D) b₁ * algebraMap D (FractionRing D) b₂ * hderE -
      (algebraMap D (FractionRing D) b₁ * algebraMap D (FractionRing D) (δ b₂) +
        algebraMap D (FractionRing D) b₂ * algebraMap D (FractionRing D) (δ b₁)) * hcE
  unfold fracDerivAux
  set hrep := exists_div_rep (algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b)
  exact hwd _ _ a b hrep.choose_spec.choose_spec.1 hb hrep.choose_spec.choose_spec.2.symm

/-- Extending a `K`-derivation on an integral domain `D` to `FractionRing D` by the quotient rule. -/
def fracDeriv {D : Type*} [CommRing D] [IsDomain D] [Algebra K D]
    (δ : Derivation K D D) : Derivation K (FractionRing D) (FractionRing D) where
  toFun := fracDerivAux δ
  map_add' x y := by
    obtain ⟨a₁, b₁, hb₁, h₁⟩ := exists_div_rep x
    obtain ⟨a₂, b₂, hb₂, h₂⟩ := exists_div_rep y
    have hb₁E : algebraMap D (FractionRing D) b₁ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective D (FractionRing D))).mpr hb₁
    have hb₂E : algebraMap D (FractionRing D) b₂ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective D (FractionRing D))).mpr hb₂
    rw [h₁, h₂]
    have hsum : algebraMap D (FractionRing D) a₁ / algebraMap D (FractionRing D) b₁ +
        algebraMap D (FractionRing D) a₂ / algebraMap D (FractionRing D) b₂ =
        algebraMap D (FractionRing D) (a₁ * b₂ + a₂ * b₁) /
          algebraMap D (FractionRing D) (b₁ * b₂) := by
      rw [div_add_div _ _ hb₁E hb₂E, map_add, map_mul, map_mul, map_mul,
        mul_comm (algebraMap D (FractionRing D) b₁)]
    rw [hsum, fracDerivAux_div δ _ _ (mul_ne_zero hb₁ hb₂),
      fracDerivAux_div δ _ _ hb₁, fracDerivAux_div δ _ _ hb₂]
    rw [div_add_div _ _ (pow_ne_zero 2 hb₁E) (pow_ne_zero 2 hb₂E),
      div_eq_div_iff (pow_ne_zero 2 (by rw [map_mul]; exact mul_ne_zero hb₁E hb₂E))
        (mul_ne_zero (pow_ne_zero 2 hb₁E) (pow_ne_zero 2 hb₂E))]
    simp only [map_add, map_mul, δ.leibniz, smul_eq_mul]
    ring
  map_smul' c x := by
    obtain ⟨a, b, hb, hx⟩ := exists_div_rep x
    rw [hx]
    have hsm : c • (algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b) =
        algebraMap D (FractionRing D) (c • a) / algebraMap D (FractionRing D) b := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_div_assoc,
        IsScalarTower.algebraMap_apply K D (FractionRing D) c]
    rw [hsm, fracDerivAux_div δ _ _ hb, fracDerivAux_div δ _ _ hb, δ.map_smul,
      Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, Algebra.smul_def, RingHom.id_apply,
      ← IsScalarTower.algebraMap_apply K D (FractionRing D) c, ← mul_div_assoc]
    congr 1; ring
  map_one_eq_zero' := by
    change fracDerivAux δ 1 = 0
    have h1 : (1 : FractionRing D) = algebraMap D (FractionRing D) 1 / algebraMap D (FractionRing D) 1 := by
      simp
    rw [h1, fracDerivAux_div δ 1 1 one_ne_zero]
    simp
  leibniz' x y := by
    change fracDerivAux δ (x * y) = x • fracDerivAux δ y + y • fracDerivAux δ x
    obtain ⟨a₁, b₁, hb₁, h₁⟩ := exists_div_rep x
    obtain ⟨a₂, b₂, hb₂, h₂⟩ := exists_div_rep y
    have hb₁E : algebraMap D (FractionRing D) b₁ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective D (FractionRing D))).mpr hb₁
    have hb₂E : algebraMap D (FractionRing D) b₂ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective D (FractionRing D))).mpr hb₂
    rw [h₁, h₂]
    have hmul : (algebraMap D (FractionRing D) a₁ / algebraMap D (FractionRing D) b₁) *
        (algebraMap D (FractionRing D) a₂ / algebraMap D (FractionRing D) b₂) =
        algebraMap D (FractionRing D) (a₁ * a₂) / algebraMap D (FractionRing D) (b₁ * b₂) := by
      rw [div_mul_div_comm, map_mul, map_mul]
    rw [hmul, fracDerivAux_div δ _ _ (mul_ne_zero hb₁ hb₂),
      fracDerivAux_div δ _ _ hb₁, fracDerivAux_div δ _ _ hb₂]
    simp only [smul_eq_mul, div_mul_div_comm]
    rw [div_add_div _ _ (mul_ne_zero hb₁E (pow_ne_zero 2 hb₂E)) (mul_ne_zero hb₂E (pow_ne_zero 2 hb₁E)),
      div_eq_div_iff (pow_ne_zero 2 (by rw [map_mul]; exact mul_ne_zero hb₁E hb₂E))
        (mul_ne_zero (mul_ne_zero hb₁E (pow_ne_zero 2 hb₂E)) (mul_ne_zero hb₂E (pow_ne_zero 2 hb₁E)))]
    simp only [map_add, map_mul, δ.leibniz, smul_eq_mul]
    ring

theorem fracDeriv_algebraMap {D : Type*} [CommRing D] [IsDomain D] [Algebra K D]
    (δ : Derivation K D D) (a : D) :
    fracDeriv δ (algebraMap D (FractionRing D) a) = algebraMap D (FractionRing D) (δ a) := by
  have h1 : algebraMap D (FractionRing D) a =
      algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) 1 := by simp
  change fracDerivAux δ _ = _
  rw [h1, fracDerivAux_div δ a 1 one_ne_zero]
  simp

/-- Descending a `K`-derivation on `A` that preserves an ideal `I` to `A ⧸ I`. -/
def quotDeriv {A : Type*} [CommRing A] [Algebra K A] (I : Ideal A)
    (δ : Derivation K A A) (hI : ∀ x ∈ I, δ x ∈ I) : Derivation K (A ⧸ I) (A ⧸ I) := by
  let fLin : A ⧸ I →ₗ[K] A ⧸ I :=
    Submodule.liftQ (I.restrictScalars K)
      ((Ideal.Quotient.mkₐ K I).toLinearMap.comp δ.toLinearMap)
      (fun x hx => by
        change Ideal.Quotient.mk I (δ x) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI x hx))
  have hf_mk (a : A) : fLin (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (δ a) := rfl
  refine
    { toLinearMap := fLin
      map_one_eq_zero' := by
        change fLin (Ideal.Quotient.mk I 1) = 0
        rw [hf_mk, δ.map_one_eq_zero, map_zero]
      leibniz' := fun x y => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
        change fLin (Ideal.Quotient.mk I (a * b)) = _
        rw [hf_mk, δ.leibniz]
        simp only [smul_eq_mul, map_add, map_mul, hf_mk] }

theorem quotDeriv_mk {A : Type*} [CommRing A] [Algebra K A] (I : Ideal A)
    (δ : Derivation K A A) (hI : ∀ x ∈ I, δ x ∈ I) (a : A) :
    quotDeriv I δ hI (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (δ a) := rfl

/-- Chain rule for a `K`-derivation on a bivariate polynomial evaluation. -/
theorem deriv_aeval_mv2 {E : Type*} [CommRing E] [Algebra K E]
    (D : Derivation K E E) (a b : E) (p : MvPolynomial (Fin 2) K) :
    D (MvPolynomial.aeval ![a, b] p) =
      MvPolynomial.aeval ![a, b] (pderiv 0 p) * D a +
      MvPolynomial.aeval ![a, b] (pderiv 1 p) * D b := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.aeval_C, D.map_algebraMap, pderiv_C, pderiv_C, map_zero, zero_mul, zero_mul, add_zero]
  | add p q hp hq =>
    simp only [map_add, hp, hq]; ring
  | mul_X p i hp =>
    rw [map_mul, D.leibniz, hp, pderiv_mul, pderiv_mul, map_add, map_add, map_mul, map_mul,
      map_mul, map_mul]
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero, pderiv_X_self,
        pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1), map_one, map_zero, mul_one, mul_zero,
        smul_eq_mul]
      ring
    · simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero, pderiv_X_self,
        pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0), map_one, map_zero, mul_one, mul_zero,
        smul_eq_mul]
      ring

/-- Chain rule for a `K`-derivation on a univariate polynomial evaluation with constant coefficients. -/
theorem deriv_aeval_poly {B E : Type*} [CommRing B] [CommRing E] [Algebra B E]
    (D : Derivation B E E) (x : E) (p : B[X]) :
    D (Polynomial.aeval x p) = Polynomial.aeval x p.derivative * D x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, add_mul]
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Polynomial.derivative_monomial, Polynomial.aeval_monomial,
      D.leibniz, D.map_algebraMap, smul_zero, add_zero, D.leibniz_pow, smul_eq_mul,
      smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    ring

/-- Any `B`-derivation on a finite field extension `E / B` whose degree is below `char B`
(or `char B = 0`) vanishes identically. -/
theorem derivation_eq_zero_of_finrank_lt_char {B E : Type*} [Field B] [Field E] [Algebra B E]
    [Module.Finite B E] (hchar : ∀ k : ℕ, 0 < k → k ≤ Module.finrank B E → (k : B) ≠ 0)
    (D : Derivation B E E) (x : E) : D x = 0 := by
  have hint : IsIntegral B x := Algebra.IsIntegral.isIntegral x
  let μ : B[X] := minpoly B x
  have hμ_irr : Irreducible μ := minpoly.irreducible hint
  have hμ_monic : μ.Monic := minpoly.monic hint
  have hμ_deg_pos : 0 < μ.natDegree := minpoly.natDegree_pos hint
  have hμ_deg_le : μ.natDegree ≤ Module.finrank B E := by
    have hli : LinearIndependent B (fun i : Fin μ.natDegree => x ^ i.val) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      let q : B[X] := ∑ j : Fin μ.natDegree, Polynomial.monomial j.val (c j)
      have hq_eval : Polynomial.aeval x q = 0 := by
        simp only [q, map_sum, Polynomial.aeval_monomial]
        simp_rw [← Algebra.smul_def]
        exact hc
      have hq_deg : q.natDegree < μ.natDegree := by
        have hle : q.natDegree ≤ μ.natDegree - 1 := by
          refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
          exact (Polynomial.natDegree_monomial_le _).trans (by omega)
        omega
      have hq0 : q = 0 := by
        by_contra hne
        have hdvd := minpoly.dvd B x hq_eval
        have hle : μ.natDegree ≤ q.natDegree := Polynomial.natDegree_le_of_dvd hdvd hne
        omega
      have hcoeff := congrArg (fun p : B[X] => p.coeff i.val) hq0
      simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hcoeff
      rw [Finset.sum_eq_single i] at hcoeff
      · simpa using hcoeff
      · intro j _ hji; simp [Fin.val_ne_of_ne hji]
      · intro h; exact absurd (Finset.mem_univ i) h
    simpa [Fintype.card_fin] using hli.fintype_card_le_finrank
  have hμ_der_ne : μ.derivative ≠ 0 := by
    intro h0
    have hcoeff := congrArg (fun p : B[X] => p.coeff (μ.natDegree - 1)) h0
    rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hμ_deg_pos,
      Polynomial.coeff_natDegree, hμ_monic.leadingCoeff, one_mul, Polynomial.coeff_zero,
      ← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hμ_deg_pos] at hcoeff
    exact hchar μ.natDegree hμ_deg_pos hμ_deg_le hcoeff
  have hμ_sep : μ.Separable := (Polynomial.separable_iff_derivative_ne_zero hμ_irr).mpr hμ_der_ne
  have hμ_der_eval_ne : Polynomial.aeval x μ.derivative ≠ 0 := by
    obtain ⟨a, b, hab⟩ := hμ_sep
    intro h0
    have h1 := congrArg (Polynomial.aeval x) hab
    rw [map_add, map_mul, map_mul, map_one, minpoly.aeval B x, h0, mul_zero, mul_zero, add_zero] at h1
    exact zero_ne_one h1
  have hD0 : Polynomial.aeval x μ.derivative * D x = 0 := by
    rw [← deriv_aeval_poly D x μ, minpoly.aeval B x, map_zero]
  exact (mul_eq_zero.mp hD0).resolve_left hμ_der_eval_ne

/-- If `D : Derivation K E E` vanishes on `u`, then `D` vanishes on `IntermediateField.adjoin K {u}`,
so it upgrades to a `K(u)`-derivation. -/
def restrictToAdjoinDeriv {E : Type*} [Field E] [Algebra K E]
    (D : Derivation K E E) (u : E) (hDu : D u = 0) :
    Derivation (IntermediateField.adjoin K ({u} : Set E)) E E := by
  let Ku := IntermediateField.adjoin K ({u} : Set E)
  have hD_Ku : ∀ a : Ku, D (a : E) = 0 := by
    -- The set `{x : E | D x = 0}` is a `K`-subalgebra closed under `inv` containing `u`, hence contains `Ku`.
    let S : IntermediateField K E :=
      { carrier := {x : E | D x = 0}
        mul_mem' := fun {x y} hx hy => by
          change D (x * y) = 0
          rw [D.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
        one_mem' := D.map_one_eq_zero
        add_mem' := fun {x y} hx hy => by change D (x + y) = 0; rw [map_add, hx, hy, add_zero]
        zero_mem' := map_zero D
        algebraMap_mem' := fun c => D.map_algebraMap c
        inv_mem' := fun {x} hx => by
          change D x⁻¹ = 0
          by_cases hx0 : x = 0
          · rw [hx0, inv_zero, map_zero]
          · have h1 := congrArg D (mul_inv_cancel₀ hx0)
            rw [D.map_one_eq_zero, D.leibniz, hx, smul_zero, add_zero, smul_eq_mul] at h1
            exact (mul_eq_zero.mp h1).resolve_left hx0 }
    have hle : Ku ≤ S := IntermediateField.adjoin_le_iff.mpr (by
      rintro _ rfl; exact hDu)
    intro a
    exact hle a.property
  refine
    { toFun := D
      map_add' := D.map_add'
      map_smul' := fun a x => by
        change D ((a : E) * x) = (a : E) * D x
        rw [D.leibniz, hD_Ku a, smul_zero, add_zero, smul_eq_mul]
      map_one_eq_zero' := D.map_one_eq_zero'
      leibniz' := D.leibniz' }

private theorem aeval_adjoin_injective {E : Type*} [Field E] [Algebra K E]
    (t : E) (ht : ∀ q : K[X], q ≠ 0 → Polynomial.aeval t q ≠ 0) :
    Function.Injective (Polynomial.aeval (R := K) (⟨t, IntermediateField.subset_adjoin K {t} rfl⟩ :
      IntermediateField.adjoin K ({t} : Set E))).toRingHom := by
  let Kt := IntermediateField.adjoin K ({t} : Set E)
  let t' : Kt := ⟨t, IntermediateField.subset_adjoin K {t} rfl⟩
  have hval_eq : ∀ q : K[X], ((Polynomial.aeval t' q : Kt) : E) = Polynomial.aeval t q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add a b ha hb => simp [map_add, ha, hb]
    | monomial n c => simp [t', Polynomial.aeval_monomial]
  rw [injective_iff_map_eq_zero]
  intro q hq
  by_contra hqne
  have hval : Polynomial.aeval t q = 0 := by
    rw [← hval_eq q, show Polynomial.aeval t' q = 0 from hq]; rfl
  exact ht q hqne hval

/-- A `K`-algebra equivalence `FractionRing K[X] ≃ₐ[K] IntermediateField.adjoin K {t}` for any
element `t` transcendental over `K`. -/
def adjoinEquivFractionRing {E : Type*} [Field E] [Algebra K E]
    (t : E) (ht : ∀ q : K[X], q ≠ 0 → Polynomial.aeval t q ≠ 0) :
    FractionRing K[X] ≃ₐ[K] IntermediateField.adjoin K ({t} : Set E) := by
  let Kt := IntermediateField.adjoin K ({t} : Set E)
  let t' : Kt := ⟨t, IntermediateField.subset_adjoin K {t} rfl⟩
  let φ : K[X] →ₐ[K] Kt := Polynomial.aeval t'
  have hφ_inj : Function.Injective φ.toRingHom := aeval_adjoin_injective t ht
  let ψRing : FractionRing K[X] →+* Kt := IsFractionRing.lift hφ_inj
  let ψ : FractionRing K[X] →ₐ[K] Kt :=
    { toRingHom := ψRing
      commutes' := fun c => by
        change ψRing (algebraMap K[X] (FractionRing K[X]) (Polynomial.C c)) = algebraMap K Kt c
        rw [IsFractionRing.lift_algebraMap hφ_inj]
        simp [φ] }
  have hψ_inj : Function.Injective ψ := ψ.toRingHom.injective
  have hψ_X : ψ (algebraMap K[X] (FractionRing K[X]) Polynomial.X) = t' := by
    change ψRing (algebraMap K[X] (FractionRing K[X]) Polynomial.X) = t'
    rw [IsFractionRing.lift_algebraMap hφ_inj]
    simp [φ]
  have hψ_surj : Function.Surjective ψ := by
    let S : IntermediateField K E := ((IntermediateField.val Kt).comp ψ).fieldRange
    have hle : Kt ≤ S := IntermediateField.adjoin_le_iff.mpr (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ⟨algebraMap K[X] (FractionRing K[X]) Polynomial.X, by
        change (ψ (algebraMap K[X] (FractionRing K[X]) Polynomial.X) : E) = t
        rw [hψ_X]⟩)
    intro y
    obtain ⟨x, hx⟩ := hle y.property
    exact ⟨x, Subtype.ext hx⟩
  exact AlgEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩

theorem adjoinEquivFractionRing_algebraMap {E : Type*} [Field E] [Algebra K E]
    (t : E) (ht : ∀ q : K[X], q ≠ 0 → Polynomial.aeval t q ≠ 0) (q : K[X]) :
    ((adjoinEquivFractionRing t ht (algebraMap K[X] (FractionRing K[X]) q)) : E) =
      Polynomial.aeval t q := by
  have h1 : adjoinEquivFractionRing t ht (algebraMap K[X] (FractionRing K[X]) q) =
      Polynomial.aeval (⟨t, IntermediateField.subset_adjoin K {t} rfl⟩ :
        IntermediateField.adjoin K ({t} : Set E)) q := by
    dsimp only [adjoinEquivFractionRing, AlgEquiv.ofBijective_apply]
    exact IsFractionRing.lift_algebraMap (aeval_adjoin_injective t ht) q
  rw [h1]
  clear h1
  induction q using Polynomial.induction_on' with
  | add a b ha hb => simp [map_add, ha, hb]
  | monomial n c => simp [Polynomial.aeval_monomial]

/-- Consequently, an irreducible `f : MvPolynomial (Fin 2) K` stays irreducible over `K(t)`
for any element `t` transcendental over `K`. -/
theorem irreducible_map_adjoin_transcendental {E : Type*} [Field E] [Algebra K E]
    (t : E) (ht : ∀ q : K[X], q ≠ 0 → Polynomial.aeval t q ≠ 0)
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f) :
    Irreducible (MvPolynomial.map (algebraMap K (IntermediateField.adjoin K ({t} : Set E))) f) := by
  let e := adjoinEquivFractionRing t ht
  let eMv : MvPolynomial (Fin 2) (FractionRing K[X]) ≃+*
      MvPolynomial (Fin 2) (IntermediateField.adjoin K ({t} : Set E)) :=
    MvPolynomial.mapEquiv (Fin 2) e.toRingEquiv
  have h1 := irreducible_map_fractionRing_poly f hf
  have h2 : Irreducible (eMv (MvPolynomial.map (algebraMap K (FractionRing K[X])) f)) :=
    (MulEquiv.irreducible_iff eMv.toMulEquiv).mpr h1
  have hcomp : eMv (MvPolynomial.map (algebraMap K (FractionRing K[X])) f) =
      MvPolynomial.map (algebraMap K (IntermediateField.adjoin K ({t} : Set E))) f := by
    change MvPolynomial.map e.toRingHom (MvPolynomial.map (algebraMap K (FractionRing K[X])) f) = _
    rw [MvPolynomial.map_map]
    exact congrArg (fun φ => MvPolynomial.map φ f) (RingHom.ext fun c => e.commutes c)
  rwa [hcomp] at h2

end AlgebraAndDerivations

#print axioms irreducible_dehom
#print axioms irreducible_map_fractionRing_poly
#print axioms fracDeriv_algebraMap
#print axioms quotDeriv_mk
#print axioms deriv_aeval_mv2
#print axioms derivation_eq_zero_of_finrank_lt_char
#print axioms irreducible_map_adjoin_transcendental

end ArkLib.ProximityGap.Frontier.PlaneCurveFunctionField
