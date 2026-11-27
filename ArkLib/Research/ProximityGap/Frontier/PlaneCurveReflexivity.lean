/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.GeometricIrreducibilitySmoothPoint
import ArkLib.Research.ProximityGap.Frontier.PlaneCurveFunctionField

/-! # Plane-curve reflexivity (Pardini Prop. 1.2)

Over an algebraically closed field `K` with `∀ k, 0 < k → k ≤ m * (m - 1) → (k : K) ≠ 0`,
this module proves Pardini's plane-curve reflexivity theorem (`pardini_reflexivity`):

If `F : MvPolynomial (Fin 3) K` is irreducible homogeneous of degree `m ≥ 2` and
`P : MvPolynomial (Fin 3) K` is nonzero homogeneous of degree `s` with `F ∣ gaussPullback F P`,
then `2 ≤ s` and `m ≤ s * (s - 1)`.
-/

set_option autoImplicit false
noncomputable section

open Polynomial MvPolynomial Finset Module
open scoped Matrix
open ArkLib.ProximityGap.Frontier.PlaneBezoutWithMultiplicity
open ArkLib.ProximityGap.Frontier.PlaneCurveLinearAlgebra
open ArkLib.ProximityGap.Frontier.PlaneCurveFunctionField

namespace ArkLib.ProximityGap.Frontier.PlaneCurveReflexivity

variable {K : Type*} [Field K]

/-- A homogeneous polynomial of degree `0` in 3 variables is a constant. -/
theorem isHomogeneous_zero_eq_C {R : Type*} [CommRing R] {p : MvPolynomial (Fin 3) R}
    (hp : p.IsHomogeneous 0) : p = MvPolynomial.C (p.coeff 0) := by
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  refine Nat.eq_zero_of_le_zero (totalDegree_le_of_forall_mem_support fun e he => ?_)
  have h := hp (MvPolynomial.mem_support_iff.mp he)
  rw [weight_one_eq_sum] at h
  exact le_of_eq h

/-- Explicit ring equivalence `MvPolynomial (Fin 2) K ≃+* K[X][X]` sending `X 0 ↦ C X` (`Z`)
and `X 1 ↦ X` (`Y`). -/
def mv2EquivBiv : MvPolynomial (Fin 2) K ≃+* K[X][X] := by
  let toFun : MvPolynomial (Fin 2) K →+* K[X][X] :=
    (MvPolynomial.aeval (R := K)
      (![Polynomial.C Polynomial.X, Polynomial.X] : Fin 2 → K[X][X])).toRingHom
  let invFun : K[X][X] →+* MvPolynomial (Fin 2) K :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))
      (MvPolynomial.X 1)
  have hto_C (c : K) : toFun (MvPolynomial.C c) = Polynomial.C (Polynomial.C c) := by
    simp [toFun]
  have hto_X0 : toFun (MvPolynomial.X 0) = Polynomial.C Polynomial.X := by simp [toFun]
  have hto_X1 : toFun (MvPolynomial.X 1) = Polynomial.X := by simp [toFun]
  have hinv_C (r : K[X]) : invFun (Polynomial.C r) =
      Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0) r := by simp [invFun]
  have hinv_X : invFun Polynomial.X = MvPolynomial.X 1 := by simp [invFun]
  have hleft : ∀ g : MvPolynomial (Fin 2) K, invFun (toFun g) = g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C c => simp [hto_C, hinv_C]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | mul_X a i ha =>
      rw [map_mul, map_mul, ha]
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · rw [hto_X0, hinv_C]; simp
      · rw [hto_X1, hinv_X]
  have hright : ∀ g : K[X][X], toFun (invFun g) = g := by
    intro g
    induction g using Polynomial.induction_on' with
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | monomial j r =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      have hr : toFun (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0) r) = Polynomial.C r := by
        induction r using Polynomial.induction_on' with
        | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
        | monomial i c =>
          rw [← Polynomial.C_mul_X_pow_eq_monomial]
          simp [hto_C, hto_X0, map_mul, map_pow]
      rw [map_mul, map_pow, hinv_C, hinv_X, map_mul, map_pow, hr, hto_X1]
  exact RingEquiv.mk (Equiv.mk toFun invFun hleft hright) (map_mul toFun) (map_add toFun)

@[simp]
theorem mv2EquivBiv_X0 : mv2EquivBiv (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) = Polynomial.C Polynomial.X := by
  change (MvPolynomial.aeval (R := K)
    (![Polynomial.C Polynomial.X, Polynomial.X] : Fin 2 → K[X][X])) (MvPolynomial.X 0) = _
  simp

@[simp]
theorem mv2EquivBiv_X1 : mv2EquivBiv (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) = (Polynomial.X : K[X][X]) := by
  change (MvPolynomial.aeval (R := K)
    (![Polynomial.C Polynomial.X, Polynomial.X] : Fin 2 → K[X][X])) (MvPolynomial.X 1) = _
  simp

@[simp]
theorem mv2EquivBiv_C (c : K) : mv2EquivBiv (MvPolynomial.C c : MvPolynomial (Fin 2) K) = Polynomial.C (Polynomial.C c) := by
  change (MvPolynomial.aeval (R := K)
    (![Polynomial.C Polynomial.X, Polynomial.X] : Fin 2 → K[X][X])) (MvPolynomial.C c) = _
  simp

theorem eval_mv2EquivBiv {E : Type*} [CommRing E] [Algebra K E]
    (g : MvPolynomial (Fin 2) K) (u v : E) :
    ((mv2EquivBiv g).map (Polynomial.aeval u).toRingHom).eval v = MvPolynomial.aeval ![u, v] g := by
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add a b ha hb => rw [map_add, Polynomial.map_add, Polynomial.eval_add, map_add, ha, hb]
  | mul_X a i ha =>
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · rw [map_mul, mv2EquivBiv_X0, Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
        Polynomial.eval_C, ha]
      simp
    · rw [map_mul, mv2EquivBiv_X1, Polynomial.map_mul, Polynomial.map_X, Polynomial.eval_mul,
        Polynomial.eval_X, ha]
      simp

theorem eval_mv2EquivBiv_K (g : MvPolynomial (Fin 2) K) (z y : K) :
    ((mv2EquivBiv g).map (evalRingHom z)).eval y = MvPolynomial.eval ![z, y] g := by
  simpa [Polynomial.aeval_def] using eval_mv2EquivBiv (E := K) g z y

theorem coeff_mv2EquivBiv (g : MvPolynomial (Fin 2) K) (j i : ℕ) :
    ((mv2EquivBiv g).coeff j).coeff i = g.coeff (Finsupp.single 0 i + Finsupp.single 1 j) := by
  classical
  induction g using MvPolynomial.induction_on generalizing j i with
  | C c =>
    rw [mv2EquivBiv_C, Polynomial.coeff_C, MvPolynomial.coeff_C]
    by_cases hj : j = 0
    · subst hj
      simp only [ite_true, Polynomial.coeff_C, Finsupp.single_zero, add_zero]
      by_cases hi : i = 0
      · subst hi; simp
      · have hne : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 i :=
          Ne.symm (Finsupp.single_ne_zero.mpr hi)
        simp [hi, hne]
    · have hne : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 i + Finsupp.single 1 j := by
        intro h; have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h; simp at this; exact hj this.symm
      simp [hj, hne]
  | add a b ha hb => simp [map_add, ha, hb]
  | mul_X a k ha =>
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · rw [map_mul, mv2EquivBiv_X0, mul_comm, Polynomial.coeff_C_mul, mul_comm]
      by_cases hi : i = 0
      · subst hi
        have h1 : ((mv2EquivBiv a).coeff j * Polynomial.X).coeff 0 = 0 := by simp
        have h2 : (a * MvPolynomial.X 0).coeff (Finsupp.single 0 0 + Finsupp.single 1 j) = 0 := by
          rw [MvPolynomial.coeff_mul]; apply Finset.sum_eq_zero; rintro ⟨u, v⟩ huv
          have h0 : u 0 + v 0 = 0 := by
            have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) (Finset.mem_antidiagonal.mp huv); simpa using this
          have hv : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K).coeff v = 0 := by
            rw [MvPolynomial.coeff_X]; split_ifs with heq
            · exfalso; have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq; simp at this; omega
            · rfl
          rw [hv, mul_zero]
        rw [h1, h2]
      · obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
        rw [Polynomial.coeff_mul_X]
        have hadd : Finsupp.single (0 : Fin 2) (i' + 1) + Finsupp.single 1 j =
            (Finsupp.single 0 i' + Finsupp.single 1 j) + Finsupp.single 0 1 := by
          ext t; fin_cases t <;> simp
        rw [hadd, MvPolynomial.coeff_mul_X, ha]
    · rw [map_mul, mv2EquivBiv_X1]
      by_cases hj : j = 0
      · subst hj
        have h1 : (mv2EquivBiv a * Polynomial.X).coeff 0 = 0 := by simp
        have h2 : (a * MvPolynomial.X 1).coeff (Finsupp.single 0 i + Finsupp.single 1 0) = 0 := by
          rw [MvPolynomial.coeff_mul]; apply Finset.sum_eq_zero; rintro ⟨u, v⟩ huv
          have h1' : u 1 + v 1 = 0 := by
            have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) (Finset.mem_antidiagonal.mp huv); simpa using this
          have hv : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).coeff v = 0 := by
            rw [MvPolynomial.coeff_X]; split_ifs with heq
            · exfalso; have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) heq; simp at this; omega
            · rfl
          rw [hv, mul_zero]
        rw [h1, Polynomial.coeff_zero, h2]
      · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        rw [Polynomial.coeff_mul_X]
        have hadd : Finsupp.single (0 : Fin 2) i + Finsupp.single 1 (j' + 1) =
            (Finsupp.single 0 i + Finsupp.single 1 j') + Finsupp.single 1 1 := by
          ext t; fin_cases t <;> simp
        rw [hadd, MvPolynomial.coeff_mul_X, ha]

theorem totalDegreeLe_mv2EquivBiv_iff (g : MvPolynomial (Fin 2) K) (m : ℕ) :
    WeightedSylvesterDegree.TotalDegreeLe (mv2EquivBiv g) m ↔ g.totalDegree ≤ m := by
  classical
  constructor
  · intro h
    refine totalDegree_le_of_forall_mem_support fun e he => ?_
    have he_eq : e = Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) := by
      ext t; fin_cases t <;> simp
    have hcoeff : ((mv2EquivBiv g).coeff (e 1)).coeff (e 0) ≠ 0 := by
      rw [coeff_mv2EquivBiv, ← he_eq]; exact MvPolynomial.mem_support_iff.mp he
    have hj_ne : (mv2EquivBiv g).coeff (e 1) ≠ 0 := by
      intro h0; rw [h0, Polynomial.coeff_zero] at hcoeff; exact hcoeff rfl
    have hle := h (e 1) hj_ne
    have hi_le : e 0 ≤ ((mv2EquivBiv g).coeff (e 1)).natDegree := Polynomial.le_natDegree_of_ne_zero hcoeff
    rw [m2_sum]; omega
  · intro h j hj
    have hcoeff : ((mv2EquivBiv g).coeff j).coeff ((mv2EquivBiv g).coeff j).natDegree ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hj
    rw [coeff_mv2EquivBiv] at hcoeff
    have hmem := MvPolynomial.mem_support_iff.mpr hcoeff
    have hsup := Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum fun _ v => v) hmem
    have hdeg := hsup.trans h
    rw [m2_sum] at hdeg
    simpa using hdeg

theorem natDegree_mv2EquivBiv_le (g : MvPolynomial (Fin 2) K) (b : ℕ)
    (hb : ∀ e ∈ g.support, e 1 ≤ b) : (mv2EquivBiv g).natDegree ≤ b := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
  ext i
  rw [coeff_mv2EquivBiv, Polynomial.coeff_zero]
  by_contra hne
  have := hb _ (MvPolynomial.mem_support_iff.mpr hne)
  simp at this; omega

/-- Partial derivatives of `dehom F` in `X 0, X 1` agree with `dehom (pderiv 0 F)` and
`dehom (pderiv 1 F)`. -/
theorem pderiv_dehom (F : MvPolynomial (Fin 3) K) (i : Fin 2) :
    pderiv i (dehom F) = dehom (pderiv i.castSucc F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [dehom]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    rw [map_mul, pderiv_mul, hp, pderiv_mul, map_add, map_mul, map_mul]
    fin_cases i <;> fin_cases k <;> simp [dehom]

/-- Total degree of `dehom G` is at most `d` when `G` is homogeneous of degree `d`. -/
theorem totalDegree_dehom_le {G : MvPolynomial (Fin 3) K} {d : ℕ}
    (hG : G.IsHomogeneous d) : (dehom G).totalDegree ≤ d := by
  classical
  refine totalDegree_le_of_forall_mem_support fun e he => ?_
  rw [MvPolynomial.mem_support_iff, G.as_sum, map_sum, MvPolynomial.coeff_sum] at he
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  rw [dehom_monomial, MvPolynomial.coeff_monomial] at hne
  split_ifs at hne with hpm
  · rw [← hpm, m2_sum, proj2_apply_0, proj2_apply_1]
    have h := hG (MvPolynomial.mem_support_iff.mp hm)
    rw [weight_one_eq_sum, m3_sum] at h
    omega
  · exact absurd rfl hne

/-- `X 2` is prime in `MvPolynomial (Fin 3) K`. -/
private theorem prime_X2 : Prime (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) := by
  have hX2_irr : Irreducible (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) := by
    refine ⟨fun hu => ?_, fun a b hab => ?_⟩
    · obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
      have h := congrArg (fun p : MvPolynomial (Fin 3) K => p.coeff (Finsupp.single 2 1)) hc
      have hne : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single 2 1 :=
        Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
      simp [MvPolynomial.coeff_X, MvPolynomial.coeff_C, hne] at h
    · obtain ⟨da, hda⟩ := isHomogeneous_of_dvd (MvPolynomial.isHomogeneous_X K (2 : Fin 3))
        (MvPolynomial.X_ne_zero 2) ⟨b, hab⟩
      obtain ⟨db, hdb⟩ := isHomogeneous_of_dvd (MvPolynomial.isHomogeneous_X K (2 : Fin 3))
        (MvPolynomial.X_ne_zero 2) ⟨a, by rw [hab, mul_comm]⟩
      have ha0 : a ≠ 0 := by rintro rfl; simp at hab
      have hb0 : b ≠ 0 := by rintro rfl; simp at hab
      have hsum : da + db = 1 := by
        have hprod := hda.mul hdb; rw [← hab] at hprod
        have h1 := hprod (show (MvPolynomial.X 2 : MvPolynomial (Fin 3) K).coeff (Finsupp.single 2 1) ≠ 0 by
          simp [MvPolynomial.coeff_X])
        rw [weight_one_eq_sum, m3_sum] at h1; simp at h1
        omega
      rcases (show da = 0 ∨ db = 0 by omega) with rfl | rfl
      · left
        have hc : a = MvPolynomial.C (a.coeff 0) := isHomogeneous_zero_eq_C hda
        have hcne : a.coeff 0 ≠ 0 := by intro h0; rw [h0, map_zero] at hc; exact ha0 hc
        exact hc ▸ hcne.isUnit.map MvPolynomial.C
      · right
        have hc : b = MvPolynomial.C (b.coeff 0) := isHomogeneous_zero_eq_C hdb
        have hcne : b.coeff 0 ≠ 0 := by intro h0; rw [h0, map_zero] at hc; exact hb0 hc
        exact hc ▸ hcne.isUnit.map MvPolynomial.C
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hX2_irr

/-- `X 2` does not divide the minimal homogenization of a nonzero 2-variable polynomial. -/
theorem X2_not_dvd_homog (g : MvPolynomial (Fin 2) K) (hg : g ≠ 0) :
    ¬ (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ homog g.totalDegree g := by
  classical
  intro ⟨W, hW⟩
  obtain ⟨e, he, he_max⟩ :=
    Finset.exists_mem_eq_sup g.support (MvPolynomial.support_nonempty.mpr hg)
      (fun s : Fin 2 →₀ ℕ => s.sum fun _ v => v)
  have hdeg_eq : e 0 + e 1 = g.totalDegree := by rw [← m2_sum]; exact he_max.symm
  have h1 : (homog g.totalDegree g).coeff (ext3 e 0) = g.coeff e := by
    simp only [homog, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single e]
    · simp [hdeg_eq]
    · intro n _ hne; split_ifs with heq
      · exfalso; exact hne (by simpa [proj2_ext3] using congrArg proj2 heq)
      · rfl
    · intro hnot; exact absurd he hnot
  have h2 : (MvPolynomial.X 2 * W).coeff (ext3 e 0) = 0 := by
    rw [MvPolynomial.coeff_mul]; apply Finset.sum_eq_zero; rintro ⟨u, v⟩ huv
    have hu2 : u 2 + v 2 = 0 := by
      have := congrArg (fun f : Fin 3 →₀ ℕ => f 2) (Finset.mem_antidiagonal.mp huv)
      simpa using this
    have hu : (MvPolynomial.X 2 : MvPolynomial (Fin 3) K).coeff u = 0 := by
      rw [MvPolynomial.coeff_X]; split_ifs with heq
      · exfalso; have := congrArg (fun f : Fin 3 →₀ ℕ => f 2) heq; simp at this; omega
      · rfl
    rw [hu, zero_mul]
  rw [← hW, h1] at h2
  exact MvPolynomial.mem_support_iff.mp he h2

/-- If `F` is homogeneous of degree `m` not divisible by `X 2` and `G` is homogeneous of degree `dG`,
then `dehom F ∣ dehom G` in `K[X₀, X₁]` implies `F ∣ G` in `K[X₀, X₁, X₂]`. -/
theorem dvd_of_dehom_dvd {F G : MvPolynomial (Fin 3) K} {m dG : ℕ}
    (hF : F.IsHomogeneous m) (hX2 : ¬ (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ F)
    (hG : G.IsHomogeneous dG) (hdvd : dehom F ∣ dehom G) : F ∣ G := by
  by_cases hG0 : G = 0
  · rw [hG0]; exact dvd_zero _
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q ≠ 0 := by
    rintro rfl; rw [mul_zero] at hq
    exact hG0 (dehom_inj_on_homogeneous dG hG (isHomogeneous_zero _ _ _) (by simpa using hq))
  have hmul_hom : (F * homog q.totalDegree q).IsHomogeneous (m + q.totalDegree) :=
    hF.mul (homog_isHomogeneous _ _ le_rfl)
  have hdehom_eq : dehom (F * homog q.totalDegree q) = dehom G := by
    rw [map_mul, dehom_homog, hq]
  have hle : m + q.totalDegree ≤ dG := by
    by_contra hgt
    have hgt' : dG < m + q.totalDegree := not_le.mp hgt
    have heq_X2 : F * homog q.totalDegree q = MvPolynomial.X 2 ^ (m + q.totalDegree - dG) * G := by
      apply dehom_inj_on_homogeneous (m + q.totalDegree) hmul_hom
      · have := ((MvPolynomial.isHomogeneous_X K (2 : Fin 3)).pow (m + q.totalDegree - dG)).mul hG
        rwa [one_mul, Nat.sub_add_cancel (le_of_lt hgt')] at this
      · rw [hdehom_eq, map_mul, map_pow, dehom]; simp
    have hX2_dvd : (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ F * homog q.totalDegree q := by
      rw [heq_X2]; exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
    rcases prime_X2.dvd_or_dvd hX2_dvd with h1 | h2
    · exact hX2 h1
    · exact X2_not_dvd_homog q hq0 h2
  refine ⟨homog (dG - m) q, ?_⟩
  apply dehom_inj_on_homogeneous dG hG
  · have := hF.mul (homog_isHomogeneous (dG - m) q (by omega))
    rwa [Nat.add_sub_of_le (by omega)] at this
  · rw [map_mul, dehom_homog, hq]

/-- Over an algebraically closed field `K`, any element `x : E` outside `range (algebraMap K E)`
is transcendental over `K`. -/
private theorem isTranscendental_of_not_mem_range [IsAlgClosed K] {E : Type*} [Field E] [Algebra K E]
    (x : E) (hx : ∀ c : K, x ≠ algebraMap K E c) :
    ∀ r : K[X], r ≠ 0 → Polynomial.aeval x r ≠ 0 := by
  intro r
  induction hdeg : r.natDegree using Nat.strong_induction_on generalizing r with
  | h n ih =>
    intro hr hr0
    rcases eq_or_ne n 0 with rfl | hn
    · have hrC : r = Polynomial.C (r.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      have hc0 : r.coeff 0 ≠ 0 := by intro h0; rw [h0, map_zero] at hrC; exact hr hrC
      rw [hrC, Polynomial.aeval_C] at hr0
      exact hc0 ((map_eq_zero_iff (algebraMap K E) (algebraMap K E).injective).mp hr0)
    · have hr_deg_ne : r.degree ≠ 0 := by
        rw [Polynomial.degree_eq_natDegree hr, hdeg]
        exact_mod_cast hn
      obtain ⟨c, hc⟩ := IsAlgClosed.exists_root r hr_deg_ne
      obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hc
      have hq_ne : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hr hq
      have hq_deg : q.natDegree < n := by
        have h1 := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero c) hq_ne
        rw [← hq, hdeg, Polynomial.natDegree_X_sub_C] at h1
        omega
      rw [hq, map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at hr0
      exact ih q.natDegree hq_deg q rfl hq_ne
        ((mul_eq_zero.mp hr0).resolve_left (sub_ne_zero.mpr (hx c)))

/-- Any `q : MvPolynomial (Fin 2) K` vanishing at `(u, v)` in `E` where `p(u, v) = 0`, `p`
irreducible, and `u` transcendental over `K` must be divisible by `p`. -/
private theorem dvd_of_aeval_eq_zero_of_transcendental {E : Type*} [Field E] [Algebra K E]
    (u v : E) (hu : ∀ r : K[X], r ≠ 0 → Polynomial.aeval u r ≠ 0)
    (p q : MvPolynomial (Fin 2) K) (hp : Irreducible p)
    (hpu : MvPolynomial.aeval ![u, v] p = 0)
    (hqu : MvPolynomial.aeval ![u, v] q = 0) :
    p ∣ q := by
  by_contra hndvd
  have hrel : IsRelPrime p q := by
    intro d hdp hdq
    obtain ⟨w, hw⟩ := hdp
    rcases hp.isUnit_or_isUnit hw with hu' | hwu
    · exact hu'
    · exfalso
      obtain ⟨w', hw'⟩ := hwu
      exact hndvd ((show p ∣ d from ⟨↑w'⁻¹, by rw [hw, ← hw', mul_assoc, Units.mul_inv, mul_one]⟩).trans hdq)
  have hrelB : IsRelPrime (mv2EquivBiv p) (mv2EquivBiv q) := by
    intro d hd1 hd2
    have h1 : mv2EquivBiv.symm d ∣ p := by simpa using map_dvd mv2EquivBiv.symm.toRingHom hd1
    have h2 : mv2EquivBiv.symm d ∣ q := by simpa using map_dvd mv2EquivBiv.symm.toRingHom hd2
    simpa using (hrel h1 h2).map mv2EquivBiv.toRingHom
  have hres_ne : resultant (mv2EquivBiv p) (mv2EquivBiv q)
      (mv2EquivBiv p).natDegree (mv2EquivBiv q).natDegree ≠ 0 :=
    resultant_ne_zero_of_isRelPrime (mv2EquivBiv p) (mv2EquivBiv q) hrelB
  by_cases hdeg0 : (mv2EquivBiv p).natDegree = 0
  · let r₀ := (mv2EquivBiv p).coeff 0
    have hpC : mv2EquivBiv p = Polynomial.C r₀ := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    have hr₀_ne : r₀ ≠ 0 := by
      intro h0; rw [h0, map_zero] at hpC
      exact hp.ne_zero (mv2EquivBiv.injective (by rw [hpC, map_zero]))
    have hroot : Polynomial.aeval u r₀ = 0 := by
      have h := eval_mv2EquivBiv p u v
      rw [hpC, Polynomial.map_C, Polynomial.eval_C, hpu] at h
      exact h
    exact hu r₀ hr₀_ne hroot
  · have hzero : (Polynomial.aeval u) (resultant (mv2EquivBiv p) (mv2EquivBiv q)
        (mv2EquivBiv p).natDegree (mv2EquivBiv q).natDegree) = 0 :=
      Polynomial.map_resultant_eq_zero_of_common_root (Polynomial.aeval u).toRingHom
        (mv2EquivBiv p) (mv2EquivBiv q) le_rfl le_rfl (Or.inl hdeg0) v
        (by rw [eval_mv2EquivBiv, hpu]) (by rw [eval_mv2EquivBiv, hqu])
    exact hu _ hres_ne hzero

/-- Generic Bézout degree bound: if `a, b : E` satisfy two relatively prime polynomial equations
`H₁, H₂` of total degrees `≤ d₁, d₂` over a subfield `B ⊆ E`, then `R = Algebra.adjoin B {a, b}`
is a subfield of `E` of `B`-dimension at most `d₁ * d₂`. If in addition `R` contains a fraction-field
generating ring `D`, then `E` itself has `finrank B E ≤ d₁ * d₂`. -/
private theorem finrank_le_of_two_equations {D : Type*} [CommRing D] [IsDomain D] [Algebra K D]
    (B : IntermediateField K (FractionRing D)) (a b : FractionRing D)
    (H₁ H₂ : MvPolynomial (Fin 2) B) {d₁ d₂ : ℕ}
    (hrel : IsRelPrime H₁ H₂) (hd₁ : H₁.totalDegree ≤ d₁) (hd₂ : H₂.totalDegree ≤ d₂)
    (hH₁ : MvPolynomial.aeval ![a, b] H₁ = 0) (hH₂ : MvPolynomial.aeval ![a, b] H₂ = 0)
    (hgen : (∀ x : FractionRing D, x ∈ Algebra.adjoin B ({a, b} : Set (FractionRing D)) →
        x⁻¹ ∈ Algebra.adjoin B ({a, b} : Set (FractionRing D))) →
      ∀ r : D, algebraMap D (FractionRing D) r ∈ Algebra.adjoin B ({a, b} : Set (FractionRing D))) :
    Module.Finite B (FractionRing D) ∧ Module.finrank B (FractionRing D) ≤ d₁ * d₂ := by
  classical
  let E := FractionRing D
  let I : Ideal (MvPolynomial (Fin 2) B) := Ideal.span {H₁, H₂}
  let φ : MvPolynomial (Fin 2) B →ₐ[B] E := MvPolynomial.aeval ![a, b]
  have hI_le : I ≤ RingHom.ker φ.toRingHom := by
    rw [Ideal.span_le]
    rintro g (rfl | rfl)
    · exact hH₁
    · exact hH₂
  let ψ : (MvPolynomial (Fin 2) B ⧸ I) →ₐ[B] E := Ideal.Quotient.liftₐ I φ hI_le
  have hfinQ := affine_quotient_finrank_le H₁ H₂ hrel hd₁ hd₂
  have : Module.Finite B (MvPolynomial (Fin 2) B ⧸ I) := hfinQ.1
  let R : Subalgebra B E := AlgHom.range ψ
  have hR_eq : R = Algebra.adjoin B ({a, b} : Set E) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      change φ p ∈ Algebra.adjoin B ({a, b} : Set E)
      induction p using MvPolynomial.induction_on with
      | C c =>
        rw [show φ (MvPolynomial.C c) = algebraMap B E c by simp [φ]]
        exact Subalgebra.algebraMap_mem (Algebra.adjoin B ({a, b} : Set E)) c
      | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
      | mul_X p i hp =>
        rw [map_mul]; refine Subalgebra.mul_mem _ hp ?_
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · rw [show φ (MvPolynomial.X 0) = a by simp [φ]]
          exact Algebra.subset_adjoin (by simp)
        · rw [show φ (MvPolynomial.X 1) = b by simp [φ]]
          exact Algebra.subset_adjoin (by simp)
    · rw [Algebra.adjoin_le_iff]
      rintro x (hx | hx)
      · rw [hx]
        exact ⟨Ideal.Quotient.mk I (MvPolynomial.X 0), by change φ (MvPolynomial.X 0) = a; simp [φ]⟩
      · rw [hx]
        exact ⟨Ideal.Quotient.mk I (MvPolynomial.X 1), by change φ (MvPolynomial.X 1) = b; simp [φ]⟩
  have hR_fin : Module.Finite B R := Module.Finite.of_surjective ψ.rangeRestrict.toLinearMap
    (fun ⟨y, hy⟩ => by obtain ⟨x, hx⟩ := hy; exact ⟨x, Subtype.ext hx⟩)
  have hR_dim : Module.finrank B R ≤ d₁ * d₂ := by
    have h1 := LinearMap.finrank_range_le ψ.toLinearMap
    exact h1.trans hfinQ.2
  -- Since `R` is a finite-dimensional (hence integral) `B`-subalgebra of the field `E`, `R` is a field!
  have : Algebra.IsIntegral B R := Algebra.IsIntegral.of_finite B R
  have hR_field : IsField R :=
    (Algebra.IsIntegral.isField_iff_isField (R := B) (S := R)
      (algebraMap B R).injective).mp (Field.toIsField B)
  have hR_inv : ∀ x : E, x ∈ R → x⁻¹ ∈ R := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]; exact R.zero_mem
    · have hne : (⟨x, hx⟩ : R) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
      obtain ⟨y, hy⟩ := hR_field.mul_inv_cancel hne
      have hxy : x * y.val = 1 := congrArg Subtype.val hy
      have hy_eq : y.val = x⁻¹ := by
        apply mul_left_cancel₀ hx0
        rw [hxy, mul_inv_cancel₀ hx0]
      exact hy_eq ▸ y.property
  -- Hence `R` contains every fraction `ι r₁ / ι r₂` in `E`, so `R = ⊤`!
  have hgen' : ∀ r : D, algebraMap D E r ∈ R := by
    intro r
    rw [hR_eq]
    exact hgen (by simpa only [← hR_eq] using hR_inv) r
  have hR_top : ∀ x : E, x ∈ R := by
    intro x
    obtain ⟨r₁, r₂, _, hx⟩ := IsFractionRing.div_surjective (A := D) x
    rw [← hx, div_eq_mul_inv]
    exact R.mul_mem (hgen' r₁) (hR_inv _ (hgen' r₂))
  let eRE : R ≃ₗ[B] E := LinearEquiv.ofBijective R.val.toLinearMap
    ⟨Subtype.val_injective, fun x => ⟨⟨x, hR_top x⟩, rfl⟩⟩
  have : Module.Finite B E := Module.Finite.equiv eRE
  refine ⟨inferInstance, ?_⟩
  rw [← LinearEquiv.finrank_eq eRE]
  exact hR_dim

set_option maxHeartbeats 800000 in
/-- **Core Pardini Reflexivity Theorem (irreducible `P`)**:
For irreducible homogeneous `F, P : MvPolynomial (Fin 3) K` of degrees `m ≥ 2` and `s ≥ 2` over an
algebraically closed field `K` with `∀ k, 0 < k → k ≤ m * (m - 1) → (k : K) ≠ 0`, if
`F ∣ gaussPullback F P`, then `m ≤ s * (s - 1)`. -/
theorem pardini_reflexivity_irreducible [IsAlgClosed K] {F P : MvPolynomial (Fin 3) K} {m s : ℕ}
    (hF_irr : Irreducible F) (hF_hom : F.IsHomogeneous m) (hm : 2 ≤ m)
    (hP_irr : Irreducible P) (hP_hom : P.IsHomogeneous s) (hs : 2 ≤ s)
    (hchar : ∀ k : ℕ, 0 < k → k ≤ m * (m - 1) → (k : K) ≠ 0)
    (hdvd : F ∣ gaussPullback F P) :
    m ≤ s * (s - 1) := by
  classical
  by_contra hlt
  have hms : s * (s - 1) < m := not_le.mp hlt
  have hchar_m : ∀ k : ℕ, 0 < k → k ≤ m → (k : K) ≠ 0 := fun k hk1 hk2 =>
    hchar k hk1 (hk2.trans (Nat.le_mul_of_pos_right m (by omega)))
  have hchar_s : ∀ k : ℕ, 0 < k → k ≤ s → (k : K) ≠ 0 := fun k hk1 hk2 => by
    have hs_le : s ≤ s * (s - 1) := Nat.le_mul_of_pos_right s (by omega)
    exact hchar_m k hk1 (by omega)
  -- Step 1: Apply a `GL_3(K)` shear so that `F'` has nonzero `X 1 ^ m` coefficient.
  obtain ⟨M, N, hMN, hNM, hF'_Y⟩ := exists_shear_coeff_Y_ne_zero hF_irr hF_hom hm
  let F' := substLin M F
  let P' := substLin Nᵀ P
  have hF'_irr : Irreducible F' :=
    (MulEquiv.irreducible_iff (substLinEquiv M N hMN hNM).toMulEquiv).mpr hF_irr
  have hF'_hom : F'.IsHomogeneous m := substLin_isHomogeneous M hF_hom
  have hP'_irr : Irreducible P' := by
    have hNT : Nᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, hMN, Matrix.transpose_one]
    have hMT : Mᵀ * Nᵀ = 1 := by rw [← Matrix.transpose_mul, hNM, Matrix.transpose_one]
    exact (MulEquiv.irreducible_iff (substLinEquiv Nᵀ Mᵀ hNT hMT).toMulEquiv).mpr hP_irr
  have hP'_hom : P'.IsHomogeneous s := substLin_isHomogeneous Nᵀ hP_hom
  have hdvd' : F' ∣ gaussPullback F' P' := by
    rw [gaussPullback_substLin M N hMN F P]
    exact map_dvd (substLin M) hdvd
  have hX2_ndvd_F' : ¬ (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ F' := by
    intro ⟨W, hW⟩
    have h0 : (MvPolynomial.X 2 * W).coeff (Finsupp.single 1 m) = 0 := by
      rw [MvPolynomial.coeff_mul]; apply Finset.sum_eq_zero; rintro ⟨u, v⟩ huv
      have hu2 : u 2 + v 2 = 0 := by
        have := congrArg (fun g : Fin 3 →₀ ℕ => g 2) (Finset.mem_antidiagonal.mp huv); simpa using this
      have hu : (MvPolynomial.X 2 : MvPolynomial (Fin 3) K).coeff u = 0 := by
        rw [MvPolynomial.coeff_X]; split_ifs with heq
        · exfalso; have := congrArg (fun g : Fin 3 →₀ ℕ => g 2) heq; simp at this; omega
        · rfl
      rw [hu, zero_mul]
    exact hF'_Y (by change F'.coeff (Finsupp.single 1 m) = 0; rw [hW]; exact h0)
  -- Step 2: Function field `E = FractionRing (K[Z, Y] / (f))`.
  let f : MvPolynomial (Fin 2) K := dehom F'
  have hf_irr : Irreducible f := irreducible_dehom hF'_irr hF'_hom hm
  have hf_prime : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf_irr
  have : (Ideal.span {f}).IsPrime := (Ideal.span_singleton_prime hf_irr.ne_zero).mpr hf_prime
  let D := MvPolynomial (Fin 2) K ⧸ Ideal.span {f}
  let E := FractionRing D
  let mkD : MvPolynomial (Fin 2) K →ₐ[K] D := Ideal.Quotient.mkₐ K (Ideal.span {f})
  let ιE : D →ₐ[K] E := IsScalarTower.toAlgHom K D E
  let π : MvPolynomial (Fin 2) K →ₐ[K] E := ιE.comp mkD
  have hπ_zero_iff (g : MvPolynomial (Fin 2) K) : π g = 0 ↔ f ∣ g := by
    change algebraMap D E (Ideal.Quotient.mk (Ideal.span {f}) g) = 0 ↔ f ∣ g
    rw [map_eq_zero_iff _ (IsFractionRing.injective D E), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
  have hπ_dehom_zero (G : MvPolynomial (Fin 3) K) (dG : ℕ) (hG : G.IsHomogeneous dG) :
      π (dehom G) = 0 ↔ F' ∣ G := by
    rw [hπ_zero_iff]
    exact ⟨dvd_of_dehom_dvd hF'_hom hX2_ndvd_F' hG, map_dvd dehom⟩
  let z : E := π (MvPolynomial.X 0)
  let y : E := π (MvPolynomial.X 1)
  have hπ_eq_aeval (g : MvPolynomial (Fin 2) K) : π g = MvPolynomial.aeval ![z, y] g := by
    have hcomp : π = MvPolynomial.aeval ![z, y] := by
      apply MvPolynomial.algHom_ext; intro i
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · simp [z]
      · simp [y]
    exact AlgHom.congr_fun hcomp g
  let fZ : E := π (dehom (pderiv 0 F'))
  let fY : E := π (dehom (pderiv 1 F'))
  let fT : E := π (dehom (pderiv 2 F'))
  have hlin_indep : ∀ a : Fin 3 → K, a ≠ 0 → a 0 • fZ + a 1 • fY + a 2 • fT ≠ 0 := by
    intro a ha h0
    let L := ∑ i : Fin 3, MvPolynomial.C (a i) * pderiv i F'
    have hL_hom : L.IsHomogeneous (m - 1) := by
      rw [← mem_homogeneousSubmodule]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [mem_homogeneousSubmodule]
      simpa using (MvPolynomial.isHomogeneous_C (Fin 3) (a i)).mul hF'_hom.pderiv
    have hπL : π (dehom L) = 0 := by
      have hdehom : dehom L = MvPolynomial.C (a 0) * dehom (pderiv 0 F') +
          MvPolynomial.C (a 1) * dehom (pderiv 1 F') +
          MvPolynomial.C (a 2) * dehom (pderiv 2 F') := by
        dsimp only [L]; rw [Fin.sum_univ_three, map_add, map_add, map_mul, map_mul, map_mul]
        simp [dehom]
      rw [hdehom, map_add, map_add, map_mul, map_mul, map_mul]
      simpa [fZ, fY, fT, Algebra.smul_def, MvPolynomial.algebraMap_eq] using h0
    exact linear_polar_not_dvd hF'_irr hF'_hom hm hchar_m a ha
      ((hπ_dehom_zero L (m - 1) hL_hom).mp hπL)
  have hfZ_ne : fZ ≠ 0 := by
    simpa using hlin_indep ![1, 0, 0] (by intro h; have := congrFun h 0; simp at this)
  have hfY_ne : fY ≠ 0 := by
    simpa using hlin_indep ![0, 1, 0] (by intro h; have := congrFun h 1; simp at this)
  have hfT_ne : fT ≠ 0 := by
    simpa using hlin_indep ![0, 0, 1] (by intro h; have := congrFun h 2; simp at this)
  let u : E := fZ / fT
  let v : E := fY / fT
  -- Step 3: Euler identity `z * u + y * v + 1 = 0` and transcendence of `u` and `z`.
  have heuler_F : z * u + y * v + 1 = 0 := by
    have heul := congrArg (fun G => π (dehom G)) (IsHomogeneous.sum_X_mul_pderiv hF'_hom)
    rw [Fin.sum_univ_three] at heul
    simp only [map_add, map_mul, map_nsmul, dehom, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, one_mul] at heul
    have hπf : π f = 0 := (hπ_zero_iff f).mpr dvd_rfl
    have heul' : z * fZ + y * fY + fT = 0 := by
      change z * fZ + y * fY + fT = m • π f at heul
      rw [hπf, nsmul_zero] at heul; exact heul
    dsimp only [u, v]
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_add_one hfT_ne, div_eq_zero_iff]
    exact Or.inl heul'
  have hu_trans : ∀ r : K[X], r ≠ 0 → Polynomial.aeval u r ≠ 0 := by
    apply isTranscendental_of_not_mem_range u
    intro c hc
    have h0 : (1 : K) • fZ + (0 : K) • fY + (-c) • fT = 0 := by
      have h1 : fZ = algebraMap K E c * fT := by rw [← hc]; exact (div_mul_cancel₀ fZ hfT_ne).symm
      simp only [Algebra.smul_def, map_one, map_zero, map_neg, one_mul, zero_mul, add_zero]
      linear_combination h1
    exact hlin_indep ![1, 0, -c] (by intro h; have := congrFun h 0; simp at this) h0
  -- Step 4: Bound `[E : K(u)] ≤ m * (m - 1)` via L2b (`affine_quotient_finrank_le`).
  let Ku : IntermediateField K E := IntermediateField.adjoin K {u}
  let uKu : Ku := ⟨u, IntermediateField.subset_adjoin K {u} rfl⟩
  let H1 : MvPolynomial (Fin 2) Ku := MvPolynomial.map (algebraMap K Ku) f
  let H2 : MvPolynomial (Fin 2) Ku :=
    MvPolynomial.map (algebraMap K Ku) (dehom (pderiv 0 F')) -
    MvPolynomial.C uKu * MvPolynomial.map (algebraMap K Ku) (dehom (pderiv 2 F'))
  have hH1_irr : Irreducible H1 := irreducible_map_adjoin_transcendental u hu_trans f hf_irr
  have hH1_deg : H1.totalDegree ≤ m := (totalDegree_map_le' _ _).trans (totalDegree_dehom_le hF'_hom)
  have hH2_deg : H2.totalDegree ≤ m - 1 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_map_le' _ _).trans (totalDegree_dehom_le hF'_hom.pderiv)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by
        rw [MvPolynomial.totalDegree_C, zero_add]
        exact (totalDegree_map_le' _ _).trans (totalDegree_dehom_le hF'_hom.pderiv))
  have hH1_deg_eq : H1.totalDegree = m := by
    apply le_antisymm hH1_deg
    have hfY : f.coeff (Finsupp.single 1 m) = F'.coeff (Finsupp.single 1 m) := by
      have hF'eq : F' = homog m f :=
        dehom_inj_on_homogeneous m hF'_hom (homog_isHomogeneous m f (totalDegree_dehom_le hF'_hom))
          (dehom_homog m f).symm
      conv_rhs => rw [hF'eq]
      simp only [homog, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      by_cases hm_mem : Finsupp.single (1 : Fin 2) m ∈ f.support
      · rw [Finset.sum_eq_single (Finsupp.single 1 m)]
        · have hthis : ext3 (Finsupp.single (1 : Fin 2) m) 0 = Finsupp.single 1 m := by
            ext i; fin_cases i <;> simp
          simp [hthis]
        · intro e _ hne; split_ifs with heq
          · exfalso; apply hne
            have h := congrArg proj2 heq; rw [proj2_ext3] at h
            rw [h]; ext i; fin_cases i <;> simp
          · rfl
        · intro h; exact absurd hm_mem h
      · rw [MvPolynomial.notMem_support_iff.mp hm_mem]
        symm; apply Finset.sum_eq_zero; intro e he; split_ifs with heq
        · exfalso; apply hm_mem
          have h := congrArg proj2 heq; rw [proj2_ext3] at h
          have he_eq : e = Finsupp.single 1 m := by rw [h]; ext i; fin_cases i <;> simp
          exact he_eq ▸ he
        · rfl
    have hcoeff : H1.coeff (Finsupp.single 1 m) ≠ 0 := by
      rw [MvPolynomial.coeff_map]
      exact (map_ne_zero_iff _ (algebraMap K Ku).injective).mpr (hfY ▸ hF'_Y)
    have hsup : (Finsupp.single (1 : Fin 2) m).sum (fun _ v => v) ≤ H1.totalDegree :=
      Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum fun _ v => v)
        (MvPolynomial.mem_support_iff.mpr hcoeff)
    rw [m2_sum] at hsup
    simpa using hsup
  have hH2_ne : H2 ≠ 0 := by
    intro h0
    -- If `H2 = 0`, then `dehom (pderiv 0 F') = c * dehom (pderiv 2 F')` at some monomial, forcing `u ∈ K`!
    have hT_ne : dehom (pderiv 2 F') ≠ 0 := fun h => hfT_ne (by simp [fT, h])
    obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hT_ne
    have hce := congrArg (fun g : MvPolynomial (Fin 2) Ku => g.coeff e) h0
    simp only [H2, MvPolynomial.coeff_sub, MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul,
      AddMonoidAlgebra.coeff_zero] at hce
    have hval := congrArg Subtype.val (sub_eq_zero.mp hce)
    have hT_c : (dehom (pderiv 2 F')).coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp he
    have hu_in_K : u = algebraMap K E ((dehom (pderiv 0 F')).coeff e / (dehom (pderiv 2 F')).coeff e) := by
      rw [map_div₀]
      have hTK : algebraMap K E ((dehom (pderiv 2 F')).coeff e) ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap K E).injective).mpr hT_c
      exact (eq_div_iff hTK).mpr (by simpa [uKu] using hval.symm)
    exact hu_trans (Polynomial.X - Polynomial.C ((dehom (pderiv 0 F')).coeff e / (dehom (pderiv 2 F')).coeff e))
      (Polynomial.X_sub_C_ne_zero _) (by simp [hu_in_K])
  have hH1_ndvd_H2 : ¬ H1 ∣ H2 := by
    intro ⟨Q, hQ⟩
    have hQ_ne : Q ≠ 0 := by rintro rfl; rw [mul_zero] at hQ; exact hH2_ne hQ
    -- Look at `H1` and `H2` in `Ku[X][X]`: `H1` has `X 1`-degree `m` while `H2` has totalDegree `≤ m - 1`.
    have h1 : (mv2EquivBiv H1).natDegree = m := by
      apply le_antisymm
      · refine natDegree_mv2EquivBiv_le H1 m fun e he => ?_
        have := (Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum fun _ v => v) he).trans hH1_deg
        rw [m2_sum] at this; omega
      · apply Polynomial.le_natDegree_of_ne_zero
        intro h0
        have hc0 := congrArg (fun p : Ku[X] => p.coeff 0) h0
        rw [coeff_mv2EquivBiv, Polynomial.coeff_zero] at hc0
        have hfY : H1.coeff (Finsupp.single 1 m) ≠ 0 := by
          have hF'eq : F' = homog m f :=
            dehom_inj_on_homogeneous m hF'_hom (homog_isHomogeneous m f (totalDegree_dehom_le hF'_hom))
              (dehom_homog m f).symm
          rw [MvPolynomial.coeff_map]
          refine (map_ne_zero_iff _ (algebraMap K Ku).injective).mpr ?_
          intro hf0
          apply hF'_Y
          change F'.coeff (Finsupp.single 1 m) = 0
          rw [hF'eq]; simp only [homog, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
          apply Finset.sum_eq_zero; intro e he; split_ifs with heq
          · exfalso
            have h := congrArg proj2 heq; rw [proj2_ext3] at h
            have he_eq : e = Finsupp.single 1 m := by rw [h]; ext i; fin_cases i <;> simp
            exact MvPolynomial.mem_support_iff.mp he (he_eq ▸ hf0)
          · rfl
        exact hfY (by simpa using hc0)
    have h2 : (mv2EquivBiv H2).natDegree ≤ m - 1 :=
      natDegree_mv2EquivBiv_le H2 (m - 1) fun e he => by
        have := (Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum fun _ v => v) he).trans hH2_deg
        rw [m2_sum] at this; omega
    have hmul := Polynomial.natDegree_mul
      ((map_ne_zero_iff mv2EquivBiv mv2EquivBiv.injective).mpr hH1_irr.ne_zero)
      ((map_ne_zero_iff mv2EquivBiv mv2EquivBiv.injective).mpr hQ_ne)
    rw [← map_mul, ← hQ, h1] at hmul
    omega
  have hH_rel : IsRelPrime H1 H2 := by
    intro d hd1 hd2
    obtain ⟨w, hw⟩ := hd1
    rcases hH1_irr.isUnit_or_isUnit hw with hu' | hwu
    · exact hu'
    · exfalso; obtain ⟨w', hw'⟩ := hwu
      exact hH1_ndvd_H2 ((show H1 ∣ d from ⟨↑w'⁻¹, by rw [hw, ← hw', mul_assoc, Units.mul_inv, mul_one]⟩).trans hd2)
  have hKu_fin := finrank_le_of_two_equations Ku z y H1 H2 hH_rel hH1_deg hH2_deg
    (by
      rw [show H1 = MvPolynomial.map (algebraMap K Ku) f from rfl, MvPolynomial.aeval_map_algebraMap]
      rw [← hπ_eq_aeval]; exact (hπ_zero_iff f).mpr dvd_rfl)
    (by
      dsimp only [H2]
      rw [map_sub, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_map_algebraMap,
        MvPolynomial.aeval_map_algebraMap, ← hπ_eq_aeval, ← hπ_eq_aeval]
      change fZ - u * fT = 0
      dsimp only [u]; rw [div_mul_cancel₀ _ hfT_ne, sub_self])
    (by
      intro _ r
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
      change π p ∈ Algebra.adjoin Ku ({z, y} : Set E)
      rw [hπ_eq_aeval]
      induction p using MvPolynomial.induction_on with
      | C c =>
        have : MvPolynomial.aeval ![z, y] (MvPolynomial.C c) = algebraMap Ku E (algebraMap K Ku c) := by
          simp
        rw [this]; exact Subalgebra.algebraMap_mem (Algebra.adjoin Ku ({z, y} : Set E)) _
      | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
      | mul_X p i hp =>
        rw [map_mul]; refine Subalgebra.mul_mem _ hp ?_
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · exact Algebra.subset_adjoin (by simp)
        · exact Algebra.subset_adjoin (by simp))
  have : Module.Finite Ku E := hKu_fin.1
  -- Step 5: Construct explicit derivation `δ : Derivation K E E` with `δ z = fY`, `δ y = -fZ`.
  let δ₀ : Derivation K (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K) :=
    dehom (pderiv 1 F') • pderiv 0 - dehom (pderiv 0 F') • pderiv 1
  have hδ₀_f : δ₀ f = 0 := by
    change dehom (pderiv 1 F') * pderiv 0 f - dehom (pderiv 0 F') * pderiv 1 f = 0
    have h0 : pderiv 0 f = dehom (pderiv 0 F') := pderiv_dehom F' 0
    have h1 : pderiv 1 f = dehom (pderiv 1 F') := pderiv_dehom F' 1
    rw [h0, h1]; ring
  have hδ₀_ideal : ∀ x ∈ Ideal.span {f}, δ₀ x ∈ Ideal.span {f} := by
    intro x hx
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [δ₀.leibniz, hδ₀_f, smul_zero, add_zero, smul_eq_mul]
    exact Ideal.mem_span_singleton.mpr ⟨δ₀ g, rfl⟩
  let δ : Derivation K E E := fracDeriv (quotDeriv (Ideal.span {f}) δ₀ hδ₀_ideal)
  have hδ_π (g : MvPolynomial (Fin 2) K) : δ (π g) = π (δ₀ g) := by
    change fracDeriv (quotDeriv (Ideal.span {f}) δ₀ hδ₀_ideal)
      (algebraMap D E (Ideal.Quotient.mk (Ideal.span {f}) g)) = _
    rw [fracDeriv_algebraMap, quotDeriv_mk]; rfl
  have hδ_z : δ z = fY := by
    dsimp only [z]; rw [hδ_π]
    have h0 : δ₀ (MvPolynomial.X 0) = dehom (pderiv 1 F') := by
      change dehom (pderiv 1 F') * pderiv 0 (MvPolynomial.X 0) -
        dehom (pderiv 0 F') * pderiv 1 (MvPolynomial.X 0) = _
      simp
    rw [h0]
  have hδ_y : δ y = -fZ := by
    dsimp only [y]; rw [hδ_π]
    have h1 : δ₀ (MvPolynomial.X 1) = -dehom (pderiv 0 F') := by
      change dehom (pderiv 1 F') * pderiv 0 (MvPolynomial.X 1) -
        dehom (pderiv 0 F') * pderiv 1 (MvPolynomial.X 1) = _
      simp
    rw [h1, map_neg]
  -- Step 6: `δ u ≠ 0` because `[E : Ku] ≤ m * (m - 1) < char K` makes `E / Ku` separable!
  have hδ_u_ne : δ u ≠ 0 := by
    intro hDu
    let δKu := restrictToAdjoinDeriv δ u hDu
    have hcharKu : ∀ k : ℕ, 0 < k → k ≤ Module.finrank Ku E → (k : Ku) ≠ 0 := by
      intro k hk1 hk2 h0
      have hK0 : (k : K) = 0 := by
        apply (algebraMap K Ku).injective
        simpa [map_natCast] using h0
      exact hchar k hk1 (hk2.trans hKu_fin.2) hK0
    have hz0 : δ z = 0 := derivation_eq_zero_of_finrank_lt_char hcharKu δKu z
    rw [hδ_z] at hz0
    exact hfY_ne hz0
  -- Step 7: Contact identity `z * δ u + y * δ v = 0` and dual curve equation `p(u, v) = 0`!
  have hcontact : z * δ u + y * δ v = 0 := by
    have h1 := congrArg δ heuler_F
    rw [map_zero, map_add, map_add, δ.map_one_eq_zero, add_zero, δ.leibniz, δ.leibniz] at h1
    simp only [smul_eq_mul, hδ_z, hδ_y] at h1
    have hcancel : fY * u + -fZ * v = 0 := by
      dsimp only [u, v]
      rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_zero_iff]
      exact Or.inl (by ring)
    linear_combination h1 - hcancel
  let p : MvPolynomial (Fin 2) K := dehom P'
  have hp_irr : Irreducible p := irreducible_dehom hP'_irr hP'_hom hs
  have hp_uv : MvPolynomial.aeval ![u, v] p = 0 := by
    -- Homogeneity of `P'`: `aeval ![fZ/fT, fY/fT, 1] P' = fT⁻¹^s * aeval ![fZ, fY, fT] P' = 0`.
    have hgp : π (dehom (gaussPullback F' P')) = 0 :=
      (hπ_dehom_zero _ (s * (m - 1)) (gaussPullback_isHomogeneous hF'_hom hP'_hom)).mpr hdvd'
    have hcomp_gp : MvPolynomial.aeval ![fZ, fY, fT] P' = π (dehom (gaussPullback F' P')) := by
      have h : (π.comp dehom).comp (MvPolynomial.aeval ![pderiv 0 F', pderiv 1 F', pderiv 2 F']) =
          MvPolynomial.aeval ![fZ, fY, fT] := by
        apply MvPolynomial.algHom_ext; intro i
        fin_cases i <;> simp [fZ, fY, fT]
      exact (AlgHom.congr_fun h P').symm
    have hscale : MvPolynomial.aeval ![u, v] p = (fT ^ s)⁻¹ * MvPolynomial.aeval ![fZ, fY, fT] P' := by
      have h1 : MvPolynomial.aeval ![u, v] p = MvPolynomial.aeval ![u, v, 1] P' := by
        have hc : (MvPolynomial.aeval (R := K) ![u, v]).comp dehom = MvPolynomial.aeval (R := K) ![u, v, 1] := by
          apply MvPolynomial.algHom_ext; intro i; fin_cases i <;> simp [dehom]
        exact AlgHom.congr_fun hc P'
      rw [h1, P'.as_sum, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      have hedeg : e 0 + e 1 + e 2 = s := by
        have h := hP'_hom (MvPolynomial.mem_support_iff.mp he); rwa [weight_one_eq_sum, m3_sum] at h
      simp only [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, one_pow, mul_one, u, v, div_pow]
      rw [← hedeg, pow_add, pow_add]
      have h0 : fT ^ e 0 ≠ 0 := pow_ne_zero _ hfT_ne
      have h1' : fT ^ e 1 ≠ 0 := pow_ne_zero _ hfT_ne
      have h2 : fT ^ e 2 ≠ 0 := pow_ne_zero _ hfT_ne
      rw [div_mul_div_comm, ← mul_div_assoc, inv_mul_eq_div,
        div_eq_div_iff (mul_ne_zero h0 h1') (mul_ne_zero (mul_ne_zero h0 h1') h2)]
      ring
    rw [hscale, hcomp_gp, hgp, mul_zero]
  let pU : MvPolynomial (Fin 2) K := dehom (pderiv 0 P')
  let pV : MvPolynomial (Fin 2) K := dehom (pderiv 1 P')
  let pW : MvPolynomial (Fin 2) K := dehom (pderiv 2 P')
  have hdual_deriv : MvPolynomial.aeval ![u, v] pU * δ u + MvPolynomial.aeval ![u, v] pV * δ v = 0 := by
    have h1 := congrArg δ hp_uv
    rw [map_zero, deriv_aeval_mv2, pderiv_dehom P' 0, pderiv_dehom P' 1] at h1
    exact h1
  have hX2_ndvd_P' : ¬ (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∣ P' := by
    intro ⟨Q, hQ⟩
    rcases hP'_irr.isUnit_or_isUnit hQ with hu' | hQu
    · obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu'
      have h := congrArg (fun g : MvPolynomial (Fin 3) K => g.coeff (Finsupp.single 2 1)) hc
      have hne : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single 2 1 :=
        Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
      simp [MvPolynomial.coeff_X, MvPolynomial.coeff_C, hne] at h
    · obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hQu
      have hdeg : P'.IsHomogeneous 1 := by
        rw [hQ, hc]
        simpa using (MvPolynomial.isHomogeneous_X K (2 : Fin 3)).mul (MvPolynomial.isHomogeneous_C (Fin 3) c)
      obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hP'_irr.ne_zero
      have h1 := hP'_hom (MvPolynomial.mem_support_iff.mp he)
      have h2 := hdeg (MvPolynomial.mem_support_iff.mp he)
      omega
  have hp_der_ne (i : Fin 3) : MvPolynomial.aeval ![u, v] (dehom (pderiv i P')) ≠ 0 := by
    intro h0
    have hdvd_p : p ∣ dehom (pderiv i P') :=
      dvd_of_aeval_eq_zero_of_transcendental u v hu_trans p _ hp_irr hp_uv h0
    have hdvd_P' : P' ∣ pderiv i P' := dvd_of_dehom_dvd hP'_hom hX2_ndvd_P' hP'_hom.pderiv hdvd_p
    let a : Fin 3 → K := fun j => if j = i then 1 else 0
    have ha : a ≠ 0 := by intro h; have := congrFun h i; simp [a] at this
    have hsum : ∑ j : Fin 3, MvPolynomial.C (a j) * pderiv j P' = pderiv i P' := by
      rw [Finset.sum_eq_single i]
      · simp [a]
      · intro j _ hji; simp [a, hji]
      · intro h; exact absurd (Finset.mem_univ i) h
    exact linear_polar_not_dvd hP'_irr hP'_hom hs hchar_s a ha (hsum.symm ▸ hdvd_P')
  have hpV_ne : MvPolynomial.aeval ![u, v] pV ≠ 0 := hp_der_ne 1
  have hpW_ne : MvPolynomial.aeval ![u, v] pW ≠ 0 := hp_der_ne 2
  have heuler_P : u * MvPolynomial.aeval ![u, v] pU + v * MvPolynomial.aeval ![u, v] pV +
      MvPolynomial.aeval ![u, v] pW = 0 := by
    have heul := congrArg (fun G => MvPolynomial.aeval ![u, v] (dehom G))
      (IsHomogeneous.sum_X_mul_pderiv hP'_hom)
    rw [Fin.sum_univ_three] at heul
    simp only [map_add, map_mul, map_nsmul, dehom, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, one_mul] at heul
    change u * MvPolynomial.aeval ![u, v] pU + v * MvPolynomial.aeval ![u, v] pV +
      MvPolynomial.aeval ![u, v] pW = s • MvPolynomial.aeval ![u, v] p at heul
    rw [hp_uv, nsmul_zero] at heul
    exact heul
  -- Step 8: Reflexivity formulas `z = pU(u,v) / pW(u,v)` and `y = pV(u,v) / pW(u,v)`!
  have hy_eq : y = MvPolynomial.aeval ![u, v] pV / MvPolynomial.aeval ![u, v] pW := by
    have hcross : z * MvPolynomial.aeval ![u, v] pV = y * MvPolynomial.aeval ![u, v] pU := by
      apply mul_right_cancel₀ hδ_u_ne
      linear_combination MvPolynomial.aeval ![u, v] pV * hcontact - y * hdual_deriv
    rw [eq_div_iff hpW_ne]
    apply mul_right_cancel₀ hpV_ne
    linear_combination MvPolynomial.aeval ![u, v] pV * y * heuler_P +
      u * MvPolynomial.aeval ![u, v] pV * hcross -
      (MvPolynomial.aeval ![u, v] pV) ^ 2 * heuler_F
  have hz_eq : z = MvPolynomial.aeval ![u, v] pU / MvPolynomial.aeval ![u, v] pW := by
    have hcross : z * MvPolynomial.aeval ![u, v] pV = y * MvPolynomial.aeval ![u, v] pU := by
      apply mul_right_cancel₀ hδ_u_ne
      linear_combination MvPolynomial.aeval ![u, v] pV * hcontact - y * hdual_deriv
    rw [eq_div_iff hpW_ne]
    apply mul_right_cancel₀ hpV_ne
    have hyW : y * MvPolynomial.aeval ![u, v] pW = MvPolynomial.aeval ![u, v] pV :=
      (eq_div_iff hpW_ne).mp hy_eq
    linear_combination MvPolynomial.aeval ![u, v] pW * hcross + MvPolynomial.aeval ![u, v] pU * hyW
  -- Step 9: Bound `m ≤ [E : K(z)] ≤ s * (s - 1)` for the final contradiction!
  have hz_trans : ∀ r : K[X], r ≠ 0 → Polynomial.aeval z r ≠ 0 := by
    intro r hr hrz
    -- `r(z) = 0` means `f ∣ eval₂ C (X 0) r`, impossible since `f` has `Y`-degree `m ≥ 2` while `r(Z)` has `Y`-degree `0`!
    let rMv : MvPolynomial (Fin 2) K := Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0) r
    have hπr : π rMv = 0 := by
      have h1 : ∀ r' : K[X], π (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0) r') =
          Polynomial.aeval z r' := by
        intro r'
        induction r' using Polynomial.induction_on' with
        | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
        | monomial i c =>
          rw [← Polynomial.C_mul_X_pow_eq_monomial]
          simp [map_mul, map_pow, z]
      exact (h1 r).trans hrz
    obtain ⟨q, hq⟩ := (hπ_zero_iff rMv).mp hπr
    have hrB : mv2EquivBiv rMv = Polynomial.C r := by
      have h1 : ∀ r' : K[X], mv2EquivBiv (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0) r') =
          Polynomial.C r' := by
        intro r'
        induction r' using Polynomial.induction_on' with
        | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
        | monomial i c =>
          rw [← Polynomial.C_mul_X_pow_eq_monomial]
          simp [map_mul, map_pow]
      exact h1 r
    have hq_ne : q ≠ 0 := by
      rintro rfl; rw [mul_zero] at hq
      have h0 := congrArg mv2EquivBiv hq
      rw [hrB, map_zero] at h0
      exact hr (Polynomial.C_eq_zero.mp h0)
    have hfB_deg : (mv2EquivBiv f).natDegree = m := by
      apply le_antisymm
      · refine natDegree_mv2EquivBiv_le f m fun e he => ?_
        have := (Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum fun _ v => v) he).trans
          (totalDegree_dehom_le hF'_hom)
        rw [m2_sum] at this; omega
      · apply Polynomial.le_natDegree_of_ne_zero
        intro h0
        have hc0 := congrArg (fun q : K[X] => q.coeff 0) h0
        rw [coeff_mv2EquivBiv, Polynomial.coeff_zero] at hc0
        have hF'eq : F' = homog m f :=
          dehom_inj_on_homogeneous m hF'_hom (homog_isHomogeneous m f (totalDegree_dehom_le hF'_hom))
            (dehom_homog m f).symm
        apply hF'_Y; change F'.coeff (Finsupp.single 1 m) = 0
        rw [hF'eq]; simp only [homog, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
        apply Finset.sum_eq_zero; intro e he; split_ifs with heq
        · exfalso
          have h := congrArg proj2 heq; rw [proj2_ext3] at h
          have he_eq : e = Finsupp.single 1 m := by rw [h]; ext i; fin_cases i <;> simp
          exact MvPolynomial.mem_support_iff.mp he (by simpa [he_eq] using hc0)
        · rfl
    have hmul := Polynomial.natDegree_mul
      ((map_ne_zero_iff mv2EquivBiv mv2EquivBiv.injective).mpr hf_irr.ne_zero)
      ((map_ne_zero_iff mv2EquivBiv mv2EquivBiv.injective).mpr hq_ne)
    rw [← map_mul, ← hq, hrB, Polynomial.natDegree_C, hfB_deg] at hmul
    omega
  let Kz : IntermediateField K E := IntermediateField.adjoin K {z}
  let zKz : Kz := ⟨z, IntermediateField.subset_adjoin K {z} rfl⟩
  let G1 : MvPolynomial (Fin 2) Kz := MvPolynomial.map (algebraMap K Kz) p
  let G2 : MvPolynomial (Fin 2) Kz :=
    MvPolynomial.map (algebraMap K Kz) pU -
    MvPolynomial.C zKz * MvPolynomial.map (algebraMap K Kz) pW
  have hG1_irr : Irreducible G1 := irreducible_map_adjoin_transcendental z hz_trans p hp_irr
  have hG1_deg : G1.totalDegree ≤ s := (totalDegree_map_le' _ _).trans (totalDegree_dehom_le hP'_hom)
  have hG2_deg : G2.totalDegree ≤ s - 1 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_map_le' _ _).trans (totalDegree_dehom_le hP'_hom.pderiv)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by
        rw [MvPolynomial.totalDegree_C, zero_add]
        exact (totalDegree_map_le' _ _).trans (totalDegree_dehom_le hP'_hom.pderiv))
  have hp_deg_eq : p.totalDegree = s := by
    apply le_antisymm (totalDegree_dehom_le hP'_hom)
    by_contra hlt'
    have hlt'' : p.totalDegree < s := not_le.mp hlt'
    have hP'eq : P' = homog s p :=
      dehom_inj_on_homogeneous s hP'_hom (homog_isHomogeneous s p (le_of_lt hlt'')) (dehom_homog s p).symm
    apply hX2_ndvd_P'
    rw [hP'eq]
    refine ⟨∑ e ∈ p.support, MvPolynomial.monomial (ext3 e (s - (e 0 + e 1) - 1)) (p.coeff e), ?_⟩
    rw [Finset.mul_sum]; unfold homog
    refine Finset.sum_congr rfl fun e he => ?_
    have hle : e 0 + e 1 ≤ p.totalDegree := by
      have := Finset.le_sup (f := fun t : Fin 2 →₀ ℕ => t.sum fun _ v => v) he
      rwa [m2_sum] at this
    rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
    exact congrArg (fun d => MvPolynomial.monomial d (p.coeff e))
      (by ext i; fin_cases i <;> simp; omega)
  have hG2_ne : G2 ≠ 0 := by
    intro h0
    have hW_ne : pW ≠ 0 := fun h => hpW_ne (by simp [h])
    obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hW_ne
    have hce := congrArg (fun g : MvPolynomial (Fin 2) Kz => g.coeff e) h0
    simp only [G2, MvPolynomial.coeff_sub, MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul,
      AddMonoidAlgebra.coeff_zero] at hce
    have hval := congrArg Subtype.val (sub_eq_zero.mp hce)
    have hW_c : pW.coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp he
    have hz_in_K : z = algebraMap K E (pU.coeff e / pW.coeff e) := by
      rw [map_div₀]
      have hWK : algebraMap K E (pW.coeff e) ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap K E).injective).mpr hW_c
      exact (eq_div_iff hWK).mpr (by simpa [zKz] using hval.symm)
    exact hz_trans (Polynomial.X - Polynomial.C (pU.coeff e / pW.coeff e))
      (Polynomial.X_sub_C_ne_zero _) (by simp [hz_in_K])
  have hG1_ndvd_G2 : ¬ G1 ∣ G2 := by
    intro ⟨Q, hQ⟩
    have hQ_ne : Q ≠ 0 := by rintro rfl; rw [mul_zero] at hQ; exact hG2_ne hQ
    have hG1_deg_eq : G1.totalDegree = s := by
      apply le_antisymm hG1_deg
      rw [← hp_deg_eq]
      refine totalDegree_le_of_forall_mem_support fun e he => ?_
      have he' : G1.coeff e ≠ 0 := by
        rw [MvPolynomial.coeff_map]; exact (map_ne_zero_iff _ (algebraMap K Kz).injective).mpr (MvPolynomial.mem_support_iff.mp he)
      exact Finset.le_sup (f := fun t : Fin 2 →₀ ℕ => t.sum fun _ v => v)
        (MvPolynomial.mem_support_iff.mpr he')
    have h1 := (totalDegreeLe_mv2EquivBiv_iff G1 G1.totalDegree).mpr le_rfl
    have h2 : Polynomial.Bivariate.totalDegree (mv2EquivBiv G1) = s := by
      apply le_antisymm
      · unfold Polynomial.Bivariate.totalDegree
        refine Finset.sup_le fun j hj => ?_
        have hj' := Polynomial.mem_support_iff.mp hj
        exact (h1 j hj').trans (le_of_eq hG1_deg_eq)
      · rw [← hG1_deg_eq]
        refine (totalDegreeLe_mv2EquivBiv_iff G1 _).mp fun j hj => ?_
        exact Polynomial.Bivariate.coeff_totalDegree_le _ (Polynomial.mem_support_iff.mpr hj)
    have h3 : Polynomial.Bivariate.totalDegree (mv2EquivBiv G2) ≤ s - 1 := by
      unfold Polynomial.Bivariate.totalDegree
      refine Finset.sup_le fun j hj => ?_
      exact ((totalDegreeLe_mv2EquivBiv_iff G2 (s - 1)).mpr hG2_deg) j (Polynomial.mem_support_iff.mp hj)
    have hmul := Polynomial.Bivariate.totalDegree_mul
      ((map_ne_zero_iff mv2EquivBiv mv2EquivBiv.injective).mpr hG1_irr.ne_zero)
      ((map_ne_zero_iff mv2EquivBiv mv2EquivBiv.injective).mpr hQ_ne)
    rw [← map_mul, ← hQ, h2] at hmul
    omega
  have hG_rel : IsRelPrime G1 G2 := by
    intro d hd1 hd2
    obtain ⟨w, hw⟩ := hd1
    rcases hG1_irr.isUnit_or_isUnit hw with hu' | hwu
    · exact hu'
    · exfalso; obtain ⟨w', hw'⟩ := hwu
      exact hG1_ndvd_G2 ((show G1 ∣ d from ⟨↑w'⁻¹, by rw [hw, ← hw', mul_assoc, Units.mul_inv, mul_one]⟩).trans hd2)
  have hKz_fin := finrank_le_of_two_equations Kz u v G1 G2 hG_rel hG1_deg hG2_deg
    (by
      rw [show G1 = MvPolynomial.map (algebraMap K Kz) p from rfl, MvPolynomial.aeval_map_algebraMap]
      exact hp_uv)
    (by
      dsimp only [G2]
      rw [map_sub, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_map_algebraMap,
        MvPolynomial.aeval_map_algebraMap]
      change MvPolynomial.aeval ![u, v] pU - z * MvPolynomial.aeval ![u, v] pW = 0
      rw [hz_eq, div_mul_cancel₀ _ hpW_ne, sub_self])
    (by
      intro hinv r
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective r
      change π g ∈ Algebra.adjoin Kz ({u, v} : Set E)
      have hz_mem : z ∈ Algebra.adjoin Kz ({u, v} : Set E) := by
        change (zKz : E) ∈ Algebra.adjoin Kz ({u, v} : Set E)
        exact Subalgebra.algebraMap_mem (Algebra.adjoin Kz ({u, v} : Set E)) zKz
      have haeval_mem : ∀ q : MvPolynomial (Fin 2) K,
          MvPolynomial.aeval ![u, v] q ∈ Algebra.adjoin Kz ({u, v} : Set E) := by
        intro q
        induction q using MvPolynomial.induction_on with
        | C c =>
          have : MvPolynomial.aeval ![u, v] (MvPolynomial.C c) =
              algebraMap Kz E (algebraMap K Kz c) := by simp
          rw [this]; exact Subalgebra.algebraMap_mem (Algebra.adjoin Kz ({u, v} : Set E)) _
        | add a b ha hb => rw [map_add]; exact Subalgebra.add_mem _ ha hb
        | mul_X a i ha =>
          rw [map_mul]; refine Subalgebra.mul_mem _ ha ?_
          rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
          · exact Algebra.subset_adjoin (by simp)
          · exact Algebra.subset_adjoin (by simp)
      have hy_mem : y ∈ Algebra.adjoin Kz ({u, v} : Set E) := by
        rw [hy_eq, div_eq_mul_inv]
        exact Subalgebra.mul_mem _ (haeval_mem pV) (hinv _ (haeval_mem pW))
      rw [hπ_eq_aeval]
      induction g using MvPolynomial.induction_on with
      | C c =>
        have : MvPolynomial.aeval ![z, y] (MvPolynomial.C c) =
            algebraMap Kz E (algebraMap K Kz c) := by simp
        rw [this]; exact Subalgebra.algebraMap_mem (Algebra.adjoin Kz ({u, v} : Set E)) _
      | add a b ha hb => rw [map_add]; exact Subalgebra.add_mem _ ha hb
      | mul_X a i ha =>
        rw [map_mul]; refine Subalgebra.mul_mem _ ha ?_
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · simpa using hz_mem
        · simpa using hy_mem)
  have : Module.Finite Kz E := hKz_fin.1
  -- Show `1, y, ..., y^(m-1)` are `Kz`-linearly independent, so `m ≤ [E : Kz] ≤ s * (s - 1)`.
  have hli : LinearIndependent Kz (fun j : Fin m => y ^ j.val) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    let e := adjoinEquivFractionRing z hz_trans
    have hex : ∀ j : Fin m, ∃ num den : K[X], den ≠ 0 ∧
        e.symm (c j) = algebraMap K[X] (FractionRing K[X]) num /
          algebraMap K[X] (FractionRing K[X]) den := by
      intro j
      obtain ⟨num, den, hden, hdiv⟩ := IsFractionRing.div_surjective (A := K[X]) (e.symm (c j))
      exact ⟨num, den, mem_nonZeroDivisors_iff_ne_zero.mp hden, hdiv.symm⟩
    choose num den hden hdiv using hex
    let D₀ : K[X] := ∏ j : Fin m, den j
    have hD₀_ne : D₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hden j
    let a : Fin m → K[X] := fun j => num j * ∏ k ∈ Finset.univ.erase j, den k
    have hcj_mul (j : Fin m) :
        c j * e (algebraMap K[X] (FractionRing K[X]) D₀) =
          e (algebraMap K[X] (FractionRing K[X]) (a j)) := by
      have h1 : e.symm (c j) * algebraMap K[X] (FractionRing K[X]) D₀ =
          algebraMap K[X] (FractionRing K[X]) (a j) := by
        rw [hdiv j]
        have hD₀_split : D₀ = den j * ∏ k ∈ Finset.univ.erase j, den k :=
          (Finset.mul_prod_erase Finset.univ den (Finset.mem_univ j)).symm
        have hdenF : algebraMap K[X] (FractionRing K[X]) (den j) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective K[X] (FractionRing K[X]))).mpr (hden j)
        rw [hD₀_split, map_mul, div_mul_eq_mul_div, mul_left_comm,
          mul_div_cancel_left₀ _ hdenF, map_mul]
      have h2 := congrArg e h1
      simpa [map_mul] using h2
    have hD₀_eval_ne : Polynomial.aeval z D₀ ≠ 0 := hz_trans D₀ hD₀_ne
    have hsum_eval : ∑ j : Fin m, Polynomial.aeval z (a j) * y ^ j.val = 0 := by
      have h1 := congrArg (fun x : E => x * Polynomial.aeval z D₀) hc
      simp only [zero_mul, Algebra.smul_def] at h1
      rw [Finset.sum_mul] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj : (c j : E) * Polynomial.aeval z D₀ = Polynomial.aeval z (a j) := by
        have := congrArg Subtype.val (hcj_mul j)
        simpa [e, adjoinEquivFractionRing_algebraMap] using this
      calc Polynomial.aeval z (a j) * y ^ j.val
          = ((c j : E) * Polynomial.aeval z D₀) * y ^ j.val := by rw [hj]
        _ = (c j : E) * y ^ j.val * Polynomial.aeval z D₀ := by ring
    let q : K[X][X] := ∑ j : Fin m, Polynomial.C (a j) * Polynomial.X ^ j.val
    have hq_eval : (q.map (Polynomial.aeval z).toRingHom).eval y = 0 := by
      simp only [q, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      exact hsum_eval
    have hπq : π (mv2EquivBiv.symm q) = 0 := by
      rw [hπ_eq_aeval, ← eval_mv2EquivBiv (mv2EquivBiv.symm q) z y, RingEquiv.apply_symm_apply]
      exact hq_eval
    obtain ⟨w, hw⟩ := (hπ_zero_iff (mv2EquivBiv.symm q)).mp hπq
    have hq_dvd : mv2EquivBiv f ∣ q := by
      refine ⟨mv2EquivBiv w, ?_⟩
      have h := congrArg mv2EquivBiv hw
      simpa [map_mul] using h
    have hq_zero : q = 0 := by
      by_contra hq_ne
      have hfB_deg : (mv2EquivBiv f).natDegree = m := by
        apply le_antisymm
        · refine natDegree_mv2EquivBiv_le f m fun t ht => ?_
          have := (Finset.le_sup (f := fun u : Fin 2 →₀ ℕ => u.sum fun _ v => v) ht).trans
            (totalDegree_dehom_le hF'_hom)
          rw [m2_sum] at this; omega
        · apply Polynomial.le_natDegree_of_ne_zero
          intro h0
          have hc0 := congrArg (fun r : K[X] => r.coeff 0) h0
          rw [coeff_mv2EquivBiv, Polynomial.coeff_zero] at hc0
          have hF'eq : F' = homog m f :=
            dehom_inj_on_homogeneous m hF'_hom (homog_isHomogeneous m f (totalDegree_dehom_le hF'_hom))
              (dehom_homog m f).symm
          apply hF'_Y; change F'.coeff (Finsupp.single 1 m) = 0
          rw [hF'eq]; simp only [homog, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
          apply Finset.sum_eq_zero; intro t ht; split_ifs with heq
          · exfalso
            have h := congrArg proj2 heq; rw [proj2_ext3] at h
            have ht_eq : t = Finsupp.single 1 m := by rw [h]; ext i; fin_cases i <;> simp
            exact MvPolynomial.mem_support_iff.mp ht (by simpa [ht_eq] using hc0)
          · rfl
      have hq_deg : q.natDegree < m := by
        have hle : q.natDegree ≤ m - 1 := by
          refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
          exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
        omega
      have hle := Polynomial.natDegree_le_of_dvd hq_dvd hq_ne
      omega
    intro j
    have haj : a j = 0 := by
      have hcoeff := congrArg (fun r : K[X][X] => r.coeff j.val) hq_zero
      simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at hcoeff
      rw [Finset.sum_eq_single j] at hcoeff
      · simpa using hcoeff
      · intro k _ hkj; simp [Fin.val_ne_of_ne (Ne.symm hkj)]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hmul0 : c j * e (algebraMap K[X] (FractionRing K[X]) D₀) = 0 := by
      rw [hcj_mul j, haj, map_zero, map_zero]
    have hD₀_Kz : e (algebraMap K[X] (FractionRing K[X]) D₀) ≠ 0 := by
      intro h0
      have := congrArg Subtype.val h0
      rw [adjoinEquivFractionRing_algebraMap] at this
      exact hD₀_eval_ne this
    exact (mul_eq_zero.mp hmul0).resolve_right hD₀_Kz
  have hm_le : m ≤ Module.finrank Kz E := by
    simpa [Fintype.card_fin] using hli.fintype_card_le_finrank
  exact hlt (hm_le.trans hKz_fin.2)

/-- **Pardini Plane-Curve Reflexivity Theorem (general nonzero homogeneous `P`)**:
Over an algebraically closed field `K` with `∀ k, 0 < k → k ≤ m * (m - 1) → (k : K) ≠ 0`,
if `F : MvPolynomial (Fin 3) K` is irreducible homogeneous of degree `m ≥ 2` and
`P : MvPolynomial (Fin 3) K` is nonzero homogeneous of degree `s` with `F ∣ gaussPullback F P`,
then `2 ≤ s` and `m ≤ s * (s - 1)`. -/
theorem pardini_reflexivity [IsAlgClosed K] {F : MvPolynomial (Fin 3) K} {m : ℕ}
    (hF_irr : Irreducible F) (hF_hom : F.IsHomogeneous m) (hm : 2 ≤ m)
    (hchar : ∀ k : ℕ, 0 < k → k ≤ m * (m - 1) → (k : K) ≠ 0) :
    ∀ s : ℕ, ∀ P : MvPolynomial (Fin 3) K, P.IsHomogeneous s → P ≠ 0 →
      F ∣ gaussPullback F P → 2 ≤ s ∧ m ≤ s * (s - 1) := by
  classical
  have hF_prime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hF_irr
  have hchar_m : ∀ k : ℕ, 0 < k → k ≤ m → (k : K) ≠ 0 := fun k hk1 hk2 =>
    hchar k hk1 (hk2.trans (Nat.le_mul_of_pos_right m (by omega)))
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro P hP_hom hP_ne hdvd
    rcases eq_or_ne s 0 with rfl | hs0
    · exfalso
      have hc : P = MvPolynomial.C (P.coeff 0) := isHomogeneous_zero_eq_C hP_hom
      have hcne : P.coeff 0 ≠ 0 := by intro h0; rw [h0, map_zero] at hc; exact hP_ne hc
      rw [hc] at hdvd
      have hgp : gaussPullback F (MvPolynomial.C (P.coeff 0)) = MvPolynomial.C (P.coeff 0) := by
        simp [gaussPullback]
      rw [hgp] at hdvd
      exact hF_irr.not_isUnit (isUnit_of_dvd_unit hdvd (hcne.isUnit.map MvPolynomial.C))
    · rcases eq_or_ne s 1 with rfl | hs1
      · exfalso
        let a : Fin 3 → K := fun i => P.coeff (Finsupp.single i 1)
        have hP_eq : P = ∑ i : Fin 3, MvPolynomial.C (a i) * MvPolynomial.X i := by
          have hsub : P.support ⊆ {Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 2 1} := by
            intro e he
            have hdeg := hP_hom (MvPolynomial.mem_support_iff.mp he)
            rw [weight_one_eq_sum, m3_sum] at hdeg
            simp only [Finset.mem_insert, Finset.mem_singleton]
            by_cases h0 : e 0 = 1
            · left; ext i; fin_cases i <;> simp <;> omega
            · by_cases h1 : e 1 = 1
              · right; left; ext i; fin_cases i <;> simp <;> omega
              · right; right; ext i; fin_cases i <;> simp <;> omega
          have hsum : P = ∑ e ∈ ({Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 2 1} :
              Finset (Fin 3 →₀ ℕ)), MvPolynomial.monomial e (P.coeff e) := by
            conv_lhs => rw [P.as_sum]
            exact Finset.sum_subset hsub fun e _ he => by
              rw [MvPolynomial.notMem_support_iff.mp he, map_zero]
          rw [hsum]
          have h01 : Finsupp.single (0 : Fin 3) 1 ≠ Finsupp.single 1 1 := by
            intro h; have := congrArg (fun f : Fin 3 →₀ ℕ => f 0) h; simp at this
          have h02 : Finsupp.single (0 : Fin 3) 1 ≠ Finsupp.single 2 1 := by
            intro h; have := congrArg (fun f : Fin 3 →₀ ℕ => f 0) h; simp at this
          have h12 : Finsupp.single (1 : Fin 3) 1 ≠ Finsupp.single 2 1 := by
            intro h; have := congrArg (fun f : Fin 3 →₀ ℕ => f 1) h; simp at this
          rw [Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
            Finset.sum_singleton, Fin.sum_univ_three]
          simp [a, MvPolynomial.X, MvPolynomial.C_mul_monomial, add_assoc]
        have ha : a ≠ 0 := by
          intro h0; apply hP_ne; rw [hP_eq]; simp [h0]
        have hgp : gaussPullback F P = ∑ i : Fin 3, MvPolynomial.C (a i) * pderiv i F := by
          rw [hP_eq, gaussPullback, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_X]
          rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> simp
        exact linear_polar_not_dvd hF_irr hF_hom hm hchar_m a ha (hgp ▸ hdvd)
      · have hs2 : 2 ≤ s := by omega
        by_cases hP_irr : Irreducible P
        · exact ⟨hs2, pardini_reflexivity_irreducible hF_irr hF_hom hm hP_irr hP_hom hs2 hchar hdvd⟩
        · have hP_nu : ¬ IsUnit P := by
            intro hu
            obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
            have h0 : P.IsHomogeneous 0 := by rw [hc]; exact MvPolynomial.isHomogeneous_C (Fin 3) c
            obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hP_ne
            have := hP_hom (MvPolynomial.mem_support_iff.mp he)
            have := h0 (MvPolynomial.mem_support_iff.mp he)
            omega
          have hfac : ∃ A B : MvPolynomial (Fin 3) K, P = A * B ∧ ¬ IsUnit A ∧ ¬ IsUnit B := by
            by_contra hall; push Not at hall
            exact hP_irr ⟨hP_nu, fun A B hAB => by
              by_cases hA : IsUnit A
              · exact Or.inl hA
              · exact Or.inr (hall A B hAB hA)⟩
          obtain ⟨A, B, hPAB, hAnu, hBnu⟩ := hfac
          have hAne : A ≠ 0 := by rintro rfl; simp at hPAB; exact hP_ne hPAB
          have hBne : B ≠ 0 := by rintro rfl; simp at hPAB; exact hP_ne hPAB
          obtain ⟨dA, hA_hom⟩ := isHomogeneous_of_dvd hP_hom hP_ne ⟨B, hPAB⟩
          obtain ⟨dB, hB_hom⟩ := isHomogeneous_of_dvd hP_hom hP_ne ⟨A, by rw [hPAB, mul_comm]⟩
          have hdAB : dA + dB = s := by
            have hprod := hA_hom.mul hB_hom; rw [← hPAB] at hprod
            obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hP_ne
            have h1 := hP_hom (MvPolynomial.mem_support_iff.mp he)
            have h2 := hprod (MvPolynomial.mem_support_iff.mp he)
            omega
          have hdA_pos : 0 < dA := by
            by_contra h0; push Not at h0
            have hdA0 : dA = 0 := by omega
            subst hdA0
            have hc : A = MvPolynomial.C (A.coeff 0) := isHomogeneous_zero_eq_C hA_hom
            have hcne : A.coeff 0 ≠ 0 := by intro h0; rw [h0, map_zero] at hc; exact hAne hc
            exact hAnu (hc ▸ hcne.isUnit.map MvPolynomial.C)
          have hdB_pos : 0 < dB := by
            by_contra h0; push Not at h0
            have hdB0 : dB = 0 := by omega
            subst hdB0
            have hc : B = MvPolynomial.C (B.coeff 0) := isHomogeneous_zero_eq_C hB_hom
            have hcne : B.coeff 0 ≠ 0 := by intro h0; rw [h0, map_zero] at hc; exact hBne hc
            exact hBnu (hc ▸ hcne.isUnit.map MvPolynomial.C)
          have hgp_mul : gaussPullback F P = gaussPullback F A * gaussPullback F B := by
            rw [hPAB, gaussPullback, map_mul]; rfl
          rw [hgp_mul] at hdvd
          rcases hF_prime.dvd_or_dvd hdvd with hA_dvd | hB_dvd
          · obtain ⟨_, hmA⟩ := ih dA (by omega) A hA_hom hAne hA_dvd
            exact ⟨hs2, hmA.trans (Nat.mul_le_mul (by omega) (by omega))⟩
          · obtain ⟨_, hmB⟩ := ih dB (by omega) B hB_hom hBne hB_dvd
            exact ⟨hs2, hmB.trans (Nat.mul_le_mul (by omega) (by omega))⟩

#print axioms pardini_reflexivity_irreducible
#print axioms pardini_reflexivity

end ArkLib.ProximityGap.Frontier.PlaneCurveReflexivity
