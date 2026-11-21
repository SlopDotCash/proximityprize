/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.MultiplicityInterpolation
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import ArkLib.ToMathlib.Polynomial.RootMultiplicity

/-! # A quartic containing every rich folded polynomial at the second prime

Counting coefficients of the specialized received line costs only one scalar constraint
per parameter degree and coordinate. The excess is 595 at the last open predecessor.
The coefficient indexing retains the separate value, parameter and coordinate exponents.
-/

set_option autoImplicit false

open Polynomial Finset
open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.SecondPrimeQuarticInterpolation

/-- Exponents in value, parameter and evaluation-coordinate order. -/
abbrev Monomials (s v d t : ℕ) :=
  (j : Fin (v+1)) × (Fin (s+1-j.val) × Fin (t-j.val*d))

variable {F ι : Type*} [Field F] [Fintype ι]
variable {s v d t : ℕ}

private noncomputable def lineTerm (m : Monomials s v d t) (x a b : F) : F[X] :=
  monomial m.2.1.val (x ^ m.2.2.val) * (C a + X * C b)^m.1.val

/-- Restrict the surface to the whole received scalar line at one coordinate. -/
noncomputable def receivedLine (c : Monomials s v d t → F) (x a b : F) : F[X] :=
  ∑ m, C (c m) * lineTerm m x a b

private theorem lineTerm_natDegree (m : Monomials s v d t) (x a b : F) :
    (lineTerm m x a b).natDegree ≤ s := by
  have hab : (C a + X * C b).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact natDegree_mul_le.trans (by simp)
  have h := (natDegree_pow_le (p := C a + X * C b) (n := m.1.val)).trans
    (Nat.mul_le_mul_left _ hab)
  have hi := m.2.1.isLt
  exact (natDegree_mul_le.trans (Nat.add_le_add (natDegree_monomial_le _) h)).trans (by omega)

/-- Substitute the scalar and the candidate into the parameter and value variables. -/
noncomputable def specialize (c : Monomials s v d t → F) (g : F) (q : F[X]) : F[X] :=
  ∑ m, monomial m.2.2.val (c m * g ^ m.2.1.val) * q ^ m.1.val

/-- Build a univariate polynomial from a dense, degree-bounded coefficient vector. -/
private noncomputable def ofFin {R : Type*} [Semiring R] {w : ℕ} (c : Fin w → R) : R[X] :=
  ∑ i, monomial i.val (c i)

private lemma coeff_ofFin {R : Type*} [Semiring R] {w : ℕ} (c : Fin w → R) (i : Fin w) :
    (ofFin c).coeff i.val = c i := by
  classical
  simp [ofFin, finsetSum_coeff, coeff_monomial, Fin.val_inj]

private lemma coeff_ofFin_outside {R : Type*} [Semiring R] {w : ℕ} (c : Fin w → R)
    {i : ℕ} (hi : w ≤ i) : (ofFin c).coeff i = 0 := by
  classical
  simp only [ofFin, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  rw [coeff_monomial, ite_eq_right (by omega)]

/-- The genuine trivariate polynomial, with the value variable outermost, then the
scalar variable, then the evaluation coordinate. -/
noncomputable def surface (c : Monomials s v d t → F) : Polynomial (Polynomial F[X]) :=
  ofFin fun j => ofFin fun i => ofFin fun a => c ⟨j, i, a⟩

theorem surface_ne_zero {c : Monomials s v d t → F} (hc : c ≠ 0) : surface c ≠ 0 := by
  intro hz
  apply hc
  funext m
  rcases m with ⟨j, i, a⟩
  have h := congrArg (fun Q : Polynomial (Polynomial F[X]) =>
    ((Q.coeff j.val).coeff i.val).coeff a.val) hz
  simpa only [surface, coeff_ofFin, coeff_zero, Pi.zero_apply] using h

/-- Every nonzero coefficient satisfies the three separate degree bounds. -/
theorem surface_support (c : Monomials s v d t → F) {j i a : ℕ}
    (h : (((surface c).coeff j).coeff i).coeff a ≠ 0) :
    j ≤ v ∧ i+j ≤ s ∧ a+j*d < t := by
  by_cases hj : j < v+1
  · let J : Fin (v+1) := ⟨j,hj⟩
    change (((surface c).coeff J.val).coeff i).coeff a ≠ 0 at h
    rw [surface, coeff_ofFin] at h
    by_cases hi : i < s+1-J.val
    · let I : Fin (s+1-J.val) := ⟨i,hi⟩
      change ((ofFin fun i' => ofFin fun a' => c ⟨J,i',a'⟩).coeff I.val).coeff a ≠ 0 at h
      rw [coeff_ofFin] at h
      have ha : a < t-J.val*d := by
        by_contra! hn
        exact h (coeff_ofFin_outside _ hn)
      dsimp only [J] at hi ha
      omega
    · rw [coeff_ofFin_outside _ (Nat.le_of_not_gt hi), coeff_zero] at h
      exact False.elim (h rfl)
  · rw [surface, coeff_ofFin_outside _ (Nat.le_of_not_gt hj), coeff_zero, coeff_zero] at h
    exact False.elim (h rfl)

/-- Substituting the scalar and candidate into the genuine trivariate polynomial
agrees with the supported-coefficient formula. -/
theorem surface_eval (c : Monomials s v d t → F) (g : F) (q : F[X]) :
    (surface c).eval₂ (evalRingHom (C g)) q = specialize c g q := by
  classical
  simp only [surface, ofFin, specialize, eval₂_finsetSum, eval₂_monomial, coe_evalRingHom,
    eval_finsetSum, eval_monomial, Fintype.sum_sigma, Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  rw [← C_pow, monomial_mul_C]

private theorem specialize_degree (c : Monomials s v d t → F) (g : F) (q : F[X])
    (hq : q.natDegree ≤ d) (ht : 0 < t) : (specialize c g q).natDegree < t := by
  apply Nat.lt_of_le_pred ht
  rw [Nat.pred_eq_sub_one]
  apply natDegree_sum_le_of_forall_le
  intro m _
  have hj := (natDegree_pow_le (p := q) (n := m.1.val)).trans
    (Nat.mul_le_mul_left _ hq)
  have hi := m.2.2.isLt
  exact (natDegree_mul_le.trans (Nat.add_le_add (natDegree_monomial_le _) hj)).trans (by omega)

/-- A nonzero supported coefficient vector vanishing identically on all rich folded candidates. -/
theorem exists_curve (dom : ι ↪ F) (u₀ u₁ : ι → F) (ht : 0 < t)
    (hcount : Fintype.card ι * (s+1) < Fintype.card (Monomials s v d t)) :
    ∃ c : Monomials s v d t → F, c ≠ 0 ∧
      (∀ i, receivedLine c (dom i) (u₀ i) (u₁ i) = 0) ∧ ∀ g : F, ∀ q : F[X], q.natDegree ≤ d →
      ∀ S : Finset ι, t ≤ S.card →
        (∀ i ∈ S, q.eval (dom i) = u₀ i + g * u₁ i) → specialize c g q = 0 := by
  classical
  let M : Matrix (ι × Fin (s+1)) (Monomials s v d t) F :=
    fun row m => (lineTerm m (dom row.1) (u₀ row.1) (u₁ row.1)).coeff row.2.val
  have hfr : Module.finrank F ((ι × Fin (s+1)) → F) <
      Module.finrank F (Monomials s v d t → F) := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] using hcount
  obtain ⟨c, hc, hker⟩ := GSMultInterp.exists_ne_zero_map_eq_zero M.mulVecLin hfr
  have hline (i : ι) : ∑ m, C (c m) * lineTerm m (dom i) (u₀ i) (u₁ i) = 0 := by
    ext l
    rw [finsetSum_coeff, coeff_zero]
    by_cases hl : l < s+1
    · change M.mulVec c = 0 at hker
      have h := congrFun hker (i, ⟨l, hl⟩)
      simpa only [M, Matrix.mulVec, dotProduct, Pi.zero_apply, coeff_C_mul, mul_comm] using h
    · apply Finset.sum_eq_zero
      intro m _
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
        (lineTerm_natDegree m _ _ _) (by omega : s < l)), mul_zero]
  refine ⟨c, hc, hline, fun g q hq S hS hag => ?_⟩
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun i : S => dom i.val)
    (dom.injective.comp Subtype.val_injective)
  · intro i
    have h := congrArg (Polynomial.eval g) (hline i.val)
    simp only [specialize, lineTerm, Polynomial.eval_finsetSum, eval_mul, eval_monomial,
      eval_pow, eval_add, eval_X, eval_C, eval_zero, hag _ i.property] at h ⊢
    convert h using 1
    apply Finset.sum_congr rfl
    intro m _
    ring
  · simpa using (specialize_degree c g q hq ht).trans_le hS

/-- At length 2^30 and the final candidate good error 715827881, a relation of value
degree at most four and total value-parameter degree at most 34 contains every rich candidate. -/
theorem secondPrime_predecessor_quartic (dom : ι ↪ F) (u₀ u₁ : ι → F)
    (hn : Fintype.card ι = 1073741824) :
    ∃ c : Monomials 34 4 67108863 357913943 → F, c ≠ 0 ∧
      (∀ i, receivedLine c (dom i) (u₀ i) (u₁ i) = 0) ∧ ∀ g : F, ∀ q : F[X],
      q.natDegree ≤ 67108863 → ∀ S : Finset ι, 357913943 ≤ S.card →
        (∀ i ∈ S, q.eval (dom i) = u₀ i + g * u₁ i) → specialize c g q = 0 := by
  apply exists_curve dom u₀ u₁ (by decide)
  rw [hn]
  simp only [Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]

/-- A genuine trivariate polynomial containing every rich candidate simultaneously.
Here the degree restrictions are stated directly on its coefficients. -/
theorem secondPrime_predecessor_surface (dom : ι ↪ F) (u₀ u₁ : ι → F)
    (hn : Fintype.card ι = 1073741824) :
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 4 ∧ i+j ≤ 34 ∧ a+j*67108863 < 357913943) ∧
      ∀ g : F, ∀ q : F[X], q.natDegree ≤ 67108863 → ∀ S : Finset ι, 357913943 ≤ S.card →
        (∀ i ∈ S, q.eval (dom i) = u₀ i + g*u₁ i) → Q.eval₂ (evalRingHom (C g)) q = 0 := by
  obtain ⟨c, hc, _, hall⟩ := secondPrime_predecessor_quartic dom u₀ u₁ hn
  refine ⟨surface c, surface_ne_zero hc, fun _ _ _ h => surface_support c h, ?_⟩
  intro g q hq S hS ha
  rw [surface_eval]
  exact hall _ _ hq _ hS ha

/-- Coordinate and value derivatives restricted to the received line. -/
private noncomputable def dxTerm (m : Monomials s v d t) (x a b : F) : F[X] :=
  monomial m.2.1.val ((m.2.2.val : F) * x^(m.2.2.val-1)) * (C a + X*C b)^m.1.val

private noncomputable def dyTerm (m : Monomials s v d t) (x a b : F) : F[X] :=
  monomial m.2.1.val ((m.1.val : F) * x^m.2.2.val) * (C a + X*C b)^(m.1.val-1)

private theorem monomial_line_degree (i j : ℕ) (y a b : F) :
    (monomial i y * (C a + X*C b)^j).natDegree ≤ i+j := by
  have hab : (C a + X * C b).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact natDegree_mul_le.trans (by simp)
  apply natDegree_mul_le.trans
  exact Nat.add_le_add (natDegree_monomial_le _) ((natDegree_pow_le).trans
    (by simpa using Nat.mul_le_mul_left j hab))

private theorem constraints_zero {μ : Type*} [Fintype μ] (coeffs : μ → F) (row : μ → F[X])
    (w : ℕ) (hdeg : ∀ m, (row m).natDegree < w)
    (h : ∀ l : Fin w, ∑ m, (row m).coeff l.val * coeffs m = 0) :
    ∑ m, C (coeffs m) * row m = 0 := by
  ext l
  rw [finsetSum_coeff, coeff_zero]
  by_cases hl : l < w
  · simp only [coeff_C_mul]
    simpa only [mul_comm] using h ⟨l,hl⟩
  · apply Finset.sum_eq_zero
    intro m _
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt ((hdeg m).trans_le (by omega)), mul_zero]

private theorem square_dvd_of_double_root (w : F[X]) (x : F)
    (hr : w.eval x = 0) (hd : w.derivative.eval x = 0) : (X-C x)^2 ∣ w := by
  obtain ⟨v,hv⟩ := dvd_iff_isRoot.mpr (show w.IsRoot x from hr)
  have hh : v.eval x = 0 := by simpa [hv, derivative_mul] using hd
  obtain ⟨z,hz⟩ := dvd_iff_isRoot.mpr (show v.IsRoot x from hh)
  exact ⟨z,by rw [hv,hz,pow_two,mul_assoc]⟩

/-- Multiplicity two. The two zeroth-scalar-degree-bound rows test the value and its
coordinate derivative. The value derivative has one fewer scalar coefficient. -/
theorem exists_curve_double (dom : ι ↪ F) (u₀ u₁ : ι → F) (ht : 0 < t) (hs : 0 < s)
    (hcount : Fintype.card ι * (2*(s+1)+s) < Fintype.card (Monomials s v d (2*t))) :
    ∃ c : Monomials s v d (2*t) → F, c ≠ 0 ∧ ∀ g : F, ∀ q : F[X], q.natDegree ≤ d →
      ∀ S : Finset ι, t ≤ S.card →
        (∀ i ∈ S, q.eval (dom i) = u₀ i + g*u₁ i) → specialize c g q = 0 := by
  classical
  let M : Matrix (ι × (Fin (s+1) ⊕ (Fin (s+1) ⊕ Fin s))) (Monomials s v d (2*t)) F :=
    fun row m => match row.2 with
    | .inl l => (lineTerm m (dom row.1) (u₀ row.1) (u₁ row.1)).coeff l.val
    | .inr (.inl l) => (dxTerm m (dom row.1) (u₀ row.1) (u₁ row.1)).coeff l.val
    | .inr (.inr l) => (dyTerm m (dom row.1) (u₀ row.1) (u₁ row.1)).coeff l.val
  have hfr : Module.finrank F ((ι × (Fin (s+1) ⊕ (Fin (s+1) ⊕ Fin s))) → F) <
      Module.finrank F (Monomials s v d (2*t) → F) := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_sum, two_mul, add_assoc] using hcount
  obtain ⟨c,hc,hker⟩ := GSMultInterp.exists_ne_zero_map_eq_zero M.mulVecLin hfr
  change M.mulVec c = 0 at hker
  refine ⟨c,hc,fun g q hq S hS hag => ?_⟩
  apply Polynomial.eq_zero_of_degree_lt_mul_of_pow_X_sub_C_dvd_at_injOn dom S 2 t
    dom.injective.injOn hS
  · intro x hx
    let a := u₀ x
    let b := u₁ x
    have hz := constraints_zero c (fun m => lineTerm m (dom x) a b) (s+1)
      (fun m => Nat.lt_succ_of_le (lineTerm_natDegree m _ _ _))
      (fun l => congrFun hker (x,.inl l))
    have hx' := constraints_zero c (fun m => dxTerm m (dom x) a b) (s+1) (fun m => by
      have hi := m.2.1.isLt
      exact (monomial_line_degree _ _ _ _ _).trans_lt (by omega))
      (fun l => congrFun hker (x,.inr (.inl l)))
    have hy := constraints_zero c (fun m => dyTerm m (dom x) a b) s (fun m => by
      have hi := m.2.1.isLt
      by_cases h0 : m.1.val = 0
      · simpa [dyTerm, h0] using hs
      · exact (monomial_line_degree _ _ _ _ _).trans_lt (by omega))
      (fun l => congrFun hker (x,.inr (.inr l)))
    have herm : q.eval (dom x) = a+g*b := hag x hx
    have h₀ := congrArg (Polynomial.eval g) hz
    have h₁ := congrArg (Polynomial.eval g) hx'
    have h₂ := congrArg (Polynomial.eval g) hy
    apply square_dvd_of_double_root
    · simp only [specialize, lineTerm, Polynomial.eval_finsetSum, eval_mul, eval_monomial,
        eval_pow, eval_add, eval_X, eval_C, eval_zero, herm] at h₀ ⊢
      convert h₀ using 1
      apply Finset.sum_congr rfl
      intro m _
      ring
    · simp only [specialize, derivative_sum, derivative_mul, derivative_monomial, derivative_pow,
        dxTerm, dyTerm, eval_finsetSum, eval_mul, eval_monomial, eval_pow, eval_add, eval_X,
        eval_C, eval_zero, herm] at h₁ h₂ ⊢
      have hchain := congrArg₂ (fun h k : F => h+k*q.derivative.eval (dom x)) h₁ h₂
      simp only [zero_mul, add_zero, Finset.sum_mul, ← Finset.sum_add_distrib] at hchain
      convert hchain using 1
      apply Finset.sum_congr rfl
      intro m _
      ring
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast specialize_degree c g q hq (by omega))

/-- At the last candidate good error, every rich fold lies simultaneously on a
nonzero curve of ordinary total degree at most twelve in the scalar and value. -/
theorem secondPrime_predecessor_degree_twelve (dom : ι ↪ F) (u₀ u₁ : ι → F)
    (hn : Fintype.card ι = 1073741824) :
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
        j ≤ 10 ∧ i+j ≤ 12 ∧ a+j*67108863 < 2*357913943) ∧
      ∀ g : F, ∀ q : F[X], q.natDegree ≤ 67108863 → ∀ S : Finset ι, 357913943 ≤ S.card →
        (∀ i ∈ S, q.eval (dom i) = u₀ i + g*u₁ i) → Q.eval₂ (evalRingHom (C g)) q = 0 := by
  obtain ⟨c,hc,hall⟩ := exists_curve_double (s:=12) (v:=10) (d:=67108863) (t:=357913943)
    dom u₀ u₁ (by decide) (by decide) (by
      rw [hn]
      simp only [Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
      norm_num [Fin.sum_univ_succ])
  refine ⟨surface c, surface_ne_zero hc, fun _ _ _ h => surface_support c h, ?_⟩
  intro g q hq S hS ha
  rw [surface_eval]
  exact hall _ _ hq _ hS ha

/-- At 418631484 agreements, both a total-degree-five relation and a value-degree-three
relation of total degree seven contain every rich candidate. -/
theorem secondPrime_cubic_quintic (dom : ι ↪ F) (u₀ u₁ : ι → F)
    (hn : Fintype.card ι = 1073741824) :
    ∀ (s v : ℕ), (s = 5 ∧ v = 5) ∨ (s = 7 ∧ v = 3) →
      ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
        (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 →
          j ≤ v ∧ i+j ≤ s ∧ a+j*67108863 < 418631484) ∧
        ∀ g : F, ∀ q : F[X], q.natDegree ≤ 67108863 → ∀ S : Finset ι, 418631484 ≤ S.card →
          (∀ i ∈ S, q.eval (dom i) = u₀ i + g*u₁ i) → Q.eval₂ (evalRingHom (C g)) q = 0 := by
  intro s v hshape
  obtain ⟨c,hc,_,hall⟩ := exists_curve (s:=s) (v:=v) (d:=67108863) (t:=418631484)
    dom u₀ u₁ (by decide) (by
      rw [hn]
      rcases hshape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        simp only [Monomials, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] <;>
        norm_num [Fin.sum_univ_succ])
  refine ⟨surface c, surface_ne_zero hc, fun _ _ _ h => surface_support c h, ?_⟩
  intro g q hq S hS ha
  rw [surface_eval]
  exact hall _ _ hq _ hS ha

end ArkLib.ProximityGap.Frontier.SecondPrimeQuarticInterpolation

#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeQuarticInterpolation.secondPrime_predecessor_quartic
#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeQuarticInterpolation.secondPrime_predecessor_surface

#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeQuarticInterpolation.secondPrime_predecessor_degree_twelve

#print axioms ArkLib.ProximityGap.Frontier.SecondPrimeQuarticInterpolation.secondPrime_cubic_quintic
