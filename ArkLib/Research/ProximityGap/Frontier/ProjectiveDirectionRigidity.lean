/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Content
import ArkLib.Research.ProximityGap.Frontier.ProjectiveDirectionIncidence

/-!
# Interpolation of a polynomial direction on proportional coordinate rows

A polynomial of degree at most D in the site coordinate has coefficients in the
challenge polynomial ring. Suppose two nonzero coefficients have challenge
degrees differing by at least two. On at most D sites can this direction be
proportional, with a fixed nonzero rational proportionality factor, to affine
received rows. The conclusion holds for every choice of received rows.
-/
namespace ProximityGap.ProjectiveDirectionRigidity

open Polynomial Finset
variable {I F : Type*} [Field F] [Fintype I]

omit [Fintype I] in
/-- Proportionality on more than D evaluation sites forces every challenge
coefficient to become affine after multiplication by the same rational function. -/
theorem affine_coefficients (dom : I ↪ F) (U : (F[X])[X]) {D : ℕ}
    (hD : U.natDegree ≤ D) (T : Finset I) (hT : D < T.card)
    (u v : I → F) (a b : F[X])
    (hfit : ∀ i ∈ T, a * U.eval (C (dom i)) = b * (C (v i)*X + C (u i))) :
    ∀ j : ℕ, ∃ P : F[X], P.natDegree ≤ 1 ∧ a * U.coeff j = b * P := by
  classical
  obtain ⟨S,hST,hS⟩ := exists_subset_card_eq (show D+1 ≤ T.card by omega)
  let f := Lagrange.interpolate S dom u
  let g := Lagrange.interpolate S dom v
  let W : (F[X])[X] := C (X : F[X]) * g.map C + f.map C
  have hbound (row : I → F) : (Lagrange.interpolate S dom row).natDegree ≤ D := by
    by_cases hzero : Lagrange.interpolate S dom row = 0
    · simp [hzero]
    · have hl := (natDegree_lt_iff_degree_lt hzero).mpr
          (Lagrange.degree_interpolate_lt row dom.injective.injOn)
      omega
  have hw : W.natDegree ≤ D := natDegree_add_le_of_degree_le
    ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans (hbound v)))
    (natDegree_map_le.trans (hbound u))
  have eq : C a * U = C b * W := by
    apply eq_of_degrees_lt_of_eval_index_eq S (C_injective.comp dom.injective).injOn
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast
        ((natDegree_C_mul_le a U).trans hD).trans_lt (by omega : D < S.card))
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast
        ((natDegree_C_mul_le b W).trans hw).trans_lt (by omega : D < S.card))
    · intro i hi
      have hf : f.eval (dom i) = u i := Lagrange.eval_interpolate_at_node _ dom.injective.injOn hi
      have hg : g.eval (dom i) = v i := Lagrange.eval_interpolate_at_node _ dom.injective.injOn hi
      simpa only [W,Function.comp_apply,eval_mul,eval_C,eval_add,eval_map_apply,hf,hg,mul_comm (C (v i)) X]
        using hfit i (hST hi)
  intro j
  refine ⟨W.coeff j,?_,by simpa only [coeff_C_mul] using congrArg (fun H : (F[X])[X] => H.coeff j) eq⟩
  simp only [W,coeff_add,coeff_C_mul,coeff_map]
  apply natDegree_add_le_of_degree_le
  · rw [mul_comm]
    exact (natDegree_C_mul_le _ _).trans (by simp)
  · simp

open Classical in
private theorem coeffs_of_long_class [DecidableEq F] (dom : I ↪ F) (U : (F[X])[X]) {D : ℕ} (hD : U.natDegree ≤ D)
    (w : I → F[X]) (hw : ∀ i, (w i).natDegree ≤ 1) (i : I)
    (hbig : D < ((univ : Finset I).filter fun j =>
      w i * U.eval (C (dom j)) = w j * U.eval (C (dom i))).card) :
    ∀ j : ℕ, ∃ P : F[X], P.natDegree ≤ 1 ∧ w i * U.coeff j = U.eval (C (dom i)) * P := by
  classical
  exact affine_coefficients dom U hD _ hbig (fun j => (w j).coeff 0)
    (fun j => (w j).coeff 1) (w i) (U.eval (C (dom i))) (by
      intro j hj
      have h := (mem_filter.mp hj).2
      rw [← eq_X_add_C_of_natDegree_le_one (hw j)]
      simpa only [mul_comm (w j)] using h)

open Classical in
/-- A gap of two between challenge degrees prevents a rational rescaling of
the entire projective family into an affine received line. -/
theorem class_card_le [DecidableEq F] (dom : I ↪ F) (U : (F[X])[X]) {D l h : ℕ} (hD : U.natDegree ≤ D)
    (hl : U.coeff l ≠ 0) (hh : U.coeff h ≠ 0)
    (hgap : (U.coeff l).natDegree + 1 < (U.coeff h).natDegree)
    (w : I → F[X]) (hw : ∀ i, (w i).natDegree ≤ 1) (i : I)
    (hi : w i ≠ 0) (hu : U.eval (C (dom i)) ≠ 0) :
    ((univ : Finset I).filter fun j =>
      w i * U.eval (C (dom j)) = w j * U.eval (C (dom i))).card ≤ D := by
  classical
  by_contra! hbig
  have steps := coeffs_of_long_class dom U hD w hw i hbig
  obtain ⟨P,hP,ep⟩ := steps l
  obtain ⟨Q,hQ,eq⟩ := steps h
  have hp : P ≠ 0 := fun hz => (mul_ne_zero hi hl) (by simpa [hz] using ep)
  have hq : Q ≠ 0 := fun hz => (mul_ne_zero hi hh) (by simpa [hz] using eq)
  have e₁ := congrArg Polynomial.natDegree ep
  have e₂ := congrArg Polynomial.natDegree eq
  rw [natDegree_mul hi hl, natDegree_mul hu hp] at e₁
  rw [natDegree_mul hi hh, natDegree_mul hu hq] at e₂
  omega

open Classical in
/-- A primitive polynomial direction of projective parameter degree at least
two satisfies the class cap for every affine received row on every domain. -/
theorem class_card_le_of_primitive [DecidableEq F] (dom : I ↪ F) (U : (F[X])[X]) {D j : ℕ}
    (hD : U.natDegree ≤ D) (hprim : U.IsPrimitive) (hhigh : 2 ≤ (U.coeff j).natDegree)
    (w : I → F[X]) (hw : ∀ i, (w i).natDegree ≤ 1) (i : I)
    (hi : w i ≠ 0) (hu : U.eval (C (dom i)) ≠ 0) :
    ((univ : Finset I).filter fun y =>
      w i * U.eval (C (dom y)) = w y * U.eval (C (dom i))).card ≤ D := by
  classical
  by_contra! hbig
  let b := U.eval (C (dom i))
  have hb : b ≠ 0 := hu
  have steps := coeffs_of_long_class dom U hD w hw i hbig
  have hdvd : C b ∣ C (w i) * U := by
    apply (C_dvd_iff_dvd_coeff ..).mpr
    intro t
    obtain ⟨Q,_,hQ⟩ := steps t
    exact ⟨Q, by simpa only [coeff_C_mul] using hQ⟩
  have hab := dvd_content_iff_C_dvd.mpr hdvd
  have had : b ∣ w i := by
    have e := associated_content_C_mul (w i) U
    rw [hprim.content_eq_one,mul_one] at e
    exact hab.trans e.dvd
  obtain ⟨v,hv⟩ := had
  have hdeg : (U.coeff j) ≠ 0 := by intro h; simp [h] at hhigh
  have hvn : v ≠ 0 := fun h => hi (by simp [hv,h])
  obtain ⟨P,hP,ep⟩ := steps j
  have eq : v * U.coeff j = P := mul_left_cancel₀ hb (by
    simpa only [hv,mul_assoc] using ep)
  rw [← eq,natDegree_mul hvn hdeg] at hP
  omega

/-- Specializing the site coordinate preserves the maximum challenge degree. -/
theorem site_height (U : (F[X])[X]) (s : ℕ) (height : ∀ j, (U.coeff j).natDegree ≤ s) (x : F) :
    (U.eval (C x)).natDegree ≤ s := by
  rw [eval_eq_sum_range]
  apply natDegree_sum_le_of_forall_le
  intro j _
  rw [← map_pow, mul_comm]
  exact (natDegree_C_mul_le _ _).trans (height j)

open ProjectiveDirectionIncidence

open Classical in
/-- Labels of all actually nonjoint witnesses carried by a fixed primitive
nonlinear polynomial direction, with an arbitrary affine translation of codewords. -/
theorem primitive_bad_count {I F : Type} [Fintype I] [DecidableEq I] [Field F] [DecidableEq F] [Fintype F]
    (dom : I ↪ F) (U : (F[X])[X]) (u₀ u₁ : I → F) (q₀ q₁ : F[X]) {D A s j : ℕ}
    (hDA : D < A) (hq₀ : q₀.natDegree ≤ D) (hq₁ : q₁.natDegree ≤ D)
    (hD : U.natDegree ≤ D) (hprim : U.IsPrimitive) (hnl : 2 ≤ (U.coeff j).natDegree)
    (height : ∀ j, (U.coeff j).natDegree ≤ s) :
    ((univ : Finset F).filter fun z => ∃ (S : Finset I) (P : F[X]) (a : F),
      A ≤ S.card ∧ P.natDegree ≤ D ∧ (∀ i ∈ S, P.eval (dom i) = u₀ i+z*u₁ i) ∧
      ¬ pairJointAgreesOn (ReedSolomon.code dom (D+1) : Set (I → F)) S u₀ u₁ ∧
      ∀ i ∈ S, (P-(q₀+C z*q₁)).eval (dom i) = a*(U.eval (C (dom i))).eval z).card ≤
      Fintype.card I-A+1+Fintype.card I*(Fintype.card I-1)*(s+1)/(A-D)^2 := by
  classical
  let w := residualRow dom u₀ u₁ q₀ q₁
  have hw (i : I) : (w i).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · rw [mul_comm]
      exact (natDegree_C_mul_le _ _).trans (by simp)
  exact captured_count dom u₀ u₁ q₀ q₁ (fun i => U.eval (C (dom i))) D A s hDA hq₀ hq₁
    (fun i => site_height U s height (dom i)) (class_card_le_of_primitive dom U hD hprim hnl w hw)
    _ (fun _ hz => (mem_filter.mp hz).2)

end ProximityGap.ProjectiveDirectionRigidity

#print axioms ProximityGap.ProjectiveDirectionRigidity.affine_coefficients
#print axioms ProximityGap.ProjectiveDirectionRigidity.class_card_le

#print axioms ProximityGap.ProjectiveDirectionRigidity.class_card_le_of_primitive

#print axioms ProximityGap.ProjectiveDirectionRigidity.primitive_bad_count
