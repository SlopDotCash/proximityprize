/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AffineHeadBudget
import ArkLib.Research.ProximityGap.Frontier.ProjectiveDirectionRigidity

/-! # Rich folds on a primitive projective direction of challenge degree at most one

A large symbolic proportionality class gives a polynomial multiplier of
degree at most one. Its product with the entire direction is affine in the
challenge and defines a pair of codewords. A bad witness on that head must
contain an accidental agreement. -/
set_option autoImplicit false
open Finset Polynomial
namespace ProximityGap.AffinePrimitiveDirection
open AffineHeadBudget ProjectiveDirectionIncidence ProjectiveDirectionRigidity
variable {I F : Type*} [Fintype I] [DecidableEq I] [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Primitive content rules out identically zero specializations at every
field element, including possible zeros of individual coordinate rows. -/
theorem specialization_ne_zero (U : (F[X])[X]) (hU : U.IsPrimitive) (z : F) :
    U.map (evalRingHom z) ≠ 0 := by
  intro h
  apply not_isUnit_X_sub_C z (isPrimitive_iff_isUnit_of_C_dvd.mp hU _ _)
  apply (C_dvd_iff_dvd_coeff ..).mpr
  intro j
  apply dvd_iff_isRoot.mpr
  simpa [IsRoot] using congrArg (fun p : F[X] => p.coeff j) h

omit [DecidableEq F] in
private theorem swap_eval (U : (F[X])[X]) (z x : F) :
    (U.eval (C x)).eval z = (U.map (evalRingHom z)).eval x := by
  simpa using (eval_map_apply (p:=U) (evalRingHom z) (C x)).symm

omit [DecidableEq I] in
/-- Over a long class the symbolic quotient is a polynomial scalar. After
multiplication all coefficients of the direction have degree at most one. -/
theorem long_class (dom : I ↪ F) (U : (F[X])[X]) {D : ℕ} (hD : U.natDegree ≤ D)
    (hU : U.IsPrimitive) (w : I → F[X]) (hw : ∀ i, (w i).natDegree ≤ 1) (i : I)
    (hi : U.eval (C (dom i)) ≠ 0)
    (hbig : D < (univ.filter fun j => w i*U.eval (C (dom j)) = w j*U.eval (C (dom i))).card) :
    let r := w i/U.eval (C (dom i))
    w i = r*U.eval (C (dom i)) ∧ r.natDegree ≤ 1 ∧ ∀ j, (r*U.coeff j).natDegree ≤ 1 := by
  classical
  let v := U.eval (C (dom i))
  have hv : v ≠ 0 := hi
  have steps := affine_coefficients dom U hD _ hbig (fun j => (w j).coeff 0)
    (fun j => (w j).coeff 1) (w i) v (by
      intro j hj
      have h := (mem_filter.mp hj).2
      rw [← eq_X_add_C_of_natDegree_le_one (hw j)]
      simpa [v,mul_comm (w j)] using h)
  have hc : C v ∣ C (w i)*U := (C_dvd_iff_dvd_coeff ..).mpr fun j => by
    obtain ⟨p,_,he⟩ := steps j
    exact ⟨p,by simpa only [coeff_C_mul] using he⟩
  have hassoc := associated_content_C_mul (w i) U
  rw [hU.content_eq_one,mul_one] at hassoc
  have hdiv : v ∣ w i := (dvd_content_iff_C_dvd.mpr hc).trans hassoc.dvd
  obtain ⟨r,hr⟩ := hdiv
  have he : w i/v = r := by rw [hr,mul_comm,mul_div_cancel_right₀ _ hv]
  change w i = w i/v*v ∧ (w i/v).natDegree ≤ 1 ∧ ∀ j, (w i/v*U.coeff j).natDegree ≤ 1
  rw [he]
  refine ⟨hr.trans (mul_comm ..),?_,?_⟩
  · by_cases hz : r = 0
    · simp [hz]
    · have h := hw i
      rw [hr,natDegree_mul hv hz] at h
      omega
  · intro j
    obtain ⟨p,hp,hep⟩ := steps j
    have e : r*U.coeff j = p := mul_left_cancel₀ hv (by rwa [hr,mul_assoc] at hep)
    rwa [e]

/-- Arithmetic data of the counting argument: the common zero sites,
occupied sites outside them, uncovered sites and number of heavy heads. -/
def Budget (n D A T b : ℕ) : Prop :=
  ∃ J K E H : ℕ, J ≤ D ∧ K+E+J = n ∧ H*(T+1-J) ≤ K ∧
    b ≤ n*(n-1)*2/(A-T)^2 +
      (if H = 0 then 0 else if H = 1 then n-T-1 else K+E*H+H^2)

/-- Numerical certificate for an arbitrary set of distinct challenge labels.
The last premise excludes a symbolic fit on a single affine codeword head. -/
theorem budget_of_direction (dom : I ↪ F) (U : (F[X])[X]) (w : I → F[X])
    (D A T : ℕ) (hD : U.natDegree ≤ D) (hU : U.IsPrimitive)
    (hu : ∀ j, (U.coeff j).natDegree ≤ 1) (hw : ∀ i, (w i).natDegree ≤ 1)
    (hDT : D ≤ T) (hTA : T < A) (B : Finset F) (S : F → Finset I) (a : F → F)
    (hs : ∀ z ∈ B, A ≤ (S z).card)
    (hf : ∀ z ∈ B, ∀ i ∈ S z, (w i).eval z = a z*(U.eval (C (dom i))).eval z)
    (hbad : ∀ z ∈ B, ∀ r : F[X], (∀ j, (r*U.coeff j).natDegree ≤ 1) →
      ∃ i ∈ S z, w i ≠ r*U.eval (C (dom i))) :
    Budget (Fintype.card I) D A T B.card := by
  classical
  let V := fun i : I => U.eval (C (dom i))
  let cl := fun i : I => univ.filter fun j => w i*V j = w j*V i
  let eligible := univ.filter fun i => V i ≠ 0 ∧ T < (cl i).card
  let ratio := fun i => w i/V i
  let H := eligible.image ratio
  have he (i : I) (hi : i ∈ eligible) : w i = ratio i*V i ∧ (ratio i).natDegree ≤ 1 ∧
      ∀ j, (ratio i*U.coeff j).natDegree ≤ 1 := by
    obtain ⟨hv,hbig⟩ := (mem_filter.mp hi).2
    exact long_class dom U hD hU w hw i hv (hDT.trans_lt hbig)
  have hlong (r : F[X]) (hr : r ∈ H) : T < (core w V r).card := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hr
    have hh := (mem_filter.mp hi).2
    apply hh.2.trans_le (card_le_card _)
    intro j hj
    apply mem_filter.mpr
    refine ⟨mem_univ _,mul_right_cancel₀ hh.1 ?_⟩
    have H := (mem_filter.mp hj).2
    rw [(he i hi).1] at H
    linear_combination -H
  have hproducts (r : F[X]) (hr : r ∈ H) : r.natDegree ≤ 1 ∧ ∀ j, (r*U.coeff j).natDegree ≤ 1 := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hr
    exact (he i hi).2
  have hV (i : I) : (V i).natDegree ≤ 1 := site_height U 1 hu _
  let Uheavy := B.filter fun z => ∃ r ∈ H, r.eval z = a z
  let L := B.filter fun z => ¬∃ r ∈ H, r.eval z = a z
  have hlight : L.card*(A-T)^2 ≤ Fintype.card I*(Fintype.card I-1)*2 := by
    let good (z : F) := (S z).filter fun i => (V i).eval z ≠ 0
    apply count_with_anchors w V L S good a T A 1 hw hV
      (fun z hz => hs z (mem_filter.mp hz).1)
      (fun z hz => hf z (mem_filter.mp hz).1)
    · intro z hz
      have hsp := specialization_ne_zero U hU z
      have hanc := anchors_of_nonzero dom _ (S z) A D (hs z (mem_filter.mp hz).1) hsp
        (natDegree_map_le.trans hD)
      simpa only [good,V,swap_eval] using (Nat.sub_le_sub_left hDT A).trans hanc
    · exact fun _ _ => filter_subset ..
    · intro z hz i hi
      by_contra! hbig
      have hvi := (mem_filter.mp hi).2
      have hh : i ∈ eligible := mem_filter.mpr ⟨mem_univ _,fun h => hvi (by simp [h]),hbig⟩
      apply (mem_filter.mp hz).2
      refine ⟨ratio i,mem_image_of_mem _ hh,mul_right_cancel₀ hvi ?_⟩
      have hfit := hf z (mem_filter.mp hz).1 i (mem_filter.mp hi).1
      rw [(he i hh).1,eval_mul] at hfit
      exact hfit
  have hh (z : F) (hz : z ∈ Uheavy) := (mem_filter.mp hz).2
  choose! r hr her using hh
  obtain ⟨K,E,ht,hk,hcount,hzero,hone⟩ := heavy_budget w V H Uheavy r S T hlong hw hV
    (fun p hp => ⟨(hproducts p hp).1,fun i => by
      simpa [V] using site_height (C p*U) 1 (fun j => by simpa using (hproducts p hp).2 j) (dom i)⟩)
    hr (fun z hz i hi => by simpa [her z hz] using hf z (mem_filter.mp hz).1 i hi)
    (fun z hz => hbad z (mem_filter.mp hz).1 (r z) (hproducts _ (hr z hz)).2)
  have hJ : (common w V).card ≤ D := by
    have hd := specialization_ne_zero U hU 0
    rw [← card_image_of_injective (common w V) dom.injective]
    apply (card_le_degree_of_subset_roots (p:=U.map (evalRingHom 0)) _).trans (natDegree_map_le.trans hD)
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp (show x ∈ (common w V).image dom from hx)
    have hv := (mem_filter.mp hi).2.2
    apply (mem_roots hd).mpr
    change ((U.map (evalRingHom 0)).eval (dom i)) = 0
    rw [← swap_eval]
    change (V i).eval 0 = 0
    simp [hv]
  have hu := (Nat.le_div_iff_mul_le (pow_pos (Nat.sub_pos_of_lt hTA) 2)).mpr hlight
  have hcard : Uheavy.card+L.card = B.card := card_filter_add_card_filter_not ..
  refine ⟨_,K,E,H.card,hJ,ht,hk,?_⟩
  split_ifs with h0 h1
  · have := hzero h0; omega
  · have := hone h1; omega
  · omega

section MCA
open Classical

/-- Distinct labels having at least one nonjoint support explained by the
given projective direction satisfy the same budget for every received pair. -/
theorem captured_budget {I F : Type} [Fintype I] [DecidableEq I] [Field F] [DecidableEq F]
    (dom : I ↪ F) (u₀ u₁ : I → F) (q₀ q₁ : F[X]) (U : (F[X])[X]) (D A T : ℕ)
    (hD : U.natDegree ≤ D) (hU : U.IsPrimitive) (hu : ∀ j, (U.coeff j).natDegree ≤ 1)
    (h₀ : q₀.natDegree ≤ D) (h₁ : q₁.natDegree ≤ D) (hDT : D ≤ T) (hTA : T < A)
    (B : Finset F) (hwitness : ∀ z ∈ B, ∃ (S : Finset I) (a : F), A ≤ S.card ∧
      (∀ i ∈ S, (residualRow dom u₀ u₁ q₀ q₁ i).eval z = a*(U.eval (C (dom i))).eval z) ∧
      ¬ pairJointAgreesOn (ReedSolomon.code dom (D+1) : Set (I → F)) S u₀ u₁) :
    Budget (Fintype.card I) D A T B.card := by
  classical
  let w := residualRow dom u₀ u₁ q₀ q₁
  have hw (i : I) : (w i).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact natDegree_mul_le.trans (by simp)
  choose! S a hs hf hind using hwitness
  apply budget_of_direction dom U w D A T hD hU hu hw hDT hTA B S a hs hf
  intro z hz r _
  by_contra! hall
  apply hind z hz
  let W := C r*U
  let p₀ := W.map (evalRingHom 0)
  let p₁ := W.map (evalRingHom 1)
  have hW : W.natDegree ≤ D := (natDegree_C_mul_le ..).trans hD
  have hP₀ : p₀.natDegree ≤ D := natDegree_map_le.trans hW
  have hP₁ : p₁.natDegree ≤ D := natDegree_map_le.trans hW
  have hd₁ := (natDegree_sub_le p₁ p₀).trans (max_le hP₁ hP₀)
  refine ⟨ReedSolomon.evalOnPoints dom (q₀+p₀),ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt
      ((natDegree_add_le ..).trans_lt (Nat.lt_succ_of_le (max_le h₀ hP₀))),
    ReedSolomon.evalOnPoints dom (q₁+(p₁-p₀)),ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt
      ((natDegree_add_le ..).trans_lt (Nat.lt_succ_of_le (max_le h₁ hd₁))),?_⟩
  intro i hi
  have hh (y : F) : (w i).eval y = (W.map (evalRingHom y)).eval (dom i) := by
    rw [← swap_eval,hall i hi]
    simp [W]
  have ha := hh 0
  have hb := hh 1
  simp only [w,residualRow,eval_add,eval_mul,eval_X,eval_C,zero_mul,one_mul,add_zero] at ha hb
  change (q₀+p₀).eval (dom i) = u₀ i ∧ (q₁+(p₁-p₀)).eval (dom i) = u₁ i
  simp only [eval_add,eval_sub,p₀,p₁]
  constructor
  · linear_combination -ha
  · linear_combination ha-hb

/-- Conditional on coverage by the single direction, the bound applies to
the full local MCA event with its joint-agreement requirement. -/
theorem mca_budget {I F : Type} [Fintype I] [DecidableEq I] [Field F] [DecidableEq F] [Fintype F]
    (dom : I ↪ F) (u₀ u₁ : I → F) (q₀ q₁ : F[X]) (U : (F[X])[X]) (D A T : ℕ) (δ : NNReal)
    (hD : U.natDegree ≤ D) (hU : U.IsPrimitive) (hu : ∀ j, (U.coeff j).natDegree ≤ 1)
    (h₀ : q₀.natDegree ≤ D) (h₁ : q₁.natDegree ≤ D) (hDT : D ≤ T) (hTA : T < A)
    (hr : ∀ S : Finset I, (1-δ)*(Fintype.card I : NNReal) ≤ S.card → A ≤ S.card)
    (hcurve : ∀ (z : F) (P : F[X]) (S : Finset I), P.natDegree ≤ D → A ≤ S.card →
      (∀ i ∈ S, P.eval (dom i) = u₀ i + z*u₁ i) →
      ¬ pairJointAgreesOn (ReedSolomon.code dom (D+1) : Set (I → F)) S u₀ u₁ →
      ∃ a : F, ∀ i ∈ S, (P-(q₀+C z*q₁)).eval (dom i) = a*(U.eval (C (dom i))).eval z) :
    Budget (Fintype.card I) D A T
      (univ.filter (mcaEvent (F:=F) (ReedSolomon.code dom (D+1) : Set (I → F)) δ u₀ u₁)).card := by
  apply captured_budget dom u₀ u₁ q₀ q₁ U D A T hD hU hu h₀ h₁ hDT hTA
  intro z hz
  obtain ⟨S,hs,⟨c,hc,hfit⟩,hind⟩ := (mem_filter.mp hz).2
  obtain ⟨P,hp,hP⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hc
  have hf (i : I) (hi : i ∈ S) : P.eval (dom i) = u₀ i+z*u₁ i := (hP i).trans (hfit i hi)
  obtain ⟨a,ha⟩ := hcurve z P S (by omega) (hr S hs) hf hind
  refine ⟨S,a,hr S hs,?_,hind⟩
  intro i hi
  have he := ha i hi
  simp only [residualRow,eval_sub,eval_add,eval_mul,eval_X,eval_C,hf i hi] at he ⊢
  linear_combination he
end MCA

/-- Uniform numerical bounds for all four affine projective directions at the
production length. The first fits the budget n, and all four fit the budget 2n. -/
theorem production_caps :
    let good := fun (k A b : ℕ) => ∀ M, Budget (2^30) (k-1) A (A-2^20) M → M ≤ b
    good (2^29) (89*2^23) 658505729 ∧ good (2^28) (61*2^23) 1128267777 ∧
      good (2^27) (42*2^23) 1518338047 ∧ good (2^26) (29*2^23) 1971322879 := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro M h <;> obtain ⟨J,K,E,H,hJ,ht,hk,hb⟩ := h
  all_goals
    norm_num at hJ ht hk hb
    have hcut {x : ℕ} (h : H*x ≤ K) (h7 : 7 ≤ H) : 7*x ≤ K :=
      (Nat.mul_le_mul_right x h7).trans h
    have hh : H ≤ 6 := by
      by_contra! he
      have := hcut hk he
      omega
    interval_cases H <;> norm_num at hk hb <;> omega

#print axioms production_caps
#print axioms captured_budget
#print axioms mca_budget
#print axioms budget_of_direction
end ProximityGap.AffinePrimitiveDirection
