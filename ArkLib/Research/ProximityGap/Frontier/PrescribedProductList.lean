/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Combinatorics.Pigeonhole

/-! # A common-product list one agreement above the Reed–Solomon dimension

Group monic locators by their constant term and their coefficients above degree
`k`. Dividing the difference of any two locators in the group by `X` gives a
polynomial of degree below `k`. The constant term is determined by the subset
product, whose number of possibilities is bounded by the subgroup order.
-/

set_option autoImplicit false
namespace ProximityGap.PrescribedProductList
open Finset Polynomial
variable {I F : Type*} [Fintype I] [Field F]
private noncomputable def locator (D : I ↪ F) (T : Finset I) : F[X] :=
  ∏ i ∈ T, (X - C (D i))

/-- Within a fiber of the key, the constant locator coefficient and all coefficients
strictly between the message dimension and the locator degree are fixed. -/
private theorem exceeds_of_keys {K : Type*} [Fintype K]
    (D : I ↪ F) (hne : ∀ i, D i ≠ 0) (key : Finset I → K)
    {k t B : ℕ} (hk : 0 < k)
    (hc : ∀ S T : Finset I, S.card = t → T.card = t → key S = key T →
      (locator D S).eval 0 = (locator D T).eval 0 ∧
      ∀ j, k < j → j < t → (locator D S).coeff j = (locator D T).coeff j)
    (hB : Fintype.card K * B < (Fintype.card I).choose t) :
    (B : ℕ∞) < Code.Lambda (ReedSolomon.code D k : Set (I → F))
      (((Fintype.card I - t : ℕ) : ℝ) / (Fintype.card I : ℝ)) := by
  classical
  let sf := (univ : Finset I).powersetCard t
  obtain ⟨v, _, hmany⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := sf) (t := (univ : Finset K)) (f := key)
    (fun _ _ => Finset.mem_univ _) (show univ.card * B < sf.card by simpa [sf] using hB)
  let members := sf.filter (fun T => key T = v)
  obtain ⟨S,hS⟩ : members.Nonempty := card_pos.mp (Nat.zero_le B |>.trans_lt hmany)
  have hcard {T : Finset I} (h : T ∈ members) : T.card = t :=
    (mem_powersetCard.mp (mem_filter.mp h).1).2
  let P := locator D S
  let delta (T : Finset I) := P - locator D T
  let center (i : I) := P.eval (D i) / D i
  let word (T : Finset I) (i : I) := (delta T).divX.eval (D i)
  have same {T : Finset I} (hT : T ∈ members) :=
    hc S T (hcard hS) (hcard hT) ((mem_filter.mp hS).2.trans (mem_filter.mp hT).2.symm)
  have hd {T : Finset I} (hT : T ∈ members) : (delta T).divX.natDegree < k := by
    rw [natDegree_divX_eq_natDegree_tsub_one]
    have bound : (delta T).natDegree ≤ k := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro j hj
      rw [show (delta T).coeff j = (locator D S).coeff j - (locator D T).coeff j by
        simp [delta,P], sub_eq_zero]
      have ds : (locator D S).natDegree = t := by simp [locator,hcard hS]
      have dt : (locator D T).natDegree = t := by simp [locator,hcard hT]
      rcases lt_trichotomy j t with hjt | rfl | htj
      · exact (same hT).2 j hj hjt
      · have ms : (locator D S).Monic := monic_prod_X_sub_C _ _
        have mt : (locator D T).Monic := monic_prod_X_sub_C _ _
        exact (ds ▸ ms.coeff_natDegree).trans (dt ▸ mt.coeff_natDegree).symm
      · rw [coeff_eq_zero_of_natDegree_lt (ds ▸ htj), coeff_eq_zero_of_natDegree_lt (dt ▸ htj)]
    omega
  have hag {T : Finset I} (hT : T ∈ members) (i : I) : word T i = center i ↔ i ∈ T := by
    have he : (locator D T).eval (D i) = 0 ↔ i ∈ T := by
      simp [locator, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, D.injective.eq_iff]
    have hzero : (delta T).coeff 0 = 0 := by
      simp [delta,P,coeff_zero_eq_eval_zero, (same hT).1]
    have h := congrArg (eval (D i)) (divX_mul_X_add (delta T))
    rw [hzero, C_0, add_zero] at h
    simp only [eval_mul, eval_X, delta, eval_sub] at h
    dsimp [word,center,delta]
    rw [eq_div_iff (hne _), h, sub_eq_self, he]
  have hi : Set.InjOn word (↑members : Set (Finset I)) := by
    intro T hT S hS he
    ext i
    have h' := congrFun he i
    exact (hag hT i).symm.trans (h' ▸ hag hS i)
  have hmem : (↑(members.image word) : Set (I → F)) ⊆
      Code.closeCodewordsRel (ReedSolomon.code D k : Set (I → F)) center
      (((Fintype.card I - t : ℕ) : ℝ)/(Fintype.card I : ℝ)) := by
    rw [← Code.closeCodewords_eq_closeCodewordsRel]
    intro u hu
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hu
    refine ⟨ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval _
      (hd hT) (fun _ => rfl), ?_⟩
    rw [Code.mem_hammingBall_iff]
    have he : univ.filter (fun i => center i = word T i) = T := by
      ext i
      simp only [mem_filter, mem_univ, true_and]
      exact eq_comm.trans (hag hT i)
    have hh := card_filter_add_card_filter_not (s := (univ : Finset I))
      (p := fun i => center i = word T i)
    rw [he, hcard hT, card_univ] at hh
    change (univ.filter fun i => center i ≠ word T i).card ≤ _
    exact Nat.le_of_eq (Nat.eq_sub_of_add_eq' hh)
  have bound := Code.encard_le_Lambda_of_subset_closeCodewordsRel hmem
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injOn hi] at bound
  exact (show (B : ℕ∞) < members.card by exact_mod_cast hmany).trans_le bound

omit [Fintype I] in
private theorem eval_zero_eq_of_prod_eq (D : I ↪ F) (H : Subgroup Fˣ)
    (z : I → H) (hz : ∀ i, D i = ((z i : Fˣ) : F)) (S T : Finset I)
    (hsize : S.card = T.card) (hp : ∏ i ∈ S, z i = ∏ i ∈ T, z i) :
    (locator D S).eval 0 = (locator D T).eval 0 := by
  have h := congrArg ((Units.coeHom F).comp H.subtype) hp
  rw [map_prod, map_prod] at h
  simpa [locator, eval_prod, Finset.prod_neg, hsize, hz] using
    congrArg (fun u : F => (-1)^T.card * u) h

/-- Any budget smaller than the average prescribed-product fiber fails at k+1 agreements. -/
theorem exceeds_budget (D : I ↪ F) (H : Subgroup Fˣ) [Fintype H]
    (z : I → H) (hz : ∀ i, D i = ((z i : Fˣ) : F)) {k B : ℕ} (hk : 0 < k)
    (hB : Fintype.card H * B < (Fintype.card I).choose (k+1)) :
    (B : ℕ∞) < Code.Lambda (ReedSolomon.code D k : Set (I → F))
      (((Fintype.card I - (k+1) : ℕ) : ℝ) / (Fintype.card I : ℝ)) :=
  exceeds_of_keys D (fun i => hz i ▸ Units.ne_zero _) (fun T => ∏ i ∈ T, z i) hk
    (fun S T hS hT h => ⟨eval_zero_eq_of_prod_eq D H z hz S T (hS.trans hT.symm) h,
      fun j hj hj' => False.elim (by omega)⟩) hB

/-- Fix the constant coefficient via the subgroup product and the other high locator
coefficients via the field. This saves a factor |F|/|H| in the raw coefficient pigeonhole. -/
theorem exceeds_budget_deeper [Fintype F] (D : I ↪ F) (H : Subgroup Fˣ) [Fintype H]
    (z : I → H) (hz : ∀ i, D i = ((z i : Fˣ) : F)) (a : ℕ) {k B : ℕ} (hk : 0 < k)
    (hB : (Fintype.card H * Fintype.card F ^ a) * B < (Fintype.card I).choose (k+1+a)) :
    (B : ℕ∞) < Code.Lambda (ReedSolomon.code D k : Set (I → F))
      (((Fintype.card I - (k+1+a) : ℕ) : ℝ) / (Fintype.card I : ℝ)) := by
  classical
  let key (T : Finset I) : H × (Fin a → F) :=
    (∏ i ∈ T, z i, fun j => (locator D T).coeff (k+1+j.val))
  apply exceeds_of_keys D (fun i => hz i ▸ Units.ne_zero _) key hk
  · intro S T hS hT he
    refine ⟨eval_zero_eq_of_prod_eq D H z hz S T (hS.trans hT.symm) (congrArg Prod.fst he), ?_⟩
    intro j hj hj'
    have h := congrFun (congrArg Prod.snd he) (⟨j-(k+1), by omega⟩ : Fin a)
    simpa only [key, show k+1+(j-(k+1)) = j by omega] using h
  · simpa [Fintype.card_prod, Fintype.card_fun] using hB

#print axioms exceeds_budget
#print axioms exceeds_budget_deeper
end ProximityGap.PrescribedProductList
