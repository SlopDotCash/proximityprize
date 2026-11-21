/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothQuinticSeventeen

/-! # Nineteen bad labels on the order-sixteen subgroup of every proper extension of the field of order seventeen

Four degree-six heads each agree with an explicit word at ten of the fifteen
ordinary sites. The ordinary scalar labels lie in the prime field. Translating
at the remaining site puts four more labels outside the prime field.
-/

set_option autoImplicit false
open Finset Polynomial ProximityGap
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.SmoothSeventeenExtension

open SmoothQuinticSeventeen (F sites card_sites)
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩
local instance : AddCommGroup F := (inferInstance : Field F).toDivisionRing.toAddCommGroup

private def head {A : Type*} [Ring A] (i : Fin 4) (x : A) : A :=
  match i with
  | 0 => 0
  | 1 => 12 + x*(13 + x*(15 + x*(6 + x*(15 + x*(4 + x)))))
  | 2 => 14 + x*(12 + x*(3 + x*(13 + x*(2 + x*(12 + x*2)))))
  | 3 => 9 + x*(5 + x*(14 + x*(2 + x*(4 + x*(8 + x*5)))))

private def center (x : F) : F :=
  match x.val with
  | 4 => 4
  | 6 => 16
  | 9 => 10
  | 13 => 1
  | 15 => 14
  | _ => 0

private def ordinary : Finset F := sites.erase 1
private def holeValues : Finset F := {0,15,7,13}
private def hole : sites := ⟨1, by decide⟩
private def fieldLabel (x : F) : F := -(x-1)⁻¹

private def core (i : Fin 4) : Finset sites :=
  univ.filter fun x => x.val ≠ 1 ∧ head i x.val = center x.val

set_option maxRecDepth 8192 in
private theorem finite_profile :
    (∀ i : Fin 4, (core i).card = 10) ∧
    (∀ x ∈ ordinary, ∃ i : Fin 4, head i x ≠ center x) ∧
    (∀ v ∈ holeValues, ∃ i : Fin 4, head i (1 : F) = v) := by decide

variable {K : Type} [Field K] (φ : F →+* K)

/-- The prescribed sixteen nonzero prime-field sites inside the extension. -/
def domain : sites ↪ K := ⟨fun x => φ x.val, φ.injective.comp Subtype.val_injective⟩

/-- The image in the extension is exactly the group of sixteenth roots of unity. -/
theorem domain_image [DecidableEq K] :
    univ.image (domain φ) = nthRootsFinset 16 (1 : K) := by
  apply eq_of_subset_of_card_le
  · intro u hu
    obtain ⟨x, _, rfl⟩ := mem_image.mp hu
    apply (mem_nthRootsFinset (by decide : 0 < 16) (1 : K)).mpr
    have hx : x.val ∈ nthRootsFinset 16 (1 : F) := SmoothQuinticSeventeen.sites_eq_roots ▸ x.property
    have hp := (mem_nthRootsFinset (by decide : 0 < 16) (1 : F)).mp hx
    change φ x.val ^ 16 = 1
    rw [← map_pow, hp, map_one]
  · rw [card_image_of_injective _ (domain φ).injective, card_univ, Fintype.card_coe, card_sites,
      nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (card_nthRoots 16 _)

/-- The first received row takes the extension element at the exceptional site. -/
def first (b : K) (x : sites) : K := if x.val = 1 then b else φ (center x.val)

/-- The second received row takes one at the exceptional site. -/
def second (x : sites) : K := if x.val = 1 then 1 else (φ x.val-1)*φ (center x.val)

private theorem head_map (i : Fin 4) (x : F) : head i (φ x) = φ (head i x) := by
  fin_cases i <;> simp [head] <;> norm_num [map_ofNat]

private theorem head_eval (i : Fin 4) (x : K) :
    (head i (Polynomial.X : K[X])).eval x = head i x := by
  fin_cases i <;> simp [head]

private theorem head_deg (i : Fin 4) : (head i (Polynomial.X : K[X])).natDegree ≤ 6 := by
  fin_cases i <;> simp only [head] <;> compute_degree!

private theorem event (b t : K) (x : sites) (i : Fin 4)
    (hx : x ∉ core i)
    (fresh : head i (φ x.val) + t*((φ x.val-1)*head i (φ x.val)) = first φ b x + t*second φ x)
    (fail : ¬(head i (φ x.val) = first φ b x ∧ (φ x.val-1)*head i (φ x.val) = second φ x)) :
    mcaEvent (ReedSolomon.code (domain φ) 8 : Set (sites → K)) (5/16) (first φ b) (second φ) t := by
  let D := head i (Polynomial.X : K[X])
  let E := (Polynomial.X-1)*D
  have hD : D.natDegree ≤ 6 := head_deg i
  have hE : E.natDegree ≤ 7 := by
    have h := natDegree_mul_le (p := (Polynomial.X-1 : K[X])) (q := D)
    have h' : (Polynomial.X-1 : K[X]).natDegree ≤ 1 := by compute_degree!
    dsimp only [E]
    omega
  have dval (y : sites) : D.eval (domain φ y) = head i (φ y.val) := head_eval i _
  have eval (y : sites) : E.eval (domain φ y) = (φ y.val-1)*head i (φ y.val) := by
    simp only [E, eval_mul, eval_sub, eval_X, eval_one, dval]
    rfl
  have pair (y : sites) (hy : y ∈ core i) :
      D.eval (domain φ y) = first φ b y ∧ E.eval (domain φ y) = second φ y := by
    obtain ⟨hne, heq⟩ := (mem_filter.mp hy).2
    simp [dval, eval, head_map φ i, heq, first, second, hne]
  have mixed : (D+C t*E).natDegree < 8 := by
    have h₁ := natDegree_mul_le (p := C t) (q := E)
    simp only [natDegree_C,zero_add] at h₁
    have h₂ := natDegree_add_le D (C t*E)
    omega
  let S := insert x (core i)
  have size : S.card = 11 := by simp [S, hx, finite_profile.1]
  refine ⟨S, ?_, ⟨fun y => (D+C t*E).eval (domain φ y),
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval _ mixed (fun _ => rfl), ?_⟩, ?_⟩
  · rw [Fintype.card_coe,card_sites,size,Nat.cast_ofNat, Nat.cast_ofNat, tsub_mul, one_mul,
      div_mul_cancel₀ _ (by norm_num), show (16 : ℝ≥0)-5=11 from tsub_eq_of_eq_add (by norm_num)]
  · intro y hy
    obtain rfl | hy := mem_insert.mp hy
    · simpa only [eval_add,eval_mul,eval_C,dval,eval,smul_eq_mul] using fresh
    · simp only [eval_add,eval_mul,eval_C,(pair y hy).1,(pair y hy).2,smul_eq_mul]
  · rintro ⟨u,hu,v,hv,hj⟩
    obtain ⟨P,hP,hpu⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hu
    obtain ⟨Q,hQ,hqv⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hv
    have pin (A B : K[X]) (ha : A.natDegree < 8) (hb : B.natDegree < 8)
        (h : ∀ y ∈ core i, A.eval (domain φ y) = B.eval (domain φ y)) : A = B := by
      apply eq_of_natDegree_lt_card_of_eval_eq A B (f := fun y : core i => domain φ y.val)
        ((domain φ).injective.comp Subtype.val_injective) (fun y => h _ y.property)
      rw [Fintype.card_coe, finite_profile.1 i]
      omega
    have pD : P = D := pin P D hP (by omega) fun y hy =>
      (hpu y).trans (((hj y (mem_insert_of_mem hy)).1).trans (pair y hy).1.symm)
    have qE : Q = E := pin Q E hQ (by omega) fun y hy =>
      (hqv y).trans (((hj y (mem_insert_of_mem hy)).2).trans (pair y hy).2.symm)
    have h := hj x (mem_insert_self ..)
    exact fail ⟨(dval x).symm.trans (pD ▸ (hpu x).trans h.1),
      (eval x).symm.trans (qE ▸ (hqv x).trans h.2)⟩

private theorem ordinary_event (b : K) (x : F) (hx : x ∈ ordinary) :
    mcaEvent (ReedSolomon.code (domain φ) 8 : Set (sites → K)) (5/16)
      (first φ b) (second φ) (φ (fieldLabel x)) := by
  obtain ⟨hne, hmem⟩ := mem_erase.mp hx
  let y : sites := ⟨x,hmem⟩
  obtain ⟨i,hi⟩ := finite_profile.2.1 x hx
  apply event φ b _ y i
  · intro hy
    exact hi (mem_filter.mp hy).2.2
  · have hn : φ x - 1 ≠ 0 := sub_ne_zero.mpr fun h => hne (φ.injective (h.trans φ.map_one.symm))
    simp only [first, second, y, ite_eq_right hne, fieldLabel, map_neg, map_inv₀, map_sub, map_one]
    field_simp [hn]
    ring
  · intro h
    exact hi (φ.injective (by simpa [y,head_map φ i, first,hne] using h.1))

private theorem hole_event (b : K) (hb : b ∉ Set.range φ) (v : F) (hv : v ∈ holeValues) :
    mcaEvent (ReedSolomon.code (domain φ) 8 : Set (sites → K)) (5/16)
      (first φ b) (second φ) (φ v-b) := by
  obtain ⟨i,hi⟩ := finite_profile.2.2 v hv
  have mapped : head i (1 : K) = φ v := by
    simpa only [map_one, hi] using head_map φ i (1 : F)
  apply event φ b _ hole i
  · simp [core,hole]
  · simp [hole, first, second, mapped]
  · intro h
    apply hb
    exact ⟨v, by simpa [hole,first,mapped] using h.1⟩

/-- Fifteen ordinary labels and four translated hole labels are MCA-bad. -/
theorem nineteen_bad [DecidableEq K] (b : K) (hb : b ∉ Set.range φ) :
    ∃ T : Finset K, T.card = 19 ∧ ∀ t ∈ T,
      mcaEvent (ReedSolomon.code (domain φ) 8 : Set (sites → K)) (5/16) (first φ b) (second φ) t := by
  let A := ordinary.image (fun x => φ (fieldLabel x))
  let B := holeValues.image (fun v => φ v-b)
  have ha : A.card = 15 := by
    apply (card_image_of_injective _ ?_).trans (by decide : ordinary.card = 15)
    intro x y hxy
    simpa [fieldLabel] using φ.injective hxy
  have hb' : B.card = 4 := by
    apply (card_image_of_injective _ ?_).trans (by decide : holeValues.card = 4)
    intro x y hxy
    exact φ.injective (sub_left_inj.mp hxy)
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro t ht hu
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    obtain ⟨v,hv,h⟩ := mem_image.mp hu
    exact hb ⟨v-fieldLabel x, by rw [map_sub]; linear_combination h⟩
  refine ⟨A∪B, by rw [card_union_of_disjoint dis,ha,hb'], ?_⟩
  intro t ht
  obtain ht | ht := mem_union.mp ht
  · obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    exact ordinary_event φ b x hx
  · obtain ⟨v,hv,rfl⟩ := mem_image.mp ht
    exact hole_event φ b hb v hv

#print axioms domain_image
#print axioms nineteen_bad
end ArkLib.ProximityGap.Frontier.SmoothSeventeenExtension
