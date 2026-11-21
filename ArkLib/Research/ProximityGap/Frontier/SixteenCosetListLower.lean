/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ReservedFiberList
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Three-word lists on every multiplicative coset of order sixteen

The three pairwise intersection sets of the decoding polynomials are fibers of
the same power map, plus shared roots. Their equality pattern depends only on
the exponents of the evaluation sites modulo sixteen.
-/

namespace ProximityGap.SixteenCosetListLower

open Finset Polynomial Code

variable {F : Type*} [Field F]

private def size : Fin 4 → ℕ := ![4, 2, 1, 0]
private def shared : Fin 4 → ℕ := ![3, 1, 0, 0]
private def site (j : Fin 4) (r : ℕ) := 3 + (16 / size j) * r
private def power (g : Fˣ) (j : Fin 4) (i : ℕ) := (g : F) ^ (i * size j)

private lemma equal_powers (g : Fˣ) (hg : orderOf g = 16) (i k : ℕ) :
    (g : F) ^ i = (g : F) ^ k ↔ i % 16 = k % 16 := by
  change ((g^i : Fˣ) : F) = ↑(g^k) ↔ _
  rw [Units.val_inj, pow_inj_mod, hg]

private lemma fiber_injective (g : Fˣ) (hg : orderOf g = 16) (j : Fin 4) (hj : j ≠ 3) :
    Function.Injective (fun i : Fin 3 => power g j i) := by
  intro i k he
  have h := (equal_powers g hg _ _).mp he
  exact (by decide : ∀ (z : Fin 4), z ≠ 3 → ∀ t v : Fin 3,
    (t.val * size z) % 16 = (v.val * size z) % 16 → t = v) j hj i k h

private def pairIndex (l r : Fin 3) : Fin 3 :=
  if l = 0 ∨ r = 0 then (if l = 2 ∨ r = 2 then 1 else 0) else 2

private def slope (v : Fin 3 → F) (l : Fin 3) : F :=
  if l = 0 then 0 else if l = 1 then v 1 - v 2 else v 0 - v 2

private def root (v : Fin 3 → F) (l : Fin 3) := if l = 2 then v 1 else v 0

private lemma raw_equal (v : Fin 3 → F) (hv : Function.Injective v) (z : F) (l r : Fin 3) :
    slope v l * (z - root v l) = slope v r * (z - root v r) ↔
      l = r ∨ z = v (pairIndex l r) := by
  have hvw : v 1 ≠ v 2 := fun e => (by decide : (1 : Fin 3) ≠ 2) (hv e)
  have huw : v 0 ≠ v 2 := fun e => (by decide : (0 : Fin 3) ≠ 2) (hv e)
  have hvu : v 1 ≠ v 0 := fun e => (by decide : (1 : Fin 3) ≠ 0) (hv e)
  have hpair : (v 1 - v 2)*(z-v 0) = (v 0-v 2)*(z-v 1) ↔ z = v 2 := by
    rw [← sub_eq_zero, show (v 1-v 2)*(z-v 0) - (v 0-v 2)*(z-v 1) =
      (v 1-v 0)*(z-v 2) by ring, mul_eq_zero]
    simp [sub_eq_zero, hvu]
  have hrev := (eq_comm (a := (v 0-v 2)*(z-v 1)) (b := (v 1-v 2)*(z-v 0))).trans hpair
  fin_cases l <;> fin_cases r <;>
    simp [slope, root, pairIndex, hpair, hrev, hvw, huw, sub_eq_zero]

private def productAt (D : Fin 16 ↪ F) (a : Fˣ) (g : Fˣ) (j : Fin 4) (i : Fin 16) :=
  ∏ r ∈ range (shared j), (D i - (a : F) * (g : F)^(site j r))

private def word (D : Fin 16 ↪ F) (a g : Fˣ) (j : Fin 4) (l : Fin 3) (i : Fin 16) : F :=
  if j = 3 then (g : F)^l.val else
    productAt D a g j i * (slope (fun t => power g j t) l *
      (power g j i - root (fun t => power g j t) l))

private def mask (j : Fin 4) (l r : Fin 3) (i : Fin 16) : Prop :=
  if j = 3 then l = r else
    (l = r ∨ (i.val * size j) % 16 = ((pairIndex l r).val * size j) % 16) ∨
      ∃ s ∈ range (shared j), i.val % 16 = site j s % 16

private instance (j : Fin 4) (l r : Fin 3) (i : Fin 16) : Decidable (mask j l r i) := by
  unfold mask
  infer_instance

private lemma word_equal (D : Fin 16 ↪ F) (a g : Fˣ) (hg : orderOf g = 16)
    (hD : ∀ i, D i = (a : F) * (g : F)^i.val) (j : Fin 4) (l r : Fin 3) (i : Fin 16) :
    word D a g j l i = word D a g j r i ↔ mask j l r i := by
  classical
  by_cases hj : j = 3
  · simp only [word, mask, hj, ↓reduceIte, equal_powers g hg]
    exact (by decide : ∀ s t : Fin 3, s.val % 16 = t.val % 16 ↔ s = t) l r
  · have hzero : productAt D a g j i = 0 ↔
        ∃ s ∈ range (shared j), i.val % 16 = site j s % 16 := by
      simp only [productAt, Finset.prod_eq_zero_iff, sub_eq_zero, hD,
        mul_right_inj' a.ne_zero, equal_powers g hg]
    simp only [word, mask, hj, ↓reduceIte, mul_eq_mul_left_iff, hzero]
    rw [raw_equal _ (fiber_injective g hg j hj) (power g j i) l r]
    simp only [power, equal_powers g hg]

private noncomputable def head (a g : Fˣ) (j : Fin 4) (l : Fin 3) : F[X] :=
  if j = 3 then C ((g : F)^l.val) else
    (∏ r ∈ range (shared j), (X - C ((a : F) * (g : F)^(site j r)))) *
      (C (slope (fun t => power g j t) l) *
        (C ((a⁻¹ : Fˣ) : F)^size j * X^size j - C (root (fun t => power g j t) l)))

private lemma word_in_code (D : Fin 16 ↪ F) (a g : Fˣ)
    (hD : ∀ i, D i = (a : F) * (g : F)^i.val) (j : Fin 4) (l : Fin 3) :
    word D a g j l ∈ ReedSolomon.code D (![8,4,2,1] j) := by
  apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (head a g j l)
  · by_cases hj : j = 3
    · subst j
      simp [head]
    · simp only [head, hj, ↓reduceIte]
      apply natDegree_mul_le.trans_lt
      rw [natDegree_finsetProd_X_sub_C_eq_card, card_range]
      apply lt_of_le_of_lt (Nat.add_le_add_left (natDegree_C_mul_le ..) _)
      rw [natDegree_sub_C, ← C_pow]
      apply lt_of_le_of_lt (Nat.add_le_add_left (natDegree_C_mul_le ..) _)
      rw [natDegree_X_pow]
      fin_cases j <;> decide
  · intro i
    by_cases hj : j = 3
    · simp [head, word, hj]
    · have hpow : ((↑a⁻¹ : F) ^ size j) * D i ^ size j = power g j i := by
        rw [← mul_pow, hD, ← mul_assoc, Units.inv_mul, one_mul]
        exact (pow_mul ..).symm
      simp only [head, word, productAt, hj, ↓reduceIte, eval_mul, eval_pow, eval_X,
        eval_sub, eval_C, eval_prod, hpow]

private def choice : Fin 4 → Fin 16 → Fin 3 :=
  ![![0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0], ![0,0,1,0,0,1,2,0,0,0,1,1,2,0,1,2],
    ![0,0,1,0,1,2,0,1,2,0,1,2,0,1,2,0], ![0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0]]

/-- For any field and any multiplicative coset of a cyclic subgroup of order sixteen,
a single center has at least three scalar words at the indicated error count. -/
theorem scalar_lower [Fintype F] [DecidableEq F] (D : Fin 16 ↪ F) (a g : Fˣ)
    (hg : orderOf g = 16) (hD : ∀ i, D i = (a : F) * (g : F)^i.val) (j : Fin 4) :
    3 ≤ Lambda (ReedSolomon.code D (![8,4,2,1] j) : Set (Fin 16 → F))
      (((![5,8,10,11] j : ℕ) : ℝ)/16) := by
  classical
  let w := word D a g j
  let center i := w (choice j i) i
  have hinj : Function.Injective w := by
    intro l r h
    have hmask := (word_equal D a g hg hD j l r 15).mp (congrFun h 15)
    exact (by decide : ∀ (z : Fin 4) (s t : Fin 3), mask z s t 15 → s = t) j l r hmask
  have hmem : (↑(univ.image w) : Set (Fin 16 → F)) ⊆ closeCodewordsRel
      (ReedSolomon.code D (![8,4,2,1] j) : Set (Fin 16 → F)) center
      (((![5,8,10,11] j : ℕ) : ℝ)/16) := by
    intro v hv
    obtain ⟨l, _, rfl⟩ := mem_image.mp hv
    apply mem_closeCodewordsRel_iff.mpr
    refine ⟨word_in_code D a g hD j l, ?_⟩
    rw [relHammingDist_coe, Fintype.card_fin]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    rw [Nat.cast_le]
    change (univ.filter (fun i : Fin 16 => center i ≠ w l i)).card ≤ _
    have hdiff : (univ.filter (fun i : Fin 16 => center i ≠ w l i)) =
        univ.filter (fun i : Fin 16 => ¬mask j (choice j i) l i) := by
      ext i
      simp only [mem_filter, mem_univ, true_and]
      exact not_congr (word_equal D a g hg hD j (choice j i) l i)
    rw [hdiff]
    exact (by decide : ∀ (z : Fin 4) (v : Fin 3),
      (univ.filter (fun i : Fin 16 => ¬mask z (choice z i) v i)).card ≤ ![5,8,10,11] z) j l
  have h := encard_le_Lambda_of_subset_closeCodewordsRel hmem
  rw [Set.encard_coe_eq_coe_finsetCard, card_image_of_injective _ hinj] at h
  simpa only [card_univ, Fintype.card_fin, Nat.cast_ofNat] using h

private lemma reindex_list {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    [Fintype F] [DecidableEq F] (D : I ↪ F) (e : Fin 16 ≃ I) (k : ℕ) (δ : ℝ) :
    Lambda (ReedSolomon.code (e.toEmbedding.trans D) k : Set (Fin 16 → F)) δ ≤
      Lambda (ReedSolomon.code D k : Set (I → F)) δ := by
  classical
  let transport (w : Fin 16 → F) : I → F := w ∘ e.symm
  have hinj : Function.Injective transport := fun w v h => funext fun i => by
    simpa [transport] using congrFun h (e i)
  have hd (w v : Fin 16 → F) : hammingDist (transport w) (transport v) = hammingDist w v := by
    have h := congrArg Finset.card
      (Finset.map_filter (s := univ) (f := e) (p := fun i => w i ≠ v i))
    simpa only [hammingDist, transport, Function.comp_def, card_map, map_univ_equiv] using h.symm
  apply Lambda_le_iff_forall_encard_le.mpr
  intro center
  apply le_trans _ (encard_closeCodewordsRel_le_Lambda _ _ (transport center))
  rw [← hinj.injOn.encard_image]
  apply Set.encard_mono
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨hwC, hdist⟩ := mem_closeCodewordsRel_iff.mp hw
  apply mem_closeCodewordsRel_iff.mpr
  constructor
  · obtain ⟨p, hp, h⟩ := ReedSolomon.mem_code_iff_eval.mp hwC
    apply ReedSolomon.mem_code_iff_eval.mpr
    exact ⟨p, hp, fun i => by simpa [transport] using h (e.symm i)⟩
  · rw [relHammingDist_coe, hd, ← Fintype.card_congr e, ← relHammingDist_coe]
    exact hdist

/-- The same list bounds on a supplied smooth domain, with any indexing of its sites. -/
theorem smooth_scalar_lower {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    [Fintype F] [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 16)
    (j : Fin 4) : 3 ≤ Lambda (ReedSolomon.code D (![8,4,2,1] j) : Set (I → F))
      (((![5,8,10,11] j : ℕ) : ℝ)/16) := by
  classical
  let H := ReedSolomon.Smooth.H D
  let a := ReedSolomon.Smooth.a D
  let : Fintype H := Fintype.ofFinite H
  have hcos : (↑(univ.image D) : Set F) = (fun u : Fˣ => (a : F) * (u : F)) '' (H : Set Fˣ) :=
    ReedSolomon.Smooth.h_coset
  have hall (i : I) : ∃ z : H, D i = (a : F) * ((z : Fˣ) : F) := by
    have hx : D i ∈ (↑(univ.image D) : Set F) := mem_image_of_mem _ (mem_univ _)
    obtain ⟨v, hv, he⟩ := hcos ▸ hx
    exact ⟨⟨v,hv⟩,he.symm⟩
  choose z hz using hall
  have hbij : Function.Bijective z := by
    constructor
    · exact fun i j hij => D.injective (by rw [hz i, hz j, hij])
    · intro v
      have hx : (a : F) * ((v : Fˣ) : F) ∈ (↑(univ.image D) : Set F) :=
        hcos ▸ ⟨v.val, v.property, rfl⟩
      obtain ⟨i, _, hi⟩ := mem_image.mp hx
      exact ⟨i, Subtype.ext (Units.ext (mul_left_cancel₀ a.ne_zero ((hz i).symm.trans hi)))⟩
  let coord := Equiv.ofBijective z hbij
  have hcard : Fintype.card H = 16 := (Fintype.card_congr coord).symm.trans hn
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
  have horder : orderOf u = 16 := hu.trans (Nat.card_eq_fintype_card.trans hcard)
  let f (i : Fin 16) : H := u ^ i.val
  have hf : Function.Injective f := by
    intro i t he
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := u) _ _ he
    · change _ < orderOf u
      simp [horder]
    · change _ < orderOf u
      simp [horder]
  let powers := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hf, by rw [Fintype.card_fin, hcard]⟩)
  let e := powers.trans coord.symm
  have hD (i : Fin 16) : e.toEmbedding.trans D i = (a : F) * ((u : Fˣ) : F) ^ i.val := by
    change D (coord.symm (powers i)) = _
    rw [hz]
    change (a : F) * ((coord (coord.symm (powers i)) : Fˣ) : F) = _
    rw [coord.apply_symm_apply]
    rfl
  exact (scalar_lower (e.toEmbedding.trans D) a u.val
    ((orderOf_injective H.subtype Subtype.val_injective u).trans horder) hD j).trans
      (reindex_list D e _ _)

#print axioms smooth_scalar_lower
#print axioms scalar_lower

end ProximityGap.SixteenCosetListLower
