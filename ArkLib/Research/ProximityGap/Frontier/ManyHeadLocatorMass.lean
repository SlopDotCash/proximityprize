/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.LinearPencilFreshLabels
import Mathlib.LinearAlgebra.Lagrange

/-! # Private cores sharing a polynomial locator

Each private site gives one bad challenge per distinct foreign head by
projecting a two-parameter pencil. All heads share a common polynomial locator.
-/

open Polynomial Finset ProximityGap
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass

variable {n h r k p d : ℕ} [Fact p.Prime]

private def owner (s : Fin (d + 1) × Fin d) := s.1
private def target (s : Fin (d + 1) × Fin d) := s.1.succAbove s.2
private def coeff (j : Fin (d + 1)) := j.val + 1
private def scale (s : Fin (d + 1) × Fin d) := coeff (target s) + coeff (owner s)

private lemma pair_unique (i j : Fin (d + 1) × Fin d) (hs : scale i = scale j)
    (ho : owner i = owner j) : i = j := by
  rcases i with ⟨a, x⟩
  rcases j with ⟨b, y⟩
  change a = b at ho
  subst b
  change (a.succAbove x).val + 1 + (a.val + 1) = (a.succAbove y).val + 1 + (a.val + 1) at hs
  exact Prod.ext rfl (Fin.succAbove_right_injective (Fin.ext (by omega : (a.succAbove x).val =
    (a.succAbove y).val)))

private lemma scale_bounds (i : Fin (d + 1) × Fin d) : 0 < scale i ∧ scale i < 2 * d + 3 := by
  have ht := (target i).isLt
  have ho := (owner i).isLt
  unfold scale coeff
  omega

private lemma coeff_bound (j : Fin (d + 1)) : coeff j < 2 * d + 3 := by
  unfold coeff
  omega

private lemma distinct_heads (i : Fin (d + 1) × Fin d) : coeff (target i) ≠ coeff (owner i) := by
  intro he
  exact i.1.succAbove_ne i.2 (Fin.ext (Nat.add_right_cancel he))

private def initialPositions (hn : h + (d + 1) * r ≤ n) : Fin h ↪ Fin n where
  toFun x := ⟨x.val, by omega⟩
  inj' _ _ hxy := Fin.ext (congrArg (fun z : Fin n => z.val) hxy)

private def slot (hn : h + (d + 1) * r ≤ n) (j : Fin (d + 1)) : Fin r ↪ Fin n where
  toFun x := ⟨h + ((d + 1) * x.val + j.val), by
    have hstep : (d + 1) * x.val + j.val < (d + 1) * (x.val + 1) := by
      simpa only [Nat.mul_add, Nat.mul_one] using Nat.add_lt_add_left j.isLt ((d + 1) * x.val)
    have hr : (d + 1) * (x.val + 1) ≤ (d + 1) * r := Nat.mul_le_mul_left _ x.isLt
    exact (Nat.add_lt_add_left (lt_of_lt_of_le hstep hr) h).trans_le hn⟩
  inj' x y hxy := by
    have hval := congrArg Fin.val hxy
    change h + ((d + 1) * x.val + j.val) = h + ((d + 1) * y.val + j.val) at hval
    have hm := Nat.add_right_cancel (Nat.add_left_cancel hval)
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos d) hm)

private def species (d h : ℕ) (x : Fin n) : Fin (d + 1) :=
  ⟨(x.val - h) % (d + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

private lemma species_slot (hn : h + (d + 1) * r ≤ n) (j : Fin (d + 1)) (x : Fin r) :
    species d h (slot hn j x) = j := by
  apply Fin.ext
  change (h + ((d + 1) * x.val + j.val) - h) % (d + 1) = j.val
  simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]

private lemma private_disjoint (hn : h + (d + 1) * r ≤ n) (j : Fin (d + 1)) :
    Disjoint (univ.map (initialPositions hn)) (univ.map (slot hn j)) := by
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨a, _, rfl⟩ := mem_map.mp hx
  obtain ⟨b, _, he⟩ := mem_map.mp hy
  have he' := congrArg Fin.val he
  change h + ((d + 1) * b.val + j.val) = a.val at he'
  omega

private lemma cast_eq {a b : ℕ} (ha : a < p) (hb : b < p)
    (he : (a : ZMod p) = (b : ZMod p)) : a = b := by
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using congrArg ZMod.val he

/-- An arbitrary evaluation domain supports `d` bad labels per private site on
`d + 1` distinct heads with a common core of size `h`. -/
theorem mass [NeZero n] (dom : Fin n ↪ ZMod p) (δ : ℝ≥0)
    (hn : h + (d + 1) * r ≤ n) (hdegree : h + 2 ≤ k) (hdecode : k ≤ h + r)
    (hsize : (1 - δ) * (n : ℝ≥0) ≤ ((h + r + 1 : ℕ) : ℝ≥0))
    (hp : 2 * d + 3 ≤ p) (hfield : ((d + 1) * d * r).choose 2 ≤ p) :
    (((d + 1) * d * r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤
      epsMCA (F := ZMod p) (ReedSolomon.code dom k : Set (Fin n → ZMod p)) δ := by
  classical
  let common := univ.map (initialPositions hn)
  let core (i : (Fin (d + 1) × Fin d) × Fin r) := common ∪ univ.map (slot hn (target i.1))
  let site (i : (Fin (d + 1) × Fin d) × Fin r) := slot hn (owner i.1) i.2
  let H := Lagrange.nodal common (fun x => dom x)
  let b (j : Fin (d + 1)) : ZMod p := coeff j
  let B (i : (Fin (d + 1) × Fin d) × Fin r) := b (target i.1)
  let c (x : Fin n) := b (species d h x)
  let key (i : (Fin (d + 1) × Fin d) × Fin r) : Fin 2 → ZMod p :=
    ![-((scale i.1 : ℕ) : ZMod p) * dom (site i), -((scale i.1 : ℕ) : ZMod p)]
  have hcard (i : (Fin (d + 1) × Fin d) × Fin r) : (core i).card = h + r := by
    simp [core, common, card_union_of_disjoint (private_disjoint hn (target i.1))]
  have hdegH : H.natDegree = h := by simp [H, common, Lagrange.natDegree_nodal]
  have hdegC (a : ZMod p) : (H * C a).natDegree ≤ h := by
    simpa [hdegH] using natDegree_mul_le (p := H) (q := C a)
  have degC (a : ZMod p) : (H * C a).degree < (k : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    exact_mod_cast lt_of_le_of_lt (hdegC a) (by omega : h < k)
  have degX (a : ZMod p) : (H * C a * X).degree < (k : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    have hle := natDegree_mul_le (p := H * C a) (q := (X : (ZMod p)[X]))
    rw [natDegree_X] at hle
    have := hdegC a
    exact_mod_cast (by omega : (H * C a * X).natDegree < k)
  have c_site (i : (Fin (d + 1) × Fin d) × Fin r) : c (site i) = b (owner i.1) := by
    simp only [c, site, species_slot]
  have H_site (i : (Fin (d + 1) × Fin d) × Fin r) : H.eval (dom (site i)) ≠ 0 := by
    apply Lagrange.eval_nodal_not_at_node
    intro x hx he
    have hsite : site i ∈ univ.map (slot hn (owner i.1)) := mem_map.mpr ⟨i.2, mem_univ _, rfl⟩
    exact disjoint_left.mp (private_disjoint hn (owner i.1)) hx (dom.injective he ▸ hsite)
  have hinj : Function.Injective key := by
    rintro ⟨i, x⟩ ⟨j, y⟩ he
    have he1 := congrFun he 1
    have he0 := congrFun he 0
    simp only [key, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      neg_inj] at he1 he0
    have hs := cast_eq (lt_of_lt_of_le (scale_bounds i).2 hp)
      (lt_of_lt_of_le (scale_bounds j).2 hp) he1
    have hs0 : (scale j : ZMod p) ≠ 0 := by
      intro hz
      have hh := cast_eq (lt_of_lt_of_le (scale_bounds j).2 hp) (by omega : 0 < p)
        (show (scale j : ZMod p) = ((0 : ℕ) : ZMod p) by simpa using hz)
      exact (scale_bounds j).1.ne' hh
    rw [hs] at he0
    have hx := dom.injective (mul_left_cancel₀ (neg_ne_zero.mpr hs0) he0)
    have ho : owner i = owner j := by
      simpa only [site, species_slot] using congrArg (species d h) hx
    have hij := pair_unique i j hs ho
    subst j
    exact Prod.ext rfl ((slot hn (owner i)).injective hx)
  have raw := LinearPencilFreshLabels.mass_of_distinct_fresh_labels dom k δ core site
    (fun i => H * C (B i ^ 2) * X) (fun i => H * C (B i ^ 2)) (fun i => H * C (B i))
    (fun x => H.eval (dom x) * c x ^ 2 * dom x) (fun x => H.eval (dom x) * c x ^ 2)
    (fun x => H.eval (dom x) * c x) key (fun _ => degX _) (fun _ => degC _) (fun _ => degC _)
    (by
      intro i x hx
      rcases mem_union.mp hx with hc | hc
      · have hz : H.eval (dom x) = 0 := Lagrange.eval_nodal_at_node hc
        simp only [eval_mul, eval_C, eval_X, hz, zero_mul, and_self]
      · obtain ⟨z, _, rfl⟩ := mem_map.mp hc
        simp only [eval_mul, eval_C, eval_X, c, species_slot, B, and_self])
    (fun i => (hcard i).symm ▸ hdecode)
    (fun i => by simpa only [hcard, Fintype.card_fin] using hsize)
    (by
      intro i he
      rw [eval_mul, eval_C, c_site] at he
      have hb := mul_left_cancel₀ (H_site i) he
      exact distinct_heads i.1 (cast_eq (lt_of_lt_of_le (coeff_bound _) hp)
        (lt_of_lt_of_le (coeff_bound _) hp) hb))
    (by
      intro i
      simp only [eval_mul, eval_C, eval_X, key, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, c_site, B, scale, Nat.cast_add, b]
      constructor <;> ring)
    hinj (by simpa only [Fintype.card_prod, Fintype.card_fin, Nat.card_eq_fintype_card,
      ZMod.card] using hfield)
  simpa only [Fintype.card_prod, Fintype.card_fin, ZMod.card] using raw

end ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass

#print axioms ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass.mass
