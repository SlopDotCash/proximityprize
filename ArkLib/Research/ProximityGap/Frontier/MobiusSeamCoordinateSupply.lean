/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize contributors
-/
import ArkLib.Research.ProximityGap.Frontier.MobiusStepanov
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Removing collisions between three fractional linear directions -/

set_option autoImplicit false
namespace ProximityGap.MobiusSeamCoordinateSupply
open Finset

/-- Matrix defining a fractional linear map. -/
structure Mobius (F : Type*) where
  a : F
  b : F
  c : F
  d : F

variable {F : Type*} [Field F]

namespace Mobius

def num (u : Mobius F) (x : F) := u.a * x + u.b
def den (u : Mobius F) (x : F) := u.c * x + u.d
def value (u : Mobius F) (x : F) := u.num x / u.den x
def det (u : Mobius F) := u.a*u.d - u.b*u.c

/-- Representative of `v⁻¹u`, without dividing by the determinant. -/
def relative (u v : Mobius F) : Mobius F :=
  ⟨v.d*u.a-v.b*u.c, v.d*u.b-v.b*u.d, v.a*u.c-v.c*u.a, v.a*u.d-v.c*u.b⟩

theorem det_relative (u v : Mobius F) : (relative u v).det = u.det * v.det := by
  simp only [relative, det]
  ring

private theorem cross_agree {u v : Mobius F} {x y : F} (hu : u.den x ≠ 0) (hv : v.den y ≠ 0)
    (h : u.value x = v.value y) : u.num x * v.den y = v.num y * u.den x :=
  (div_eq_div_iff hu hv).mp h

/-- A nonsingular map is injective on its finite nonpoles. -/
theorem injective_on_finite (u : Mobius F) (hu : u.det ≠ 0) {x y : F}
    (hx : u.den x ≠ 0) (hy : u.den y ≠ 0) (h : u.value x = u.value y) : x = y := by
  have hc := cross_agree hx hy h
  have hzero : u.det * (x-y) = 0 := by
    dsimp [num, den] at hc
    dsimp [det]
    linear_combination hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hu)

/-- Equality at two finite nonpoles transfers the first point to the second by the relative map. -/
theorem relative_of_agree {u v : Mobius F} (hd : v.det ≠ 0) {x y : F}
    (hx : u.den x ≠ 0) (hy : v.den y ≠ 0) (h : u.value x = v.value y) :
    (relative u v).value x = y := by
  have hc := cross_agree hx hy h
  have hdprod : (relative u v).den x * v.den y = v.det * u.den x := by
    dsimp [num, den] at hc
    dsimp [den, det, relative]
    linear_combination -v.c * hc
  have hrd : (relative u v).den x ≠ 0 := by
    intro hh
    rw [hh, zero_mul] at hdprod
    exact (mul_ne_zero hd hx) hdprod.symm
  apply (div_eq_iff hrd).mpr
  dsimp [num, den] at hc
  dsimp [relative, num, den]
  linear_combination hc

/-- The proved subgroup bound in usual matrix coordinates. -/
theorem subgroup_intersection_le {p : ℕ} [CharP F p] [Fintype F] [DecidableEq F]
    (hp : p.Prime) (hbig : 2^37 < p) (u : Mobius F) (ha : u.a ≠ 0) (hb : u.b ≠ 0)
    (hc : u.c ≠ 0) (hdet : u.det ≠ 0) :
    (univ.filter (fun x : F => x ^ (2^30 : ℕ) = 1 ∧ (u.value x) ^ (2^30 : ℕ) = 1)).card ≤
      66060289 := by
  let a := -u.b / u.a
  let b := -u.d / u.c
  have haa : a ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) ha
  have hab : a ≠ b := by
    intro h
    have hh := (div_eq_div_iff ha hc).mp h
    apply hdet
    dsimp [det]
    linear_combination hh
  have hv (x : F) : u.value x = u.a/u.c * (x-a)/(x-b) := by
    dsimp [value, num, den, a, b]
    by_cases hz : u.c*x + u.d = 0
    · have hz' : x - -u.d/u.c = 0 := by field_simp; linear_combination hz
      simp [hz, hz']
    · have hz' : x - -u.d/u.c ≠ 0 := by
        intro h
        apply hz
        field_simp at h
        linear_combination h
      field_simp
      ring
  simpa only [hv] using MobiusStepanov.production_mobius_intersection hp hbig haa hab (div_ne_zero ha hc)

end Mobius

variable [Fintype F] [DecidableEq F]

private def edgePairs := (univ : Finset (Fin 3 × Fin 3)).filter (fun e => e.1 ≠ e.2)

private def collisions (m : Fin 3 → Mobius F) (H : Finset F) : Finset F :=
  edgePairs.biUnion (fun ij => H.filter (fun x => ((m ij.1).relative (m ij.2)).value x ^ (2^30 : ℕ) = 1))

private def polesAndValues (u : Mobius F) (H T : Finset F) : Finset F :=
  (H.filter (fun x => u.den x = 0)) ∪ (H.filter (fun x => u.den x ≠ 0 ∧ u.value x ∈ T))

/-- Coordinates surviving all cross-map collision, special-coordinate, pole and special-label exclusions. -/
noncomputable def ordinary (m : Fin 3 → Mobius F) (H Y T : Finset F) : Finset F :=
  H \ (collisions m H ∪ Y ∪ univ.biUnion (fun i => polesAndValues (m i) H T))

omit [Fintype F] in
private theorem card_polesAndValues (u : Mobius F) (hu : u.det ≠ 0) (H T : Finset F) :
    (polesAndValues u H T).card ≤ 1 + T.card := by
  apply (card_union_le _ _).trans
  apply Nat.add_le_add
  · apply card_le_one.mpr
    intro x hx y hy
    have h1 := (mem_filter.mp hx).2
    have h2 := (mem_filter.mp hy).2
    have hc : u.c ≠ 0 := by
      intro hc
      obtain hd : u.d = 0 := by simpa [Mobius.den, hc] using h1
      exact hu (by simp [Mobius.det,hc,hd])
    have hz : u.c * (x-y) = 0 := by dsimp [Mobius.den] at h1 h2; linear_combination h1 - h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hc)
  · apply card_le_card_of_injOn u.value
    · intro x hx
      exact (mem_filter.mp hx).2.2
    · intro x hx y hy hxy
      exact u.injective_on_finite hu (mem_filter.mp hx).2.1 (mem_filter.mp hy).2.1 hxy

/-- A bound on each of the six ordered cross-map intersections leaves this many
ordinary sites after excluding the six marked coordinates and their scalar values. -/
theorem ordinary_card_of_pair_cap {L : ℕ} (m : Fin 3 → Mobius F) (H Y T : Finset F)
    (hpow : ∀ x ∈ H, x^(2^30 : ℕ)=1) (hY : Y.card ≤ 6) (hT : T.card ≤ 6)
    (hdet : ∀ i, (m i).det ≠ 0) (hpair : ∀ i j, i ≠ j →
      (univ.filter fun x : F => x^(2^30 : ℕ)=1 ∧
        (((m i).relative (m j)).value x)^(2^30 : ℕ)=1).card ≤ L) :
    H.card-(6*L+27) ≤ (ordinary m H Y T).card := by
  have hpairs : edgePairs.card = 6 := by decide
  have hcross : (collisions m H).card ≤ 6*L := by
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _ ∈ edgePairs, L := by
        apply sum_le_sum
        intro ij hij
        apply le_trans _ (hpair ij.1 ij.2 (mem_filter.mp hij).2)
        apply card_le_card
        intro x hx
        obtain ⟨hxH,hxp⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨mem_univ _, hpow x hxH, hxp⟩
      _ = _ := by simp [hpairs]
  let E := univ.biUnion (fun i => polesAndValues (m i) H T)
  have he : E.card ≤ 3*7 := by
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _ : Fin 3, 7 := sum_le_sum (fun i _ => (card_polesAndValues _ (hdet i) H T).trans (by omega))
      _ = _ := by decide
  let B := collisions m H ∪ Y ∪ E
  have hB : B.card ≤ 6*L+6+3*7 := by
    apply (card_union_le _ _).trans
    exact Nat.add_le_add ((card_union_le _ _).trans (Nat.add_le_add hcross hY)) he
  have hmass := card_sdiff_add_card H B
  have hle : H.card ≤ (H ∪ B).card := card_le_card subset_union_left
  change (H.card-(6*L+27)) ≤ (H \ B).card
  omega

/-- At least the required number of ordinary coordinates survives for the three maps. -/
theorem ordinary_card {p : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2^37 < p)
    (m : Fin 3 → Mobius F) (H Y T : Finset F) (hH : H.card = 2^30)
    (hpow : ∀ x ∈ H, x^(2^30 : ℕ) = 1) (hY : Y.card ≤ 6) (hT : T.card ≤ 6)
    (hdet : ∀ i, (m i).det ≠ 0)
    (hrel : ∀ i j, i ≠ j → let M := (m i).relative (m j); M.a ≠ 0 ∧ M.b ≠ 0 ∧ M.c ≠ 0) :
    677380063 ≤ (ordinary m H Y T).card := by
  have h := ordinary_card_of_pair_cap (L:=66060289) m H Y T hpow hY hT hdet (by
    intro i j hij
    obtain ⟨ha,hb,hc⟩ := hrel i j hij
    exact Mobius.subgroup_intersection_le hp hbig _ ha hb hc (by
      rw [Mobius.det_relative]
      exact mul_ne_zero (hdet _) (hdet _)))
  rwa [hH] at h

omit [Fintype F] in
/-- Every ordinary coordinate avoids all poles and prescribed labels. Equal scalar values at
ordinary coordinates require the same map and the same coordinate. -/
theorem ordinary_separation (m : Fin 3 → Mobius F) (H Y T : Finset F)
    (hpow : ∀ x ∈ H, x^(2^30 : ℕ) = 1) (hdet : ∀ i, (m i).det ≠ 0) :
    (∀ x ∈ ordinary m H Y T, x ∈ H ∧ x ∉ Y ∧ ∀ i, (m i).den x ≠ 0 ∧ (m i).value x ∉ T) ∧
    (∀ x ∈ ordinary m H Y T, ∀ y ∈ ordinary m H Y T, ∀ i j, (m i).value x = (m j).value y → i = j ∧ x = y) := by
  have hreg : ∀ x ∈ ordinary m H Y T, x ∈ H ∧ x ∉ Y ∧ ∀ i, (m i).den x ≠ 0 ∧ (m i).value x ∉ T := by
    intro x hx
    obtain ⟨hxH,hout⟩ := mem_sdiff.mp hx
    have hY : x ∉ Y := fun h => hout (mem_union_left _ (mem_union_right _ h))
    refine ⟨hxH,hY,?_⟩
    intro i
    have havoid : x ∉ polesAndValues (m i) H T := fun h =>
      hout (mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _, h⟩))
    have hn : (m i).den x ≠ 0 := fun hh => havoid (mem_union_left _ (mem_filter.mpr ⟨hxH,hh⟩))
    exact ⟨hn, fun hh => havoid (mem_union_right _ (mem_filter.mpr ⟨hxH,hn,hh⟩))⟩
  refine ⟨hreg, ?_⟩
  intro x hx y hy i j heq
  have hx' := hreg x hx
  have hy' := hreg y hy
  by_cases hij : i = j
  · subst j
    exact ⟨rfl, (m i).injective_on_finite (hdet _) (hx'.2.2 i).1 (hy'.2.2 i).1 heq⟩
  · exfalso
    apply (mem_sdiff.mp hx).2
    apply mem_union_left
    apply mem_union_left
    apply mem_biUnion.mpr
    refine ⟨(i,j), mem_filter.mpr ⟨mem_univ _, hij⟩, mem_filter.mpr ⟨hx'.1,?_⟩⟩
    have he := Mobius.relative_of_agree (hdet j) (hx'.2.2 i).1 (hy'.2.2 j).1 heq
    simpa [he] using hpow y hy'.1

#print axioms Mobius.subgroup_intersection_le
#print axioms ordinary_card
#print axioms ordinary_separation

end ProximityGap.MobiusSeamCoordinateSupply
