/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicFoldedNorm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! # Three-fiber antipodal energy and the quarter-rate norm thresholds -/

namespace ProximityGap.QuarterSplitRamification
open Finset

/-- Color three is unoccupied. The other colors distinguish the three fibers. -/
def mark (x : Fin 4) (i : Fin 3) : ℤ := if x = i.castSucc then 1 else 0
def occupied (x : Fin 4) : ℤ := if x = 3 then 0 else 1
def imbalance (x y : Fin 4) (i : Fin 3) : ℤ := mark x i - mark y i
def pairEnergy (x y : Fin 4) (i j : Fin 3) : ℤ := (imbalance x y i - imbalance x y j)^2

private theorem point : ∀ x y : Fin 4,
    pairEnergy x y 0 1 + pairEnergy x y 0 2 + pairEnergy x y 1 2 ≤
      3*(occupied x+occupied y) := by decide

/-- Among three disjoint fibers with 3D marked sites, at least one pair has
folded coefficient energy at most 3D. -/
theorem small_pair {I : Type*} [Fintype I] (x y : I → Fin 4) (D : ℕ)
    (mass : (∑ j, (occupied (x j)+occupied (y j))) = 3*(D : ℤ)) :
    ∃ i l : Fin 3, i ≠ l ∧ ∑ j, pairEnergy (x j) (y j) i l ≤ 3*(D : ℤ) := by
  have total := sum_le_sum (s := (univ : Finset I)) (fun j _ => point (x j) (y j))
  simp only [sum_add_distrib, ← mul_sum] at total
  rw [sum_add_distrib] at mass
  rw [mass] at total
  by_cases h : ∑ j, pairEnergy (x j) (y j) 0 1 ≤ 3*(D : ℤ)
  · exact ⟨0,1,by decide,h⟩
  by_cases h' : ∑ j, pairEnergy (x j) (y j) 0 2 ≤ 3*(D : ℤ)
  · exact ⟨0,2,by decide,h'⟩
  exact ⟨1,2,by decide,by omega⟩

/-- If a folded pair difference vanishes, both disjoint color classes consist
of entire antipodal pairs. -/
theorem stable : ∀ (x y : Fin 4) (i l : Fin 3), i ≠ l →
    imbalance x y i = imbalance x y l →
    (x = i.castSucc ↔ y = i.castSucc) ∧ (x = l.castSucc ↔ y = l.castSucc) := by decide

/-- The power sum of one fiber, with the two antipodal halves of the index
interval written separately. -/
def moment {m p : ℕ} (x y : Fin m → Fin 4) (i : Fin 3) (z : ZMod p) :=
  ∑ j, ((mark (x j) i : ZMod p)*z^j.val + (mark (y j) i : ZMod p)*z^(j.val+m))

private theorem fold_difference {m p : ℕ} [NeZero m] [Fact p.Prime]
    (x y : Fin m → Fin 4) (i l : Fin 3) (z : ZMod p) (odd : z^m = -1) :
    (∑ j, ((imbalance (x j) (y j) i-imbalance (x j) (y j) l : ℤ) : ZMod p)*z^j.val) =
      moment x y i z - moment x y l z := by
  unfold moment
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  simp only [imbalance,Int.cast_sub,pow_add,odd]
  ring

/-- Equal modular moments of the three fibers at sufficiently many odd
frequencies force two entire fibers to be antipodally stable. -/
theorem stable_pair {k p D : ℕ} [Fact p.Prime] (x y : Fin (2^k) → Fin 4)
    (mass : (∑ j, (occupied (x j)+occupied (y j))) = 3*(D : ℤ))
    (t : Fin (2^k) → ZMod p) (inj : Function.Injective t) (S : Finset (Fin (2^k)))
    (odd : ∀ j ∈ S, (t j)^(2^k) = -1)
    (moments : ∀ j ∈ S, ∀ i l, moment x y i (t j) = moment x y l (t j))
    (large : (3*D)^(2^k) < p^(2*S.card)) :
    ∃ i l : Fin 3, i ≠ l ∧
      ∀ j, mark (x j) i = mark (y j) i ∧ mark (x j) l = mark (y j) l := by
  obtain ⟨i,l,hne,hE⟩ := small_pair x y D mass
  let a (j : Fin (2^k)) := imbalance (x j) (y j) i - imbalance (x j) (y j) l
  have zero := DyadicFoldedNorm.zero_of_moments a t inj S odd (by
    intro j hj
    rw [show (∑ v, (a v : ZMod p)*(t j)^v.val) = _ from fold_difference x y i l _ (odd j hj)]
    exact sub_eq_zero.mpr (moments j hj i l)) (by simpa [a,pairEnergy] using hE) large
  refine ⟨i,l,hne,fun j => ?_⟩
  have he := congrFun zero j
  change imbalance (x j) (y j) i - imbalance (x j) (y j) l = 0 at he
  obtain ⟨hi,hl⟩ := stable _ _ _ _ hne (sub_eq_zero.mp he)
  exact ⟨by simp [mark,hi], by simp [mark,hl]⟩

/-- A short rational upper bound for the logarithm can certify a production
power comparison without expanding the full-size norm. -/
theorem compare {E q h N p t : ℕ} (hN : 0<N) (hp : 2^158 ≤ p)
    (c : E^q < 2^h) (bound : h*N ≤ 158*(q*t)) : E^N < p^t := by
  by_contra! hn
  have high : (E^N)^q < (p^t)^q := by
    calc (E^N)^q = (E^q)^N := by rw [← pow_mul, Nat.mul_comm N q, pow_mul]
         _ < (2^h)^N := Nat.pow_lt_pow_left c hN.ne'
         _ = 2^(h*N) := (pow_mul ..).symm
         _ ≤ 2^(158*(q*t)) := Nat.pow_le_pow_right (by decide) bound
         _ = ((2^158)^t)^q := by rw [← pow_mul, ← pow_mul]; congr 1; ring
         _ ≤ (p^t)^q := Nat.pow_le_pow_left (Nat.pow_le_pow_left hp _) _
  exact (not_lt_of_ge (Nat.pow_le_pow_left hn q)) high

set_option exponentiation.threshold 400000 in
set_option maxRecDepth 4096 in
/-- Named determinant thresholds for degree D=2^28−2 and its odd half. -/
theorem thresholds {p : ℕ} (hp : 2^158 ≤ p) :
    805306362^268435456 < p^50263626 ∧ 402653181^134217728 < p^24282334 := by
  exact ⟨compare (q := 12276) (h := 363185) (by decide) hp (by decide) (by decide),
         compare (q := 3631) (h := 103792) (by decide) hp (by decide) (by decide)⟩

/-- Two truncated moment intervals and their lengths after squaring suffice
at both successive dyadic levels. -/
theorem frequency_counts {e f : ℕ} (h : 100527252 < e+f) :
    50263626 ≤ e/2+f/2 ∧ 24634900 ≤ (e/2)/2+(f/2)/2 := by omega

/-- A pair with odd cardinality cannot pass a second dyadic norm test. -/
theorem odd_pair {k p d : ℕ} [Fact p.Prime] (x y : Fin (2^k) → Fin 4)
    (i l : Fin 3) (hne : i ≠ l)
    (mi : ∑ j, (mark (x j) i+mark (y j) i) = d)
    (ml : ∑ j, (mark (x j) l+mark (y j) l) = d) (hodd : d % 2 = 1)
    (t : Fin (2^k) → ZMod p) (inj : Function.Injective t) (T : Finset (Fin (2^k)))
    (on : ∀ j ∈ T, (t j)^(2^k) = -1) (same : ∀ j ∈ T, moment x y i (t j) = moment x y l (t j))
    (large : (4*d)^(2^k) < p^(2*T.card)) : False := by
  let a (j : Fin (2^k)) := imbalance (x j) (y j) i - imbalance (x j) (y j) l
  have pointwise : ∀ (u v : Fin 4) (a b : Fin 3), a ≠ b →
      pairEnergy u v a b ≤ 2*((mark u a+mark v a)+(mark u b+mark v b)) := by decide
  have E := sum_le_sum (s := (univ : Finset (Fin (2^k)))) (fun j _ => pointwise (x j) (y j) i l hne)
  rw [← mul_sum, sum_add_distrib, mi, ml] at E
  have zero := DyadicFoldedNorm.zero_of_moments a t inj T on (by
    intro j hj
    rw [show (∑ v, (a v : ZMod p)*(t j)^v.val) = _ from fold_difference x y i l _ (on j hj)]
    exact sub_eq_zero.mpr (same j hj)) (by change (∑ j, pairEnergy (x j) (y j) i l) ≤ ((4*d : ℕ) : ℤ); omega) large
  have canceled (j) : mark (x j) i = mark (y j) i := by
    have he := congrFun zero j
    change imbalance (x j) (y j) i - imbalance (x j) (y j) l = 0 at he
    simp [mark,(stable _ _ _ _ hne (sub_eq_zero.mp he)).1]
  simp_rw [canceled] at mi
  rw [sum_add_distrib] at mi
  omega

private def low {m : ℕ} (x : Fin (m+m) → Fin 4) (i : Fin m) := x (i.castAdd m)
private def high {m : ℕ} (x : Fin (m+m) → Fin 4) (i : Fin m) := x (Fin.natAdd m i)

private theorem down_mass {m : ℕ} (x y : Fin (m+m) → Fin 4) (i : Fin 3)
    (stable : ∀ j, mark (x j) i = mark (y j) i) :
    (∑ j, (mark (x j) i+mark (y j) i)) = 2*(∑ j, (mark (low x j) i+mark (high x j) i)) := by
  simp_rw [← stable]
  rw [sum_add_distrib, two_mul, Fin.sum_univ_add]
  simp [low,high,sum_add_distrib]

private theorem down_moment {m p : ℕ} (x y : Fin (m+m) → Fin 4) (i : Fin 3)
    (stable : ∀ j, mark (x j) i = mark (y j) i) (z : ZMod p) (hz : z^m = -1) :
    moment x y i z = 2 * moment (low x) (high x) i z := by
  have full : z^(m+m) = 1 := by rw [pow_add,hz]; ring
  calc moment x y i z = ∑ j : Fin (m+m), 2*((mark (x j) i : ZMod p)*z^j.val) := by
         apply sum_congr rfl
         intro j _
         rw [← stable j,pow_add,full]
         ring
       _ = 2 * ∑ j : Fin (m+m), (mark (x j) i : ZMod p)*z^j.val := (mul_sum ..).symm
       _ = 2 * moment (low x) (high x) i z := by
         congr 1
         rw [Fin.sum_univ_add]
         simp [moment, low, high, sum_add_distrib, Nat.add_comm]

private theorem exponent_double {E h p T t : ℕ} (hp : 0 < p)
    (power : E^h < p^t) (le : t ≤ T) : E^(h+h) < p^(2*T) := by
  rw [show h+h = h*2 by omega, pow_mul, Nat.mul_comm 2 T, pow_mul]
  exact Nat.pow_lt_pow_left (power.trans_le (Nat.pow_le_pow_right hp le)) (by decide)

private theorem half_mass {a : ℤ} (h : 2*a = 268435454) : a = 134217727 := by omega

private abbrev H := 268435456
private abbrev M := 536870912

/-- At the production half and quarter orders simultaneously, three disjoint
D-point fibers cannot have equal power sums at the two indicated populations
of odd nodes. The lower nodes test the even frequencies of the original domain. -/
theorem no_three_moments {p : ℕ} [Fact p.Prime] (hp : 2^158 ≤ p) (x y : Fin M → Fin 4)
    (sizes : ∀ i, (∑ j, (mark (x j) i+mark (y j) i)) = 268435454)
    (t : Fin M → ZMod p) (inj : Function.Injective t) (S : Finset (Fin M))
    (odd : ∀ j ∈ S, (t j)^M = -1) (sn : 50263626 ≤ S.card)
    (same : ∀ j ∈ S, ∀ i l, moment x y i (t j) = moment x y l (t j))
    (u : Fin H → ZMod p) (uinj : Function.Injective u) (T : Finset (Fin H))
    (quarter : ∀ j ∈ T, (u j)^H = -1) (tn : 24634900 ≤ T.card)
    (even : ∀ j ∈ T, ∀ i l, moment x y i (u j) = moment x y l (u j)) : False := by
  have pointcount : ∀ s t : Fin 4, occupied s + occupied t =
      (mark s 0+mark t 0)+(mark s 1+mark t 1)+(mark s 2+mark t 2) := by decide
  have mass : (∑ j, (occupied (x j)+occupied (y j))) = 3*(268435454 : ℤ) := by
    simp_rw [pointcount]
    rw [sum_add_distrib, sum_add_distrib, sizes, sizes, sizes]
    decide
  have hp2 : 2 < p := (by decide : 2 < 2^158).trans_le hp
  have hp' : 0 < p := (by decide : 0 < 2).trans hp2
  have first : (3*268435454)^(2^29) < p^(2*S.card) := by
    rw [show 3*268435454 = (805306362 : ℕ) by decide, show 2^29 = 268435456+268435456 by decide]
    exact @exponent_double 805306362 268435456 p S.card 50263626 hp' (thresholds hp).1 sn
  obtain ⟨i,l,hne,st⟩ := stable_pair (k := 29) (D := 268435454) x y mass t inj S odd same first
  have hmi := (down_mass (m := H) x y i (fun j => (st j).1)).symm.trans (sizes i)
  have hml := (down_mass (m := H) x y l (fun j => (st j).2)).symm.trans (sizes l)
  have two : (2 : ZMod p) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hp2
      ((ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h))
  have lower : 536870908^134217728 < p^24634900 :=
    compare (q := 1) (h := 29) (by decide) hp (by decide) (by decide)
  have second : (4*134217727)^(2^28) < p^(2*T.card) := by
    rw [show 4*134217727 = (536870908 : ℕ) by decide, show 2^28 = 134217728+134217728 by decide]
    exact @exponent_double 536870908 134217728 p T.card 24634900 hp' lower tn
  apply odd_pair (k := 28) (d := 134217727) (low x) (high x) i l hne
    (half_mass hmi) (half_mass hml) (by decide) u uinj T quarter _ second
  intro j hj
  have e := even j hj i l
  rw [down_moment (m := H) x y i (fun k => (st k).1) _ (quarter j hj),
    down_moment (m := H) x y l (fun k => (st k).2) _ (quarter j hj)] at e
  exact mul_left_cancel₀ two e

#print axioms no_three_moments
#print axioms stable_pair
#print axioms small_pair
#print axioms stable
#print axioms thresholds
#print axioms frequency_counts
end ProximityGap.QuarterSplitRamification
