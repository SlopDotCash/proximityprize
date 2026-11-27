/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.HalfBlowupGaussWindow
import Mathlib.Algebra.Order.Chebyshev

/-! # Interpolation after choosing up to five rich cores -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.CoreMultiplicityMCA

open Finset Polynomial SecondPrimeQuarticInterpolation HalfSuccessorJetInterpolation
open HalfBlowupGaussWindow (rowCount columnCount card_rows card_columns)

abbrev n : ℕ := 2 ^ 30
abbrev errors (half : Bool) : ℕ := if half then 313250000 else 534425000
abbrev d (half : Bool) : ℕ := if half then 536870911 else 268435455
abbrev t (half : Bool) : ℕ := n - errors half
abbrev core (half : Bool) : ℕ := t half - (errors half / 500000 + 1)

structure Shape where
  order : ℕ
  plane : ℕ
  drop : ℕ

/-- Primary and companion interpolation shapes at the two production radii. -/
private def baseShape (half companion : Bool) (h : Fin 6) : Shape :=
  let drop := if h.val = 0 then 0 else if companion then 2 else 1
  match half, companion with
  | true, false => ⟨90, ![266426, 260278, 254455, 248957, 243779, 238921] h, drop⟩
  | true, true => ⟨174, ![15258, 15019, 14796, 14589, 14400, 14227] h, drop⟩
  | false, false => ⟨55, ![181766, 176938, 172281, 167795, 163477, 159325] h, drop⟩
  | false, true => ⟨108, ![8175, 8028, 7886, 7750, 7619, 7494] h, drop⟩

def weight (half : Bool) (h : Fin 6) (k : Shape) : ℕ := k.order * t half - h.val * k.drop * d half
def ordinate (half : Bool) (h : Fin 6) (k : Shape) : ℕ := (weight half h k - 1) / d half
/-- The three surfaces use lanes zero, one and two for the primary, companion and auxiliary. -/
def shape (half : Bool) (lane : Fin 3) (h : Fin 6) : Shape :=
  let k := baseShape half (lane == 1) h
  if lane = 2 then {k with plane := 1000000} else k

def ordCap (half : Bool) (lane : Fin 3) (h : Fin 6) : ℕ :=
  ordinate half h (shape half lane h) - if lane = 2 ∧ half = false then 1 else 0

def weightCap (half : Bool) (lane : Fin 3) (h : Fin 6) : ℕ :=
  if lane = 2 then
    if half then ![68443081893, 67906192016, 67369302375, 66832412975, 66295523815, 65758634897] h
    else ![29662395881, 29393953144, 29125510544, 28857068083, 28588625763, 28320183583] h
  else weight half h (shape half lane h)

private def saving (k : Shape) := rowCount k.plane k.order - rowCount k.plane (k.order - k.drop)
private def pairCost (k : Shape) := k.drop ^ 2 * (k.plane + 1)

set_option maxRecDepth 8192 in
private theorem local_rows : ∀ (half : Bool) (lane : Fin 3), ∀ h : Fin 6, ∀ m : Fin (h.val + 1),
    let k := shape half lane h
    rowCount k.plane (k.order - k.drop * m.val) + m.val * saving k ≤
      rowCount k.plane k.order + m.val.choose 2 * pairCost k := by decide +kernel

set_option maxRecDepth 8192 in
/-- Every conditioned monomial space has a strictly positive dimension surplus. -/
theorem rank_room : ∀ (half : Bool) (lane : Fin 3), ∀ h : Fin 6,
    let k := shape half lane h
    k.drop * h.val ≤ k.order ∧ k.order ≤ k.plane + 1 ∧ 0 < weightCap half lane h ∧
      weightCap half lane h ≤ weight half h k ∧
      n * rowCount k.plane k.order + h.val.choose 2 * d half * pairCost k <
        columnCount k.plane (ordCap half lane h) (d half) (weightCap half lane h) +
          h.val * core half * saving k := by decide +kernel

/-- A nonzero surface has the prescribed jets on the received lines and vanishes
on any witnessing section outside the chosen polynomial heads. The two core incidence
hypotheses follow by summing the individual core sizes and their pairwise overlaps. -/
theorem surfaces {I F : Type} [Fintype I] [Field F] (dom : I ↪ F) (u v : I → F)
    (hn : Fintype.card I = n) (half : Bool) (lane : Fin 3) (h : Fin 6) (own : I → Fin (h.val + 1))
    (coverage : h.val * core half ≤ ∑ x, (own x).val)
    (pairs : (∑ x, (own x).val.choose 2) ≤ h.val.choose 2 * d half) :
    let k := shape half lane h
    ∃ c : Monomials k.plane (ordCap half lane h) (d half) (weightCap half lane h) → F, c ≠ 0 ∧
      (∀ x i j, i + j < k.order - k.drop * (own x).val →
        ∑ m, C (c m) * jetTerm m i j (dom x) (u x) (v x) = 0) ∧
      ∀ g : F, ∀ q : F[X], q.natDegree ≤ d half → ∀ S : Finset I, t half ≤ S.card →
        (∑ x ∈ S, (own x).val) ≤ h.val * d half →
        (∀ x ∈ S, q.eval (dom x) = u x + g * v x) → specialize c g q = 0 := by
  classical
  dsimp only
  let k := shape half lane h
  obtain ⟨hdrop, hs, hw, hcap, hstrict⟩ := rank_room half lane h
  let localOrder x := k.order - k.drop * (own x).val
  have room : Fintype.card ((x : I) × JetRows k.plane (localOrder x)) <
      Fintype.card (Monomials k.plane (ordCap half lane h) (d half) (weightCap half lane h)) := by
    rw [Fintype.card_sigma, card_columns]
    simp_rw [card_rows]
    have total := sum_le_sum (s := univ) (fun x _ => local_rows half lane h (own x))
    simp only [sum_add_distrib, ← sum_mul, sum_const, card_univ, smul_eq_mul, hn] at total
    have left := Nat.mul_le_mul_right (saving k) coverage
    have right := Nat.mul_le_mul_right (pairCost k) pairs
    change (∑ x, rowCount k.plane (k.order - k.drop * (own x).val)) < _
    dsimp only [k] at left right ⊢
    omega
  obtain ⟨c, nz, jet, capture⟩ := exists_order_surface dom u v localOrder hw
    (fun x => (Nat.sub_le _ _).trans hs) room
  refine ⟨c, nz, jet, ?_⟩
  intro g q hq S hc hov hag
  apply capture g q hq S _ hag
  have hn' x : k.drop * (own x).val ≤ k.order :=
    (Nat.mul_le_mul_left _ (Nat.le_of_lt_succ (own x).isLt)).trans hdrop
  have add := sum_congr (s₁ := S) rfl (fun x _ => Nat.sub_add_cancel (hn' x))
  rw [sum_add_distrib, ← mul_sum] at add
  simp only [sum_const, smul_eq_mul] at add
  have low := Nat.mul_le_mul_left k.order hc
  have high := Nat.mul_le_mul_left k.drop hov
  rw [Nat.mul_comm S.card k.order] at add
  apply hcap.trans
  change k.order * t half - h.val * k.drop * d half ≤ ∑ x ∈ S, (k.order - k.drop * (own x).val)
  rw [show h.val * k.drop * d half = k.drop * (h.val * d half) by ring]
  omega

/-- A largest-capacity-first fill has at most one partially filled slot and
preserves the order of capacities. Its square mass therefore loses at most
one quarter of the square of the largest possible capacity. -/
theorem greedy_square_mass {I : Type*} (s : Finset I)
    (cap fill : I → ℚ) (p : I) (hp : p ∈ s) (b : ℚ)
    (ordered : MonovaryOn fill cap s)
    (full : ∀ i ∈ s, i ≠ p → fill i = 0 ∨ fill i = cap i)
    (nonneg : 0 ≤ fill p) (bounded : cap p ≤ b) :
    (∑ i ∈ s, fill i) * (∑ i ∈ s, cap i) ≤
      (s.card : ℚ) * ((∑ i ∈ s, fill i ^ 2) + b ^ 2 / 4) := by
  classical
  have loss (i) (hi : i ∈ s) :
      fill i * cap i ≤ fill i ^ 2 + if i = p then b ^ 2 / 4 else 0 := by
    by_cases hip : i = p
    · subst i
      simp only [ite_true]
      have hcap := mul_le_mul_of_nonneg_left bounded nonneg
      nlinarith [sq_nonneg (2 * fill p - b)]
    · rcases full i hi hip with h | h <;> simp [hip, h, pow_two]
  have total := sum_le_sum loss
  simp only [sum_add_distrib, sum_ite_eq', hp, ite_true] at total
  exact ordered.sum_mul_sum_le_card_mul_sum.trans
    (mul_le_mul_of_nonneg_left total (Nat.cast_nonneg _))

/-- Interpolating the two endpoint prices gives a uniform square-mass bonus
when the agreement sites receive the minimal permitted mass plus a fraction of a full order. -/
theorem fill_bonus (a c x : ℚ) (hx : 0 ≤ x) (hy : x ≤ 1) :
    min a c ≤ a * x + c * (1 - x) := by
  have left := mul_le_mul_of_nonneg_right (min_le_left a c) hx
  have right := mul_le_mul_of_nonneg_right (min_le_right a c) (sub_nonneg.mpr hy)
  linarith

/-- Combine a coprime auxiliary resultant, an improved common-factor price and
the unconditional two-surface price into a single linear bound in both degrees. -/
theorem auxiliary_price (p m b a c x y s v z : ℚ) (hb : 0 ≤ b)
    (hv : v < x) (hx : x ≤ a) (hy : y ≤ z) (hz : 0 ≤ z)
    (slope : (a - x) * s ≤ (z - c) * (x - v))
    (original : p ≤ a * m + c * b)
    (third : p ≤ max (x * m + y * b) (v * m + s * b)) :
    p ≤ x * m + z * b := by
  by_cases hm : s * b ≤ (x - v) * m
  · apply third.trans (max_le _ _)
    · exact add_le_add_right (mul_le_mul_of_nonneg_right hy hb) _
    · nlinarith [mul_nonneg hz hb]
  · have cut : (a - x) * ((x - v) * m) ≤ (a - x) * (s * b) :=
      mul_le_mul_of_nonneg_left (le_of_not_ge hm) (sub_nonneg.mpr hx)
    have hline := mul_le_mul_of_nonneg_right slope hb
    have hcost : (a - x) * m ≤ (z - c) * b := by
      by_contra! bad
      have strict := mul_lt_mul_of_pos_right bad (sub_pos.mpr hv)
      nlinarith
    linarith only [original, hcost]

#print axioms surfaces
#print axioms rank_room
#print axioms greedy_square_mass
#print axioms fill_bonus
#print axioms auxiliary_price

end ArkLib.ProximityGap.Frontier.CoreMultiplicityMCA
