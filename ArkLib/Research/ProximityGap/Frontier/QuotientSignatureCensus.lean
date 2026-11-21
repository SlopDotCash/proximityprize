/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-! # Weighted counts of dyadic locator signatures

At each node there are two inverse roots. Translating by the involution exchanges
sibling occupancies and fixes the root pair. The digit of a weighted count
recovers the exact number of masks at a specified subset cardinality.
-/

namespace ProximityGap.QuotientSignatureCensus
open Finset
open scoped BigOperators

/-- Required leaf sum for the original signature, with an optional rotated requirement. -/
inductive Tree where
  | leaf (v : ℕ) (w : Option ℕ)
  | fork (left right : Tree)
deriving Repr, DecidableEq

/-- Two independent inverse roots, encoded by their two selection bits. -/
abbrev Choice := Fin 4
def occ (q : Choice) : ℕ := if q = 0 then 0 else if q = 3 then 2 else 1

/-- Descendant choices under a node, omitting its own root pair. -/
def Tail : Tree → Type
  | .leaf _ _ => Unit
  | .fork l r => (Choice × Tail l) × (Choice × Tail r)

instance tailFintype : (t : Tree) → Fintype (Tail t)
  | .leaf _ _ => inferInstanceAs (Fintype Unit)
  | .fork l r =>
    let _ := tailFintype l
    let _ := tailFintype r
    inferInstanceAs (Fintype ((Choice × Tail l) × (Choice × Tail r)))

def size : (t : Tree) → Tail t → ℕ
  | .leaf _ _, _ => 0
  | .fork l r, c => occ c.1.1 + size l c.1.2 + (occ c.2.1 + size r c.2.2)

def accepted : (t : Tree) → ℕ → ℕ → Tail t → Bool
  | .leaf v w, x, y, _ => decide (x = v) && w.all (· == y)
  | .fork l r, x, y, c =>
    accepted l (x+occ c.1.1) (y+occ c.2.1) c.1.2 &&
    accepted r (x+occ c.2.1) (y+occ c.1.1) c.2.2

/-- Univariate weighted census on descendants. A selected site contributes one power. -/
def mass (B : ℕ) : Tree → ℕ → ℕ → ℕ
  | .leaf v w, x, y => if decide (x = v) && w.all (· == y) then 1 else 0
  | .fork l r, x, y => ∑ a : Choice, ∑ b : Choice,
     (B^(occ a) * B^(occ b)) *
       (mass B l (x+occ a) (y+occ b) * mass B r (x+occ b) (y+occ a))

private theorem combine_sum {L R : Type} [Fintype L] [Fintype R]
    (B : ℕ) (sl : L → ℕ) (sr : R → ℕ) (vl : L → Bool) (vr : R → Bool) (a b : ℕ) :
    (∑ c : L, ∑ d : R, if vl c && vr d then B^(a+sl c+(b+sr d)) else 0) =
    (B^a*B^b) * ((∑ c : L, if vl c then B^(sl c) else 0) *
      (∑ d : R, if vr d then B^(sr d) else 0)) := by
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  cases vl c <;> cases vr d <;> simp [pow_add]
  ac_rfl

/-- Exact semantics of the recurrence for every tree and choice of ancestor occupancies. -/
theorem mass_eq_sum (B : ℕ) (t : Tree) (x y : ℕ) :
    mass B t x y = ∑ c : Tail t, if accepted t x y c then B^(size t c) else 0 := by
  induction t generalizing x y with
  | leaf v w =>
    have hu : (univ : Finset (Tail (.leaf v w))).card = 1 := by
      change (@univ Unit _).card = 1
      simp
    simp [mass, accepted, size, hu]
  | fork l r il ir =>
    change _ = ∑ c : (Choice × Tail l) × (Choice × Tail r),
      if accepted l (x+occ c.1.1) (y+occ c.2.1) c.1.2 &&
        accepted r (x+occ c.2.1) (y+occ c.1.1) c.2.2
      then B^(occ c.1.1+size l c.1.2+(occ c.2.1+size r c.2.2)) else 0
    simp only [mass, Fintype.sum_prod_type, il, ir]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    exact (combine_sum B (size l) (size r) _ _ _ _).symm

/-- Include the top inverse pair, which is fixed by negating all quotient roots. -/
def fullMass (B : ℕ) (t : Tree) : ℕ := ∑ a : Choice, B^(occ a)*mass B t (occ a) (occ a)

def fullSize (t : Tree) (x : Choice × Tail t) : ℕ := occ x.1 + size t x.2
def fullAccepted (t : Tree) (x : Choice × Tail t) : Bool := accepted t (occ x.1) (occ x.1) x.2

theorem fullMass_eq_sum (B : ℕ) (t : Tree) : fullMass B t =
    ∑ x : Choice × Tail t, if fullAccepted t x then B^(fullSize t x) else 0 := by
  simp only [fullMass, fullAccepted, fullSize, Fintype.sum_prod_type, mass_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases he : accepted t (occ a) (occ a) b = true <;> simp [he, pow_add]

/-- A weighted finite count can be packed into a natural number without carries.
The digit at m counts selections having exactly m sites. -/
theorem digit_count {α : Type} (s : Finset α) (w : α → ℕ) (B m : ℕ) (hB : s.card < B) :
    (∑ x ∈ s, B^(w x)) / B^m % B = (s.filter fun x => w x = m).card := by
  classical
  have hpos : 0 < B := Nat.zero_lt_of_lt hB
  let low := ∑ x ∈ s, if w x < m then B^(w x) else 0
  let high := ∑ x ∈ s, if m < w x then B^(w x-(m+1)) else 0
  let middle := (s.filter fun x => w x = m).card
  have hm : middle = ∑ x ∈ s, if w x = m then 1 else 0 := by simp [middle, sum_boole]
  have expand : (∑ x ∈ s, B^(w x)) = low + (middle + high*B)*B^m := by
    dsimp only [low, high]
    rw [hm, Nat.add_mul, sum_mul, sum_mul, sum_mul, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    rcases lt_trichotomy (w x) m with hl | he | hh
    · simp [hl, hl.ne, not_lt.mpr hl.le]
    · simp [he]
    · simp only [not_lt_of_ge hh.le, hh.ne', hh, ite_false, ite_true, zero_mul, zero_add]
      nth_rw 1 [show w x = (w x-(m+1)) + (m+1) by omega]
      rw [pow_add, pow_succ']
      ac_rfl
  have hlow : low < B^m := by
    cases m with
    | zero => simp [low]
    | succ k =>
      calc
        low ≤ s.card * B^k := by
          apply sum_le_card_nsmul
          intro x _
          split
          · exact Nat.pow_le_pow_right hpos (by omega)
          · exact Nat.zero_le _
        _ < B * B^k := Nat.mul_lt_mul_of_pos_right hB (pow_pos hpos _)
        _ = B^(k+1) := (pow_succ' ..).symm
  have hmid : middle < B := (card_filter_le ..).trans_lt hB
  rw [expand, Nat.add_mul_div_right _ _ (pow_pos hpos _), Nat.div_eq_of_lt hlow, zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmid]

/-- Count masks with a prescribed subset size that realize all leaf conditions. -/
noncomputable def population (t : Tree) (m : ℕ) : ℕ := by
  classical
  exact (univ.filter fun x : Choice × Tail t => fullAccepted t x = true ∧ fullSize t x = m).card

/-- Extract a signature class without enumerating its root subsets. -/
theorem population_eq_digit (t : Tree) (m B : ℕ) (h : Fintype.card (Choice × Tail t) < B) :
    population t m = fullMass B t / B^m % B := by
  classical
  let s := univ.filter fun x : Choice × Tail t => fullAccepted t x = true
  have hs : s.card < B := (card_filter_le ..).trans_lt (by simpa using h)
  have hh := digit_count s (fullSize t) B m hs
  rw [fullMass_eq_sum, ← sum_filter]
  simpa [s, population, filter_filter] using hh.symm

/-- Duplicate a shape k times in the balanced binary tree. -/
def repeatTree : ℕ → Tree → Tree
  | 0, t => t
  | k+1, t => let u := repeatTree k t; .fork u u

/-- The number of selectable dyadic inverse pairs. -/
def nodes : Tree → ℕ
  | .leaf _ _ => 1
  | .fork l r => 1+nodes l+nodes r

theorem card_masks (t : Tree) : Fintype.card (Choice × Tail t) = 4^nodes t := by
  induction t with
  | leaf v w =>
    change Fintype.card (Fin 4 × Unit) = 4^1
    decide
  | fork l r il ir =>
    change Fintype.card (Choice × ((Choice × Tail l) × (Choice × Tail r))) = 4^(1+nodes l+nodes r)
    rw [Fintype.card_prod, Fintype.card_prod, il, ir, pow_add, pow_add, pow_one, Fintype.card_fin]
    ac_rfl

/-- Sum the four root-pair choices by occupancy. The two singleton orientations have equal weight. -/
def mix (B : ℕ) (z : ℕ → ℕ) := z 0 + 2*B*z 1 + B^2*z 2

theorem mix_eq (B : ℕ) (z : ℕ → ℕ) :
    mix B z = ∑ a : Choice, B^(occ a) * z (occ a) := by
  simp [mix, Fin.sum_univ_four, occ]
  ring

theorem mass_fork (B : ℕ) (l r : Tree) (x y : ℕ) :
    mass B (.fork l r) x y = mix B (fun a => mix B (fun b =>
      mass B l (x+a) (y+b) * mass B r (x+b) (y+a))) := by
  simp only [mass, mix_eq, Finset.mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  ac_rfl

/-- Row-major lookup in a finite square of ancestor occupancies. -/
def lookup (n : ℕ) (t : Array ℕ) (x y : ℕ) : ℕ := t.getD (x*(n+1)+y) 0

/-- Verify all finite entries without expanding descendant recurrence proofs. -/
def squareCheck (n : ℕ) (f g : ℕ → ℕ → ℕ) : Bool :=
  (List.range (n+1)).all fun x => (List.range (n+1)).all fun y => f x y == g x y

private theorem squareCheck_at {n : ℕ} {f g : ℕ → ℕ → ℕ} (h : squareCheck n f g = true)
    {x y : ℕ} (hx : x ≤ n) (hy : y ≤ n) : f x y = g x y := by
  unfold squareCheck at h
  exact eq_of_beq (List.all_eq_true.mp (List.all_eq_true.mp h x (List.mem_range.mpr (by omega)))
    y (List.mem_range.mpr (by omega)))

/-- Every entry equals the corresponding mass in the enumerative recurrence. -/
def Correct (B : ℕ) (t : Tree) (n : ℕ) (table : Array ℕ) : Prop :=
  ∀ x y, x ≤ n → y ≤ n → mass B t x y = lookup n table x y

theorem leaf_correct (B v : ℕ) (w : Option ℕ) (n : ℕ) (table : Array ℕ)
    (h : squareCheck n (fun x y => if decide (x=v) && w.all (· == y) then 1 else 0)
      (lookup n table) = true) : Correct B (.leaf v w) n table := by
  intro x y hx hy
  exact squareCheck_at h hx hy

/-- Compute the nine possible pairs of child occupancies. -/
def nodeEntry (B n : ℕ) (left right : Array ℕ) (x y : ℕ) : ℕ :=
  mix B fun a => mix B fun b =>
    lookup (n+2) left (x+a) (y+b) * lookup (n+2) right (x+b) (y+a)

theorem fork_correct (B : ℕ) (l r : Tree) (n : ℕ) (left right table : Array ℕ)
    (hl : Correct B l (n+2) left) (hr : Correct B r (n+2) right)
    (h : squareCheck n (nodeEntry B n left right) (lookup n table) = true) :
    Correct B (.fork l r) n table := by
  intro x y hx hy
  rw [mass_fork, ← squareCheck_at h hx hy]
  have entry (a b : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) :
      mass B l (x+a) (y+b) * mass B r (x+b) (y+a) =
      lookup (n+2) left (x+a) (y+b) * lookup (n+2) right (x+b) (y+a) := by
    rw [hl _ _ (by omega) (by omega), hr _ _ (by omega) (by omega)]
  simp only [nodeEntry, mix, entry 0 0 (by decide) (by decide),
    entry 0 1 (by decide) (by decide),
    entry 0 2 (by decide) (by decide),
    entry 1 0 (by decide) (by decide),
    entry 1 1 (by decide) (by decide),
    entry 1 2 (by decide) (by decide),
    entry 2 0 (by decide) (by decide),
    entry 2 1 (by decide) (by decide),
    entry 2 2 (by decide) (by decide)]

/-- Read the desired size digit from a complete root table. -/
theorem population_of_table (B m : ℕ) (t : Tree) (table : Array ℕ)
    (h : Correct B t 2 table) (room : 4^nodes t < B) : population t m =
    mix B (fun a => lookup 2 table a a) / B^m % B := by
  rw [population_eq_digit _ _ B (by rwa [card_masks]), fullMass,
    ← mix_eq B (fun a => mass B t a a)]
  simp only [mix, h 0 0 (by decide) (by decide), h 1 1 (by decide) (by decide),
    h 2 2 (by decide) (by decide)]

#print axioms population_eq_digit
#print axioms digit_count
#print axioms fullMass_eq_sum
end ProximityGap.QuotientSignatureCensus
